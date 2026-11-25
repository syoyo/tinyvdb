/* Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
   SPDX-License-Identifier: Apache-2.0 */

/* Differential harness: the `mesh_triangle_double` double-precision fallback
 * of `tri_closest_point_c` (src/tinyvdb_mesh.c). This driver #includes
 * tinyvdb_mesh.c so that the *real* static `mesh_triangle_double`, `sub_c`,
 * `dot_c`, `cross_c` and friends are used -- nothing in src/ is modified.
 *
 * `mesh_triangle_double` computes the closest point entirely in double and
 * only casts the three result components to float at the return. The float32
 * kernel `tri_closest_point_c` diverts to it whenever a float predicate is
 * non-finite (overflow) or a degenerate equality holds. This driver builds a
 * corpus of such cases (huge coordinates, overflowing dot products, collinear
 * / identical vertices) and dumps, per case:
 *
 *   case <id> <label> p <%08x> <%08x> <%08x> a ... c ... d <%016x> <%016x>
 *        <%016x> f <%08x> <%08x> <%08x> v <%08x> reason <r> branch <b> txok <t>
 *
 * where:
 *   p/a/b/c  = float32 bit patterns of the query and the three vertices
 *              (the exact inputs of the double computation);
 *   d        = the three double closest-point components BEFORE the (float)
 *              cast, as raw IEEE-754 binary64 bit patterns (via memcpy);
 *   f        = the float32 bit patterns returned by the REAL
 *              `mesh_triangle_double` (its final (float) cast);
 *   v        = the final float32 voxel value, computed exactly as
 *              `mesh_fill_rows` does for this single triangle:
 *              d = point - cp; dsq = dot(d,d); dist = sqrtf(dsq);
 *              dir = dot(d, cross(b-a, c-a)); v = clamp(dir >= 0 ? dist :
 *              -dist, -band, band);
 *   reason   = which float32 predicate diverts `tri_closest_point_c` into the
 *              fallback (0 = none, 1..10 = the ten `mesh_triangle_double`
 *              call sites in source order); computed here by an instrumented
 *              transcription of those predicates;
 *   branch   = which branch of `mesh_triangle_double` was taken
 *              (0 = degenerate-normal edge loop, 1 = vert a, 2 = vert b,
 *               3 = edge ab, 4 = vert c, 5 = edge ac, 6 = edge bc,
 *               7 = face interior);
 *   txok     = 1 iff the instrumented transcription's float32 result equals
 *              the real function's result (validates the transcription).
 *
 * The Lean twin (Vdb.MeshSdfDoubleCheck) decodes d to an exact rational,
 * applies its own IEEE round-to-nearest-even binary64 -> binary32 conversion
 * and checks it equals f bit-for-bit; it also recomputes the closest point in
 * exact rationals from p/a/b/c and compares with d within a documented
 * tolerance. No secrets, no generated binaries.
 *
 * Build: cc -O2 -std=c11 -I<repo>/src meshsdf_double_c.c <support> -lm -o ...
 */
#if !defined(_WIN32) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 199309L
#endif
#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_mesh.c"

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned fbits(float v) { unsigned w; memcpy(&w, &v, 4); return w; }
static uint64_t dbits(double v) { uint64_t w; memcpy(&w, &v, 8); return w; }

/* Which float32 predicate would divert tri_closest_point_c into the double
 * fallback? Line-for-line transcription of its predicate order. */
static int f32_fallback_reason(tvdb_vec3f p, tvdb_vec3f a, tvdb_vec3f b, tvdb_vec3f c) {
    tvdb_vec3f ab = sub_c(b, a), ac = sub_c(c, a), ap = sub_c(p, a);
    float d1 = dot_c(ab, ap), d2 = dot_c(ac, ap);
    if (!isfinite(d1) || !isfinite(d2)) return 1;
    if (d1 <= 0.0f && d2 <= 0.0f) return 0;
    tvdb_vec3f bp = sub_c(p, b);
    float d3 = dot_c(ab, bp), d4 = dot_c(ac, bp);
    if (!isfinite(d3) || !isfinite(d4)) return 2;
    if (d3 >= 0.0f && d4 <= d3) return 0;
    float vc = d1 * d4 - d3 * d2;
    if (!isfinite(vc)) return 3;
    if (vc <= 0.0f && d1 >= 0.0f && d3 <= 0.0f) { if (d1 == d3) return 4; return 0; }
    tvdb_vec3f cp = sub_c(p, c);
    float d5 = dot_c(ab, cp), d6 = dot_c(ac, cp);
    if (!isfinite(d5) || !isfinite(d6)) return 5;
    if (d6 >= 0.0f && d5 <= d6) return 0;
    float vb = d5 * d2 - d1 * d6;
    if (!isfinite(vb)) return 6;
    if (vb <= 0.0f && d2 >= 0.0f && d6 <= 0.0f) { if (d2 == d6) return 7; return 0; }
    float va = d3 * d6 - d5 * d4;
    if (!isfinite(va)) return 8;
    if (va <= 0.0f && (d4 - d3) >= 0.0f && (d5 - d6) >= 0.0f) {
        if ((d4 - d3) + (d5 - d6) == 0) return 9;
        return 0;
    }
    if (!isfinite(va + vb + vc) || va + vb + vc <= 0) return 10;
    return 0;
}

/* Line-for-line transcription of the real mesh_triangle_double, recording the
 * three double components r[3] before their (float) cast and the branch tag.
 * Returns the same float32 vector as the real function. */
static tvdb_vec3f double_dump(tvdb_vec3f p, tvdb_vec3f a, tvdb_vec3f b, tvdb_vec3f c,
                              double *r, int *branch) {
    double pa[3] = {(double)p.x - a.x, (double)p.y - a.y, (double)p.z - a.z};
    double ab[3] = {(double)b.x - a.x, (double)b.y - a.y, (double)b.z - a.z},
           ac[3] = {(double)c.x - a.x, (double)c.y - a.y, (double)c.z - a.z};
    double normal[3] = {ab[1] * ac[2] - ab[2] * ac[1], ab[2] * ac[0] - ab[0] * ac[2],
                        ab[0] * ac[1] - ab[1] * ac[0]};
    if (!mesh_dot3d(normal, normal)) {
        const tvdb_vec3f v[3] = {a, b, c};
        double best = INFINITY;
        for (int e = 0; e < 3; ++e) {
            tvdb_vec3f x = v[e], y = v[(e + 1) % 3];
            double d[3] = {(double)y.x - x.x, (double)y.y - x.y, (double)y.z - x.z};
            double q[3] = {(double)p.x - x.x, (double)p.y - x.y, (double)p.z - x.z},
                   length = mesh_dot3d(d, d);
            double t = length ? mesh_dot3d(q, d) / length : 0;
            if (t < 0) t = 0;
            if (t > 1) t = 1;
            double rr[3] = {x.x + t * d[0], x.y + t * d[1], x.z + t * d[2]};
            double delta[3] = {(double)p.x - rr[0], (double)p.y - rr[1], (double)p.z - rr[2]},
                   distance = mesh_dot3d(delta, delta);
            if (distance < best) { best = distance; r[0] = rr[0]; r[1] = rr[1]; r[2] = rr[2]; }
        }
        *branch = 0;
        return (tvdb_vec3f){(float)r[0], (float)r[1], (float)r[2]};
    }
    double d1 = mesh_dot3d(ab, pa), d2 = mesh_dot3d(ac, pa);
    if (d1 <= 0 && d2 <= 0) {
        *branch = 1; r[0] = a.x; r[1] = a.y; r[2] = a.z; return a;
    }
    double pb[3] = {(double)p.x - b.x, (double)p.y - b.y, (double)p.z - b.z};
    double d3 = mesh_dot3d(ab, pb), d4 = mesh_dot3d(ac, pb);
    if (d3 >= 0 && d4 <= d3) {
        *branch = 2; r[0] = b.x; r[1] = b.y; r[2] = b.z; return b;
    }
    double vc = d1 * d4 - d3 * d2;
    if (vc <= 0 && d1 >= 0 && d3 <= 0) {
        double t = d1 / (d1 - d3);
        *branch = 3;
        r[0] = a.x + t * ab[0]; r[1] = a.y + t * ab[1]; r[2] = a.z + t * ab[2];
        return (tvdb_vec3f){(float)r[0], (float)r[1], (float)r[2]};
    }
    double pc[3] = {(double)p.x - c.x, (double)p.y - c.y, (double)p.z - c.z};
    double d5 = mesh_dot3d(ab, pc), d6 = mesh_dot3d(ac, pc);
    if (d6 >= 0 && d5 <= d6) {
        *branch = 4; r[0] = c.x; r[1] = c.y; r[2] = c.z; return c;
    }
    double vb = d5 * d2 - d1 * d6;
    if (vb <= 0 && d2 >= 0 && d6 <= 0) {
        double t = d2 / (d2 - d6);
        *branch = 5;
        r[0] = a.x + t * ac[0]; r[1] = a.y + t * ac[1]; r[2] = a.z + t * ac[2];
        return (tvdb_vec3f){(float)r[0], (float)r[1], (float)r[2]};
    }
    double va = d3 * d6 - d5 * d4;
    if (va <= 0 && d4 - d3 >= 0 && d5 - d6 >= 0) {
        double t = (d4 - d3) / ((d4 - d3) + (d5 - d6));
        *branch = 6;
        r[0] = b.x + t * ((double)c.x - b.x);
        r[1] = b.y + t * ((double)c.y - b.y);
        r[2] = b.z + t * ((double)c.z - b.z);
        return (tvdb_vec3f){(float)r[0], (float)r[1], (float)r[2]};
    }
    double v = vb / (va + vb + vc), w = vc / (va + vb + vc);
    *branch = 7;
    r[0] = a.x + v * ab[0] + w * ac[0];
    r[1] = a.y + v * ab[1] + w * ac[1];
    r[2] = a.z + v * ab[2] + w * ac[2];
    return (tvdb_vec3f){(float)r[0], (float)r[1], (float)r[2]};
}

static void emit(int id, const char *label, tvdb_vec3f p, tvdb_vec3f a, tvdb_vec3f b,
                 tvdb_vec3f c, float band) {
    int reason = f32_fallback_reason(p, a, b, c);
    double r[3] = {0, 0, 0};
    int branch = -1;
    tvdb_vec3f cp = double_dump(p, a, b, c, r, &branch);
    tvdb_vec3f real = mesh_triangle_double(p, a, b, c);
    int txok = (fbits(cp.x) == fbits(real.x) && fbits(cp.y) == fbits(real.y) &&
                fbits(cp.z) == fbits(real.z)) ? 1 : 0;

    /* Final voxel value, exactly the mesh_fill_rows per-voxel chain. */
    tvdb_vec3f dd = sub_c(p, cp);
    float dsq = dot_c(dd, dd);
    float dist = sqrtf(dsq);
    float dir = dot_c(dd, cross_c(sub_c(b, a), sub_c(c, a)));
    float vv = dir >= 0.0f ? dist : -dist;
    if (vv > band) vv = band;
    if (vv < -band) vv = -band;

    printf("case %d %s p %08x %08x %08x a %08x %08x %08x b %08x %08x %08x c %08x %08x %08x "
           "d %016llx %016llx %016llx f %08x %08x %08x v %08x reason %d branch %d txok %d "
           "band %08x\n",
           id, label, fbits(p.x), fbits(p.y), fbits(p.z), fbits(a.x), fbits(a.y), fbits(a.z),
           fbits(b.x), fbits(b.y), fbits(b.z), fbits(c.x), fbits(c.y), fbits(c.z),
           (unsigned long long)dbits(r[0]), (unsigned long long)dbits(r[1]),
           (unsigned long long)dbits(r[2]), fbits(real.x), fbits(real.y), fbits(real.z),
           fbits(vv), reason, branch, txok, fbits(band));
}

int main(void) {
    const float BIG = 1.0e30f;
    const float band = 1.0e30f;
    /* Curated cases: overflow, vc-overflow, degenerate normal, controls. */
    emit(0, "ovf_d1a", (tvdb_vec3f){BIG, BIG, 0}, (tvdb_vec3f){0, 0, 0},
         (tvdb_vec3f){BIG, 0, 0}, (tvdb_vec3f){0, BIG, 0}, band);
    emit(1, "ovf_d1b", (tvdb_vec3f){-BIG, BIG, 0}, (tvdb_vec3f){0, 0, 0},
         (tvdb_vec3f){-BIG, 0, 0}, (tvdb_vec3f){0, BIG, 0}, band);
    emit(2, "ovf_d2", (tvdb_vec3f){BIG, 0, BIG}, (tvdb_vec3f){0, 0, 0},
         (tvdb_vec3f){1, 0, 0}, (tvdb_vec3f){0, 0, BIG}, band);
    emit(3, "ovf_vc", (tvdb_vec3f){1.0e18f, -1.0e18f, 0}, (tvdb_vec3f){0, 0, 0},
         (tvdb_vec3f){1.0e19f, 0, 0}, (tvdb_vec3f){0, 1.0e19f, 0}, band);
    emit(4, "ovf_vc2", (tvdb_vec3f){-2.0e18f, 1.0e18f, 0}, (tvdb_vec3f){0, 0, 0},
         (tvdb_vec3f){1.0e19f, 0, 0}, (tvdb_vec3f){0, 1.0e19f, 0}, band);
    emit(5, "degen_collinear", (tvdb_vec3f){BIG, BIG, 0}, (tvdb_vec3f){0, 0, 0},
         (tvdb_vec3f){BIG, 0, 0}, (tvdb_vec3f){2 * BIG, 0, 0}, band);
    emit(6, "degen_identical", (tvdb_vec3f){BIG, BIG, 0}, (tvdb_vec3f){BIG, 0, 0},
         (tvdb_vec3f){BIG, 0, 0}, (tvdb_vec3f){BIG, 0, 0}, band);
    emit(7, "degen_line_mid", (tvdb_vec3f){0, BIG, 0}, (tvdb_vec3f){-BIG, 0, 0},
         (tvdb_vec3f){BIG, 0, 0}, (tvdb_vec3f){0, 0, 0}, band);

    /* Eight seeded huge-coordinate overflow cases with a known edge-bc result
     * t = (f1 - f0 + 1)/2, giving a spread of non-trivial double values to
     * stress the double -> float32 rounding. */
    uint64_t st = 0x9e3779b97f4a7c15ULL;
    for (int i = 0; i < 8; ++i) {
        st = st * 6364136223846793005ULL + 1442695040888963407ULL;
        double u0 = (double)(st >> 33) / (double)(1ULL << 31); /* 0 .. ~2 */
        st = st * 6364136223846793005ULL + 1442695040888963407ULL;
        double u1 = (double)(st >> 33) / (double)(1ULL << 31);
        float f0 = (float)(0.6 + 0.8 * (u0 - (long)u0)); /* 0.6 .. 1.4 */
        float f1 = (float)(0.6 + 0.8 * (u1 - (long)u1));
        emit(8 + i, "ovf_rnd", (tvdb_vec3f){BIG * f0, BIG * f1, 0}, (tvdb_vec3f){0, 0, 0},
             (tvdb_vec3f){BIG, 0, 0}, (tvdb_vec3f){0, BIG, 0}, band);
    }
    return 0;
}
