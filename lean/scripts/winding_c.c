/* Executable check: generalized winding number on closed meshes.
 *
 * For a closed, outward-oriented mesh the winding number is 1 strictly inside
 * and 0 strictly outside (topological degree). This pins the *executable*
 * claim of the C implementation (src/tinyvdb_winding.c) on the two closed
 * meshes used by the mesh→SDF differential harness:
 *   mesh 0  cube         8 verts,  12 faces
 *   mesh 1  icosahedron 12 verts,  20 faces
 *
 * For 48 seeded-random interior sample points (box [-0.45, 0.45]^3) and 48
 * seeded-random exterior sample points (radial shell [2.35, 3.0]) per mesh,
 * plus the origin, it evaluates BOTH kinds (TVDB_WINDING_EXACT and
 * TVDB_WINDING_FAST) and prints the values as double bit patterns:
 *
 *   pt <mesh> <0=in 1=out|2=origin> <x bits> <y bits> <z bits> <we bits> <wf bits>
 *
 * `lean/scripts/check_winding.sh` drives this and the Lean checker
 * (Vdb.WindingCheck), which asserts |w − expected| ≤ 1e-9 (EXACT, both
 * classes) and |w_f − expected| ≤ 1e-2 (FAST).
 *
 * Build: cc -O2 -std=c11 -I<repo>/src winding_c.c <sources...> -lm -o winding_c
 */
#if !defined(_WIN32) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 199309L
#endif
#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_mesh.h"
#include "tinyvdb_winding.h"

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint64_t g_state;
static uint64_t next_rand(void) {
    g_state = g_state * 6364136223846793005ULL + 1442695040888963407ULL;
    return g_state >> 33;
}

static unsigned long long bits_of(double v) {
    unsigned long long w;
    memcpy(&w, &v, 8);
    return w;
}

static void dump_pt(int mesh, int kind, const double p[3], double we, double wf) {
    printf("pt %d %d %016llx %016llx %016llx %016llx %016llx\n", mesh, kind,
           bits_of(p[0]), bits_of(p[1]), bits_of(p[2]), bits_of(we), bits_of(wf));
}

/* Outward-orientation fix-up (same rule as meshsdf_c.c). */
static void fix_orientation(tvdb_vec3f* verts, tvdb_triangle* faces, size_t n) {
    for (size_t f = 0; f < n; ++f) {
        tvdb_vec3f a = verts[faces[f].v0], b = verts[faces[f].v1], c = verts[faces[f].v2];
        double ab[3] = {(double)b.x - a.x, (double)b.y - a.y, (double)b.z - a.z},
               ac[3] = {(double)c.x - a.x, (double)c.y - a.y, (double)c.z - a.z};
        double nrm[3] = {ab[1] * ac[2] - ab[2] * ac[1], ab[2] * ac[0] - ab[0] * ac[2],
                         ab[0] * ac[1] - ab[1] * ac[0]};
        double cx = (a.x + b.x + c.x) / 3.0, cy = (a.y + b.y + c.y) / 3.0,
               cz = (a.z + b.z + c.z) / 3.0;
        double d = nrm[0] * cx + nrm[1] * cy + nrm[2] * cz;
        if (d < 0.0) {
            uint32_t t = faces[f].v1;
            faces[f].v1 = faces[f].v2;
            faces[f].v2 = t;
        }
    }
}

static void run_mesh(int id, tvdb_triangle_mesh* m) {
    tvdb_winding_t* wExact = NULL;
    tvdb_winding_t* wFast = NULL;
    tvdb_error_t err;
    if (tvdb_winding_create(m, TVDB_WINDING_EXACT, &wExact, &err) != TVDB_OK) {
        fprintf(stderr, "winding_create EXACT failed for mesh %d\n", id);
        exit(2);
    }
    if (tvdb_winding_create(m, TVDB_WINDING_FAST, &wFast, &err) != TVDB_OK) {
        fprintf(stderr, "winding_create FAST failed for mesh %d\n", id);
        exit(2);
    }
    for (int i = 0; i < 48; ++i) {
        double p[3];
        for (int k = 0; k < 3; ++k)
            p[k] = 0.9 * ((double)(next_rand() % 100000) / 100000.0 - 0.5);
        dump_pt(id, 0, p, tvdb_winding_eval(wExact, p), tvdb_winding_eval(wFast, p));
    }
    for (int i = 0; i < 48; ++i) {
        double p[3];
        do {
            for (int k = 0; k < 3; ++k)
                p[k] = 6.0 * ((double)(next_rand() % 100000) / 100000.0 - 0.5);
        } while (hypot(hypot(p[0], p[1]), p[2]) < 2.35);
        dump_pt(id, 1, p, tvdb_winding_eval(wExact, p), tvdb_winding_eval(wFast, p));
    }
    {
        double p[3] = {0.0, 0.0, 0.0};
        dump_pt(id, 2, p, tvdb_winding_eval(wExact, p), tvdb_winding_eval(wFast, p));
    }
    tvdb_winding_destroy(wExact);
    tvdb_winding_destroy(wFast);
}

int main(void) {
    g_state = 0x9e3779b97f4a7c15ULL;
    {
        const tvdb_vec3f verts[8] = {
            {-1.0f, -1.0f, -1.0f}, {1.0f, -1.0f, -1.0f}, {1.0f, 1.0f, -1.0f}, {-1.0f, 1.0f, -1.0f},
            {-1.0f, -1.0f, 1.0f},  {1.0f, -1.0f, 1.0f},  {1.0f, 1.0f, 1.0f},  {-1.0f, 1.0f, 1.0f}};
        tvdb_triangle faces[12] = {
            {0, 2, 1}, {0, 3, 2}, {4, 5, 6}, {4, 6, 7}, {0, 4, 7}, {0, 7, 3},
            {1, 2, 6}, {1, 6, 5}, {0, 1, 5}, {0, 5, 4}, {3, 7, 6}, {3, 6, 2}};
        fix_orientation((tvdb_vec3f*)verts, faces, 12);
        tvdb_triangle_mesh m = {(tvdb_vec3f*)verts, 8, 8, faces, 12, 12};
        run_mesh(0, &m);
    }
    {
        const float phi = 1.6180339887498949f;
        tvdb_vec3f verts[12] = {
            {-1.0f, phi, 0.0f}, {1.0f, phi, 0.0f},   {-1.0f, -phi, 0.0f}, {1.0f, -phi, 0.0f},
            {0.0f, -1.0f, phi}, {0.0f, 1.0f, phi},   {0.0f, -1.0f, -phi}, {0.0f, 1.0f, -phi},
            {phi, 0.0f, -1.0f}, {phi, 0.0f, 1.0f},   {-phi, 0.0f, -1.0f}, {-phi, 0.0f, 1.0f}};
        tvdb_triangle faces[20] = {
            {0, 11, 5},  {0, 5, 1},   {0, 1, 7},   {0, 7, 10}, {0, 10, 11},
            {1, 5, 9},   {5, 11, 4},  {11, 10, 2}, {10, 7, 6}, {7, 1, 8},
            {3, 9, 4},   {3, 4, 2},   {3, 2, 6},   {3, 6, 8},  {3, 8, 9},
            {4, 9, 5},   {2, 4, 11},  {6, 2, 10},  {8, 6, 7},  {9, 8, 1}};
        fix_orientation(verts, faces, 20);
        tvdb_triangle_mesh m = {verts, 12, 12, faces, 20, 20};
        run_mesh(1, &m);
    }
    return 0;
}
