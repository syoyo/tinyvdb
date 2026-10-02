/* Audit regressions: each case reproduces a defect found in review. */
#include <math.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Make any UBSan report (e.g. float-cast-overflow) fatal in sanitizer builds so
   undefined conversions fail this test instead of only printing a diagnostic.
   Unused when the runtime is absent. */
const char *__ubsan_default_options(void);
const char *__ubsan_default_options(void) { return "halt_on_error=1:print_stacktrace=1"; }

/* Compile tinyvdb_ops.c into this test with a failing malloc (the library has
   no production allocator hooks; same approach as test_alloc_failure.c). The
   definitions here satisfy every ops symbol, so the archive copy is not used. */
static int allocation_count, fail_at;
static void *failing_malloc(size_t n) {
    int call;
    #pragma omp atomic capture
    call = ++allocation_count;
    return call == fail_at ? NULL : malloc(n);
}
#define malloc failing_malloc
#include "../src/tinyvdb_ops.c"
#undef malloc

#include "tinyvdb_levelset.h"
#include "tinyvdb_ray.h"
#include "tinyvdb_render.h"
#include "tinyvdb_stats.h"
#include "tinyvdb_tsdf.h"

static int failures;
#define CHECK(c) do { if (!(c)) { fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #c); ++failures; } } while (0)

/* 1. In-place MacCormack/BFECC: an internal scratch allocation failure must
      leave `result` (aliasing `field`) unchanged, not copy uninitialized tmp. */
static void test_advect_inplace_scratch_failure(void) {
    for (int scheme = TVDB_ADVECT_MACCORMACK; scheme <= TVDB_ADVECT_BFECC; ++scheme) {
        tvdb_dense_grid f; tvdb_dense_grid_init(&f, 8, 8, 8);
        tvdb_dense_vec_grid v; tvdb_dense_vec_grid_init(&v, 8, 8, 8);
        CHECK(f.data && v.data);
        if (!f.data || !v.data) { tvdb_dense_grid_free(&f); tvdb_dense_vec_grid_free(&v); return; }
        for (int i = 0; i < 512; ++i) { f.data[i] = (float)i; v.data[3 * i] = 0.5f; }
        /* ops.c allocation #1 is the in-place scratch, #2 the clamp bounds. */
        allocation_count = 0; fail_at = 2;
        tvdb_advect(&f, &v, 1.0f, scheme, 1, &f);
        fail_at = 0;
        int changed = 0;
        for (int i = 0; i < 512; ++i) if (f.data[i] != (float)i) ++changed;
        CHECK(changed == 0);
        /* Sanity: without a failure the same call does advect. */
        tvdb_advect(&f, &v, 1.0f, scheme, 1, &f);
        changed = 0;
        for (int i = 0; i < 512; ++i) if (f.data[i] != (float)i) ++changed;
        CHECK(changed > 0);
        tvdb_dense_grid_free(&f); tvdb_dense_vec_grid_free(&v);
    }
}

/* 2. DDA entry voxel: floor of the slab entry point can round to -1. Rays
      aimed at an interior point must report at least one voxel. */
static void test_dda_entry_voxel_clamped(void) {
    tvdb_dense_grid g; tvdb_dense_grid_init(&g, 16, 16, 16);
    g.voxel_size = 0.1f; g.ox = g.oy = g.oz = -0.8f;
    unsigned s = 3; int zero = 0;
    for (int k = 0; k < 20000; ++k) {
        float r[5];
        for (int j = 0; j < 5; ++j) { s = s * 1103515245u + 12345u; r[j] = (float)(s >> 8) / 16777216.0f; }
        float o[3] = { -2.0f, -1.5f + 3 * r[0], -1.5f + 3 * r[1] };
        float t[3] = { -0.7f + 1.4f * r[2], -0.7f + 1.4f * r[3], -0.7f + 1.4f * r[4] };
        float d[3] = { t[0] - o[0], t[1] - o[1], t[2] - o[2] };
        float L = sqrtf(d[0] * d[0] + d[1] * d[1] + d[2] * d[2]);
        tvdb_ray ray = { { o[0], o[1], o[2] }, { d[0] / L, d[1] / L, d[2] / L }, 0.0f, 1e30f };
        if (tvdb_voxels_along_ray_dense(&g, &ray, NULL, 0) == 0) ++zero;
    }
    CHECK(zero == 0);
    /* Axis rays through an 8^3 grid with a non-unit voxel size cross 8 voxels. */
    tvdb_dense_grid g8; tvdb_dense_grid_init(&g8, 8, 8, 8);
    g8.voxel_size = 0.1f; g8.ox = g8.oy = g8.oz = -0.4f;
    int wrong = 0; s = 1;
    for (int k = 0; k < 20000; ++k) {
        s = s * 1103515245u + 12345u; float a = (float)(s >> 8) / 16777216.0f;
        s = s * 1103515245u + 12345u; float b = (float)(s >> 8) / 16777216.0f;
        tvdb_ray rr = { { -1.3f, -0.39f + 0.78f * a, -0.39f + 0.78f * b }, { 1, 0, 0 }, 0.0f, 1e30f };
        if (tvdb_voxels_along_ray_dense(&g8, &rr, NULL, 0) != 8) ++wrong;
    }
    CHECK(wrong == 0);
    tvdb_dense_grid_free(&g); tvdb_dense_grid_free(&g8);
}

/* 3. DDA must keep the voxel containing the segment end point. */
static void test_dda_keeps_last_voxel(void) {
    tvdb_dense_grid g; tvdb_dense_grid_init(&g, 4, 1, 1);
    tvdb_ray r = { { 0.5f, 0.5f, 0.5f }, { 1, 0, 0 }, 0.0f, 2.2f };
    tvdb_vec3i v[16];
    size_t n = tvdb_voxels_along_ray_dense(&g, &r, v, 16);
    CHECK(n == 3);
    if (n == 3) CHECK(v[0].x == 0 && v[1].x == 1 && v[2].x == 2);
    CHECK(tvdb_voxels_along_ray_dense(&g, &r, NULL, 0) == 3);
    /* Ending exactly on a face does not enter the next voxel. */
    r.tmax = 1.5f;
    CHECK(tvdb_voxels_along_ray_dense(&g, &r, NULL, 0) == 2);
    tvdb_dense_grid g8; tvdb_dense_grid_init(&g8, 8, 8, 8);
    tvdb_ray r2 = { { -3.0f, 2.5f, 2.5f }, { 1, 0, 0 }, 0.0f, 1e30f };
    CHECK(tvdb_voxels_along_ray_dense(&g8, &r2, NULL, 0) == 8);
    r2.tmax = 6.5f;   /* ends at x = 3.5 */
    CHECK(tvdb_voxels_along_ray_dense(&g8, &r2, NULL, 0) == 4);
    /* Non-finite rays are rejected rather than converted. */
    r2.origin.x = NAN;
    CHECK(tvdb_voxels_along_ray_dense(&g8, &r2, NULL, 0) == 0);
    tvdb_dense_grid_free(&g); tvdb_dense_grid_free(&g8);
}

/* 4. Volume render: a step below the float spacing of t never advanced
      (infinite loop), and NaN fov_y passed validation. Must return quickly. */
static void test_render_rejects_degenerate_step(void) {
    tvdb_dense_grid g; tvdb_dense_grid_init(&g, 4, 4, 4);   /* zero density */
    float eye[3] = { 2, 2, -10 }, ctr[3] = { 2, 2, 2 }, up[3] = { 0, 1, 0 };
    float img[1] = { -7.0f };
    CHECK(!tvdb_volume_render(&g, eye, ctr, up, 0.8f, 1, 1, 1.0f, 1e-7f, 0.0f, img));
    CHECK(!tvdb_volume_render(&g, eye, ctr, up, NAN, 1, 1, 1.0f, 0.01f, 0.0f, img));
    CHECK(!tvdb_volume_render(&g, eye, ctr, up, 0.8f, 1, 1, 1.0f, NAN, 0.0f, img));
    CHECK(!tvdb_volume_render(&g, eye, eye, up, 0.8f, 1, 1, 1.0f, 0.01f, 0.0f, img));
    CHECK(img[0] == -7.0f);
    /* A normal render still works: empty volume over background 0.25. */
    CHECK(tvdb_volume_render(&g, eye, ctr, up, 0.8f, 1, 1, 1.0f, 0.01f, 0.25f, img));
    CHECK(fabsf(img[0] - 0.25f) < 1e-6f);
    /* Opaque volume: the center ray is absorbed. */
    for (int i = 0; i < 64; ++i) g.data[i] = 10.0f;
    CHECK(tvdb_volume_render(&g, eye, ctr, up, 0.2f, 1, 1, 1.0f, 0.05f, 0.0f, img));
    CHECK(img[0] > 0.99f);
    tvdb_dense_grid_free(&g);
}

/* 5. Segments: a sample exactly on the isovalue, or a sign change whose
      product underflows, must still produce the crossing. */
static void test_segments_exact_and_underflow(void) {
    tvdb_dense_grid g; tvdb_dense_grid_init(&g, 5, 1, 1);
    tvdb_ray r = { { 0.5f, 0.5f, 0.5f }, { 1, 0, 0 }, 0.0f, 4.0f };
    float pairs[8];
    const float a[5] = { 1, 0, -1, 0, 1 };
    for (int i = 0; i < 5; ++i) g.data[i] = a[i];
    size_t n = tvdb_segments_along_ray(&g, &r, 0.0f, 5, pairs, 4);
    CHECK(n == 1);
    if (n == 1) CHECK(fabsf(pairs[0] - 1.0f) < 1e-5f && fabsf(pairs[1] - 3.0f) < 1e-5f);
    const float b[5] = { 0, -1, -1, 1, 1 };
    for (int i = 0; i < 5; ++i) g.data[i] = b[i];
    n = tvdb_segments_along_ray(&g, &r, 0.0f, 5, pairs, 4);
    CHECK(n == 1);
    if (n == 1) CHECK(fabsf(pairs[0] - 0.0f) < 1e-5f && fabsf(pairs[1] - 2.5f) < 1e-5f);
    tvdb_dense_grid_free(&g);

    tvdb_dense_grid u; tvdb_dense_grid_init(&u, 2, 1, 1);
    u.data[0] = -1e-30f; u.data[1] = 1e-30f;            /* product underflows */
    tvdb_ray ru = { { 0.5f, 0.5f, 0.5f }, { 1, 0, 0 }, 0.0f, 1.0f };
    n = tvdb_segments_along_ray(&u, &ru, 0.0f, 2, pairs, 4);
    CHECK(n == 1);
    if (n == 1) CHECK(pairs[0] == 0.0f && fabsf(pairs[1] - 0.5f) < 1e-5f);
    tvdb_dense_grid_free(&u);
}

/* 6. Histogram: out-of-range values must clamp to the last bin without an
      undefined float->int conversion; NaN is not counted. */
static void test_histogram_out_of_range_and_nan(void) {
    tvdb_dense_grid h; tvdb_dense_grid_init(&h, 3, 1, 1);
    h.data[0] = 0.25f; h.data[1] = 1e30f; h.data[2] = 0.75f;
    size_t c[2] = { 99, 99 };
    CHECK(tvdb_grid_histogram(&h, 0.0, 1.0, 2, c));
    CHECK(c[0] == 1 && c[1] == 2);
    h.data[1] = -INFINITY;
    CHECK(tvdb_grid_histogram(&h, 0.0, 1.0, 2, c));
    CHECK(c[0] == 2 && c[1] == 1);
    h.data[1] = NAN;
    CHECK(tvdb_grid_histogram(&h, 0.0, 1.0, 2, c));
    CHECK(c[0] == 1 && c[1] == 1);
    CHECK(!tvdb_grid_histogram(&h, 0.0, NAN, 2, c));
    tvdb_dense_grid_free(&h);
}

/* 7. Level-set generators: NaN or tiny voxel sizes/parameters used to hit an
      undefined cast and "succeed" with a 1x1x1 grid. */
static void test_levelset_generators_validate(void) {
    const float c[3] = { 0, 0, 0 }, he[3] = { 1, 1, 1 }, p1[3] = { 1, 0, 0 };
    const float cn[3] = { NAN, 0, 0 };
    tvdb_dense_grid g; memset(&g, 0, sizeof(g));
    CHECK(!tvdb_level_set_sphere(NAN, c, 0.1f, 3, &g));
    CHECK(!tvdb_level_set_sphere(1.0f, c, NAN, 3, &g));
    CHECK(!tvdb_level_set_sphere(1.0f, c, 1e-30f, 3, &g));
    CHECK(!tvdb_level_set_sphere(1.0f, c, INFINITY, 3, &g));
    CHECK(!tvdb_level_set_sphere(1.0f, cn, 0.1f, 3, &g));
    CHECK(!tvdb_level_set_sphere(1.0f, c, 0.1f, INFINITY, &g));
    CHECK(!tvdb_level_set_box(he, c, 1e-30f, 3, &g));
    CHECK(!tvdb_level_set_torus(NAN, 0.3f, c, 0.1f, 3, &g));
    CHECK(!tvdb_level_set_torus(1.0f, 0.3f, c, NAN, 3, &g));
    CHECK(!tvdb_level_set_capsule(c, p1, NAN, 0.1f, 3, &g));
    CHECK(!tvdb_level_set_platonic(6, NAN, c, 0.1f, 3, &g));
    CHECK(!tvdb_level_set_platonic(6, 1.0f, c, 1e-30f, 3, &g));
    CHECK(g.data == NULL);
    CHECK(tvdb_level_set_sphere(1.0f, c, 0.25f, 3, &g));
    CHECK(g.data && g.nx > 8);
    tvdb_dense_grid_free(&g);
}

/* 8. TSDF: a voxel arbitrarily close to the camera plane projects to a huge
      pixel coordinate; converting it to int was undefined. */
static void test_tsdf_near_camera_plane(void) {
    tvdb_dense_grid t, w; tvdb_dense_grid_init(&t, 1, 1, 1); tvdb_dense_grid_init(&w, 1, 1, 1);
    t.voxel_size = w.voxel_size = 1.0f;
    t.ox = w.ox = 0.5f; t.oy = w.oy = -0.5f; t.oz = w.oz = -0.4999999f; /* center z ~ 1e-7 */
    t.data[0] = 0.1f;
    float depth[4] = { 1, 1, 1, 1 };
    tvdb_depth_frame f; memset(&f, 0, sizeof(f));
    f.width = 2; f.height = 2; f.depth = depth; f.fx = f.fy = 500; f.cx = f.cy = 1;
    const float pose[12] = { 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0 };
    memcpy(f.pose, pose, sizeof(pose));
    f.trunc_distance = 0.1f; f.depth_min = 0.1f; f.depth_max = 10;
    CHECK(tvdb_integrate_tsdf(&t, &w, &f));
    CHECK(w.data[0] == 0.0f && t.data[0] == 0.1f);   /* projects off-image */
    t.voxel_size = NAN;
    CHECK(!tvdb_integrate_tsdf(&t, &w, &f));
    CHECK(w.data[0] == 0.0f);
    tvdb_dense_grid_free(&t); tvdb_dense_grid_free(&w);
}

/* 9. Fog check must not report a NaN grid as valid. */
static void test_fog_check_nonfinite(void) {
    tvdb_dense_grid h; tvdb_dense_grid_init(&h, 3, 1, 1);
    h.data[0] = 0.5f; h.data[1] = NAN; h.data[2] = 0.5f;
    int valid = -1; double mn = 0, mx = 0;
    CHECK(tvdb_check_fog_volume(&h, 0.0, &valid, &mn, &mx));
    CHECK(valid == 0);
    CHECK(mn == 0.5 && mx == 0.5);
    h.data[1] = INFINITY;
    CHECK(tvdb_check_fog_volume(&h, 0.0, &valid, &mn, &mx));
    CHECK(valid == 0);
    h.data[1] = 1.0f;
    CHECK(tvdb_check_fog_volume(&h, 0.0, &valid, &mn, &mx));
    CHECK(valid == 1);
    tvdb_dense_grid_free(&h);
}

/* 10. Stats entry points must validate dimensions (nx = -1 over-read). */
static void test_stats_validate_dims(void) {
    float buf[4] = { 0, 0, 0, 0 };
    tvdb_dense_grid g; memset(&g, 0, sizeof(g));
    g.nx = -1; g.ny = 1; g.nz = 1; g.voxel_size = 1; g.data = buf;
    tvdb_grid_stats_t st;
    CHECK(!tvdb_grid_statistics(&g, &st));
    size_t c[2];
    CHECK(!tvdb_grid_histogram(&g, 0.0, 1.0, 2, c));
    int valid; double mn, mx;
    CHECK(!tvdb_check_fog_volume(&g, 0.0, &valid, &mn, &mx));
    g.nx = 1; g.ny = -1; g.nz = -1;          /* product wraps to 1 in size_t */
    CHECK(!tvdb_grid_statistics(&g, &st));
    g.nx = -4; g.ny = 4; g.nz = -4;
    tvdb_level_set_check_t ck;
    CHECK(!tvdb_check_level_set(&g, 0.0, 0.1, &ck));
}

/* Extra: NaN voxel_size passed `<= 0` guards. */
static void test_nan_voxel_size_rejected(void) {
    tvdb_dense_grid_d d; tvdb_dense_grid_d_init(&d, 2, 1, 1);
    CHECK(d.data);
    if (d.data) {
        d.data[0] = -1; d.data[1] = 1; d.voxel_size = NAN;
        CHECK(tvdb_volume_d(&d) == 0.0);
        CHECK(tvdb_surface_area_d(&d) == 0.0);
        d.voxel_size = 1.0;
        CHECK(tvdb_volume_d(&d) == 1.0);
        CHECK(tvdb_surface_area_d(&d) == 1.0);
        free(d.data);
    }
    tvdb_dense_grid g; tvdb_dense_grid_init(&g, 4, 4, 4);
    for (int i = 0; i < 64; ++i) g.data[i] = (float)(i % 4) - 1.5f;
    g.voxel_size = NAN;
    tvdb_dense_grid out; memset(&out, 0, sizeof(out));
    CHECK(!tvdb_sdf_to_fog_volume(&g, 3, &out));
    CHECK(out.data == NULL);
    tvdb_level_set_check_t ck;
    CHECK(!tvdb_check_level_set(&g, 0.0, 0.1, &ck));
    CHECK(!tvdb_level_set_rebuild(&g, 0.0f, 0.0f, 3.0f, 0, &out));
    CHECK(out.data == NULL);
    g.voxel_size = 1.0f;
    CHECK(!tvdb_level_set_rebuild(&g, 0.0f, NAN, INFINITY, 0, &out));
    CHECK(tvdb_check_level_set(&g, 0.0, 0.1, &ck));
    tvdb_dense_grid_free(&g);
}

/* Extra: Poisson stopped on the 32-iteration restart check (an iteration the
   candidate stride does not sample) and returned a stale best iterate that it
   then reported as not converged. Any early stop must be a converged one. */
static void test_poisson_restart_convergence_reported(void) {
    const int N = 16;
    const size_t n = (size_t)N * N * N;
    tvdb_dense_grid b; tvdb_dense_grid_init(&b, N, N, N);
    tvdb_dense_grid x; tvdb_dense_grid_init(&x, N, N, N);
    CHECK(b.data && x.data);
    if (!b.data || !x.data) { tvdb_dense_grid_free(&b); tvdb_dense_grid_free(&x); return; }
    unsigned s = 3; double sum = 0;
    for (size_t i = 0; i < n; ++i) {
        s = s * 1103515245u + 12345u;
        b.data[i] = (float)(s >> 8) / 16777216.0f - 0.5f; sum += b.data[i];
    }
    for (size_t i = 0; i < n; ++i) b.data[i] -= (float)(sum / (double)n);
    sum = 0; for (size_t i = 0; i < n; ++i) sum += b.data[i];
    b.data[0] -= (float)sum;
    /* Tolerances bracketing the gap between the recurrence and the true
       residual at iteration 32 for this problem in the scalar build. */
    for (int k = -4; k <= 4; ++k) {
        const float tol = 0.009566135f + (float)k * 2e-9f;
        memset(x.data, 0, n * sizeof(float));
        tvdb_poisson_result_t r; tvdb_error_t e;
        CHECK(tvdb_solve_poisson_ex(&b, &x, 100, tol, &r, &e) == TVDB_OK);
        if (r.iterations < 100) {
            CHECK(r.converged);
            CHECK(r.final_residual_norm <= (double)tol * r.initial_residual_norm);
        }
    }
    tvdb_dense_grid_free(&b); tvdb_dense_grid_free(&x);
}

int main(int argc, char **argv) {
    (void)argc; (void)argv;
    test_advect_inplace_scratch_failure();
    test_dda_entry_voxel_clamped();
    test_dda_keeps_last_voxel();
    test_render_rejects_degenerate_step();
    test_segments_exact_and_underflow();
    test_histogram_out_of_range_and_nan();
    test_levelset_generators_validate();
    test_tsdf_near_camera_plane();
    test_fog_check_nonfinite();
    test_stats_validate_dims();
    test_nan_voxel_size_rejected();
    test_poisson_restart_convergence_reported();
    printf("failures=%d\n", failures);
    return failures ? 1 : 0;
}
