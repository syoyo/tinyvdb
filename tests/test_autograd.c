// Autograd / VJP tests: every analytic VJP is checked against a finite-
// difference reference. Tolerance is set generously enough that fp32
// rounding doesn't cause flakes, but tight enough to catch sign/transpose
// bugs.

#include "tinyvdb_autograd.h"
#include "tinyvdb_ops.h"
#include "tinyvdb_sample.h"
#include "tinyvdb_sparse.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int fail_count = 0;
#define CHECK(cond, msg) do { \
    if (!(cond)) { fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, msg); ++fail_count; } \
} while (0)
#define CHECK_NEAR(a, b, tol, msg) do { \
    double da_ = (double)(a), db_ = (double)(b); \
    if (fabs(da_ - db_) > (tol)) { \
        fprintf(stderr, "FAIL %s:%d: %s (got %.6g vs %.6g, |diff|=%.2e tol=%.2e)\n", \
                __FILE__, __LINE__, msg, da_, db_, fabs(da_ - db_), (double)(tol)); \
        ++fail_count; \
    } \
} while (0)

// Loss: L = sum_j out[j].
// dL/dout[j] = 1 for all j.

// ---------- Trilinear sample VJP gridcheck ----------

static void test_sample_vjp_grid(void) {
    const int N = 8;
    tvdb_dense_grid g; tvdb_dense_grid_init(&g, N, N, N);
    g.voxel_size = 1.0f / N; g.ox = -0.5f; g.oy = -0.5f; g.oz = -0.5f;
    // Fill with a smooth pattern.
    for (int z = 0; z < N; ++z)
        for (int y = 0; y < N; ++y)
            for (int x = 0; x < N; ++x) {
                size_t i = (size_t)((z * N + y) * N + x);
                g.data[i] = (float)(0.1 * x + 0.2 * y + 0.3 * z);
            }

    // 4 sample points scattered in the interior.
    tvdb_vec3f pts[4] = {
        {-0.10f,  0.05f,  0.20f},
        { 0.15f, -0.20f, -0.10f},
        { 0.30f,  0.30f,  0.30f},
        {-0.30f, -0.05f,  0.10f},
    };
    const size_t n = 4;
    float out[4]; tvdb_sample_trilinear_dense_batch(&g, pts, n, out);
    float grad_out[4] = {1.0f, 1.0f, 1.0f, 1.0f};

    // Analytic VJP grid.
    tvdb_dense_grid grad_g; tvdb_dense_grid_init(&grad_g, N, N, N);
    grad_g.voxel_size = g.voxel_size; grad_g.ox = g.ox; grad_g.oy = g.oy; grad_g.oz = g.oz;
    tvdb_sample_trilinear_dense_vjp_grid(&g, pts, n, grad_out, &grad_g);

    // Finite-difference check at a few voxels (perturb one voxel, recompute
    // sum of out, compare to analytic grad at that voxel).
    const float eps = 1e-3f;
    int checks[][3] = { {2,3,4}, {0,0,0}, {7,7,7}, {3,5,2} };
    for (int t = 0; t < 4; ++t) {
        int x = checks[t][0], y = checks[t][1], z = checks[t][2];
        size_t idx = (size_t)((z * N + y) * N + x);
        float orig = g.data[idx];
        g.data[idx] = orig + eps;
        float plus = 0.0f;
        for (size_t j = 0; j < n; ++j)
            plus += tvdb_sample_trilinear_dense(&g, pts[j].x, pts[j].y, pts[j].z);
        g.data[idx] = orig - eps;
        float minus = 0.0f;
        for (size_t j = 0; j < n; ++j)
            minus += tvdb_sample_trilinear_dense(&g, pts[j].x, pts[j].y, pts[j].z);
        g.data[idx] = orig;
        float fd = (plus - minus) / (2.0f * eps);
        float an = grad_g.data[idx];
        CHECK_NEAR(an, fd, 1e-3, "sample_vjp_grid");
    }
    tvdb_dense_grid_free(&g);
    tvdb_dense_grid_free(&grad_g);
}

// ---------- Trilinear sample VJP pts check ----------

static void test_sample_vjp_pts(void) {
    const int N = 8;
    tvdb_dense_grid g; tvdb_dense_grid_init(&g, N, N, N);
    g.voxel_size = 1.0f / N; g.ox = -0.5f; g.oy = -0.5f; g.oz = -0.5f;
    for (int z = 0; z < N; ++z)
        for (int y = 0; y < N; ++y)
            for (int x = 0; x < N; ++x) {
                size_t i = (size_t)((z * N + y) * N + x);
                // Quadratic pattern so analytic grad is non-trivial.
                float wx = g.ox + ((float)x + 0.5f) * g.voxel_size;
                float wy = g.oy + ((float)y + 0.5f) * g.voxel_size;
                float wz = g.oz + ((float)z + 0.5f) * g.voxel_size;
                g.data[i] = wx * wx + wy * 0.5f + wz * wz * 0.25f;
            }

    tvdb_vec3f pts[3] = {
        { 0.10f,  0.05f,  0.20f},
        {-0.05f, -0.15f, -0.10f},
        { 0.20f,  0.10f,  0.05f},
    };
    const size_t n = 3;
    float grad_out[3] = {1.0f, 1.0f, 1.0f};

    tvdb_vec3f grad_pts[3] = { {0,0,0}, {0,0,0}, {0,0,0} };
    tvdb_sample_trilinear_dense_vjp_pts(&g, pts, n, grad_out, grad_pts);

    // FD check by perturbing each axis of each point.
    const float eps = 1e-3f;
    for (size_t j = 0; j < n; ++j) {
        for (int ax = 0; ax < 3; ++ax) {
            tvdb_vec3f pp = pts[j], pm = pts[j];
            float* axp = (ax == 0) ? &pp.x : (ax == 1) ? &pp.y : &pp.z;
            float* axm = (ax == 0) ? &pm.x : (ax == 1) ? &pm.y : &pm.z;
            *axp += eps; *axm -= eps;
            float vp = tvdb_sample_trilinear_dense(&g, pp.x, pp.y, pp.z);
            float vm = tvdb_sample_trilinear_dense(&g, pm.x, pm.y, pm.z);
            float fd = (vp - vm) / (2.0f * eps);
            float an = (ax == 0) ? grad_pts[j].x : (ax == 1) ? grad_pts[j].y : grad_pts[j].z;
            CHECK_NEAR(an, fd, 1e-2, "sample_vjp_pts");
        }
    }
    tvdb_dense_grid_free(&g);
}

// ---------- Splat VJP values check ----------

static void test_splat_vjp_values(void) {
    // Splat is linear in values. Forward: g[i] = sum_j w_ij v_j.
    // VJP: dL/dv_j = sum_i w_ij dL/dg[i] = sample(grad_g, p_j).
    // We test by:
    //   1. Building an arbitrary grad_g.
    //   2. Computing analytic grad_v via VJP.
    //   3. FD: perturb v_j, splat, sum_i grad_g[i] * g[i], compare slope.
    const int N = 6;
    tvdb_dense_grid grad_g; tvdb_dense_grid_init(&grad_g, N, N, N);
    grad_g.voxel_size = 1.0f / N;
    grad_g.ox = -0.5f; grad_g.oy = -0.5f; grad_g.oz = -0.5f;
    for (int i = 0; i < N*N*N; ++i) grad_g.data[i] = (float)(i % 7) * 0.1f - 0.3f;

    tvdb_vec3f pts[3] = { {0.1f, 0.0f, -0.1f}, {-0.2f, 0.15f, 0.05f}, {0.05f, -0.05f, 0.2f} };
    const size_t n = 3;
    float vals[3] = { 0.5f, -0.3f, 0.7f };
    float grad_vals[3] = { 0.0f, 0.0f, 0.0f };
    tvdb_splat_trilinear_dense_vjp_values(&grad_g, pts, n, grad_vals);

    const float eps = 1e-3f;
    for (size_t j = 0; j < n; ++j) {
        // FD: L(v + eps e_j) - L(v - eps e_j), L = sum_i grad_g[i] * splat(v)[i].
        tvdb_dense_grid gp; tvdb_dense_grid_init(&gp, N, N, N);
        gp.voxel_size = grad_g.voxel_size; gp.ox = grad_g.ox; gp.oy = grad_g.oy; gp.oz = grad_g.oz;
        float vp[3]; memcpy(vp, vals, sizeof(vals)); vp[j] += eps;
        tvdb_splat_trilinear_dense(&gp, pts, vp, n, NULL);
        double Lp = 0.0;
        for (int i = 0; i < N*N*N; ++i) Lp += (double)grad_g.data[i] * gp.data[i];

        memset(gp.data, 0, sizeof(float) * (size_t)(N*N*N));
        float vm[3]; memcpy(vm, vals, sizeof(vals)); vm[j] -= eps;
        tvdb_splat_trilinear_dense(&gp, pts, vm, n, NULL);
        double Lm = 0.0;
        for (int i = 0; i < N*N*N; ++i) Lm += (double)grad_g.data[i] * gp.data[i];

        double fd = (Lp - Lm) / (2.0 * eps);
        CHECK_NEAR(grad_vals[j], (float)fd, 1e-3, "splat_vjp_values");
        tvdb_dense_grid_free(&gp);
    }
    tvdb_dense_grid_free(&grad_g);
}

// ---------- CSG union VJP ----------

static void test_csg_union_vjp(void) {
    const int N = 4;
    tvdb_dense_grid a, b, gout, ga, gb;
    tvdb_dense_grid_init(&a, N, N, N);
    tvdb_dense_grid_init(&b, N, N, N);
    tvdb_dense_grid_init(&gout, N, N, N);
    tvdb_dense_grid_init(&ga, N, N, N);
    tvdb_dense_grid_init(&gb, N, N, N);
    for (int i = 0; i < N*N*N; ++i) {
        a.data[i] = (float)i * 0.1f - 1.0f;
        b.data[i] = (float)i * 0.1f - 1.5f + (i & 1) * 0.2f;
        gout.data[i] = 1.0f;  // dL/dout = 1 everywhere
    }
    tvdb_csg_union_vjp(&a, &b, &gout, &ga, &gb);
    // FD check: perturb a few elements of `a` and `b` separately and
    // verify slope = grad.
    const float eps = 1e-3f;
    int idxs[] = { 0, 5, 17, 31 };
    for (int t = 0; t < 4; ++t) {
        int i = idxs[t];
        // Perturb a[i].
        float orig = a.data[i];
        a.data[i] = orig + eps;
        double Lp = 0.0;
        for (int k = 0; k < N*N*N; ++k) Lp += fminf(a.data[k], b.data[k]);
        a.data[i] = orig - eps;
        double Lm = 0.0;
        for (int k = 0; k < N*N*N; ++k) Lm += fminf(a.data[k], b.data[k]);
        a.data[i] = orig;
        float fd = (float)((Lp - Lm) / (2.0 * eps));
        CHECK_NEAR(ga.data[i], fd, 1e-2, "csg_union_vjp wrt a");

        orig = b.data[i];
        b.data[i] = orig + eps;
        Lp = 0.0;
        for (int k = 0; k < N*N*N; ++k) Lp += fminf(a.data[k], b.data[k]);
        b.data[i] = orig - eps;
        Lm = 0.0;
        for (int k = 0; k < N*N*N; ++k) Lm += fminf(a.data[k], b.data[k]);
        b.data[i] = orig;
        fd = (float)((Lp - Lm) / (2.0 * eps));
        CHECK_NEAR(gb.data[i], fd, 1e-2, "csg_union_vjp wrt b");
    }
    tvdb_dense_grid_free(&a);
    tvdb_dense_grid_free(&b);
    tvdb_dense_grid_free(&gout);
    tvdb_dense_grid_free(&ga);
    tvdb_dense_grid_free(&gb);
}

// ---------- Sparse conv VJP wrt values ----------

static void test_sparse_conv_vjp_values(void) {
    // Build a 3x3x3 dense block of active voxels with arbitrary values
    // and an arbitrary kernel; check VJP_values matches FD.
    tvdb_sparse_grid sg; tvdb_sparse_grid_init(&sg);
    tvdb_sparse_grid_reserve(&sg, 27);
    size_t k = 0;
    for (int z = 0; z < 3; ++z)
        for (int y = 0; y < 3; ++y)
            for (int x = 0; x < 3; ++x) {
                sg.coords[k].x = x; sg.coords[k].y = y; sg.coords[k].z = z;
                sg.values[k] = (float)(k % 5) * 0.3f - 0.5f;
                ++k;
            }
    sg.count = 27;

    // 3x3x3 random-ish kernel.
    float kern[27];
    for (int i = 0; i < 27; ++i) kern[i] = (float)(i % 7) * 0.1f - 0.2f;

    // Forward.
    tvdb_sparse_grid out; tvdb_sparse_grid_init(&out);
    tvdb_sparse_conv3d(&sg, kern, 3, 3, 3, 0.0f, &out);

    // Set grad_out[i] = 1 for all i. Loss L = sum_i out[i].
    float* grad_out = (float*)malloc(sg.count * sizeof(float));
    for (size_t i = 0; i < sg.count; ++i) grad_out[i] = 1.0f;

    float* grad_in = (float*)calloc(sg.count, sizeof(float));
    bool ok = tvdb_sparse_conv3d_vjp_values(&sg, grad_out, kern, 3, 3, 3, grad_in);
    CHECK(ok, "sparse_conv3d_vjp_values returned");

    // FD on a few input values.
    const float eps = 1e-3f;
    int picks[] = { 0, 13, 26, 7 };
    for (int t = 0; t < 4; ++t) {
        size_t j = (size_t)picks[t];
        float orig = sg.values[j];
        sg.values[j] = orig + eps;
        tvdb_sparse_grid op; tvdb_sparse_grid_init(&op);
        tvdb_sparse_conv3d(&sg, kern, 3, 3, 3, 0.0f, &op);
        double Lp = 0.0;
        for (size_t i = 0; i < op.count; ++i) Lp += op.values[i];
        sg.values[j] = orig - eps;
        tvdb_sparse_grid om; tvdb_sparse_grid_init(&om);
        tvdb_sparse_conv3d(&sg, kern, 3, 3, 3, 0.0f, &om);
        double Lm = 0.0;
        for (size_t i = 0; i < om.count; ++i) Lm += om.values[i];
        sg.values[j] = orig;
        float fd = (float)((Lp - Lm) / (2.0 * eps));
        CHECK_NEAR(grad_in[j], fd, 1e-3, "sparse_conv3d_vjp_values");
        tvdb_sparse_grid_free(&op);
        tvdb_sparse_grid_free(&om);
    }
    free(grad_out); free(grad_in);
    tvdb_sparse_grid_free(&sg);
    tvdb_sparse_grid_free(&out);
}

// ---------- Sparse conv VJP wrt kernel ----------

static void test_sparse_conv_vjp_kernel(void) {
    tvdb_sparse_grid sg; tvdb_sparse_grid_init(&sg);
    tvdb_sparse_grid_reserve(&sg, 27);
    size_t k = 0;
    for (int z = 0; z < 3; ++z)
        for (int y = 0; y < 3; ++y)
            for (int x = 0; x < 3; ++x) {
                sg.coords[k].x = x; sg.coords[k].y = y; sg.coords[k].z = z;
                sg.values[k] = (float)(k % 5) * 0.3f - 0.5f;
                ++k;
            }
    sg.count = 27;

    float kern[27];
    for (int i = 0; i < 27; ++i) kern[i] = (float)(i % 7) * 0.1f - 0.2f;

    float* grad_out = (float*)malloc(sg.count * sizeof(float));
    for (size_t i = 0; i < sg.count; ++i) grad_out[i] = 1.0f;
    float grad_kern[27]; memset(grad_kern, 0, sizeof(grad_kern));

    bool ok = tvdb_sparse_conv3d_vjp_kernel(&sg, grad_out, 3, 3, 3, grad_kern);
    CHECK(ok, "sparse_conv3d_vjp_kernel returned");

    const float eps = 1e-3f;
    int picks[] = { 0, 13, 26, 4 };
    for (int t = 0; t < 4; ++t) {
        int p = picks[t];
        float orig = kern[p];
        kern[p] = orig + eps;
        tvdb_sparse_grid op; tvdb_sparse_grid_init(&op);
        tvdb_sparse_conv3d(&sg, kern, 3, 3, 3, 0.0f, &op);
        double Lp = 0.0;
        for (size_t i = 0; i < op.count; ++i) Lp += op.values[i];
        kern[p] = orig - eps;
        tvdb_sparse_grid om; tvdb_sparse_grid_init(&om);
        tvdb_sparse_conv3d(&sg, kern, 3, 3, 3, 0.0f, &om);
        double Lm = 0.0;
        for (size_t i = 0; i < om.count; ++i) Lm += om.values[i];
        kern[p] = orig;
        float fd = (float)((Lp - Lm) / (2.0 * eps));
        CHECK_NEAR(grad_kern[p], fd, 1e-3, "sparse_conv3d_vjp_kernel");
        tvdb_sparse_grid_free(&op);
        tvdb_sparse_grid_free(&om);
    }
    free(grad_out);
    tvdb_sparse_grid_free(&sg);
}

int main(void) {
    test_sample_vjp_grid();
    test_sample_vjp_pts();
    test_splat_vjp_values();
    test_csg_union_vjp();
    test_sparse_conv_vjp_values();
    test_sparse_conv_vjp_kernel();
    if (fail_count) { fprintf(stderr, "%d FAILURES\n", fail_count); return 1; }
    printf("All autograd VJP gradient checks passed.\n");
    return 0;
}
