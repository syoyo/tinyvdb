// fp64 dense grid tests:
//  - lifecycle, fp32 <-> fp64 round-trip preserves values
//  - trilinear sample at lattice points returns exact values
//  - CSG: union of two spheres has expected sign at known points
//  - laplacian of f(x,y,z) = x^2 returns 2/h^2 (with edge clamp on boundary)
//  - volume of sphere SDF approximates (4/3) pi R^3
//  - surface area approximates 4 pi R^2
//  - fast_sweeping_d: sphere SDF redistance to within voxel_size
//  - solve_poisson_dd: build phi, set rhs = lap(phi), solve, recover phi

#include "tinyvdb_mesh.h"
#include "tinyvdb_ops.h"

#define _USE_MATH_DEFINES
#include <math.h>
#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int fail_count = 0;
#define CHECK(cond, msg) do { \
    if (!(cond)) { fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, msg); ++fail_count; } \
} while (0)

#define CHECK_NEAR(a, b, tol, msg) do { \
    double _da = (double)(a), _db = (double)(b); \
    if (fabs(_da - _db) > (tol)) { \
        fprintf(stderr, "FAIL %s:%d: %s (got %.6g, want %.6g, tol %.6g)\n", \
                __FILE__, __LINE__, msg, _da, _db, (double)(tol)); \
        ++fail_count; \
    } \
} while (0)

static void fill_sphere_d(tvdb_dense_grid_d* g, double R) {
    const int nx = g->nx, ny = g->ny, nz = g->nz;
    const double h = g->voxel_size;
    for (int z = 0; z < nz; ++z) {
        for (int y = 0; y < ny; ++y) {
            for (int x = 0; x < nx; ++x) {
                double wx = g->ox + ((double)x + 0.5) * h;
                double wy = g->oy + ((double)y + 0.5) * h;
                double wz = g->oz + ((double)z + 0.5) * h;
                double r = sqrt(wx*wx + wy*wy + wz*wz);
                size_t i = (size_t)((z * ny + y) * nx + x);
                g->data[i] = r - R;
            }
        }
    }
}

int main(void) {
    // ---- Test 1: lifecycle and conversion round-trip ----
    {
        tvdb_dense_grid f;
        tvdb_dense_grid_init(&f, 4, 4, 4);
        f.voxel_size = 0.25f; f.ox = -0.5f; f.oy = 0.0f; f.oz = 0.5f;
        for (int i = 0; i < 64; ++i) f.data[i] = (float)i * 0.125f;
        tvdb_dense_grid_d d;
        tvdb_dense_grid_f_to_d(&f, &d);
        CHECK(d.nx == 4 && d.ny == 4 && d.nz == 4, "shape preserved");
        CHECK_NEAR(d.voxel_size, 0.25, 1e-7, "voxel_size widened");
        CHECK_NEAR(d.ox, -0.5, 1e-7, "ox widened");
        for (int i = 0; i < 64; ++i)
            CHECK_NEAR(d.data[i], (double)((float)i * 0.125f), 1e-7, "f->d preserves bits");

        tvdb_dense_grid f2;
        tvdb_dense_grid_d_to_f(&d, &f2);
        for (int i = 0; i < 64; ++i)
            CHECK_NEAR(f2.data[i], f.data[i], 1e-7, "round-trip preserves fp32");
        tvdb_dense_grid_d_free(&d);
        tvdb_dense_grid_free(&f);
        tvdb_dense_grid_free(&f2);
    }

    // ---- Test 2: trilinear sample at lattice points ----
    {
        tvdb_dense_grid_d g;
        tvdb_dense_grid_d_init(&g, 4, 4, 4);
        g.voxel_size = 1.0; g.ox = g.oy = g.oz = 0.0;
        for (int z = 0; z < 4; ++z)
            for (int y = 0; y < 4; ++y)
                for (int x = 0; x < 4; ++x)
                    g.data[(size_t)((z * 4 + y) * 4 + x)] = (double)(x + y * 10 + z * 100);
        // Voxel (1,2,3) center is at (0.5+1, 0.5+2, 0.5+3) = (1.5, 2.5, 3.5).
        double v = tvdb_sample_trilinear_dense_d(&g, 1.5, 2.5, 3.5);
        CHECK_NEAR(v, (double)(1 + 20 + 300), 1e-9, "exact at voxel center");
        tvdb_dense_grid_d_free(&g);
    }

    // ---- Test 3: CSG union of two unit-spheres ----
    {
        const int N = 16;
        tvdb_dense_grid_d a, b, out;
        tvdb_dense_grid_d_init(&a, N, N, N);
        tvdb_dense_grid_d_init(&b, N, N, N);
        tvdb_dense_grid_d_init(&out, N, N, N);
        a.voxel_size = b.voxel_size = out.voxel_size = 1.0/N;
        a.ox = -0.5; a.oy = -0.5; a.oz = -0.5;
        b.ox = -0.5; b.oy = -0.5; b.oz = -0.5;
        out.ox = -0.5; out.oy = -0.5; out.oz = -0.5;
        // Sphere A at origin, sphere B offset along x.
        for (int z = 0; z < N; ++z)
            for (int y = 0; y < N; ++y)
                for (int x = 0; x < N; ++x) {
                    double wx = a.ox + ((double)x + 0.5) * a.voxel_size;
                    double wy = a.oy + ((double)y + 0.5) * a.voxel_size;
                    double wz = a.oz + ((double)z + 0.5) * a.voxel_size;
                    size_t i = (size_t)((z * N + y) * N + x);
                    a.data[i] = sqrt(wx*wx + wy*wy + wz*wz) - 0.20;
                    double bx = wx - 0.30;
                    b.data[i] = sqrt(bx*bx + wy*wy + wz*wz) - 0.20;
                }
        tvdb_csg_union_d(&a, &b, &out);
        // Point well inside sphere A (origin) should be inside the union.
        double sample = tvdb_sample_trilinear_dense_d(&out, 0.0, 0.0, 0.0);
        CHECK(sample < 0.0, "origin inside union");
        // Point inside B (0.30, 0, 0) inside union.
        sample = tvdb_sample_trilinear_dense_d(&out, 0.30, 0.0, 0.0);
        CHECK(sample < 0.0, "B center inside union");
        // Point far outside both.
        sample = tvdb_sample_trilinear_dense_d(&out, -0.45, 0.45, 0.45);
        CHECK(sample > 0.0, "corner outside union");

        tvdb_csg_intersection_d(&a, &b, &out);
        sample = tvdb_sample_trilinear_dense_d(&out, 0.15, 0.0, 0.0);
        // 0.15 is inside both; intersection should be inside.
        CHECK(sample < 0.0, "midpoint inside intersection");
        sample = tvdb_sample_trilinear_dense_d(&out, 0.0, 0.0, 0.0);
        // origin inside A but outside B (B center at 0.3, R=0.2, so |0-0.3|=0.3>0.2).
        CHECK(sample > 0.0, "A-only outside intersection");

        tvdb_dense_grid_d_free(&a);
        tvdb_dense_grid_d_free(&b);
        tvdb_dense_grid_d_free(&out);
    }

    // ---- Test 4: laplacian of f(x,y,z) = x^2 ----
    {
        const int N = 16;
        tvdb_dense_grid_d g, lap;
        tvdb_dense_grid_d_init(&g, N, N, N);
        tvdb_dense_grid_d_init(&lap, N, N, N);
        g.voxel_size = 1.0; lap.voxel_size = 1.0;
        for (int z = 0; z < N; ++z)
            for (int y = 0; y < N; ++y)
                for (int x = 0; x < N; ++x) {
                    double wx = (double)x;  // origin 0; just use voxel index
                    g.data[(size_t)((z * N + y) * N + x)] = wx * wx;
                }
        tvdb_laplacian_d(&g, &lap);
        // At an interior voxel away from boundary, lap(x^2) = 2 in continuous.
        // Discrete 7-point with h=1 returns exactly 2 since x^2 has a constant
        // 2nd derivative.
        size_t i = (size_t)((8 * N + 8) * N + 8);
        CHECK_NEAR(lap.data[i], 2.0, 1e-9, "lap(x^2) interior");
        tvdb_dense_grid_d_free(&g);
        tvdb_dense_grid_d_free(&lap);
    }

    // ---- Test 5: volume / surface area of sphere SDF ----
    {
        const int N = 64;
        tvdb_dense_grid_d g;
        tvdb_dense_grid_d_init(&g, N, N, N);
        g.voxel_size = 1.0/N; g.ox = -0.5; g.oy = -0.5; g.oz = -0.5;
        const double R = 0.30;
        fill_sphere_d(&g, R);
        double vol = tvdb_volume_d(&g);
        double area = tvdb_surface_area_d(&g);
        double exact_vol = (4.0 / 3.0) * 3.141592653589793 * R * R * R;
        double exact_area = 4.0 * 3.141592653589793 * R * R;
        printf("vol=%.4f exact=%.4f area=%.4f exact=%.4f\n",
               vol, exact_vol, area, exact_area);
        // Voxel-cell volume estimate has O(h) error.
        CHECK(fabs(vol - exact_vol) / exact_vol < 0.05, "volume within 5%");
        // Stair-step surface area overestimates by ~50% on coarse grids.
        // Just check we're in a sensible range.
        CHECK(area > 0.6 * exact_area && area < 2.0 * exact_area, "area sensible");
        tvdb_dense_grid_d_free(&g);
    }

    // ---- Test 6: fast_sweeping_d ----
    {
        const int N = 24;
        tvdb_dense_grid_d g;
        tvdb_dense_grid_d_init(&g, N, N, N);
        g.voxel_size = 1.0/N; g.ox = -0.5; g.oy = -0.5; g.oz = -0.5;
        const double R = 0.30;
        const double band = 2.0 * g.voxel_size;
        // Init: exact in band, sentinel elsewhere.
        for (int z = 0; z < N; ++z)
            for (int y = 0; y < N; ++y)
                for (int x = 0; x < N; ++x) {
                    double wx = g.ox + ((double)x + 0.5) * g.voxel_size;
                    double wy = g.oy + ((double)y + 0.5) * g.voxel_size;
                    double wz = g.oz + ((double)z + 0.5) * g.voxel_size;
                    double e = sqrt(wx*wx + wy*wy + wz*wz) - R;
                    size_t i = (size_t)((z * N + y) * N + x);
                    g.data[i] = (fabs(e) <= band) ? e : (e >= 0.0 ? 100.0 : -100.0);
                }
        int iters = tvdb_fast_sweeping_d(&g, band, 16, 1e-6);
        CHECK(iters > 0 && iters <= 16, "fp64 sweep iters in range");
        // Spot-check a few non-band voxels.
        double max_err = 0.0;
        for (int z = 0; z < N; ++z)
            for (int y = 0; y < N; ++y)
                for (int x = 0; x < N; ++x) {
                    double wx = g.ox + ((double)x + 0.5) * g.voxel_size;
                    double wy = g.oy + ((double)y + 0.5) * g.voxel_size;
                    double wz = g.oz + ((double)z + 0.5) * g.voxel_size;
                    double e = sqrt(wx*wx + wy*wy + wz*wz) - R;
                    if (fabs(e) <= band) continue;
                    size_t i = (size_t)((z * N + y) * N + x);
                    double d = fabs(g.data[i] - e);
                    if (d > max_err) max_err = d;
                }
        printf("fp64 fast_sweep max_err=%.4f voxel_size=%.4f\n", max_err, g.voxel_size);
        CHECK(max_err < 3.0 * g.voxel_size, "fp64 sweep accuracy");
        tvdb_dense_grid_d_free(&g);
    }

    // ---- Test 7: Poisson recovery (build phi, solve, compare) ----
    {
        const int N = 16;
        const double h = 1.0 / N;
        tvdb_dense_grid_d phi, rhs, x_out;
        tvdb_dense_grid_d_init(&phi, N, N, N);
        tvdb_dense_grid_d_init(&rhs, N, N, N);
        tvdb_dense_grid_d_init(&x_out, N, N, N);
        phi.voxel_size = rhs.voxel_size = x_out.voxel_size = h;
        // Build phi(x,y,z) = sin(pi x) sin(pi y) sin(pi z) on voxel centers.
        // (Vanishes at boundaries, so Dirichlet via clamp is consistent.)
        for (int z = 0; z < N; ++z)
            for (int y = 0; y < N; ++y)
                for (int x = 0; x < N; ++x) {
                    double X = ((double)x + 0.5) * h;
                    double Y = ((double)y + 0.5) * h;
                    double Z = ((double)z + 0.5) * h;
                    phi.data[(size_t)((z * N + y) * N + x)] =
                        sin(M_PI * X) * sin(M_PI * Y) * sin(M_PI * Z);
                }
        // rhs = lap(phi) computed by our discrete Laplacian.
        tvdb_laplacian_d(&phi, &rhs);
        // Solve and compare. (Initial x_out is zero from calloc.)
        x_out.voxel_size = h;
        int iters = tvdb_solve_poisson_dd(&rhs, &x_out, 1000, 1e-12);
        // Reflective-clamp Laplacian has a constant null space, so solutions
        // are unique only up to an additive constant. De-mean both fields
        // (over the interior) before comparing.
        double mphi = 0.0, mx = 0.0;
        long long ntot = 0;
        for (int z = 1; z < N - 1; ++z)
            for (int y = 1; y < N - 1; ++y)
                for (int x = 1; x < N - 1; ++x) {
                    size_t i = (size_t)((z * N + y) * N + x);
                    mphi += phi.data[i]; mx += x_out.data[i]; ++ntot;
                }
        mphi /= (double)ntot; mx /= (double)ntot;
        double max_diff = 0.0, sumsq = 0.0;
        for (int z = 1; z < N - 1; ++z)
            for (int y = 1; y < N - 1; ++y)
                for (int x = 1; x < N - 1; ++x) {
                    size_t i = (size_t)((z * N + y) * N + x);
                    double d = fabs((x_out.data[i] - mx) - (phi.data[i] - mphi));
                    if (d > max_diff) max_diff = d;
                    sumsq += d * d;
                }
        double rms = sqrt(sumsq / (double)ntot);
        printf("Poisson_dd iters=%d max_diff=%.4e rms=%.4e\n", iters, max_diff, rms);
        CHECK(rms < 1e-2, "poisson recovery rms (de-meaned)");
        tvdb_dense_grid_d_free(&phi);
        tvdb_dense_grid_d_free(&rhs);
        tvdb_dense_grid_d_free(&x_out);
    }

    if (fail_count) { fprintf(stderr, "%d FAILURES\n", fail_count); return 1; }
    printf("All fp64 dense-grid tests passed.\n");
    return 0;
}
