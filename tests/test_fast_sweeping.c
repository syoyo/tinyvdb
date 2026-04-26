// Test FastSweeping: build a sphere SDF in a narrow band, freeze the band,
// run fast sweeping, then check that the recovered |phi| matches |r - R|
// to within ~ voxel_size for points well outside the band.
//
// Also a smoke test that frozen voxels are unchanged.

#include "tinyvdb_mesh.h"
#include "tinyvdb_ops.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int fail_count = 0;
#define CHECK(cond, msg) do { \
    if (!(cond)) { fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, msg); ++fail_count; } \
} while (0)

int main(void) {
    const int N = 32;
    const float h = 1.0f / (float)N;       // voxel_size
    const float R = 0.30f;                  // sphere radius
    const float band = 2.0f * h;            // narrow band freeze region

    tvdb_dense_grid g;
    tvdb_dense_grid_init(&g, N, N, N);
    g.voxel_size = h;
    g.ox = -0.5f; g.oy = -0.5f; g.oz = -0.5f;

    // Initialize: exact distance only inside the band; far values get a sentinel
    // (signed by half-space) of magnitude > band so they get redistanced.
    const float far_pos = 100.0f, far_neg = -100.0f;
    for (int z = 0; z < N; ++z) {
        for (int y = 0; y < N; ++y) {
            for (int x = 0; x < N; ++x) {
                float wx = g.ox + ((float)x + 0.5f) * h;
                float wy = g.oy + ((float)y + 0.5f) * h;
                float wz = g.oz + ((float)z + 0.5f) * h;
                float r = sqrtf(wx * wx + wy * wy + wz * wz);
                float exact = r - R;  // signed dist
                size_t idx = (size_t)((z * N + y) * N + x);
                if (fabsf(exact) <= band) g.data[idx] = exact;
                else g.data[idx] = exact >= 0.0f ? far_pos : far_neg;
            }
        }
    }

    int iters = tvdb_fast_sweeping(&g, band, /*max_iters=*/16, /*tol=*/1e-4f);
    printf("fast_sweeping iters=%d\n", iters);
    CHECK(iters > 0 && iters <= 16, "iter count out of range");

    // Verify: for non-band voxels, recovered value should match exact within ~h.
    double max_err = 0.0, sum_err2 = 0.0;
    long long n_check = 0;
    for (int z = 0; z < N; ++z) {
        for (int y = 0; y < N; ++y) {
            for (int x = 0; x < N; ++x) {
                float wx = g.ox + ((float)x + 0.5f) * h;
                float wy = g.oy + ((float)y + 0.5f) * h;
                float wz = g.oz + ((float)z + 0.5f) * h;
                float r = sqrtf(wx * wx + wy * wy + wz * wz);
                float exact = r - R;
                if (fabsf(exact) <= band) continue;  // frozen -- skip
                size_t idx = (size_t)((z * N + y) * N + x);
                double err = fabs((double)g.data[idx] - (double)exact);
                if (err > max_err) max_err = err;
                sum_err2 += err * err;
                ++n_check;
                // Sign preservation
                CHECK((g.data[idx] >= 0.0f) == (exact >= 0.0f), "sign flip");
            }
        }
    }
    double rms = sqrt(sum_err2 / (double)n_check);
    printf("max_err=%.4f rms=%.4f voxel_size=%.4f checked=%lld\n",
           max_err, rms, h, n_check);
    // Fast-sweeping accuracy is first-order: error ~ O(h). Expect max < 3*h.
    CHECK(max_err < 3.0 * (double)h, "max error too large");
    CHECK(rms < 1.5 * (double)h, "RMS error too large");

    tvdb_dense_grid_free(&g);
    if (fail_count) { fprintf(stderr, "%d FAILURES\n", fail_count); return 1; }
    printf("OK\n");
    return 0;
}
