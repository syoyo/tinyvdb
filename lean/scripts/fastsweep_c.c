/* Differential harness: tvdb_fast_sweeping (dense 3D Eikonal solver).
 *
 * Generates the same seeded 8x8x8 random grids as the Lean twin
 * (Vdb.FastSweepCheck, same LCG and value mapping), runs the solver with
 * frozen_band = 0.25, voxel_size = 0.25, max_iters = 10, tol = 1e-6,
 * and prints the FINAL grid: "case i idx value" with %.17e for every voxel.
 *
 * The Lean twin regenerates the same seeds, recomputes the sweep, and
 * compares every voxel (abs diff <= 1e-5 * h, exact sign identity).
 *
 * Build: cc -O2 -std=c11 -I<repo>/src fastsweep_c.c <sources...> -lm -o fastsweep_c
 */
#if !defined(_WIN32) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 199309L
#endif
#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_mesh.h"
#include "tinyvdb_ops.h"

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

int main(void) {
    enum { N = 200, NX = 8, NY = 8, NZ = 8 };
    const float band = 0.25f;
    g_state = 0x9e3779b97f4a7c15ULL;
    for (int case_i = 0; case_i < N; ++case_i) {
        tvdb_dense_grid g = {0};
        tvdb_dense_grid_init(&g, NX, NY, NZ);
        if (!g.data) return 1;
        g.voxel_size = 0.25f;
        for (int k = 0; k < NZ; ++k)
            for (int j = 0; j < NY; ++j)
                for (int i = 0; i < NX; ++i) {
                    uint64_t u = next_rand() % 100000;
                    size_t idx = ((size_t)k * NY + j) * NX + i;
                    g.data[idx] = (float)((double)u / 100000.0 - 0.5);
                }
        int iters = tvdb_fast_sweeping(&g, band, 10, 1e-6f);
        printf("case %d iters %d\n", case_i, iters);
        for (int k = 0; k < NZ; ++k)
            for (int j = 0; j < NY; ++j)
                for (int i = 0; i < NX; ++i) {
                    size_t idx = ((size_t)k * NY + j) * NX + i;
                    printf("case %d %zu %.17e\n", case_i, idx, g.data[idx]);
                }
        tvdb_dense_grid_free(&g);
    }
    return 0;
}
