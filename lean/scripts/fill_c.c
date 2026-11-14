/* Differential harness: tvdb_signed_flood_fill (dense) over seeded random
 * grids, printing the post-fill sign map for comparison against the Lean
 * twin (Vdb.FillCheck).
 *
 * Both sides generate the same 8x8x8 grids from the same LCG as the other
 * harnesses (u = next() % 100000, value = u/100000 - 0.5), run the same
 * fill with band = 0.25, and print one line per case:
 *
 *   case i sign*
 *
 * where sign is '+' for a far voxel filled exterior, '-' for a far voxel
 * filled interior, and '.' for a band voxel (left unchanged). Exact byte
 * comparison.
 *
 * Build: cc -O2 -std=c11 -I<repo>/src -c fill_c.c + link against the lib.
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
    enum { N = 400, NX = 8, NY = 8, NZ = 8 };
    const float band = 0.25f;
    g_state = 0x9e3779b97f4a7c15ULL;
    for (int case_i = 0; case_i < N; ++case_i) {
        tvdb_dense_grid g = {0};
        tvdb_dense_grid_init(&g, NX, NY, NZ);
        if (!g.data) return 1;
        for (int k = 0; k < NZ; ++k)
            for (int j = 0; j < NY; ++j)
                for (int i = 0; i < NX; ++i) {
                    uint64_t u = next_rand() % 100000;
                    size_t idx = ((size_t)k * NY + j) * NX + i;
                    g.data[idx] = (float)((double)u / 100000.0 - 0.5);
                }
        tvdb_signed_flood_fill(&g, band);
        printf("case %d ", case_i);
        for (int k = 0; k < NZ; ++k)
            for (int j = 0; j < NY; ++j)
                for (int i = 0; i < NX; ++i) {
                    size_t idx = ((size_t)k * NY + j) * NX + i;
                    float v = g.data[idx];
                    char c = fabsf(v) < band ? '.' : (v > 0.0f ? '+' : '-');
                    putchar(c);
                }
        putchar('\n');
        tvdb_dense_grid_free(&g);
    }
    return 0;
}
