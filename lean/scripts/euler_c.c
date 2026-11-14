/* Differential harness: tvdb_level_set_euler_characteristic (dense SDF).
 *
 * Generates the same seeded 5x5x5 random grids as the Lean twin
 * (Vdb.EulerCheck, same LCG and value mapping, isovalue 0) and prints
 * "case i value" with the C return value (2 * chi(solid), i.e. the
 * Euler characteristic of the isosurface, by Poincare-Lefschetz).
 *
 * Build: cc -O2 -std=c11 -I<repo>/src euler_c.c <sources...> -lm -o euler_c
 */
#if !defined(_WIN32) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200809L
#endif
#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_mesh.h"
#include "tinyvdb_levelset.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t g_state;
static uint64_t next_rand(void) {
    g_state = g_state * 6364136223846793005ULL + 1442695040888963407ULL;
    return g_state >> 33;
}

int main(void) {
    enum { N = 400 };
    const float iso = 0.0f;
    g_state = 0x9e3779b97f4a7c15ULL;
    for (int case_i = 0; case_i < N; ++case_i) {
        tvdb_dense_grid g = {0};
        tvdb_dense_grid_init(&g, 5, 5, 5);
        if (!g.data) return 1;
        for (int k = 0; k < 5; ++k)
            for (int j = 0; j < 5; ++j)
                for (int i = 0; i < 5; ++i) {
                    uint64_t u = next_rand() % 100000;
                    size_t idx = ((size_t)k * 5 + j) * 5 + i;
                    g.data[idx] = (float)((double)u / 100000.0 - 0.5);
                }
        double chi2 = tvdb_level_set_euler_characteristic(&g, iso);
        printf("case %d %.17e\n", case_i, chi2);
        tvdb_dense_grid_free(&g);
    }
    return 0;
}
