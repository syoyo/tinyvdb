/* Differential harness: dense CSG (tvdb_csg_union/intersection/difference)
 * over seeded random grids, printed for comparison against the Lean
 * Float32 twin (Vdb.CsgCheck).
 *
 * The same 8x8x8 grids (u/100000-0.5 value mapping, same LCG) are generated
 * on both sides. Tie/zero/NaN injection (identical on both sides):
 *   i %  5 == 3  -> b[i] = a[i]        (exact ties hit both ternary arms)
 *   i % 11 == 0  -> a[i] =  0.0f
 *   i % 13 == 7  -> b[i] = -0.0f
 *   case 7       -> a[0] = NaN
 *   case 19      -> b[0] = NaN
 *
 * Output lines:
 *   case i ins a <512x %08x>   (float bit patterns, little-endian boxes)
 *   case i ins b <512x %08x>
 *   case i op 0|1|2 <512x %08x>  (0 = union, 1 = intersection, 2 = difference)
 *
 * Build: cc -O2 -std=c11 -I<repo>/src csg_c.c <sources...> -lm -o csg_c
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

static unsigned bits_of(float v) {
    unsigned w;
    memcpy(&w, &v, 4);
    return w;
}

static void print_bits(const char* tag, const tvdb_dense_grid* g) {
    printf("%s", tag);
    for (int i = 0; i < 512; ++i) printf(" %08x", bits_of(g->data[i]));
    putchar('\n');
}

int main(void) {
    enum { N = 400 };
    g_state = 0x9e3779b97f4a7c15ULL;
    for (int case_i = 0; case_i < N; ++case_i) {
        tvdb_dense_grid a, b, u, i2, d;
        tvdb_dense_grid_init(&a, 8, 8, 8);
        tvdb_dense_grid_init(&b, 8, 8, 8);
        tvdb_dense_grid_init(&u, 8, 8, 8);
        tvdb_dense_grid_init(&i2, 8, 8, 8);
        tvdb_dense_grid_init(&d, 8, 8, 8);
        a.voxel_size = b.voxel_size = u.voxel_size = i2.voxel_size = d.voxel_size = 0.25f;
        a.ox = b.ox = u.ox = i2.ox = d.ox = -1.0f;
        a.oy = b.oy = u.oy = i2.oy = d.oy = 0.5f;
        a.oz = b.oz = u.oz = i2.oz = d.oz = 2.0f;
        for (int i = 0; i < 512; ++i) {
            uint64_t ua = next_rand() % 100000, ub = next_rand() % 100000;
            float va = (float)((double)ua / 100000.0 - 0.5);
            float vb = (float)((double)ub / 100000.0 - 0.5);
            if (i % 5 == 3) vb = va;         /* tie */
            if (i % 11 == 0) va = 0.0f;      /* +0.0f */
            if (i % 13 == 7) vb = -0.0f;     /* -0.0f */
            if (case_i == 7 && i == 0) va = NAN;
            if (case_i == 19 && i == 0) vb = NAN;
            a.data[i] = va;
            b.data[i] = vb;
        }
        tvdb_csg_union(&a, &b, &u);
        tvdb_csg_intersection(&a, &b, &i2);
        tvdb_csg_difference(&a, &b, &d);
        printf("case %d ins a", case_i);
        print_bits("", &a);
        printf("case %d ins b", case_i);
        print_bits("", &b);
        printf("case %d op 0", case_i);
        print_bits("", &u);
        printf("case %d op 1", case_i);
        print_bits("", &i2);
        printf("case %d op 2", case_i);
        print_bits("", &d);
        tvdb_dense_grid_free(&a);
        tvdb_dense_grid_free(&b);
        tvdb_dense_grid_free(&u);
        tvdb_dense_grid_free(&i2);
        tvdb_dense_grid_free(&d);
    }
    return 0;
}
