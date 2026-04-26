// Tests world<->index transform helpers on tvdb_nanovdb_grid_t.
//
// Two cases:
//   1. Identity-with-voxel-size (uniform scale) — round-trip and direct
//      formula match.
//   2. General affine (rotation + scale + translation) — round-trip
//      preserves coords to ~1e-12.

#include "tinyvdb_nanovdb.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int fails = 0;
#define CHECK_NEAR(a, b, tol, msg) do { \
    double da_ = (double)(a), db_ = (double)(b); \
    if (fabs(da_ - db_) > (tol)) { \
        fprintf(stderr, "FAIL %s:%d: %s (got %.12g, want %.12g, |diff|=%.2e)\n", \
                __FILE__, __LINE__, msg, da_, db_, fabs(da_ - db_)); \
        ++fails; \
    } \
} while (0)

int main(void) {
    // Case 1: uniform-scale 0.25 voxel_size, origin (-0.5, 0.0, 0.5).
    tvdb_nanovdb_grid_t g; memset(&g, 0, sizeof(g));
    g.voxel_size[0] = 0.25; g.voxel_size[1] = 0.25; g.voxel_size[2] = 0.25;
    g.map[0] = 0.25; g.map[1] = 0.0;  g.map[2]  = 0.0;  g.map[3]  = -0.5;
    g.map[4] = 0.0;  g.map[5] = 0.25; g.map[6]  = 0.0;  g.map[7]  =  0.0;
    g.map[8] = 0.0;  g.map[9] = 0.0;  g.map[10] = 0.25; g.map[11] =  0.5;

    double w[3];
    tvdb_status_t st = tvdb_nanovdb_index_to_world(&g, 4, 0, 0, w);
    if (st != TVDB_OK) { fprintf(stderr, "FAIL: index_to_world status\n"); return 1; }
    // index (4,0,0) -> world (4*0.25 + (-0.5), 0+0, 0+0.5) = (0.5, 0.0, 0.5)
    CHECK_NEAR(w[0], 0.5, 1e-12, "uniform i2w x");
    CHECK_NEAR(w[1], 0.0, 1e-12, "uniform i2w y");
    CHECK_NEAR(w[2], 0.5, 1e-12, "uniform i2w z");

    double idx[3];
    st = tvdb_nanovdb_world_to_index(&g, 0.5, 0.0, 0.5, idx);
    if (st != TVDB_OK) { fprintf(stderr, "FAIL: world_to_index status\n"); return 1; }
    CHECK_NEAR(idx[0], 4.0, 1e-12, "uniform w2i x");
    CHECK_NEAR(idx[1], 0.0, 1e-12, "uniform w2i y");
    CHECK_NEAR(idx[2], 0.0, 1e-12, "uniform w2i z");

    // Round-trip on arbitrary coords.
    double pts[][3] = { { 7.3, -2.1, 11.4}, {-100.0, 50.5, 0.25}, {0.0, 0.0, 0.0} };
    for (int t = 0; t < 3; ++t) {
        tvdb_nanovdb_index_to_world(&g, pts[t][0], pts[t][1], pts[t][2], w);
        tvdb_nanovdb_world_to_index(&g, w[0], w[1], w[2], idx);
        CHECK_NEAR(idx[0], pts[t][0], 1e-10, "uniform round-trip x");
        CHECK_NEAR(idx[1], pts[t][1], 1e-10, "uniform round-trip y");
        CHECK_NEAR(idx[2], pts[t][2], 1e-10, "uniform round-trip z");
    }

    // Case 2: a 30deg-around-z rotation + non-uniform scale + translation.
    double cs = cos(0.5235987755982988);  // 30deg
    double sn = sin(0.5235987755982988);
    g.map[0] = 0.5 * cs;  g.map[1] = -0.5 * sn; g.map[2]  = 0.0; g.map[3]  = 1.0;
    g.map[4] = 0.5 * sn;  g.map[5] =  0.5 * cs; g.map[6]  = 0.0; g.map[7]  = 2.0;
    g.map[8] = 0.0;       g.map[9] =  0.0;      g.map[10] = 0.3; g.map[11] = -1.0;
    for (int t = 0; t < 3; ++t) {
        tvdb_nanovdb_index_to_world(&g, pts[t][0], pts[t][1], pts[t][2], w);
        tvdb_nanovdb_world_to_index(&g, w[0], w[1], w[2], idx);
        CHECK_NEAR(idx[0], pts[t][0], 1e-10, "rot/scale round-trip x");
        CHECK_NEAR(idx[1], pts[t][1], 1e-10, "rot/scale round-trip y");
        CHECK_NEAR(idx[2], pts[t][2], 1e-10, "rot/scale round-trip z");
    }

    // Singular matrix returns invalid data error.
    memset(g.map, 0, sizeof(g.map));
    st = tvdb_nanovdb_world_to_index(&g, 1.0, 1.0, 1.0, idx);
    if (st == TVDB_OK) { fprintf(stderr, "FAIL: singular map should fail\n"); ++fails; }

    if (fails) { fprintf(stderr, "%d FAILURES\n", fails); return 1; }
    printf("All NanoVDB transform tests passed.\n");
    return 0;
}
