// Smoke test for the OpenVDB-tree sparse op bridge. Loads sphere.vdb,
// counts active voxels, extracts active coords + values, materializes a
// dense subregion, and runs a dense op on it.

#include "tinyvdb_io.h"
#include "tinyvdb_sparse_tree.h"
#include "tinyvdb_sparse.h"
#include "tinyvdb_mesh.h"
#include "tinyvdb_ops.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int g_failures = 0;
#define EXPECT(cond) do { if (!(cond)) { \
  fprintf(stderr, "FAIL [%s:%d]: %s\n", __FILE__, __LINE__, #cond); \
  ++g_failures; } } while (0)

int main(int argc, char **argv) {
    const char *path = argc > 1 ? argv[1] : "../sphere.vdb";

    tvdb_file_t file;
    memset(&file, 0, sizeof(file));
    tvdb_error_t err = {0};
    if (tvdb_file_open(&file, path, NULL, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL: tvdb_file_open(%s): %s\n", path, err.message);
        return 1;
    }
    if (tvdb_read_all_grids(&file, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL: tvdb_read_all_grids: %s\n", err.message);
        tvdb_file_close(&file);
        return 1;
    }
    if (file.num_grids == 0) {
        fprintf(stderr, "FAIL: file has no grids\n");
        tvdb_file_close(&file);
        return 1;
    }

    const tvdb_grid_t *grid = &file.grids[0];
    printf("[bridge] grid name='%s' type='%s' levels=%d\n",
           grid->descriptor.grid_name ? grid->descriptor.grid_name : "(none)",
           grid->descriptor.grid_type ? grid->descriptor.grid_type : "(none)",
           grid->tree.layout.num_levels);

    // Count active voxels.
    size_t n_active = tvdb_grid_active_voxel_count(grid);
    printf("[bridge] active voxels: %zu\n", n_active);
    EXPECT(n_active > 0);

    // BBox.
    int32_t bb_min[3], bb_max[3];
    bool ok_bbox = tvdb_grid_active_bbox(grid, bb_min, bb_max);
    EXPECT(ok_bbox);
    printf("[bridge] active bbox: [%d, %d, %d] x [%d, %d, %d]\n",
           bb_min[0], bb_min[1], bb_min[2], bb_max[0], bb_max[1], bb_max[2]);

    // Sparse extraction.
    tvdb_sparse_grid sg; tvdb_sparse_grid_init(&sg);
    EXPECT(tvdb_grid_to_sparse(grid, &sg));
    EXPECT(sg.count == n_active);
    printf("[bridge] sparse count = %zu (matches active count: %s)\n",
           sg.count, sg.count == n_active ? "yes" : "no");

    // Dense materialization of the active bbox.
    tvdb_dense_grid dense;
    bool ok = tvdb_grid_materialize_dense(grid, bb_min, bb_max,
                                          0.0f, /*background*/ &dense);
    EXPECT(ok);
    EXPECT(dense.nx == bb_max[0] - bb_min[0]);
    EXPECT(dense.ny == bb_max[1] - bb_min[1]);
    EXPECT(dense.nz == bb_max[2] - bb_min[2]);
    printf("[bridge] dense materialized %dx%dx%d at origin (%.3f, %.3f, %.3f) vs=%.3f\n",
           dense.nx, dense.ny, dense.nz, dense.ox, dense.oy, dense.oz, dense.voxel_size);

    // Run a dense op on the materialized region — surface_area should be > 0
    // for an SDF-like grid (sphere.vdb).
    float sa = tvdb_surface_area(&dense);
    float vol = tvdb_volume(&dense);
    printf("[bridge] dense surface_area = %.4f, volume = %.4f\n", sa, vol);
    EXPECT(sa > 0.0f);

    // Leaf-stamp dilate (1 iteration) — values should generally decrease for
    // SDF (each cell takes min of self + 6 neighbors). Topology is preserved,
    // so output count should match input active count.
    tvdb_sparse_grid dilated; tvdb_sparse_grid_init(&dilated);
    EXPECT(tvdb_grid_dilate_active(grid, 1, &dilated));
    EXPECT(dilated.count == n_active);

    // For an SDF, after dilation the sum of values should DECREASE
    // (more cells become more negative since neighbors were closer to surface).
    double in_sum = 0.0, out_sum = 0.0;
    for (size_t i = 0; i < sg.count; ++i)      in_sum  += sg.values[i];
    for (size_t i = 0; i < dilated.count; ++i) out_sum += dilated.values[i];
    printf("[bridge] dilate: in_sum=%.4f out_sum=%.4f (delta=%.4f)\n",
           in_sum, out_sum, out_sum - in_sum);
    EXPECT(out_sum <= in_sum + 1e-3);

    tvdb_sparse_grid eroded; tvdb_sparse_grid_init(&eroded);
    EXPECT(tvdb_grid_erode_active(grid, 1, &eroded));
    EXPECT(eroded.count == n_active);
    double er_sum = 0.0;
    for (size_t i = 0; i < eroded.count; ++i) er_sum += eroded.values[i];
    printf("[bridge] erode:  in_sum=%.4f out_sum=%.4f (delta=%.4f)\n",
           in_sum, er_sum, er_sum - in_sum);
    EXPECT(er_sum >= in_sum - 1e-3);

    // Multi-iteration: 2 iterations should produce a strictly larger delta than 1.
    tvdb_sparse_grid dilated2; tvdb_sparse_grid_init(&dilated2);
    EXPECT(tvdb_grid_dilate_active(grid, 2, &dilated2));
    double out2_sum = 0.0;
    for (size_t i = 0; i < dilated2.count; ++i) out2_sum += dilated2.values[i];
    printf("[bridge] dilate(2): out_sum=%.4f\n", out2_sum);
    EXPECT(out2_sum <= out_sum);

    tvdb_sparse_grid_free(&dilated);
    tvdb_sparse_grid_free(&dilated2);
    tvdb_sparse_grid_free(&eroded);
    tvdb_sparse_grid_free(&sg);
    tvdb_dense_grid_free(&dense);
    tvdb_file_close(&file);

    if (g_failures == 0) {
        printf("\nAll bridge tests passed.\n");
        return 0;
    } else {
        printf("\n%d failure(s).\n", g_failures);
        return 1;
    }
}
