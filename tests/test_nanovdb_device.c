/* The GPU level-set sampler reads NanoVDB buffers directly
 * (src/tinyvdb_nanovdb_device.h, compiled by NVRTC/hiprtc as well). This tests
 * that accessor on the host against the CPU reference tree lookup: leaf
 * voxels, internal-node tiles, root tiles and the background, for a generated
 * 5-4-3 grid with a narrow band, interior tiles and negative coordinates. */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "sdf_tree_fixture.h"
#include "tinyvdb_nanovdb_device.h"
#include "tinyvdb_tree_internal.h"

#define CHECK(x)                                                              \
  do {                                                                        \
    if (!(x)) {                                                               \
      fprintf(stderr, "line %d: %s\n", __LINE__, #x);                         \
      return 1;                                                               \
    }                                                                         \
  } while (0)

/* tvdb_grid_to_nanovdb lives in tinyvdb_to_nanovdb.c; tinyvdb_nanovdb.h would
 * redefine the shared io types, so declare what this test needs. */
tvdb_status_t tvdb_grid_to_nanovdb(const tvdb_grid_t *grid, uint8_t **out_data,
                                   size_t *out_size, tvdb_error_t *err);

static int compare(const tvdb_tree_index *ix, const uint8_t *bytes, size_t size,
                   int32_t bmin[3], int32_t bmax[3], int step, long *checked,
                   int *shown) {
  tvdb_nvdb_grid g;
  g.base = bytes;
  g.size = (tvdb_nvdb_u64)size;
  for (int32_t x = bmin[0] - step; x <= bmax[0] + step; x += step)
    for (int32_t y = bmin[1] - step; y <= bmax[1] + step; y += step)
      for (int32_t z = bmin[2] - step; z <= bmax[2] + step; z += step) {
        const int32_t c[3] = {x, y, z};
        const float want = tvdb_tree_get(ix, c, NULL);
        const float got = tvdb_nvdb_get(&g, x, y, z);
        ++*checked;
        if (got != want) {
          if (*shown < 8) {
            fprintf(stderr, "(%d,%d,%d): tree %g, nanovdb %g\n", x, y, z, (double)want,
                    (double)got);
            ++*shown;
          }
          return 0;
        }
      }
  return 1;
}

int main(void) {
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  long checked = 0;
  int shown = 0;

  /* A sphere so the grid has a narrow band and flood-filled interior tiles. */
  tvdb_grid_t grid;
  memset(&grid, 0, sizeof(grid));
  CHECK(sdf_fixture_cube(&grid, 64, 1, 1));
  tvdb_tree_index ix;
  memset(&ix, 0, sizeof(ix));
  CHECK(tvdb_tree_index_create(&grid, 1, &ix, &err) == TVDB_OK);
  CHECK(ix.has_bbox);
  uint8_t *bytes = NULL;
  size_t size = 0;
  CHECK(tvdb_grid_to_nanovdb(&grid, &bytes, &size, &err) == TVDB_OK);
  CHECK(bytes != NULL && size > TVDB_NVDB_GRID_BYTES);
  int32_t bmin[3] = {ix.bbox_min[0], ix.bbox_min[1], ix.bbox_min[2]};
  int32_t bmax[3] = {ix.bbox_max[0], ix.bbox_max[1], ix.bbox_max[2]};
  CHECK(compare(&ix, bytes, size, bmin, bmax, 1, &checked, &shown));
  printf("nanovdb device sampler: %ld voxels match the tree\n", checked);
  free(bytes);
  tvdb_tree_index_destroy(&ix);
  tvdb_grid_destroy_owned(&grid);

  /* Coarse grid: leaf-local and node-local slot arithmetic over a big range
   * (upper/lower nodes, negative coordinates, background far outside). */
  memset(&grid, 0, sizeof(grid));
  CHECK(sdf_fixture_cube(&grid, 33, 1, 0));
  memset(&ix, 0, sizeof(ix));
  CHECK(tvdb_tree_index_create(&grid, 1, &ix, &err) == TVDB_OK);
  bytes = NULL;
  size = 0;
  CHECK(tvdb_grid_to_nanovdb(&grid, &bytes, &size, &err) == TVDB_OK);
  bmin[0] = ix.bbox_min[0] - 40;
  bmin[1] = ix.bbox_min[1] - 40;
  bmin[2] = ix.bbox_min[2] - 40;
  bmax[0] = ix.bbox_max[0] + 40;
  bmax[1] = ix.bbox_max[1] + 40;
  bmax[2] = ix.bbox_max[2] + 40;
  CHECK(compare(&ix, bytes, size, bmin, bmax, 7, &checked, &shown));
  printf("nanovdb device sampler: %ld voxels match the tree (coarse grid)\n", checked);
  free(bytes);
  tvdb_tree_index_destroy(&ix);
  tvdb_grid_destroy_owned(&grid);

  /* Truncated buffers must fall back to the background, not read past the end. */
  {
    tvdb_nvdb_grid g;
    g.base = (const uint8_t *)"";
    g.size = 0;
    CHECK(tvdb_nvdb_get(&g, 0, 0, 0) == 0.0f);
  }
  puts("nanovdb device sampler: ok");
  return 0;
}
