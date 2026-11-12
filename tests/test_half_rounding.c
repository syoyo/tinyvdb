/* Half-float writer regression test.
 *
 * The scalar and F16C float-to-half encoders must agree: round to nearest,
 * ties to even, preserve NaN (as a quiet NaN) and the sign of zero. The
 * previous scalar encoder truncated instead of rounding, flushed values
 * below 2^-24 to zero and turned NaN into Inf, so SIMD and scalar builds
 * wrote different bytes for the same grid.
 *
 * Builds a float grid from the fixture's template, marks it half-precision,
 * writes and re-reads it, then checks the promoted values:
 *   1 + 2^-12 + 2^-23  ->  1 + 2^-10        (round up, not truncate)
 *   2^-30              ->  +0               (flush)
 *   -0.0f              ->  -0.0f            (sign preserved)
 *   +Inf               ->  +Inf
 *   NaN                ->  NaN
 *
 * The test needs the generated fixture (argv[1]); exits 77 when missing.
 */
#include "tinyvdb_io.h"
#include "tinyvdb_sparse_tree.h"
#include "tinyvdb_tree_internal.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CHECK(cond)                                                            \
  do {                                                                         \
    if (!(cond)) {                                                             \
      fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #cond);          \
      return 1;                                                                \
    }                                                                          \
  } while (0)

static int round_trip(const char *fixture) {
  tvdb_file_t src = {0};
  tvdb_error_t err = {0};
  tvdb_grid_t grid = {0}, back = {0};
  tvdb_file_t rd = {0};
  tvdb_tree_index idx = {0};
  uint8_t *blob = NULL;
  size_t blob_size = 0;
  int rc = 1;

  if (tvdb_file_open(&src, fixture, NULL, &err) != TVDB_OK) {
    fprintf(stderr, "cannot open fixture %s: %s\n", fixture, err.message);
    return 77;
  }
  CHECK(tvdb_read_all_grids(&src, &err) == TVDB_OK);
  CHECK(src.num_grids > 0);

  /* Sample voxels: one per behaviour under test, spread over three leaves. */
  tvdb_vec3i coords[5] = {
      {0, 0, 0}, {1, 0, 0}, {2, 0, 0}, {9, 0, 0}, {10, 0, 0}};
  float values[5];
  values[0] = 1.0f + 0x1p-11f + 0x1p-23f; /* mantissa 0x000801 */
  values[1] = 0x1p-30f;                   /* below half's smallest normal */
  values[2] = -0.0f;
  values[3] = INFINITY;
  values[4] = NAN;

  CHECK(tvdb_grid_from_sparse_typed_using_template(
      &src.grids[0], coords, values, 5, TVDB_VALUE_FLOAT, &values[2] /* bg +0 */
      , "half_round", &grid));
  grid.descriptor.save_float_as_half = 1;

  {
    tvdb_file_t out = {0};
    tvdb_file_init_for_write(&out, NULL);
    out.num_grids = 1;
    out.grids = &grid;
    CHECK(tvdb_write_to_memory(&out, TVDB_COMPRESS_NONE, 0, &blob, &blob_size,
                               &err) == TVDB_OK);
    CHECK(tvdb_file_open_memory(&rd, blob, blob_size, NULL, &err) == TVDB_OK);
    CHECK(tvdb_read_all_grids(&rd, &err) == TVDB_OK);
    CHECK(rd.num_grids == 1);
    back = rd.grids[0];
    /* Detach so the file's owner does not free what we inspect here. The
       grid's metadata keeps a pointer to the reader's allocator, so `rd`
       stays open until `back` is destroyed. */
    memset(rd.grids, 0, sizeof(rd.grids[0]));
    rd.num_grids = 0;
  }

  CHECK(tvdb_tree_index_create(&back, 1, &idx, &err) == TVDB_OK);

  {
    float v0 = tvdb_tree_get(&idx, (const int32_t *)&coords[0], NULL);
    float expect = 1.0f + 0x1p-10f; /* round-to-nearest gives 0x3c01 */
    CHECK(v0 == expect);

    float v1 = tvdb_tree_get(&idx, (const int32_t *)&coords[1], NULL);
    CHECK(v1 == 0.0f && !signbit(v1));

    float v2 = tvdb_tree_get(&idx, (const int32_t *)&coords[2], NULL);
    CHECK(v2 == 0.0f && signbit(v2));

    float v3 = tvdb_tree_get(&idx, (const int32_t *)&coords[3], NULL);
    CHECK(isinf(v3) && v3 > 0.0f);

    float v4 = tvdb_tree_get(&idx, (const int32_t *)&coords[4], NULL);
    CHECK(isnan(v4));
  }

  rc = 0;
  tvdb_tree_index_destroy(&idx);
  tvdb_grid_destroy_owned(&back);
  tvdb_file_close(&rd);
  tvdb_grid_destroy_owned(&grid);
  free(blob);
  tvdb_file_close(&src);
  return rc;
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s <fixture.vdb>\n", argv[0]);
    return 77;
  }
  return round_trip(argv[1]);
}
