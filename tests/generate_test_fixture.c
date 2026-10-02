/* Analytic test data, generated outside the source tree. */
#include <math.h>
#include <stdio.h>

#include "tinyvdb_tree.h"

int main(int argc, char** argv) {
  tvdb_file_t file = {0};
  tvdb_error_t err = {0};
  tvdb_sparse_grid samples = {0};
  tvdb_grid_t band = {0}, filled = {0};
  int ok = argc == 3;
  if (ok) ok = tvdb_file_open(&file, argv[1], NULL, &err) == TVDB_OK;
  if (ok)
    ok = tvdb_read_all_grids(&file, &err) == TVDB_OK && file.num_grids > 0;
  if (ok) ok = tvdb_sparse_grid_reserve(&samples, 17 * 17 * 17);
  if (ok) {
    for (int x = -8; x <= 8; ++x)
      for (int y = -8; y <= 8; ++y)
        for (int z = -8; z <= 8; ++z) {
          float phi = sqrtf((float)(x * x + y * y + z * z)) - 5;
          if (fabsf(phi) >= 3) continue;
          samples.coords[samples.count] = (tvdb_vec3i){x, y, z};
          samples.values[samples.count++] = phi;
        }
    ok = tvdb_grid_from_sparse_using_template(file.grids, &samples, "sphere", 3,
                                              &band);
  }
  if (ok)
    ok = tvdb_grid_signed_flood_fill(&band, 3, -3, &filled, &err) == TVDB_OK;
  if (ok) {
    tvdb_file_t output = {0};
    output.alloc = file.alloc;
    output.num_grids = 1;
    output.grids = &filled;
    ok = tvdb_file_save(&output, argv[2], TVDB_COMPRESS_ZIP, 5, 0, &err) ==
         TVDB_OK;
  }
  if (!ok) fprintf(stderr, "Cannot generate test fixture: %s\n", err.message);
  tvdb_grid_destroy_owned(&filled);
  tvdb_grid_destroy_owned(&band);
  tvdb_sparse_grid_free(&samples);
  tvdb_file_close(&file);
  return ok ? 0 : 1;
}
