#include "tinyvdb_ops.h"
#include <stdlib.h>
#include <string.h>

void tvdb_dense_vec_grid_init(tvdb_dense_vec_grid* grid, int nx, int ny, int nz) {
  grid->nx = nx; grid->ny = ny; grid->nz = nz;
  grid->data = (float*)malloc((size_t)nx * ny * nz * 3 * sizeof(float));
}

void tvdb_dense_vec_grid_free(tvdb_dense_vec_grid* grid) {
  if (grid->data) free(grid->data);
  grid->data = NULL;
}

void tvdb_dilate(tvdb_dense_grid* grid, int iterations) { /* TODO */ }
void tvdb_erode(tvdb_dense_grid* grid, int iterations) { /* TODO */ }
void tvdb_open(tvdb_dense_grid* grid, int iterations) { /* TODO */ }
void tvdb_close(tvdb_dense_grid* grid, int iterations) { /* TODO */ }

void tvdb_gaussian_filter(tvdb_dense_grid* grid, int width, int iterations) { /* TODO */ }
void tvdb_mean_filter(tvdb_dense_grid* grid, int width, int iterations) { /* TODO */ }
void tvdb_laplacian_filter(tvdb_dense_grid* grid, int iterations) { /* TODO */ }

void tvdb_csg_union(const tvdb_dense_grid* a, const tvdb_dense_grid* b, tvdb_dense_grid* result) { /* TODO */ }
void tvdb_csg_intersection(const tvdb_dense_grid* a, const tvdb_dense_grid* b, tvdb_dense_grid* result) { /* TODO */ }
void tvdb_csg_difference(const tvdb_dense_grid* a, const tvdb_dense_grid* b, tvdb_dense_grid* result) { /* TODO */ }

float tvdb_surface_area(const tvdb_dense_grid* grid) { return 0.0f; }
float tvdb_volume(const tvdb_dense_grid* grid) { return 0.0f; }

void tvdb_gradient(const tvdb_dense_grid* scalar, tvdb_dense_vec_grid* grad) { /* TODO */ }
void tvdb_divergence(const tvdb_dense_vec_grid* vec, tvdb_dense_grid* div) { /* TODO */ }
void tvdb_laplacian(const tvdb_dense_grid* scalar, tvdb_dense_grid* laplacian) { /* TODO */ }
void tvdb_curl(const tvdb_dense_vec_grid* vec, tvdb_dense_vec_grid* curl) { /* TODO */ }

float tvdb_central_diff_x(const tvdb_dense_grid* g, int ix, int iy, int iz) { return 0.0f; }
float tvdb_central_diff_y(const tvdb_dense_grid* g, int ix, int iy, int iz) { return 0.0f; }
float tvdb_central_diff_z(const tvdb_dense_grid* g, int ix, int iy, int iz) { return 0.0f; }

void tvdb_advect_semi_lagrangian(const tvdb_dense_grid* field,
                                 const tvdb_dense_vec_grid* velocity,
                                 float dt,
                                 tvdb_dense_grid* result) { /* TODO */ }

int tvdb_solve_poisson(const tvdb_dense_grid* rhs, tvdb_dense_grid* x, int max_iters, float tolerance) { return 0; }
