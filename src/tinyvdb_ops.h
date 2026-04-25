#pragma once

#ifdef __cplusplus
extern "C" {
#endif

#include "tinyvdb_mesh.h"

// Dense vector grid (3-component)
typedef struct {
  int nx, ny, nz;
  float ox, oy, oz;
  float voxel_size;
  float* data; // nx * ny * nz * 3, interleaved
} tvdb_dense_vec_grid;

// Phase 1: Morphology
void tvdb_dilate(tvdb_dense_grid* grid, int iterations);
void tvdb_erode(tvdb_dense_grid* grid, int iterations);
void tvdb_open(tvdb_dense_grid* grid, int iterations);
void tvdb_close(tvdb_dense_grid* grid, int iterations);

// Phase 1: Filtering
void tvdb_gaussian_filter(tvdb_dense_grid* grid, int width, int iterations);
void tvdb_mean_filter(tvdb_dense_grid* grid, int width, int iterations);
void tvdb_laplacian_filter(tvdb_dense_grid* grid, int iterations);

// Phase 1: CSG
void tvdb_csg_union(const tvdb_dense_grid* a, const tvdb_dense_grid* b, tvdb_dense_grid* result);
void tvdb_csg_intersection(const tvdb_dense_grid* a, const tvdb_dense_grid* b, tvdb_dense_grid* result);
void tvdb_csg_difference(const tvdb_dense_grid* a, const tvdb_dense_grid* b, tvdb_dense_grid* result);

// Phase 1: Measurement
float tvdb_surface_area(const tvdb_dense_grid* grid);
float tvdb_volume(const tvdb_dense_grid* grid);

// Phase 2: Differential operators
void tvdb_gradient(const tvdb_dense_grid* scalar, tvdb_dense_vec_grid* grad);
void tvdb_divergence(const tvdb_dense_vec_grid* vec, tvdb_dense_grid* div);
void tvdb_laplacian(const tvdb_dense_grid* scalar, tvdb_dense_grid* laplacian);
void tvdb_curl(const tvdb_dense_vec_grid* vec, tvdb_dense_vec_grid* curl);

// Phase 2: Finite differences
float tvdb_central_diff_x(const tvdb_dense_grid* g, int ix, int iy, int iz);
float tvdb_central_diff_y(const tvdb_dense_grid* g, int ix, int iy, int iz);
float tvdb_central_diff_z(const tvdb_dense_grid* g, int ix, int iy, int iz);

// Phase 2: Advection
void tvdb_advect_semi_lagrangian(const tvdb_dense_grid* field,
                                 const tvdb_dense_vec_grid* velocity,
                                 float dt,
                                 tvdb_dense_grid* result);

// Phase 2: Poisson solver
int tvdb_solve_poisson(const tvdb_dense_grid* rhs,
                       tvdb_dense_grid* x,
                       int max_iters,
                       float tolerance);

// Higher-precision Poisson solve. Identical interface to tvdb_solve_poisson
// but performs all CG iterates and the 7-point Laplacian apply in fp64
// internally (input/output remain fp32). Use when the fp32 path stalls or
// for grids large enough that fp32 rounding limits convergence (≥ 64^3).
// Returns iterations used.
int tvdb_solve_poisson_d(const tvdb_dense_grid* rhs,
                         tvdb_dense_grid* x,
                         int max_iters,
                         double tolerance);

// Memory management
void tvdb_dense_vec_grid_init(tvdb_dense_vec_grid* grid, int nx, int ny, int nz);
void tvdb_dense_vec_grid_free(tvdb_dense_vec_grid* grid);

#ifdef __cplusplus
}
#endif
