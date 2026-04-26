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

// Fast Sweeping: solve the Eikonal equation |∇φ|=1 on a dense grid to
// redistance an SDF away from its zero-crossing band. Voxels with
// |grid->data[i]| <= frozen_band are treated as boundary conditions (kept
// fixed); all other voxels are recomputed from the upwind 3D quadratic
// (Zhao 2005) using `voxel_size` as the metric. The solver runs eight
// directional sweeps per iteration and stops when no update exceeds
// `tol` (in world units) or after `max_iters` iterations. Sign of each
// non-frozen voxel is preserved from its initial value (positive vs negative
// half-space) so an outside-positive / inside-negative SDF is reproduced.
// Returns the number of iterations executed.
int tvdb_fast_sweeping(tvdb_dense_grid* grid, float frozen_band,
                       int max_iters, float tol);

// Memory management
void tvdb_dense_vec_grid_init(tvdb_dense_vec_grid* grid, int nx, int ny, int nz);
void tvdb_dense_vec_grid_free(tvdb_dense_vec_grid* grid);

// =============================================================================
// fp64 dense grid (`tvdb_dense_grid_d`). Mirrors `tvdb_dense_grid` but uses
// double for storage and world-space metrics. A subset of ops is provided
// where fp64 accuracy is most valuable (Poisson, Eikonal, large-grid CSG,
// volume/surface integrals). For ops not in this subset, convert to fp32
// via `tvdb_dense_grid_d_to_f` and use the fp32 path.
// =============================================================================

typedef struct {
  int nx, ny, nz;
  double ox, oy, oz;
  double voxel_size;
  double* data;
} tvdb_dense_grid_d;

void tvdb_dense_grid_d_init(tvdb_dense_grid_d* grid, int nx, int ny, int nz);
void tvdb_dense_grid_d_free(tvdb_dense_grid_d* grid);

// fp32 <-> fp64 deep-copy converters. `out` must be uninitialized; on
// return it owns its data and the caller frees with the matching free fn.
// Voxel-size and origin are widened/narrowed accordingly.
void tvdb_dense_grid_f_to_d(const tvdb_dense_grid* in, tvdb_dense_grid_d* out);
void tvdb_dense_grid_d_to_f(const tvdb_dense_grid_d* in, tvdb_dense_grid* out);

// Sampling
double tvdb_sample_trilinear_dense_d(const tvdb_dense_grid_d* g,
                                     double wx, double wy, double wz);

// Differential
void tvdb_laplacian_d(const tvdb_dense_grid_d* scalar, tvdb_dense_grid_d* laplacian);

// CSG
void tvdb_csg_union_d(const tvdb_dense_grid_d* a, const tvdb_dense_grid_d* b, tvdb_dense_grid_d* result);
void tvdb_csg_intersection_d(const tvdb_dense_grid_d* a, const tvdb_dense_grid_d* b, tvdb_dense_grid_d* result);
void tvdb_csg_difference_d(const tvdb_dense_grid_d* a, const tvdb_dense_grid_d* b, tvdb_dense_grid_d* result);

// Measurement (zero-crossing 6-edge area; volume of `value < 0` half-space)
double tvdb_surface_area_d(const tvdb_dense_grid_d* grid);
double tvdb_volume_d(const tvdb_dense_grid_d* grid);

// FastSweeping (full fp64 path)
int tvdb_fast_sweeping_d(tvdb_dense_grid_d* grid, double frozen_band,
                         int max_iters, double tol);

// Poisson solver: fp64 input/output, fp64 internals.
// (Distinct from `tvdb_solve_poisson_d` which takes fp32 in/out with fp64
// internals.) Returns iterations used.
int tvdb_solve_poisson_dd(const tvdb_dense_grid_d* rhs,
                          tvdb_dense_grid_d* x,
                          int max_iters,
                          double tolerance);

#ifdef __cplusplus
}
#endif
