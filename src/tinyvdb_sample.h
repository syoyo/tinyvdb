#pragma once

// Trilinear sampling and splatting on dense scalar / vector grids,
// plus simple world<->voxel coordinate transforms.

#include <stddef.h>
#include "tinyvdb_mesh.h"   // tvdb_dense_grid, tvdb_vec3f
#include "tinyvdb_ops.h"    // tvdb_dense_vec_grid

#ifdef __cplusplus
extern "C" {
#endif

// Sampling context: validates the grid once and caches the world->voxel
// constants, avoiding per-query validation and repeated divisions. Build one
// per grid and reuse for many queries (render, ray marching, gradients).
typedef struct tvdb_sampler {
  const float* data;
  int nx, ny, nz;
  double inv_vs;
  double ox, oy, oz;
} tvdb_sampler;

// Returns true on success. On failure the context is invalidated and queries
// return 0.
bool tvdb_sampler_init(tvdb_sampler* s, const tvdb_dense_grid* g);
float tvdb_sampler_trilinear(const tvdb_sampler* s, float wx, float wy, float wz);
float tvdb_sampler_quadratic(const tvdb_sampler* s, float wx, float wy, float wz);

// Sample a dense scalar grid at world-space point (wx, wy, wz).
// Out-of-range queries clamp to the grid edge.
float tvdb_sample_trilinear_dense(const tvdb_dense_grid* g,
                                  float wx, float wy, float wz);

// Batched scalar sampler.
void tvdb_sample_trilinear_dense_batch(const tvdb_dense_grid* g,
                                       const tvdb_vec3f* pts,
                                       size_t n,
                                       float* out);

// Triquadratic sampling (parallels OpenVDB QuadraticSampler / fvdb higher-order
// sample): smoother than trilinear via a 3x3x3 stencil, per-axis 3-point
// parabola. Out-of-range queries clamp to the grid edge.
float tvdb_sample_quadratic_dense(const tvdb_dense_grid* g,
                                  float wx, float wy, float wz);
void tvdb_sample_quadratic_dense_batch(const tvdb_dense_grid* g,
                                       const tvdb_vec3f* pts,
                                       size_t n,
                                       float* out);

// Sample a 3-component vector grid at world-space point.
void tvdb_sample_trilinear_vec_dense(const tvdb_dense_vec_grid* g,
                                     float wx, float wy, float wz,
                                     tvdb_vec3f* out);

// Splat (inverse interpolation): scatter point values onto a dense grid using
// trilinear weights. The grid is expected to be zero-initialized; callers
// must allocate a separate weight buffer (same shape) if they want a
// normalized average.
void tvdb_splat_trilinear_dense(tvdb_dense_grid* g,
                                const tvdb_vec3f* pts,
                                const float* vals,
                                size_t n,
                                float* weights /* nullable */);

// Triquadratic splat: the scatter adjoint of tvdb_sample_quadratic_dense
// (3x3x3 stencil, per-axis 3-point parabola weights). As with the trilinear
// splat, out-of-range taps are skipped and the grid/weights are accumulated in
// place (zero them first).
void tvdb_splat_quadratic_dense(tvdb_dense_grid* g,
                                const tvdb_vec3f* pts,
                                const float* vals,
                                size_t n,
                                float* weights /* nullable */);

// Coordinate transforms. xform is a 4x3 row-major matrix (3x3 linear + 3
// translation): [m00 m01 m02 tx, m10 m11 m12 ty, m20 m21 m22 tz].
// world_to_voxel applies the transform to convert world points into
// voxel-index space; voxel_to_world is the inverse (for rotations + uniform
// scale, the inverse is straightforward; for general affine, callers should
// provide the precomputed inverse).
void tvdb_apply_xform(const float xform[12],
                      const tvdb_vec3f* in,
                      tvdb_vec3f* out,
                      size_t n);

#ifdef __cplusplus
}
#endif
