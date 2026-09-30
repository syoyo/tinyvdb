#pragma once

// Optional runtime-loaded GPU backend for TinyVDB.
//
// This header intentionally exposes no Vulkan or CUDA SDK types. Backends are
// resolved at runtime, so applications can compile without GPU SDK headers or
// libraries installed.

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "tinyvdb_io.h"     // tvdb_status_t, tvdb_error_t
#include "tinyvdb_mesh.h"   // tvdb_dense_grid, tvdb_vec3f
#include "tinyvdb_ops.h"    // tvdb_dense_vec_grid, tvdb_dense_grid_d
#include "tinyvdb_sparse.h" // tvdb_sparse_grid
#include "tinyvdb_stats.h"  // tvdb_grid_stats_t
#include "tinyvdb_tsdf.h"   // tvdb_depth_frame
#include "tinyvdb_nanovdb.h" // tvdb_projected_gaussian_t, tvdb_raster_output_t, tvdb_gaussian_grad_t

#ifdef __cplusplus
extern "C" {
#endif

typedef enum {
  TVDB_GPU_BACKEND_AUTO = 0,
  TVDB_GPU_BACKEND_VULKAN = 1,
  TVDB_GPU_BACKEND_CUDA = 2
} tvdb_gpu_backend_t;

typedef struct tvdb_gpu_context tvdb_gpu_context_t;
typedef struct tvdb_gpu_buffer tvdb_gpu_buffer_t;
typedef struct tvdb_gpu_dense_grid tvdb_gpu_dense_grid_t;
typedef struct tvdb_gpu_sparse_grid tvdb_gpu_sparse_grid_t;
typedef struct tvdb_gpu_vulkan_sparse_image3d tvdb_gpu_vulkan_sparse_image3d_t;
typedef struct tvdb_gpu_index_map tvdb_gpu_index_map_t;
typedef struct tvdb_gpu_vulkan_sample_batch tvdb_gpu_vulkan_sample_batch_t;

typedef struct {
  tvdb_gpu_backend_t backend;
  char name[128];
  uint32_t device_index;
  int available;
  int supports_sparse_3d_images;
} tvdb_gpu_device_info_t;

typedef struct {
  tvdb_gpu_backend_t backend;
  char device_name[128];
  int supports_sparse_3d_images;
} tvdb_gpu_context_info_t;

// Returns the number of devices written to `devices` (up to `capacity`).
// Passing devices=NULL/capacity=0 returns the number of available runtime
// backends/devices. CUDA enumeration requires both the driver and NVRTC runtime
// libraries because kernels are compiled to PTX at runtime.
size_t tvdb_gpu_enumerate_devices(tvdb_gpu_backend_t backend,
                                  tvdb_gpu_device_info_t* devices,
                                  size_t capacity);

tvdb_status_t tvdb_gpu_context_create(tvdb_gpu_backend_t backend,
                                      uint32_t device_index,
                                      tvdb_gpu_context_t** out,
                                      tvdb_error_t* err);
void tvdb_gpu_context_destroy(tvdb_gpu_context_t* ctx);
// 1 when this build contains GPU SPIR-V, 0 when the shaders are the all-zero
// fallback include (built without glslangValidator). In the latter case a context
// still creates and every op returns TVDB_ERROR_UNIMPLEMENTED, so this is how a
// caller or a test tells "not built for this" from "genuinely unsupported".
int tvdb_gpu_spirv_available(void);

tvdb_status_t tvdb_gpu_context_info(const tvdb_gpu_context_t* ctx,
                                    tvdb_gpu_context_info_t* out,
                                    tvdb_error_t* err);

// Blocking high-level operations. They upload inputs, dispatch one GPU kernel,
// copy the result back, and return only after device completion.
tvdb_status_t tvdb_gpu_level_set_sphere(tvdb_gpu_context_t* ctx,
                                        float radius,
                                        const float center[3],
                                        float voxel_size,
                                        float half_width,
                                        tvdb_dense_grid* out,
                                        tvdb_error_t* err);
tvdb_status_t tvdb_gpu_level_set_box(tvdb_gpu_context_t* ctx,
                                     const float half_extents[3],
                                     const float center[3],
                                     float voxel_size,
                                     float half_width,
                                     tvdb_dense_grid* out,
                                     tvdb_error_t* err);
tvdb_status_t tvdb_gpu_level_set_torus(tvdb_gpu_context_t* ctx,
                                       float major_radius,
                                       float minor_radius,
                                       const float center[3],
                                       float voxel_size,
                                       float half_width,
                                       tvdb_dense_grid* out,
                                       tvdb_error_t* err);

tvdb_status_t tvdb_gpu_csg_dense(tvdb_gpu_context_t* ctx,
                                 const tvdb_dense_grid* a,
                                 const tvdb_dense_grid* b,
                                 int op, // 0 union/min, 1 intersection/max, 2 difference/max(a,-b)
                                 tvdb_dense_grid* out,
                                 tvdb_error_t* err);

tvdb_status_t tvdb_gpu_sample_trilinear_dense_batch(tvdb_gpu_context_t* ctx,
                                                    const tvdb_dense_grid* grid,
                                                    const tvdb_vec3f* pts,
                                                    size_t n,
                                                    float* out_values,
                                                    tvdb_error_t* err);

// Triquadratic (3x3x3 stencil, per-axis 3-point parabola) batch sampler,
// mirroring tvdb_sample_quadratic_dense — smoother than trilinear. One thread
// per query point; out-of-range fetches clamp to the grid edge. Vulkan and
// CUDA/NVRTC.
tvdb_status_t tvdb_gpu_sample_quadratic_dense_batch(tvdb_gpu_context_t* ctx,
                                                    const tvdb_dense_grid* grid,
                                                    const tvdb_vec3f* pts,
                                                    size_t n,
                                                    float* out_values,
                                                    tvdb_error_t* err);

// Vulkan-only experimental path that uploads the dense grid to a 3D sampled
// image and uses hardware linear filtering. Returns TVDB_ERROR_UNIMPLEMENTED
// for non-Vulkan contexts or when SPIR-V/image support is unavailable.
tvdb_status_t tvdb_gpu_sample_trilinear_dense_batch_vulkan_image3d(tvdb_gpu_context_t* ctx,
                                                                   const tvdb_dense_grid* grid,
                                                                   const tvdb_vec3f* pts,
                                                                   size_t n,
                                                                   float* out_values,
                                                                   tvdb_error_t* err);

// Vulkan-only sparse-resident 3D sampled image path. The initial implementation
// binds all pages resident for the uploaded dense grid, validating sparse image
// binding and preserving the SSBO/regular-image fallback behavior.
tvdb_status_t tvdb_gpu_sample_trilinear_dense_batch_vulkan_sparse_image3d(tvdb_gpu_context_t* ctx,
                                                                          const tvdb_dense_grid* grid,
                                                                          const tvdb_vec3f* pts,
                                                                          size_t n,
                                                                          float* out_values,
                                                                          tvdb_error_t* err);

// Vulkan-only partial sparse-resident 3D image path from a sparse voxel list.
// Pages containing active voxels are bound and uploaded; samples must avoid
// unbound pages unless a later occupancy/background fallback is layered on top.
tvdb_status_t tvdb_gpu_sample_trilinear_sparse_vulkan_sparse_image3d(tvdb_gpu_context_t* ctx,
                                                                     const tvdb_sparse_grid* sparse,
                                                                     float background,
                                                                     int nx, int ny, int nz,
                                                                     const tvdb_vec3f* pts,
                                                                     size_t n,
                                                                     float* out_values,
                                                                     tvdb_error_t* err);

tvdb_status_t tvdb_gpu_vulkan_sparse_image3d_create(tvdb_gpu_context_t* ctx,
                                                    const tvdb_sparse_grid* sparse,
                                                    float background,
                                                    int nx, int ny, int nz,
                                                    tvdb_gpu_vulkan_sparse_image3d_t** out,
                                                    tvdb_error_t* err);
void tvdb_gpu_vulkan_sparse_image3d_destroy(tvdb_gpu_vulkan_sparse_image3d_t* image);
tvdb_status_t tvdb_gpu_vulkan_sparse_image3d_sample(tvdb_gpu_vulkan_sparse_image3d_t* image,
                                                    const tvdb_vec3f* pts,
                                                    size_t n,
                                                    float* out_values,
                                                    tvdb_error_t* err);
tvdb_status_t tvdb_gpu_vulkan_sample_batch_create(tvdb_gpu_context_t* ctx,
                                                  const tvdb_vec3f* pts,
                                                  size_t n,
                                                  tvdb_gpu_vulkan_sample_batch_t** out,
                                                  tvdb_error_t* err);
void tvdb_gpu_vulkan_sample_batch_destroy(tvdb_gpu_vulkan_sample_batch_t* batch);
tvdb_status_t tvdb_gpu_vulkan_sample_batch_update_points(tvdb_gpu_vulkan_sample_batch_t* batch,
                                                         const tvdb_vec3f* pts,
                                                         size_t n,
                                                         tvdb_error_t* err);
tvdb_status_t tvdb_gpu_vulkan_sparse_image3d_sample_batch(tvdb_gpu_vulkan_sparse_image3d_t* image,
                                                          tvdb_gpu_vulkan_sample_batch_t* batch,
                                                          tvdb_error_t* err);
tvdb_status_t tvdb_gpu_vulkan_sparse_image3d_sample_batch_submit(tvdb_gpu_vulkan_sparse_image3d_t* image,
                                                                 tvdb_gpu_vulkan_sample_batch_t* batch,
                                                                 tvdb_error_t* err);
tvdb_status_t tvdb_gpu_vulkan_sample_batch_poll(tvdb_gpu_vulkan_sample_batch_t* batch,
                                                int* done,
                                                tvdb_error_t* err);
tvdb_status_t tvdb_gpu_vulkan_sample_batch_wait(tvdb_gpu_vulkan_sample_batch_t* batch,
                                                tvdb_error_t* err);
tvdb_status_t tvdb_gpu_vulkan_sample_batch_readback(tvdb_gpu_vulkan_sample_batch_t* batch,
                                                    float* out_values,
                                                    size_t n,
                                                    tvdb_error_t* err);

tvdb_status_t tvdb_gpu_sparse_conv3d(tvdb_gpu_context_t* ctx,
                                     const tvdb_sparse_grid* in,
                                     const float* kernel,
                                     int kx, int ky, int kz,
                                     float pad_value,
                                     tvdb_sparse_grid* out,
                                     tvdb_error_t* err);

// Spatial queries over a flat active-coordinate set (GPU mirrors of the CPU
// helpers in tinyvdb_grid_index.h). `active`/`query` are int32 xyz triples;
// the kernels brute-force linear-scan `active` (one GPU thread per query /
// active voxel), exactly matching the CPU reference. Indices are computed in
// int32 on device, so `na` must fit in int32 (always true in practice).

// out[i] = 1 if query coord i is in the active set, else 0.
tvdb_status_t tvdb_gpu_coords_in_grid(tvdb_gpu_context_t* ctx,
                                      const int32_t* active, size_t na,
                                      const int32_t* query, size_t nq,
                                      uint8_t* out, tvdb_error_t* err);

// For each world point, 1 if its voxel floor((p-origin)/voxel_size) is active.
tvdb_status_t tvdb_gpu_points_in_grid(tvdb_gpu_context_t* ctx,
                                      const float* points, size_t np,
                                      const float voxel_size[3],
                                      const float origin[3],
                                      const int32_t* active, size_t na,
                                      uint8_t* out, tvdb_error_t* err);

// For each query coord, its first-seen index in `active` (0..na-1) or -1.
tvdb_status_t tvdb_gpu_ijk_to_index(tvdb_gpu_context_t* ctx,
                                    const int32_t* active, size_t na,
                                    const int32_t* query, size_t nq,
                                    int64_t* out, tvdb_error_t* err);

// For each active voxel, the count of its active neighbors. `connectivity`
// is 6 (face) or 26 (face+edge+vertex).
tvdb_status_t tvdb_gpu_neighbor_counts(tvdb_gpu_context_t* ctx,
                                       const int32_t* active, size_t na,
                                       int connectivity,
                                       int32_t* out_counts, tvdb_error_t* err);

// Dense topology / morphology ops (GPU mirrors of tinyvdb_ops.h /
// tinyvdb_topology.h). All operate in place on `grid->data`.

// SDF morphology: dilate = 6-neighbor min, erode = 6-neighbor max, `iterations`
// steps with edge clamp (parallels tvdb_dilate / tvdb_erode).
tvdb_status_t tvdb_gpu_dilate(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                              int iterations, tvdb_error_t* err);
tvdb_status_t tvdb_gpu_erode(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                             int iterations, tvdb_error_t* err);

// Snap voxels within `tolerance` of `background` exactly to it (parallels
// tvdb_prune_grid).
tvdb_status_t tvdb_gpu_prune(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                             float background, float tolerance, tvdb_error_t* err);

// Downsample by integer `factor` via block averaging (parallels
// tvdb_coarsen_grid). `out` is filled (dims = ceil(in/factor), vs*factor).
tvdb_status_t tvdb_gpu_coarsen(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* in,
                               int factor, tvdb_dense_grid* out, tvdb_error_t* err);

// Upsample by integer `factor` via trilinear resampling (parallels
// tvdb_refine_grid). `out` is filled (dims = in*factor, vs/factor).
tvdb_status_t tvdb_gpu_refine(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* in,
                              int factor, tvdb_dense_grid* out, tvdb_error_t* err);

// Emission-absorption volume render of a density grid with a pinhole camera
// (parallels tvdb_volume_render). One GPU thread per pixel; ray-AABB clip +
// front-to-back march. `out_image` is width*height floats (row-major, top row
// first), caller-allocated.
tvdb_status_t tvdb_gpu_volume_render(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* density,
                                     const float eye[3], const float center[3],
                                     const float up[3], float fov_y, int width, int height,
                                     float sigma, float step, float background,
                                     float* out_image, tvdb_error_t* err);

// Batched ray queries. `rays` is `n_rays` * 8 floats: per ray
// (ox,oy,oz,tmin, dx,dy,dz,tmax) — matching tvdb_ray laid out flat.

// Uniform samples along each ray in [tmin,tmax] (parallels
// tvdb_uniform_ray_samples). out_points = n_rays*n_samples*3 floats,
// out_t = n_rays*n_samples floats (both caller-allocated, output index
// ray*n_samples+sample).
tvdb_status_t tvdb_gpu_uniform_ray_samples(tvdb_gpu_context_t* ctx,
                                           const float* rays, size_t n_rays, size_t n_samples,
                                           float* out_points, float* out_t, tvdb_error_t* err);

// Amanatides-Woo DDA voxel traversal per ray (parallels
// tvdb_voxels_along_ray_dense). Writes up to `cap` voxels into
// out_voxels[ray*cap*3 ...] and the per-ray written count into
// out_counts[ray] (<= cap).
tvdb_status_t tvdb_gpu_voxels_along_ray(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                                        const float* rays, size_t n_rays, size_t cap,
                                        int32_t* out_voxels, int32_t* out_counts, tvdb_error_t* err);

// SDF-zero crossings per ray as (entry,exit) t-pairs for each inside run
// (parallels tvdb_segments_along_ray; ray-SDF intersection = first pair).
// Writes up to `cap` pairs into out_t_pairs[ray*cap*2 ...] and the per-ray
// total pair count into out_counts[ray] (may exceed cap). `step_count` >= 2.
tvdb_status_t tvdb_gpu_segments_along_ray(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                                          const float* rays, size_t n_rays, float isovalue,
                                          size_t step_count, size_t cap,
                                          float* out_t_pairs, int32_t* out_counts, tvdb_error_t* err);

// Integrate a depth frame into an existing TSDF + weight grid (parallels
// tvdb_integrate_tsdf). One GPU thread per voxel; `tsdf`/`weights` must be the
// same shape and are updated in place. On the first call initialize tsdf to
// trunc_distance and weights to 0.
tvdb_status_t tvdb_gpu_integrate_tsdf(tvdb_gpu_context_t* ctx, tvdb_dense_grid* tsdf,
                                      tvdb_dense_grid* weights, const tvdb_depth_frame* frame,
                                      tvdb_error_t* err);

// Min/max/mean/stddev/sum over all voxels (parallels tvdb_grid_statistics).
// GPU computes (min,max,sum,sumsq) partials via a grid-stride reduction; the
// host finalizes mean/stddev in double.
tvdb_status_t tvdb_gpu_grid_statistics(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                                       tvdb_grid_stats_t* out, tvdb_error_t* err);

// Fog-volume validity check (parallels tvdb_check_fog_volume): reports the
// value range and whether all voxels lie in [-eps, 1+eps]. Reuses the stats
// reduction for min/max.
tvdb_status_t tvdb_gpu_check_fog_volume(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                                        double eps, int* out_valid, double* out_min,
                                        double* out_max, tvdb_error_t* err);

// Narrow-band |grad| ~ 1 level-set health check (parallels
// tvdb_check_level_set), via a band-voxel gradient reduction.
tvdb_status_t tvdb_gpu_check_level_set(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                                       double band_world, double tol,
                                       tvdb_level_set_check_t* out, tvdb_error_t* err);

// Signed flood fill (parallels tvdb_signed_flood_fill): flood the exterior
// through far voxels (|value| >= band) from the grid boundary, then set
// reached far voxels to +band (exterior) and unreached to -band (interior).
// In place. The GPU runs the reachability flood as iterative label
// propagation; the host seeds the boundary and assigns final signs.
tvdb_status_t tvdb_gpu_signed_flood_fill(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                                         float band_world, tvdb_error_t* err);

// Trilinear splat: scatter `n` point values onto `grid` (accumulated in place,
// so callers zero it first), mirroring tvdb_splat_trilinear_dense. `points` is
// `n` xyz triples; `weights` (nullable, same shape as grid) receives the splat
// weight sum for normalization. Corner accumulation uses a portable CAS
// atomic-add. This also realizes the trilinear-sample VJP w.r.t. the grid
// (sample.vjp(grid) == splat(grad_out, points)); the splat VJP w.r.t. values is
// tvdb_gpu_sample_trilinear_dense_batch.
tvdb_status_t tvdb_gpu_splat_trilinear_dense(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                                             const float* points, const float* vals, size_t n,
                                             float* weights, tvdb_error_t* err);

// Triquadratic splat: the 3x3x3-stencil scatter adjoint of the quadratic
// sampler, mirroring tvdb_splat_quadratic_dense. Same in-place accumulation,
// CAS atomic-add, and nullable `weights` semantics as the trilinear splat; this
// realizes the triquadratic-sample VJP w.r.t. the grid.
tvdb_status_t tvdb_gpu_splat_quadratic_dense(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                                             const float* points, const float* vals, size_t n,
                                             float* weights, tvdb_error_t* err);

// Rasterize a point cloud into a dense occupancy mask (grid construction):
// marks `mask->data[ijk] = 1` for the voxel containing each point, using
// `mask`'s dims/origin/voxel_size. `mask` must be allocated (and zeroed by the
// caller for a clean mask). `points` is `n` xyz triples.
tvdb_status_t tvdb_gpu_points_to_mask(tvdb_gpu_context_t* ctx, tvdb_dense_grid* mask,
                                      const float* points, size_t n, tvdb_error_t* err);

// Sparse grid construction: world point cloud -> unique occupied voxel coords
// (parallels tvdb_voxelize_points). `*out_coords` is malloc'd (caller frees),
// `*out_count` is the unique-voxel count. Output order is arbitrary (set
// semantics). Uses a dense bbox-local occupancy grid + atomic-counter
// compaction when the ijk bounding box fits in VRAM, and automatically falls
// back to the O(n) hash-set path (tvdb_gpu_voxelize_points_unbounded) when it
// does not.
tvdb_status_t tvdb_gpu_voxelize_points(tvdb_gpu_context_t* ctx, const float* points, size_t n,
                                       const float voxel_size[3], const float origin[3],
                                       int32_t** out_coords, size_t* out_count, tvdb_error_t* err);

// Unbounded sparse grid construction: same result as tvdb_gpu_voxelize_points
// but always via an open-addressing GPU hash set sized O(point count), so the
// memory is independent of the ijk bounding-box volume (for point clouds spread
// over a huge region). A host-side dedup finalizes the set exactly. Vulkan and
// CUDA/NVRTC.
tvdb_status_t tvdb_gpu_voxelize_points_unbounded(tvdb_gpu_context_t* ctx, const float* points, size_t n,
                                                 const float voxel_size[3], const float origin[3],
                                                 int32_t** out_coords, size_t* out_count, tvdb_error_t* err);

// Sparse erode (parallels tvdb_erode_sparse): keep an active voxel only if all
// 6 face neighbors are active, with max-pooled value; `iterations` steps. `out`
// is filled (set semantics: output coord order is arbitrary). Uses a dense
// bbox-local occupancy + atomic-counter compaction, so the active set's ijk
// bbox volume must fit in VRAM.
tvdb_status_t tvdb_gpu_erode_sparse(tvdb_gpu_context_t* ctx, const tvdb_sparse_grid* in,
                                    int iterations, tvdb_sparse_grid* out, tvdb_error_t* err);

// Sparse dilate (parallels tvdb_dilate_sparse): grow the active set by the 6
// face neighbors, min-pooling each active voxel's value into itself and its
// neighbors (inactive neighbors fall back to `background`); `iterations` steps.
// `out` is filled (set semantics). Uses a dense bbox-local occupancy + value
// grid (CAS atomic-min) + atomic-counter compaction; the dilated set's ijk
// bbox volume must fit in VRAM.
tvdb_status_t tvdb_gpu_dilate_sparse(tvdb_gpu_context_t* ctx, const tvdb_sparse_grid* in,
                                     float background, int iterations,
                                     tvdb_sparse_grid* out, tvdb_error_t* err);

// Merge two dense grids (same voxel size) into an output covering both world
// AABBs, min-pooling overlaps (SDF-union), background elsewhere (parallels
// tvdb_merge_grids). `out` is allocated/filled by the call.
tvdb_status_t tvdb_gpu_merge_grids(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* a,
                                   const tvdb_dense_grid* b, float background,
                                   tvdb_dense_grid* out, tvdb_error_t* err);

// Active-coordinate extraction: dense grid -> sparse grid of voxels whose value
// differs from `background` by more than `tolerance` (parallels
// tvdb_active_grid_coords / tvdb_dense_to_sparse). `out` is filled; coord order
// is arbitrary (set semantics). Single-pass atomic-counter compaction.
tvdb_status_t tvdb_gpu_active_grid_coords(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* dense,
                                          float background, float tolerance,
                                          tvdb_sparse_grid* out, tvdb_error_t* err);

// Order-independent additive checksum over a dense grid's values (NanoVDB-style
// validation hash). Parallel grid-stride partial sums folded on the host;
// `*out_checksum` is a 32-bit wrapping sum of a per-element (value,index) mix.
tvdb_status_t tvdb_gpu_grid_checksum(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                                     uint32_t* out_checksum, tvdb_error_t* err);

// Brute-force triangle mesh -> narrow-band SDF (grid construction from meshes;
// parallels tvdb_mesh_to_sdf). One GPU thread per voxel computes the closest-
// triangle distance with a per-voxel normal sign, clamped to +/-band_width.
// `out` is allocated/filled with the CPU's bbox/dims/origin conventions.
// O(voxels * triangles) — keep voxel sizes coarse, like the CPU path.
// Surface area / volume for a dense scalar grid (parallels tvdb_surface_area and
// tvdb_volume). The counted predicate is exact and the count is an integer, so
// the fp32 results match the CPU bit-for-bit rather than to a tolerance.
//
// A NULL grid->data returns 0 like the CPU does. The fp64 device feature is
// required only by the _d variants.
// Jacobi-preconditioned CG for the 7-point Poisson solve (parallels
// tvdb_solve_poisson / tvdb_solve_poisson_d). Returns the iteration count, or 0
// on a shape mismatch, empty grid, or already-converged input, matching the CPU.
//
// The checked _ex variants below use a device edge-clamped Laplacian with host
// projected PCG updates and double reductions. Buffers persist through a solve;
// each iteration transfers vectors and synchronizes. No speedup is claimed.
int tvdb_gpu_solve_poisson(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* rhs,
                           tvdb_dense_grid* x, int max_iters, float tolerance,
                           tvdb_error_t* err);
int tvdb_gpu_solve_poisson_d(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* rhs,
                             tvdb_dense_grid* x, int max_iters, double tolerance,
                             tvdb_error_t* err);

// fp64 in and fp64 out (parallels tvdb_solve_poisson_dd), as distinct from
// tvdb_gpu_solve_poisson_d above, which takes fp32 grids. Same kernel and device
// buffers; only the input widening and output narrowing are skipped.
int tvdb_gpu_solve_poisson_dd(tvdb_gpu_context_t* ctx, const tvdb_dense_grid_d* rhs,
                              tvdb_dense_grid_d* x, int max_iters, double tolerance,
                              tvdb_error_t* err);

// Elementwise binary scalar-grid ops (parallels tvdb_comp_max/min/sum/mult).
// Invalid data or shape mismatch returns INVALID_ARGUMENT and leaves result
// untouched. Exact same-handle in-place output is supported.
// Semi-Lagrangian advection of a scalar grid by a vec3 velocity grid
// (parallels tvdb_advect). All six schemes are supported: the four RK ones in a
// single pass, MacCormack and BFECC in three to four.
//
// Invalid input or options return INVALID_ARGUMENT without changing result.
// Same-handle in-place output is supported through transactional scratch.
// Dense scalar-grid filters (parallels tvdb_mean_filter, tvdb_gaussian_filter and
// tvdb_laplacian_filter). These modify the grid in place, and `grid` is left
// untouched if any pass fails, so a failure cannot leave it half-filtered.
//
// The separable filters run one axis at a time through distinct buffers, as
// tvdb_apply_separable does, rather than as a fused 3-D pass -- a fused pass is a
// different algorithm, not a faster one. The Laplacian filter is Jacobi for the
// same reason.
tvdb_status_t tvdb_gpu_mean_filter(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                                   int width, int iterations, tvdb_error_t* err);
tvdb_status_t tvdb_gpu_gaussian_filter(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                                       int width, int iterations, tvdb_error_t* err);
tvdb_status_t tvdb_gpu_laplacian_filter(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                                        int iterations, tvdb_error_t* err);

// Single-node (Euler) semi-Lagrangian advect (parallels
// tvdb_advect_semi_lagrangian). Unlike the RK family in tvdb_gpu_advect above,
// this reads the velocity at the voxel itself rather than interpolating it. A
// shape mismatch returns INVALID_ARGUMENT and leaves result untouched.
// Windowed median (parallels tvdb_median_filter), Jacobi like the CPU.
//
// This is a coverage port, not an accelerated one: it counts ranks, which is
// O((2r+1)^6) comparisons per voxel, because a bitonic sort of the padded window
// needs 128-512 floats of private memory per thread. It is still bit-identical to
// the CPU's quickselect on finite input, since the selected value is order
// independent.
//
// radius is bounded at 2. Above that this reports UNIMPLEMENTED rather than
// silently using a smaller window, which would be a different filter. The CPU
// accepts any radius.
tvdb_status_t tvdb_gpu_median_filter(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                                     int radius, int iterations, tvdb_error_t* err);

tvdb_status_t tvdb_gpu_advect_semi_lagrangian(tvdb_gpu_context_t* ctx,
    const tvdb_dense_grid* field, const tvdb_dense_vec_grid* velocity, float dt,
    tvdb_dense_grid* result, tvdb_error_t* err);

tvdb_status_t tvdb_gpu_advect(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* field,
                              const tvdb_dense_vec_grid* velocity, float dt, int scheme,
                              int clamp, tvdb_dense_grid* result, tvdb_error_t* err);

tvdb_status_t tvdb_gpu_comp_max(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* a,
                                const tvdb_dense_grid* b, tvdb_dense_grid* result,
                                tvdb_error_t* err);
tvdb_status_t tvdb_gpu_comp_min(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* a,
                                const tvdb_dense_grid* b, tvdb_dense_grid* result,
                                tvdb_error_t* err);
tvdb_status_t tvdb_gpu_comp_sum(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* a,
                                const tvdb_dense_grid* b, tvdb_dense_grid* result,
                                tvdb_error_t* err);
tvdb_status_t tvdb_gpu_comp_mult(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* a,
                                 const tvdb_dense_grid* b, tvdb_dense_grid* result,
                                 tvdb_error_t* err);

tvdb_status_t tvdb_gpu_surface_area(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                                    float* out_area, tvdb_error_t* err);
tvdb_status_t tvdb_gpu_volume(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                              float* out_volume, tvdb_error_t* err);
tvdb_status_t tvdb_gpu_surface_area_d(tvdb_gpu_context_t* ctx, const tvdb_dense_grid_d* grid,
                                     double* out_area, tvdb_error_t* err);
tvdb_status_t tvdb_gpu_volume_d(tvdb_gpu_context_t* ctx, const tvdb_dense_grid_d* grid,
                               double* out_volume, tvdb_error_t* err);

tvdb_status_t tvdb_gpu_mesh_to_sdf(tvdb_gpu_context_t* ctx, const tvdb_triangle_mesh* mesh,
                                   float voxel_size, float band_width,
                                   tvdb_dense_grid* out, tvdb_error_t* err);

// Marching cubes on the GPU (parallels tvdb_sdf_to_mesh) producing a triangle
// soup. One thread per cell; emits each cell's triangles in scan/table order so
// the result matches the CPU mesh triangle-for-triangle (positions). `*out_verts`
// is malloc'd (caller frees): `*out_tri_count` triangles * 9 floats (3 xyz
// vertices each), non-indexed.
tvdb_status_t tvdb_gpu_marching_cubes(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                                      float isovalue, float** out_verts, size_t* out_tri_count,
                                      tvdb_error_t* err);

// Strided sparse 3D convolution with output-grid building (extends
// tvdb_gpu_sparse_conv3d): output active coords are the unique floor(coord/
// stride) of the input set, and out[oc] = sum_k kernel[k] * input(oc*stride +
// tap_k), with pad_value for absent voxels. stride 1 = same-topology conv. `out`
// is filled (set semantics: output coord order is arbitrary).
tvdb_status_t tvdb_gpu_sparse_conv3d_strided(tvdb_gpu_context_t* ctx, const tvdb_sparse_grid* in,
                                             const float* kernel, int kx, int ky, int kz,
                                             int stride, float pad_value,
                                             tvdb_sparse_grid* out, tvdb_error_t* err);

// Transposed (adjoint) sparse 3D convolution — the upsampling adjoint of the
// strided conv. Each input voxel scatters kernel[k]*value to output coord
// `coord*stride + tap_k`, accumulating; the output active set is the union of
// scattered coords. `out` is filled (set semantics). stride 1 with a centred
// kernel mirrors a same-topology accumulation.
tvdb_status_t tvdb_gpu_sparse_conv3d_transpose(tvdb_gpu_context_t* ctx, const tvdb_sparse_grid* in,
                                               const float* kernel, int kx, int ky, int kz,
                                               int stride, tvdb_sparse_grid* out, tvdb_error_t* err);

// ---- Generic compute-dispatch engine ----------------------------------------
// A backend-uniform way to run a single compute kernel, factoring out the
// per-op buffer-lifecycle + dispatch boilerplate (the tinyvdb analogue of
// fvdb::dispatch). Describe the kernel and its host-side buffer bindings; the
// engine allocates device buffers, uploads inputs, dispatches, downloads
// outputs, and frees — on whichever backend the context uses. CUDA kernels
// receive the binding device pointers as arguments in binding order (the
// uniform binding arrives as a `const T*`); Vulkan binds them at set 0,
// binding i (the uniform as a uniform block). Max 6 bindings.

typedef enum {
  TVDB_GPU_BIND_STORAGE_IN = 0,    // host -> device storage buffer (read in kernel)
  TVDB_GPU_BIND_STORAGE_OUT,       // device storage buffer -> host (written by kernel)
  TVDB_GPU_BIND_STORAGE_INOUT,     // host -> device -> host
  TVDB_GPU_BIND_UNIFORM            // host -> device uniform/const buffer (read in kernel)
} tvdb_gpu_binding_kind_t;

typedef struct {
  tvdb_gpu_binding_kind_t kind;
  void*  host_data;    // IN/INOUT/UNIFORM: upload source; OUT/INOUT: download dest
  size_t size_bytes;   // buffer size (>= 1)
} tvdb_gpu_binding_t;

typedef struct {
  const unsigned char* spv;   // Vulkan SPIR-V blob
  unsigned int spv_len;       // SPIR-V length in bytes (0 => Vulkan unavailable)
  const char* cuda_kernel;    // CUDA kernel name (resolved in the bundled module)
  const tvdb_gpu_binding_t* bindings;
  unsigned int num_bindings;  // <= 6
  unsigned int group_count_x; // workgroup count (kernel uses local_size_x = 128)
  // On Vulkan, queue the dispatch and copy outputs back on dispatch_flush.
  // Input and uniform contents are copied during dispatch; callers may reuse
  // them after it returns. Output/INOUT host storage must remain valid until
  // flush (or context destruction) completes. Flush before reading an output
  // or using it as a subsequent dispatch's input. Queues belong to each context.
  // CUDA dispatches are synchronous and ignore this flag.
  int defer;
} tvdb_gpu_dispatch_spec_t;

// Run one compute dispatch described by `spec`. Returns TVDB_ERROR_UNIMPLEMENTED
// when the backend can't run it (e.g. no SPIR-V on Vulkan).
tvdb_status_t tvdb_gpu_dispatch(tvdb_gpu_context_t* ctx, const tvdb_gpu_dispatch_spec_t* spec,
                                tvdb_error_t* err);

// Wait for any dispatches queued with spec->defer and copy their output bindings
// back. Must be called before reading a buffer written by a deferred dispatch, and
// before the buffers themselves are released. A no-op when nothing is queued.
tvdb_status_t tvdb_gpu_dispatch_flush(tvdb_gpu_context_t* ctx, tvdb_error_t* err);

// Demonstration op built on the dispatch engine: out = alpha*x + y over `n`
// floats, on Vulkan and CUDA. Useful as a BLAS-like primitive and as the worked
// example of authoring a kernel against tvdb_gpu_dispatch.
tvdb_status_t tvdb_gpu_axpy(tvdb_gpu_context_t* ctx, const float* x, const float* y,
                            float alpha, size_t n, float* out, tvdb_error_t* err);

// Device-resident buffer interop. A caller-owned GPU buffer that stays on
// device across uploads/downloads, with its native handle exported so the
// caller's own Vulkan/CUDA code can consume the data without a host round-trip
// (the foundation for keeping sample/query results on device).
tvdb_status_t tvdb_gpu_buffer_create(tvdb_gpu_context_t* ctx, size_t size_bytes,
                                     tvdb_gpu_buffer_t** out, tvdb_error_t* err);
void tvdb_gpu_buffer_destroy(tvdb_gpu_buffer_t* buf);
tvdb_status_t tvdb_gpu_buffer_upload(tvdb_gpu_buffer_t* buf, const void* src, size_t size, tvdb_error_t* err);
tvdb_status_t tvdb_gpu_buffer_download(tvdb_gpu_buffer_t* buf, void* dst, size_t size, tvdb_error_t* err);
size_t tvdb_gpu_buffer_size(const tvdb_gpu_buffer_t* buf);
// Native device handle (Vulkan VkBuffer or CUDA CUdeviceptr) as a uint64 for
// caller-side interop; 0 if unavailable.
uint64_t tvdb_gpu_buffer_native_handle(const tvdb_gpu_buffer_t* buf);

// Cross-API external-memory interop (Linux opaque-fd). Lets a device buffer be
// shared between a Vulkan context (exporter) and a CUDA context (importer)
// referencing the same physical GPU, with no host round-trip. Requires
// VK_KHR_external_memory{,_fd} on the Vulkan side and the CUDA driver's
// external-memory entry points; the calls return TVDB_ERROR_UNIMPLEMENTED when
// unsupported, so callers can degrade gracefully.
//
// Returns nonzero if `ctx` can participate in external-memory interop: a Vulkan
// context that can export, or a CUDA context that can import.
int tvdb_gpu_context_supports_external_memory(const tvdb_gpu_context_t* ctx);
// Create a device-local Vulkan buffer whose backing memory can be exported.
// Upload/download stage through a temporary host-visible buffer (it is not
// host-mapped). Vulkan context only.
tvdb_status_t tvdb_gpu_buffer_create_exportable(tvdb_gpu_context_t* ctx, size_t size_bytes,
                                                tvdb_gpu_buffer_t** out, tvdb_error_t* err);
// Export an exportable buffer's memory as an opaque POSIX fd packed into a
// uint64 handle. The handle is owned by the caller until passed to
// tvdb_gpu_buffer_import, which always consumes it (CUDA takes ownership on
// success; the handle is closed on failure) — so the caller never closes it
// after a call to import. `size_bytes` passed to import must match the size
// used to create the exportable buffer.
tvdb_status_t tvdb_gpu_buffer_export(tvdb_gpu_buffer_t* buf, uint64_t* out_handle, tvdb_error_t* err);
// Import a handle from tvdb_gpu_buffer_export into a CUDA context, yielding a
// device buffer that aliases the same memory. CUDA context only. Consumes the
// handle (see tvdb_gpu_buffer_export).
tvdb_status_t tvdb_gpu_buffer_import(tvdb_gpu_context_t* ctx, uint64_t handle, size_t size_bytes,
                                     tvdb_gpu_buffer_t** out, tvdb_error_t* err);

// GPU Gaussian-splat rasterizer forward (parallels
// tvdb_gaussian_rasterize_forward): tile-based depth-sorted front-to-back alpha
// blend. The per-tile entry list is built and depth-sorted host-side (same as
// the CPU), then composited one thread per pixel — bit-for-bit the CPU order.
// `out` is allocated/filled (image, alpha, last_ids). num_features <= 3.
tvdb_status_t tvdb_gpu_gaussian_rasterize_forward(tvdb_gpu_context_t* ctx,
    const tvdb_projected_gaussian_t* gaussians, uint32_t num_gaussians,
    uint32_t width, uint32_t height, uint32_t num_features,
    float background[3], float alpha_threshold, tvdb_raster_output_t* out, tvdb_error_t* err);

// GPU Gaussian-splat rasterizer backward (parallels
// tvdb_gaussian_rasterize_backward): replays the depth-sorted blend in reverse,
// one thread per pixel with local T/S state, scatter-adding per-gaussian
// gradients (CAS atomic-add). `grad_out` must be pre-initialized
// (tvdb_gaussian_grad_init) and matching shape; contributions are accumulated.
tvdb_status_t tvdb_gpu_gaussian_rasterize_backward(tvdb_gpu_context_t* ctx,
    const tvdb_projected_gaussian_t* gaussians, uint32_t num_gaussians,
    const tvdb_raster_output_t* fwd, const float* dL_dC, const float* dL_dA,
    float background[3], float alpha_threshold, tvdb_gaussian_grad_t* grad_out, tvdb_error_t* err);

// GPU windowed SSIM (Gaussian-splat training-loss helper): structural
// similarity between two HxWxC images with an 11x11 Gaussian window (sigma 1.5,
// clamp-to-edge), averaged over channels. `*out_mean` gets the image-mean SSIM;
// `out_map` (nullable) gets the per-pixel SSIM (width*height floats).
tvdb_status_t tvdb_gpu_ssim(tvdb_gpu_context_t* ctx, const float* img_a, const float* img_b,
                            uint32_t width, uint32_t height, uint32_t channels, float data_range,
                            float* out_mean, float* out_map, tvdb_error_t* err);

// GPU view-dependent spherical-harmonics color evaluation (Gaussian-splat
// helper), mirroring tvdb_gaussian_sh_eval. `degree` in [0,3]; `sh_coeffs` is
// num_gaussians * K * 3 floats (K=(degree+1)^2, layout [(g*K+k)*3+c]); `dirs`
// is num_gaussians * 3 view directions (normalized internally); `out_colors`
// receives num_gaussians * 3 = max(sh_result + 0.5, 0). One thread per Gaussian
// on Vulkan and CUDA/NVRTC.
tvdb_status_t tvdb_gpu_gaussian_sh_eval(tvdb_gpu_context_t* ctx, uint32_t num_gaussians,
                                        uint32_t degree, const float* sh_coeffs, const float* dirs,
                                        float* out_colors, tvdb_error_t* err);

// GPU Gaussian projection (3D -> 2D screen-space conic), mirroring the CPU
// tvdb_gaussian_project: each Gaussian's mean is projected through the camera,
// its rotated covariance is projected to a 2D conic, and a screen-space radius
// is derived. `means` (N*3), `quats` (N*4, xyzw), `log_scales` (N*3), nullable
// `opacities` (N logits; default 0) and `sh_dc` (N*3 DC color; default {1,0,0}).
// `extrinsics` is a column-major 4x4; `intrinsics` is a 3x3 (fx,_,cx,_,fy,cy,...).
// `out` receives N filled tvdb_projected_gaussian_t. Bit-exact vs the CPU path
// (the radius reuses the same fast-sqrt bit trick). Vulkan and CUDA/NVRTC.
tvdb_status_t tvdb_gpu_gaussian_project(tvdb_gpu_context_t* ctx, uint32_t num_gaussians,
                                        const float* means, const float* quats, const float* log_scales,
                                        const float* opacities, const float* sh_dc,
                                        const float extrinsics[16], const float intrinsics[9],
                                        float z_near, float z_far,
                                        tvdb_projected_gaussian_t* out, tvdb_error_t* err);

// GPU MCMC densification helpers (parallel tvdb_gaussian_mcmc_relocation /
// _add_noise in tinyvdb_nanovdb.h). Relocation recomputes per-copy opacity +
// scale so splitting a Gaussian into `ratios[g]` copies preserves the render;
// add_noise adds covariance-aware, opacity-gated exploration noise to the means
// from a caller-supplied standard-normal `rand` buffer (deterministic). Both on
// Vulkan + CUDA/NVRTC, one thread per Gaussian.
tvdb_status_t tvdb_gpu_gaussian_mcmc_relocation(tvdb_gpu_context_t* ctx, uint32_t num_gaussians,
                                                const float* opacities, const float* scales,
                                                const int32_t* ratios, float* new_opacities,
                                                float* new_scales, tvdb_error_t* err);
tvdb_status_t tvdb_gpu_gaussian_mcmc_add_noise(tvdb_gpu_context_t* ctx, uint32_t num_gaussians,
                                               const float* means, const float* quats, const float* log_scales,
                                               const float* opacities_logit, const float* rand, float lr,
                                               float* out_means, tvdb_error_t* err);

// Batched sparse convolution (GridBatch / JaggedTensor-style): run a
// same-topology sparse conv3d over `n_grids` grids in a single GPU dispatch.
// The grids are concatenated jagged on device and each voxel's lookups are
// confined to its own grid. `out` is an array of `n_grids` filled grids (same
// topology as inputs). Demonstrates batched device-resident sparse workloads.
tvdb_status_t tvdb_gpu_sparse_conv3d_batched(tvdb_gpu_context_t* ctx,
    const tvdb_sparse_grid* in, size_t n_grids, const float* kernel, int kx, int ky, int kz,
    float pad_value, tvdb_sparse_grid* out, tvdb_error_t* err);

// Multi-context (multi-GPU) scheduling: partition a grid batch into contiguous
// chunks across `n_ctx` contexts and run the batched conv on each, so distinct
// contexts on distinct devices process disjoint chunks in parallel. With one
// context it degenerates to the single-context path. (Each context's chunk is
// dispatched in turn here; callers wanting overlap can drive contexts on
// separate host threads.)
tvdb_status_t tvdb_gpu_multi_sparse_conv3d_batched(tvdb_gpu_context_t* const* ctxs, size_t n_ctx,
    const tvdb_sparse_grid* in, size_t n_grids, const float* kernel, int kx, int ky, int kz,
    float pad_value, tvdb_sparse_grid* out, tvdb_error_t* err);

// Checked projected PCG: device Laplacian, host projection/double reductions.
tvdb_status_t tvdb_gpu_solve_poisson_ex(tvdb_gpu_context_t* ctx,const tvdb_dense_grid* rhs,tvdb_dense_grid* x,
  int max_iters,float tolerance,tvdb_poisson_result_t* result,tvdb_error_t* err);

// Checked projected PCG: device Laplacian, host projection/double reductions.
tvdb_status_t tvdb_gpu_solve_poisson_d_ex(tvdb_gpu_context_t* ctx,const tvdb_dense_grid* rhs,tvdb_dense_grid* x,
  int max_iters,double tolerance,tvdb_poisson_result_t* result,tvdb_error_t* err);

// Checked projected PCG: device Laplacian, host projection/double reductions.
tvdb_status_t tvdb_gpu_solve_poisson_dd_ex(tvdb_gpu_context_t* ctx,const tvdb_dense_grid_d* rhs,tvdb_dense_grid_d* x,
  int max_iters,double tolerance,tvdb_poisson_result_t* result,tvdb_error_t* err);

#ifdef __cplusplus
}
#endif

// ---------------------------------------------------------------------------
// PDE stencils.
//
// These mirror the CPU reference exactly, including its edge handling: reads
// are clamped at the grid boundary (tvdb_at / tvdb_vec_at), laplacian is the
// 7-point stencil (sum of 6 neighbours - 6*centre) scaled by 1/h^2, and the
// central differences are (f(+1) - f(-1)) scaled by 1/(2h).
//
// `out` is (re)allocated to match `in`; on the CUDA backend these fall back to
// the CPU reference when the device cannot run them.

// laplacian (op 0) or one central difference: 0 = laplacian, 1 = dx, 2 = dy, 3 = dz.
tvdb_status_t tvdb_gpu_stencil_scalar_scalar(tvdb_gpu_context_t* ctx,
                                             const tvdb_dense_grid* in,
                                             int op,
                                             tvdb_dense_grid* out,
                                             tvdb_error_t* err);

// gradient of a scalar grid into a vec3 grid.
tvdb_status_t tvdb_gpu_gradient(tvdb_gpu_context_t* ctx,
                                const tvdb_dense_grid* in,
                                tvdb_dense_vec_grid* out,
                                tvdb_error_t* err);

// divergence of a vec3 grid into a scalar grid.
tvdb_status_t tvdb_gpu_divergence(tvdb_gpu_context_t* ctx,
                                  const tvdb_dense_vec_grid* in,
                                  tvdb_dense_grid* out,
                                  tvdb_error_t* err);

// curl of a vec3 grid into a vec3 grid.
tvdb_status_t tvdb_gpu_curl(tvdb_gpu_context_t* ctx,
                            const tvdb_dense_vec_grid* in,
                            tvdb_dense_vec_grid* out,
                            tvdb_error_t* err);

// ---------------------------------------------------------------------------
// fp64 scalar stencils.
//
// fp64 is an optional device feature and runs at a small fraction of fp32 rate
// on consumer parts, so these check for it and return TVDB_ERROR_UNIMPLEMENTED
// when the device cannot do it. They never silently compute in fp32: a caller who
// asked for double precision would otherwise get different answers with no
// indication.

// True when the device can run the fp64 ops.
bool tvdb_gpu_supports_fp64(tvdb_gpu_context_t* ctx);

// laplacian (op 0) or one central difference: 0 = laplacian, 1 = dx, 2 = dy, 3 = dz.
// fp64 CSG: op 0 union (min), 1 intersection (max), 2 difference (max with -b).
// Matches tvdb_csg_union_d / _intersection_d / _difference_d, including their
// comparison form so signed zero agrees. Falls back to the CPU reference when the
// device lacks shaderFloat64.
// Batched fp64 trilinear sample against tvdb_sample_trilinear_dense_d. Points are
// (x, y, z) triples in world space; the grid geometry is carried in fp64
// end-to-end. Falls back to the CPU reference when the device lacks fp64.
tvdb_status_t tvdb_gpu_sample_trilinear_dense_d_batch(tvdb_gpu_context_t* ctx,
                                                     const tvdb_dense_grid_d* grid,
                                                     const double* points,
                                                     size_t npoints,
                                                     double* out_values,
                                                     tvdb_error_t* err);

tvdb_status_t tvdb_gpu_csg_dense_d(tvdb_gpu_context_t* ctx,
                                   const tvdb_dense_grid_d* a,
                                   const tvdb_dense_grid_d* b,
                                   int op,
                                   tvdb_dense_grid_d* result,
                                   tvdb_error_t* err);
tvdb_status_t tvdb_gpu_stencil_scalar_d(tvdb_gpu_context_t* ctx,
                                        const tvdb_dense_grid_d* in,
                                        int op,
                                        tvdb_dense_grid_d* out,
                                        tvdb_error_t* err);

// ---------------------------------------------------------------------------
// vec3 grid elementwise ops.
//
// These mirror the CPU reference exactly, including its edge case: normalize
// writes zero (not NaN) where the magnitude is 0. Each is an op selector on the
// stencil shader for the matching shape, so no new shader or kernel is needed.

// magnitude of a vec3 grid: sqrt(x^2 + y^2 + z^2).
tvdb_status_t tvdb_gpu_magnitude(tvdb_gpu_context_t* ctx,
                                 const tvdb_dense_vec_grid* in,
                                 tvdb_dense_grid* out,
                                 tvdb_error_t* err);

// unit-length vec3 grid; zero where the magnitude is 0.
tvdb_status_t tvdb_gpu_normalize_vec(tvdb_gpu_context_t* ctx,
                                     const tvdb_dense_vec_grid* in,
                                     tvdb_dense_vec_grid* out,
                                     tvdb_error_t* err);

// closest-point transform: p - d * grad(sdf), per voxel centre.
tvdb_status_t tvdb_gpu_cpt(tvdb_gpu_context_t* ctx,
                           const tvdb_dense_grid* in,
                           tvdb_dense_vec_grid* out,
                           tvdb_error_t* err);

// ---------------------------------------------------------------------------
// Mean curvature flow.
//
// The CPU reference is Jacobi (each step reads a snapshot and writes the
// interior), so this is `iterations` dispatches ping-ponging two device buffers.
// A no-op when any axis is below 3, matching the CPU.

tvdb_status_t tvdb_gpu_mean_curvature_flow(tvdb_gpu_context_t* ctx,
                                           const tvdb_dense_grid* in,
                                           float dt, int iterations,
                                           tvdb_dense_grid* out,
                                           tvdb_error_t* err);

// ---------------------------------------------------------------------------
// Eikonal fast sweeping.
//
// The CPU reference is Gauss-Seidel, so this decomposes each sweep into
// wavefront planes and issues one dispatch per plane, deferred and flushed once
// per iteration. The returned iteration count matches the CPU's.
//
// Returns TVDB_ERROR_UNIMPLEMENTED when the SPIR-V is unavailable (the build
// without glslangValidator); the CUDA backend uses the CPU reference, since the
// same plane decomposition would need its own kernel.

// ---- Persistent device-resident index map -----------------------------------
//
// The index ops (ijk_to_index, neighbor_counts, points_in_grid, sparse_conv)
// replace an O(n) linear scan of the active set with a host-built
// open-addressing map. Above ~2048 active voxels that map is worth it, and at
// large active sets it is the whole cost: the map depends only on the active
// set, but the per-call path rebuilds it on the host and re-uploads it every time,
// which is 12-25 MB of transfer per call for a 700k active set. Measured
// interleaved A/B at 699k active voxels: Vulkan 161.8 ms vs CUDA 59.4 ms for
// ijk_to_index, both bound by that build-and-upload rather than by the kernel.
//
// This is the reusable form. Build once, query any number of times, and the map
// lives in DEVICE_LOCAL memory -- write-once/read-many, which is exactly what
// device-local is for, so there is no host-visible staging buffer to flush and no
// per-call upload at all. It is opt-in: the existing per-call entry points keep
// working unchanged, because they cannot know whether the caller's active set is
// still the same buffer with the same contents.
//
// Not valid across an active-set mutation, and not valid across contexts. Build a
// new one if the active set changes.
tvdb_status_t tvdb_gpu_index_map_create(tvdb_gpu_context_t* ctx,
                                        const int32_t* active, size_t na,
                                        tvdb_gpu_index_map_t** out,
                                        tvdb_error_t* err);
void tvdb_gpu_index_map_destroy(tvdb_gpu_context_t* ctx, tvdb_gpu_index_map_t* map);

// Number of active voxels the map was built from.
size_t tvdb_gpu_index_map_active_count(const tvdb_gpu_index_map_t* map);

// First-seen index of each query ijk, or -1 when absent. Same contract as
// tvdb_gpu_ijk_to_index, including first-seen ordering for duplicate coordinates.
tvdb_status_t tvdb_gpu_ijk_to_index_mapped(tvdb_gpu_context_t* ctx,
                                           const tvdb_gpu_index_map_t* map,
                                           const int32_t* query, size_t nq,
                                           int32_t* out, tvdb_error_t* err);
// Per-active-voxel neighbour count, 6- or 26-connectivity.
tvdb_status_t tvdb_gpu_neighbor_counts_mapped(tvdb_gpu_context_t* ctx,
                                              const tvdb_gpu_index_map_t* map,
                                              int connectivity,
                                              int32_t* out_counts,
                                              tvdb_error_t* err);
// Index of the active voxel containing each world-space point, or -1 when absent.
tvdb_status_t tvdb_gpu_points_in_grid_mapped(tvdb_gpu_context_t* ctx,
                                             const tvdb_gpu_index_map_t* map,
                                             const float* points, size_t np,
                                             const float voxel_size[3],
                                             const float origin[3],
                                             int32_t* out, tvdb_error_t* err);

// fp64 fast sweeping (parallels tvdb_fast_sweeping_d). Returns TVDB_OK and sets
// *out_iters, or reports UNIMPLEMENTED when the device lacks shaderFloat64 --
// computing it in fp32 would return different values than were asked for.
//
// One behavioural difference from the fp32 twin: the device-side change
// accumulator can only atomicMax 32 bits (GLSL has no uint64_t and `union` is a
// reserved word), so it tracks the high half of the pattern and the host
// reconstructs to 2^-20 relative. That underestimates, so convergence can be
// detected up to 1e-6 relative late and never early. CUDA uses the CPU reference.
int tvdb_gpu_fast_sweeping_d(tvdb_gpu_context_t* ctx, tvdb_dense_grid_d* grid,
                             double frozen_band, int max_iters, double tol,
                             int* out_iters, tvdb_error_t* err);

tvdb_status_t tvdb_gpu_fast_sweeping(tvdb_gpu_context_t* ctx,
                                     tvdb_dense_grid* grid,
                                     float frozen_band,
                                     int max_iters, float tol,
                                     int* out_iters,
                                     tvdb_error_t* err);
