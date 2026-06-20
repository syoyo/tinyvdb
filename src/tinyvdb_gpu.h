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
#include "tinyvdb_sparse.h" // tvdb_sparse_grid

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

#ifdef __cplusplus
}
#endif
