#pragma once
#include "tinyvdb_gpu.h"
#ifdef __cplusplus
extern "C" {
#endif

/* Explicit device storage. Contexts outlive their handles; calls on a context
 * are serialized by the caller. Operations are synchronous, with no implicit
 * grid readback. Destroying a handle does not destroy its context. */
typedef enum { TVDB_GPU_F32 = 0, TVDB_GPU_F64 = 1 } tvdb_gpu_value_type_t;
typedef struct {
    int nx, ny, nz, channels; /* channels: 1 or 3; f64 currently scalar only */
    tvdb_gpu_value_type_t type;
    double ox, oy, oz, voxel_size;
} tvdb_gpu_grid_desc_t;
typedef struct {
    uint64_t upload_bytes, download_bytes, allocations, submissions;
    size_t live_bytes, peak_bytes;
} tvdb_gpu_resident_metrics_t;
void tvdb_gpu_resident_metrics(tvdb_gpu_context_t*, tvdb_gpu_resident_metrics_t*);
/* Reset cumulative counters; current live bytes remain the peak baseline. */
void tvdb_gpu_resident_metrics_reset(tvdb_gpu_context_t*);
tvdb_status_t tvdb_gpu_buffer_create_device(tvdb_gpu_context_t*, size_t,
    tvdb_gpu_buffer_t**, tvdb_error_t*);
tvdb_status_t tvdb_gpu_dense_grid_create(tvdb_gpu_context_t*, const tvdb_gpu_grid_desc_t*,
    tvdb_gpu_dense_grid_t**, tvdb_error_t*);
void tvdb_gpu_dense_grid_destroy(tvdb_gpu_dense_grid_t*);
tvdb_status_t tvdb_gpu_dense_grid_upload(tvdb_gpu_dense_grid_t*, const void*, size_t, tvdb_error_t*);
tvdb_status_t tvdb_gpu_dense_grid_download(const tvdb_gpu_dense_grid_t*, void*, size_t, tvdb_error_t*);
tvdb_status_t tvdb_gpu_dense_grid_description(const tvdb_gpu_dense_grid_t*, tvdb_gpu_grid_desc_t*);
/* Borrowed buffer; invalidated by a mutating operation or grid destruction. */
tvdb_gpu_buffer_t* tvdb_gpu_dense_grid_buffer(const tvdb_gpu_dense_grid_t*);

/* Bind either a resident buffer or copied uniform bytes, never both. CUDA
 * kernels receive pointers in binding order. local_size must match the shader.
 * A batch records all Vulkan dispatches before submitting once. All bindings
 * stay alive until return. Raw dispatch may partially write outputs on error;
 * typed grid operations use transactional scratch instead. */
typedef struct {
    tvdb_gpu_buffer_t* buffer;
    const void* uniform;
    size_t uniform_size;
} tvdb_gpu_resident_binding_t;
typedef struct {
    const unsigned char* spv;
    unsigned int spv_len;
    const char* cuda_kernel;
    tvdb_gpu_resident_binding_t bindings[8];
    unsigned int num_bindings;
    unsigned int groups[3], local_size[3];
} tvdb_gpu_resident_dispatch_t;
tvdb_status_t tvdb_gpu_dispatch_resident(tvdb_gpu_context_t*,
    const tvdb_gpu_resident_dispatch_t*, size_t count, tvdb_error_t*);

/* op: 0 max, 1 min, 2 sum, 3 product; shapes, types and contexts must match. */
tvdb_status_t tvdb_gpu_comp_resident(tvdb_gpu_context_t*, const tvdb_gpu_dense_grid_t*,
    const tvdb_gpu_dense_grid_t*, int op, tvdb_gpu_dense_grid_t*, tvdb_error_t*);
/* kind: 0 mean, 1 Gaussian, 2 Laplacian, 3 median. Width is the CPU width
 * convention; median supports radii <=2, as the existing GPU entry point. */
tvdb_status_t tvdb_gpu_filter_resident(tvdb_gpu_context_t*, tvdb_gpu_dense_grid_t*,
    int kind, int width, int iterations, tvdb_error_t*);
/* Scalar stencils: op 0 Laplacian, 1/2/3 derivatives. Scalar->vec3:
 * 0 gradient, 1 CPT. Vec3->scalar: 0 divergence, 1 magnitude.
 * Vec3->vec3: 0 curl, 1 normalization. Result geometry matches input. */
tvdb_status_t tvdb_gpu_stencil_resident(tvdb_gpu_context_t*, const tvdb_gpu_dense_grid_t*,
    int op, tvdb_gpu_dense_grid_t*, tvdb_error_t*);
tvdb_status_t tvdb_gpu_csg_resident(tvdb_gpu_context_t*, const tvdb_gpu_dense_grid_t*,
    const tvdb_gpu_dense_grid_t*, int op, tvdb_gpu_dense_grid_t*, tvdb_error_t*);
/* scheme: TVDB_ADVECT_* or -1 for voxel-velocity semi-Lagrangian advection. */
tvdb_status_t tvdb_gpu_advect_resident(tvdb_gpu_context_t*, const tvdb_gpu_dense_grid_t*,
    const tvdb_gpu_dense_grid_t* velocity, float dt, int scheme, int clamp,
    tvdb_gpu_dense_grid_t*, tvdb_error_t*);
/* kind: 0 dilate, 1 erode, 2 open, 3 close. */
tvdb_status_t tvdb_gpu_morph_resident(tvdb_gpu_context_t*, tvdb_gpu_dense_grid_t*,
    int kind, int iterations, tvdb_error_t*);
/* Result dimensions must be ceil(input/factor) for coarsen, input*factor for
 * refine. Geometry is set on successful completion. */
tvdb_status_t tvdb_gpu_resample_resident(tvdb_gpu_context_t*, const tvdb_gpu_dense_grid_t*,
    int factor, int refine, tvdb_gpu_dense_grid_t*, tvdb_error_t*);
/* Ordered compact triangle soup. On success output owns exactly count*9 floats
 * (an empty mesh owns a minimal buffer); free with tvdb_gpu_buffer_destroy. */
tvdb_status_t tvdb_gpu_marching_cubes_resident(tvdb_gpu_context_t*, const tvdb_gpu_dense_grid_t*,
    float isovalue, tvdb_gpu_buffer_t** output, size_t* triangle_count, tvdb_error_t*);
/* Sparse topology is immutable and shared by topology-preserving results.
 * Output handle slots must contain NULL or an owning handle from this context.
 * Success replaces/destroys the old output; failure leaves it unchanged. */
tvdb_status_t tvdb_gpu_sparse_grid_upload(tvdb_gpu_context_t*, const tvdb_sparse_grid*,
    tvdb_gpu_sparse_grid_t**, tvdb_error_t*);
void tvdb_gpu_sparse_grid_destroy(tvdb_gpu_sparse_grid_t*);
/* Update values transactionally while retaining the resident coordinate map. */
tvdb_status_t tvdb_gpu_sparse_grid_update_values(tvdb_gpu_sparse_grid_t*,const float*,size_t count,tvdb_error_t*);
size_t tvdb_gpu_sparse_grid_count(const tvdb_gpu_sparse_grid_t*);
tvdb_status_t tvdb_gpu_sparse_grid_download(const tvdb_gpu_sparse_grid_t*, tvdb_sparse_grid*, tvdb_error_t*);
/* kind: 0 same topology, 1 strided, 2 transpose. Full signed coordinates and
 * first-occurrence duplicate lookup semantics match the CPU sparse APIs.
 * Transpose sums all duplicate contributions and rejects coordinate overflow. */
tvdb_status_t tvdb_gpu_sparse_conv_resident(tvdb_gpu_context_t*, const tvdb_gpu_sparse_grid_t*,
    const float* kernel, int kx,int ky,int kz,int stride,int kind,float pad,
    tvdb_gpu_sparse_grid_t**,tvdb_error_t*);
/* kind: 0 dilate, 1 erode; iterations must be positive. */
tvdb_status_t tvdb_gpu_sparse_morph_resident(tvdb_gpu_context_t*,const tvdb_gpu_sparse_grid_t*,
    int kind,int iterations,float background,tvdb_gpu_sparse_grid_t**,tvdb_error_t*);
/* Precision: 0 float workspace/input, 1 double workspace with float input,
 * 2 double workspace/input. Modes 0/1 use relative residual tolerance; mode 2
 * uses absolute tolerance. Neumann compatibility and warm-start mean are
 * preserved. Requires fp64 reductions; only reduced scalars leave the device.
 * Workspace uses 40/64/72 bytes per voxel (plus reductions/output scratch),
 * with double true residuals in all modes. RHS and output may alias. */
tvdb_status_t tvdb_gpu_poisson_resident(tvdb_gpu_context_t*,const tvdb_gpu_dense_grid_t*,
    tvdb_gpu_dense_grid_t*,int precision,int max_iters,double tolerance,
    tvdb_poisson_result_t*,tvdb_error_t*);
tvdb_status_t tvdb_gpu_dense_to_sparse_resident(tvdb_gpu_context_t*,const tvdb_gpu_dense_grid_t*,
    float background,float tolerance,tvdb_gpu_sparse_grid_t**,tvdb_error_t*);
/* Coordinates use the target's index frame; out-of-bounds coordinates are ignored. */
tvdb_status_t tvdb_gpu_sparse_to_dense_resident(tvdb_gpu_context_t*,const tvdb_gpu_sparse_grid_t*,
    float background,tvdb_gpu_dense_grid_t*,tvdb_error_t*);
/* XYZ float triples in a device buffer. Isotropic spacing; rejects nonfinite or
 * out-of-int32 points transactionally. Occupied values are one. */
tvdb_status_t tvdb_gpu_voxelize_resident(tvdb_gpu_context_t*,tvdb_gpu_buffer_t* points,size_t count,
    const float origin[3],float voxel_size,tvdb_gpu_sparse_grid_t**,tvdb_error_t*);
/* Reduced results only: 16 bytes for statistics/level-set validation, four for
 * checksum, eight for measurement. Measurement supports f32/f64 grids and
 * requires fp64; the other reductions currently accept f32 scalar grids. */
tvdb_status_t tvdb_gpu_statistics_resident(tvdb_gpu_context_t*,const tvdb_gpu_dense_grid_t*,tvdb_grid_stats_t*,tvdb_error_t*);
tvdb_status_t tvdb_gpu_levelset_check_resident(tvdb_gpu_context_t*,const tvdb_gpu_dense_grid_t*,double band,double tolerance,tvdb_level_set_check_t*,tvdb_error_t*);
tvdb_status_t tvdb_gpu_checksum_resident(tvdb_gpu_context_t*,const tvdb_gpu_dense_grid_t*,uint32_t*,tvdb_error_t*);
tvdb_status_t tvdb_gpu_measure_resident(tvdb_gpu_context_t*,const tvdb_gpu_dense_grid_t*,int volume,double*,tvdb_error_t*);
#ifdef __cplusplus
}
#endif
