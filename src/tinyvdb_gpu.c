#include "tinyvdb_gpu.h"
#include "tinyvdb_checked.h"
#include "tinyvdb_poisson_internal.h"
#include <math.h>
#include <float.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32)
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
// <windows.h> defines legacy 16-bit `near`/`far` macros (expand to nothing),
// which collide with parameter/identifier names like tvdb_gpu_gaussian_project's
// near/far plane. Undefine them; nothing here relies on the macros.
#undef near
#undef far
#else
#include <dlfcn.h>
#include <unistd.h>   // close() for external-memory opaque fds
#endif

static bool tvdb_gpu_shape_valid(int nx,int ny,int nz,double h,const void* data,size_t width) {
  size_t bytes;
  return tvdb_grid_valid(nx,ny,nz,h,data,width) &&
    tvdb_grid_bytes(nx,ny,nz,width,&bytes) && bytes/width <= INT_MAX;
}

static tvdb_status_t resident_double_host(tvdb_gpu_context_t*,const tvdb_dense_grid_d*,const tvdb_dense_grid_d*,int,tvdb_dense_grid_d*,tvdb_error_t*);
static tvdb_status_t resident_reduce_host(tvdb_gpu_context_t*,const tvdb_dense_grid*,int,double,double,void*,tvdb_error_t*);
static tvdb_status_t resident_measure_host(tvdb_gpu_context_t*,const void*,int,int,int,int,int,double*,tvdb_error_t*);
static tvdb_status_t resident_active_host(tvdb_gpu_context_t*,const tvdb_dense_grid*,float,float,tvdb_sparse_grid*,tvdb_error_t*);
static tvdb_status_t resident_stencil_host(tvdb_gpu_context_t*,const tvdb_dense_grid*,int,int,int,float**,tvdb_error_t*);
static tvdb_status_t resident_morph_host(tvdb_gpu_context_t*,tvdb_dense_grid*,int,int,tvdb_error_t*);
static tvdb_status_t resident_resample_host(tvdb_gpu_context_t*,const tvdb_dense_grid*,int,int,tvdb_dense_grid*,tvdb_error_t*);
static tvdb_status_t resident_sparse_host(tvdb_gpu_context_t*,const tvdb_sparse_grid*,const float*,int,int,int,int,int,int,float,tvdb_sparse_grid*,tvdb_error_t*);
static tvdb_status_t resident_poisson_host(tvdb_gpu_context_t*,const void*,void*,const tvdb_gpu_grid_desc_t*,int,int,double,tvdb_poisson_result_t*,tvdb_error_t*);
static tvdb_status_t resident_binary_host(tvdb_gpu_context_t*,const tvdb_dense_grid*,const tvdb_dense_grid*,int,int,tvdb_dense_grid*,tvdb_error_t*);
static tvdb_status_t resident_filter_host(tvdb_gpu_context_t*,tvdb_dense_grid*,int,int,int,tvdb_error_t*);
static tvdb_status_t resident_advect_host(tvdb_gpu_context_t*,const tvdb_dense_grid*,const tvdb_dense_vec_grid*,float,int,int,tvdb_dense_grid*,tvdb_error_t*);

// Close an exported opaque-fd handle (POSIX only; opaque-fd interop is Linux).
static void tvdb_close_opaque_fd(uint64_t handle) {
#if !defined(_WIN32)
  close((int)(unsigned int)handle);
#else
  (void)handle;
#endif
}

#if defined(__has_include)
#if __has_include("tinyvdb_gpu_csg_spv.inc")
#include "tinyvdb_gpu_csg_spv.inc"
#include "tinyvdb_gpu_sample_spv.inc"
#include "tinyvdb_gpu_sample_image_spv.inc"
#include "tinyvdb_gpu_sample_quadratic_spv.inc"
#include "tinyvdb_gpu_sparse_conv_spv.inc"
#include "tinyvdb_gpu_sparse_index_scatter_spv.inc"
#include "tinyvdb_gpu_sparse_conv_dense_spv.inc"
#include "tinyvdb_gpu_sdf_sphere_spv.inc"
#include "tinyvdb_gpu_sdf_box_spv.inc"
#include "tinyvdb_gpu_sdf_torus_spv.inc"
#include "tinyvdb_gpu_ijk_to_index_spv.inc"
#include "tinyvdb_gpu_index_probe_spv.inc"
#include "tinyvdb_gpu_neighbor_counts_probe_spv.inc"
#include "tinyvdb_gpu_points_in_grid_probe_spv.inc"
#include "tinyvdb_gpu_sparse_conv_map_spv.inc"
#include "tinyvdb_gpu_points_in_grid_spv.inc"
#include "tinyvdb_gpu_neighbor_counts_spv.inc"
#include "tinyvdb_gpu_morph_spv.inc"
#include "tinyvdb_gpu_prune_spv.inc"
#include "tinyvdb_gpu_coarsen_spv.inc"
#include "tinyvdb_gpu_refine_spv.inc"
#include "tinyvdb_gpu_volume_render_spv.inc"
#include "tinyvdb_gpu_ray_samples_spv.inc"
#include "tinyvdb_gpu_voxels_along_ray_spv.inc"
#include "tinyvdb_gpu_segments_along_ray_spv.inc"
#include "tinyvdb_gpu_tsdf_spv.inc"
#include "tinyvdb_gpu_stats_spv.inc"
#include "tinyvdb_gpu_levelset_check_spv.inc"
#include "tinyvdb_gpu_flood_spv.inc"
#include "tinyvdb_gpu_splat_spv.inc"
#include "tinyvdb_gpu_splat_quadratic_spv.inc"
#include "tinyvdb_gpu_points_to_mask_spv.inc"
#include "tinyvdb_gpu_voxelize_mark_spv.inc"
#include "tinyvdb_gpu_voxelize_compact_spv.inc"
#include "tinyvdb_gpu_hash_insert_spv.inc"
#include "tinyvdb_gpu_hash_compact_spv.inc"
#include "tinyvdb_gpu_sparse_mark_spv.inc"
#include "tinyvdb_gpu_sparse_erode_spv.inc"
#include "tinyvdb_gpu_sparse_dilate_scatter_spv.inc"
#include "tinyvdb_gpu_sparse_finalize_spv.inc"
#include "tinyvdb_gpu_merge_scatter_spv.inc"
#include "tinyvdb_gpu_active_coords_spv.inc"
#include "tinyvdb_gpu_checksum_spv.inc"
#include "tinyvdb_gpu_stencil_scalar_scalar_spv.inc"
#include "tinyvdb_gpu_stencil_scalar_d_spv.inc"
#include "tinyvdb_gpu_csg_d_spv.inc"
#include "tinyvdb_gpu_sample_d_spv.inc"
#include "tinyvdb_gpu_stencil_scalar_vec_spv.inc"
#include "tinyvdb_gpu_stencil_vec_scalar_spv.inc"
#include "tinyvdb_gpu_stencil_vec_vec_spv.inc"
#include "tinyvdb_gpu_mean_curvature_flow_spv.inc"
#include "tinyvdb_gpu_fast_sweeping_plane_spv.inc"
#include "tinyvdb_gpu_fast_sweeping_plane_d_spv.inc"
#include "tinyvdb_gpu_mesh_to_sdf_spv.inc"
#include "tinyvdb_gpu_mesh_to_sdf_bvh_spv.inc"
#include "tinyvdb_gpu_measure_spv.inc"
#include "tinyvdb_gpu_measure_d_spv.inc"
#include "tinyvdb_gpu_filter_spv.inc"
#include "tinyvdb_gpu_advect_spv.inc"
#include "tinyvdb_gpu_comp_spv.inc"
#include "tinyvdb_gpu_marching_cubes_spv.inc"
#include "tinyvdb_gpu_scan_spv.inc"
#include "tinyvdb_gpu_resident_reduce_spv.inc"
#include "tinyvdb_gpu_resident_poisson_spv.inc"
#include "tinyvdb_gpu_resident_sparse_spv.inc"
#include "tinyvdb_gpu_resident_map_spv.inc"
#include "tinyvdb_gpu_sparse_conv_strided_spv.inc"
#include "tinyvdb_gpu_conv_transpose_scatter_spv.inc"
#include "tinyvdb_gpu_gaussian_forward_spv.inc"
#include "tinyvdb_gpu_gaussian_backward_spv.inc"
#include "tinyvdb_gpu_gaussian_sh_spv.inc"
#include "tinyvdb_gpu_gaussian_project_spv.inc"
#include "tinyvdb_gpu_mcmc_relocation_spv.inc"
#include "tinyvdb_gpu_mcmc_noise_spv.inc"
#include "tinyvdb_gpu_axpy_spv.inc"
#include "tinyvdb_gpu_ssim_spv.inc"
#include "tinyvdb_gpu_sparse_conv_batched_spv.inc"
#else
#include "tinyvdb_gpu_spv_fallback.inc"
#endif
#else
#include "tinyvdb_gpu_spv_fallback.inc"
#endif

typedef uint32_t VkBool32;
typedef uint32_t VkFlags;
typedef uint64_t VkDeviceSize;
typedef int32_t VkResult;
typedef struct VkInstance_T* VkInstance;
typedef struct VkPhysicalDevice_T* VkPhysicalDevice;
typedef struct VkDevice_T* VkDevice;
typedef struct VkQueue_T* VkQueue;
typedef struct VkCommandBuffer_T* VkCommandBuffer;
typedef uint64_t VkBuffer;
typedef uint64_t VkDeviceMemory;
typedef uint64_t VkShaderModule;
typedef uint64_t VkPipelineLayout;
typedef uint64_t VkPipeline;
typedef uint64_t VkDescriptorSetLayout;
typedef uint64_t VkDescriptorPool;
typedef uint64_t VkDescriptorSet;
typedef uint64_t VkCommandPool;
typedef uint64_t VkFence;
typedef uint64_t VkImage;
typedef uint64_t VkImageView;
typedef uint64_t VkSampler;

typedef int CUresult;
typedef int CUdevice;
typedef struct CUctx_st* CUcontext;
typedef struct CUmod_st* CUmodule;
typedef struct CUfunc_st* CUfunction;
typedef uint64_t CUdeviceptr;
typedef struct CUextMemory_st* CUexternalMemory;
typedef struct {
  unsigned int type;
  union { int fd; struct { void* handle; const void* name; } win32; const void* nvSciBufObject; } handle;
  unsigned long long size;
  unsigned int flags;
  unsigned int reserved[16];
} CUDA_EXTERNAL_MEMORY_HANDLE_DESC;
typedef struct {
  unsigned long long offset;
  unsigned long long size;
  unsigned int flags;
  unsigned int reserved[16];
} CUDA_EXTERNAL_MEMORY_BUFFER_DESC;
#define CU_EXTERNAL_MEMORY_HANDLE_TYPE_OPAQUE_FD 1
#define CUDA_EXTERNAL_MEMORY_DEDICATED 0x1u
typedef int nvrtcResult;
typedef struct _nvrtcProgram* nvrtcProgram;

#define CUDA_SUCCESS 0
#define NVRTC_SUCCESS 0

#define VK_NULL_HANDLE 0
#define VK_SUCCESS 0
#define VK_NOT_READY 1
#define VK_TRUE 1
#define VK_FALSE 0
#define VK_STRUCTURE_TYPE_APPLICATION_INFO 0
#define VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO 1
#define VK_STRUCTURE_TYPE_DEVICE_QUEUE_CREATE_INFO 2
#define VK_STRUCTURE_TYPE_DEVICE_CREATE_INFO 3
#define VK_STRUCTURE_TYPE_SUBMIT_INFO 4
#define VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO 5
#define VK_STRUCTURE_TYPE_BIND_SPARSE_INFO 7
#define VK_STRUCTURE_TYPE_FENCE_CREATE_INFO 8
#define VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO 12
#define VK_STRUCTURE_TYPE_IMAGE_CREATE_INFO 14
#define VK_STRUCTURE_TYPE_IMAGE_VIEW_CREATE_INFO 15
#define VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO 16
#define VK_STRUCTURE_TYPE_SAMPLER_CREATE_INFO 31
#define VK_STRUCTURE_TYPE_PIPELINE_SHADER_STAGE_CREATE_INFO 18
#define VK_STRUCTURE_TYPE_PIPELINE_LAYOUT_CREATE_INFO 30
#define VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO 32
#define VK_DESCRIPTOR_POOL_CREATE_FREE_DESCRIPTOR_SET_BIT 0x00000001u
#define VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO 33
#define VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO 34
#define VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET 35
#define VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO 39
#define VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO 40
#define VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO 42
#define VK_STRUCTURE_TYPE_IMAGE_MEMORY_BARRIER 45
#define VK_STRUCTURE_TYPE_BUFFER_MEMORY_BARRIER 44
#define VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO 29
#define VK_API_VERSION_1_0 ((uint32_t)(1u << 22))
#define VK_API_VERSION_1_1 ((uint32_t)((1u << 22) | (1u << 12)))
#define VK_QUEUE_COMPUTE_BIT 0x00000002u
#define VK_QUEUE_SPARSE_BINDING_BIT 0x00000008u
#define VK_QUEUE_FAMILY_IGNORED UINT32_MAX
#define VK_IMAGE_CREATE_SPARSE_BINDING_BIT 0x00000001u
#define VK_IMAGE_CREATE_SPARSE_RESIDENCY_BIT 0x00000002u
#define VK_IMAGE_CREATE_SPARSE_ALIASED_BIT 0x00000004u
#define VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT 0x00000010u
#define VK_BUFFER_USAGE_STORAGE_BUFFER_BIT 0x00000020u
#define VK_BUFFER_USAGE_TRANSFER_SRC_BIT 0x00000001u
#define VK_IMAGE_USAGE_TRANSFER_DST_BIT 0x00000002u
#define VK_IMAGE_USAGE_SAMPLED_BIT 0x00000004u
#define VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT 0x00000002u
#define VK_MEMORY_PROPERTY_HOST_COHERENT_BIT 0x00000004u
#define VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT 0x00000001u
#define VK_BUFFER_USAGE_TRANSFER_DST_BIT 0x00000002u
// External memory (VK_KHR_external_memory + VK_KHR_external_memory_fd).
#define VK_STRUCTURE_TYPE_EXTERNAL_MEMORY_BUFFER_CREATE_INFO 1000072000
#define VK_STRUCTURE_TYPE_EXPORT_MEMORY_ALLOCATE_INFO 1000072002
#define VK_STRUCTURE_TYPE_MEMORY_DEDICATED_ALLOCATE_INFO 1000127001
#define VK_STRUCTURE_TYPE_MEMORY_GET_FD_INFO_KHR 1000074002
#define VK_EXTERNAL_MEMORY_HANDLE_TYPE_OPAQUE_FD_BIT 0x00000001u
#define VK_SHARING_MODE_EXCLUSIVE 0
#define VK_IMAGE_TYPE_3D 2
#define VK_IMAGE_VIEW_TYPE_3D 2
#define VK_FORMAT_R32_SFLOAT 100
#define VK_SAMPLE_COUNT_1_BIT 0x00000001u
#define VK_IMAGE_TILING_OPTIMAL 0
#define VK_IMAGE_LAYOUT_UNDEFINED 0
#define VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL 7
#define VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL 5
#define VK_IMAGE_ASPECT_COLOR_BIT 0x00000001u
#define VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER 1
#define VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER 6
#define VK_DESCRIPTOR_TYPE_STORAGE_BUFFER 7
#define VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER_DYNAMIC 8
#define VK_DESCRIPTOR_TYPE_STORAGE_BUFFER_DYNAMIC 9
#define VK_FILTER_LINEAR 1
#define VK_SAMPLER_MIPMAP_MODE_NEAREST 0
#define VK_SAMPLER_ADDRESS_MODE_CLAMP_TO_EDGE 2
#define VK_BORDER_COLOR_FLOAT_TRANSPARENT_BLACK 0
#define VK_ACCESS_TRANSFER_WRITE_BIT 0x00001000u
#define VK_ACCESS_HOST_READ_BIT 0x00002000u
#define VK_ACCESS_HOST_WRITE_BIT 0x00004000u
#define VK_ACCESS_UNIFORM_READ_BIT 0x00000008u
#define VK_ACCESS_SHADER_READ_BIT 0x00000020u
#define VK_ACCESS_SHADER_WRITE_BIT 0x00000040u
#define VK_ACCESS_TRANSFER_READ_BIT 0x00000800u
#define VK_ACCESS_TRANSFER_WRITE_BIT 0x00001000u
#define VK_PIPELINE_STAGE_TOP_OF_PIPE_BIT 0x00000001u
#define VK_PIPELINE_STAGE_TRANSFER_BIT 0x00001000u
#define VK_PIPELINE_STAGE_HOST_BIT 0x00004000u
#define VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT 0x00000800u
#define VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT 0x00000001u
#define VK_SPARSE_MEMORY_BIND_METADATA_BIT 0x00000001u
#define VK_SHADER_STAGE_COMPUTE_BIT 0x00000020u
#define VK_PIPELINE_BIND_POINT_COMPUTE 1
#define VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT 0x00000002u
#define VK_COMMAND_POOL_CREATE_FREE_COMMAND_BUFFER_BIT 0x00000004u
#define VK_COMMAND_BUFFER_LEVEL_PRIMARY 0

/* vkGetPhysicalDeviceProperties2 with a VkPhysicalDeviceIDProperties chain.
 * The core VkPhysicalDeviceProperties payload (824 bytes on LP64) is not
 * read, so it is kept opaque and generously sized. */
#define VK_STRUCTURE_TYPE_PHYSICAL_DEVICE_PROPERTIES_2 1000059001
#define VK_STRUCTURE_TYPE_PHYSICAL_DEVICE_ID_PROPERTIES 1000071004
typedef struct {
  uint32_t sType; void* pNext;
  uint8_t deviceUUID[16]; uint8_t driverUUID[16]; uint8_t deviceLUID[8];
  uint32_t deviceNodeMask; uint32_t deviceLUIDValid;
} VkPhysicalDeviceIDProperties;
typedef struct {
  uint32_t sType; void* pNext;
  union { uint64_t align; uint8_t bytes[2048]; } properties;
} VkPhysicalDeviceProperties2;
typedef void (*PFN_vkGetPhysicalDeviceProperties2)(VkPhysicalDevice, VkPhysicalDeviceProperties2*);

typedef struct {
  uint32_t sType;
  const void* pNext;
  const char* pApplicationName;
  uint32_t applicationVersion;
  const char* pEngineName;
  uint32_t engineVersion;
  uint32_t apiVersion;
} VkApplicationInfo;
typedef struct {
  uint32_t sType; const void* pNext; VkFlags flags;
  const VkApplicationInfo* pApplicationInfo;
  uint32_t enabledLayerCount; const char* const* ppEnabledLayerNames;
  uint32_t enabledExtensionCount; const char* const* ppEnabledExtensionNames;
} VkInstanceCreateInfo;
typedef struct {
  uint32_t sType; const void* pNext; VkFlags flags; uint32_t queueFamilyIndex;
  uint32_t queueCount; const float* pQueuePriorities;
} VkDeviceQueueCreateInfo;
typedef struct {
  uint32_t sType; const void* pNext; VkFlags flags; uint32_t queueCreateInfoCount;
  const VkDeviceQueueCreateInfo* pQueueCreateInfos; uint32_t enabledLayerCount;
  const char* const* ppEnabledLayerNames; uint32_t enabledExtensionCount;
  const char* const* ppEnabledExtensionNames; const void* pEnabledFeatures;
} VkDeviceCreateInfo;
typedef struct { uint32_t propertyFlags; uint32_t heapIndex; } VkMemoryType;
typedef struct { VkDeviceSize size; uint32_t flags; } VkMemoryHeap;
typedef struct { uint32_t memoryTypeCount; VkMemoryType memoryTypes[32]; uint32_t memoryHeapCount; VkMemoryHeap memoryHeaps[16]; } VkPhysicalDeviceMemoryProperties;
typedef struct {
  VkBool32 robustBufferAccess;
  VkBool32 fullDrawIndexUint32;
  VkBool32 imageCubeArray;
  VkBool32 independentBlend;
  VkBool32 geometryShader;
  VkBool32 tessellationShader;
  VkBool32 sampleRateShading;
  VkBool32 dualSrcBlend;
  VkBool32 logicOp;
  VkBool32 multiDrawIndirect;
  VkBool32 drawIndirectFirstInstance;
  VkBool32 depthClamp;
  VkBool32 depthBiasClamp;
  VkBool32 fillModeNonSolid;
  VkBool32 depthBounds;
  VkBool32 wideLines;
  VkBool32 largePoints;
  VkBool32 alphaToOne;
  VkBool32 multiViewport;
  VkBool32 samplerAnisotropy;
  VkBool32 textureCompressionETC2;
  VkBool32 textureCompressionASTC_LDR;
  VkBool32 textureCompressionBC;
  VkBool32 occlusionQueryPrecise;
  VkBool32 pipelineStatisticsQuery;
  VkBool32 vertexPipelineStoresAndAtomics;
  VkBool32 fragmentStoresAndAtomics;
  VkBool32 shaderTessellationAndGeometryPointSize;
  VkBool32 shaderImageGatherExtended;
  VkBool32 shaderStorageImageExtendedFormats;
  VkBool32 shaderStorageImageMultisample;
  VkBool32 shaderStorageImageReadWithoutFormat;
  VkBool32 shaderStorageImageWriteWithoutFormat;
  VkBool32 shaderUniformBufferArrayDynamicIndexing;
  VkBool32 shaderSampledImageArrayDynamicIndexing;
  VkBool32 shaderStorageBufferArrayDynamicIndexing;
  VkBool32 shaderStorageImageArrayDynamicIndexing;
  VkBool32 shaderClipDistance;
  VkBool32 shaderCullDistance;
  VkBool32 shaderFloat64;
  VkBool32 shaderInt64;
  VkBool32 shaderInt16;
  VkBool32 shaderResourceResidency;
  VkBool32 shaderResourceMinLod;
  VkBool32 sparseBinding;
  VkBool32 sparseResidencyBuffer;
  VkBool32 sparseResidencyImage2D;
  VkBool32 sparseResidencyImage3D;
  VkBool32 sparseResidency2Samples;
  VkBool32 sparseResidency4Samples;
  VkBool32 sparseResidency8Samples;
  VkBool32 sparseResidency16Samples;
  VkBool32 sparseResidencyAliased;
  VkBool32 variableMultisampleRate;
  VkBool32 inheritedQueries;
} VkPhysicalDeviceFeatures;
typedef struct { VkDeviceSize size; VkDeviceSize alignment; uint32_t memoryTypeBits; } VkMemoryRequirements;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; VkDeviceSize size; VkFlags usage; uint32_t sharingMode; uint32_t queueFamilyIndexCount; const uint32_t* pQueueFamilyIndices; } VkBufferCreateInfo;
typedef struct { uint32_t width; uint32_t height; uint32_t depth; } VkExtent3D;
typedef struct { VkFlags queueFlags; uint32_t queueCount; uint32_t timestampValidBits; VkExtent3D minImageTransferGranularity; } VkQueueFamilyProperties;
typedef struct { int32_t x; int32_t y; int32_t z; } VkOffset3D;
typedef struct { uint32_t aspectMask; uint32_t mipLevel; uint32_t arrayLayer; } VkImageSubresource;
typedef struct { uint32_t aspectMask; uint32_t mipLevel; uint32_t baseArrayLayer; uint32_t layerCount; } VkImageSubresourceLayers;
typedef struct { uint32_t aspectMask; uint32_t baseMipLevel; uint32_t levelCount; uint32_t baseArrayLayer; uint32_t layerCount; } VkImageSubresourceRange;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; uint32_t imageType; uint32_t format; VkExtent3D extent; uint32_t mipLevels; uint32_t arrayLayers; uint32_t samples; uint32_t tiling; VkFlags usage; uint32_t sharingMode; uint32_t queueFamilyIndexCount; const uint32_t* pQueueFamilyIndices; uint32_t initialLayout; } VkImageCreateInfo;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; VkImage image; uint32_t viewType; uint32_t format; uint32_t components[4]; VkImageSubresourceRange subresourceRange; } VkImageViewCreateInfo;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; uint32_t magFilter; uint32_t minFilter; uint32_t mipmapMode; uint32_t addressModeU; uint32_t addressModeV; uint32_t addressModeW; float mipLodBias; VkBool32 anisotropyEnable; float maxAnisotropy; VkBool32 compareEnable; uint32_t compareOp; float minLod; float maxLod; uint32_t borderColor; VkBool32 unnormalizedCoordinates; } VkSamplerCreateInfo;
typedef struct { uint32_t sType; const void* pNext; VkFlags srcAccessMask; VkFlags dstAccessMask; uint32_t oldLayout; uint32_t newLayout; uint32_t srcQueueFamilyIndex; uint32_t dstQueueFamilyIndex; VkImage image; VkImageSubresourceRange subresourceRange; } VkImageMemoryBarrier;
typedef struct { uint32_t sType; const void* pNext; VkFlags srcAccessMask; VkFlags dstAccessMask; uint32_t srcQueueFamilyIndex; uint32_t dstQueueFamilyIndex; VkBuffer buffer; VkDeviceSize offset; VkDeviceSize size; } VkBufferMemoryBarrier;
typedef struct { VkDeviceSize bufferOffset; uint32_t bufferRowLength; uint32_t bufferImageHeight; VkImageSubresourceLayers imageSubresource; VkOffset3D imageOffset; VkExtent3D imageExtent; } VkBufferImageCopy;
typedef struct { VkDeviceSize resourceOffset; VkDeviceSize size; VkDeviceMemory memory; VkDeviceSize memoryOffset; VkFlags flags; } VkSparseMemoryBind;
typedef struct { VkImage image; uint32_t bindCount; const VkSparseMemoryBind* pBinds; } VkSparseImageOpaqueMemoryBindInfo;
typedef struct { VkImageSubresource subresource; VkOffset3D offset; VkExtent3D extent; VkDeviceMemory memory; VkDeviceSize memoryOffset; VkFlags flags; } VkSparseImageMemoryBind;
typedef struct { VkImage image; uint32_t bindCount; const VkSparseImageMemoryBind* pBinds; } VkSparseImageMemoryBindInfo;
typedef struct { uint32_t sType; const void* pNext; uint32_t waitSemaphoreCount; const void* pWaitSemaphores; uint32_t bufferBindCount; const void* pBufferBinds; uint32_t imageOpaqueBindCount; const VkSparseImageOpaqueMemoryBindInfo* pImageOpaqueBinds; uint32_t imageBindCount; const VkSparseImageMemoryBindInfo* pImageBinds; uint32_t signalSemaphoreCount; const void* pSignalSemaphores; } VkBindSparseInfo;
typedef struct { uint32_t aspectMask; VkExtent3D imageGranularity; VkFlags flags; } VkSparseImageFormatProperties;
typedef struct { VkSparseImageFormatProperties formatProperties; uint32_t imageMipTailFirstLod; VkDeviceSize imageMipTailSize; VkDeviceSize imageMipTailOffset; VkDeviceSize imageMipTailStride; } VkSparseImageMemoryRequirements;
typedef struct { uint32_t sType; const void* pNext; VkDeviceSize allocationSize; uint32_t memoryTypeIndex; } VkMemoryAllocateInfo;
typedef struct { uint32_t sType; const void* pNext; uint32_t handleTypes; } VkExternalMemoryBufferCreateInfo;
typedef struct { uint32_t sType; const void* pNext; uint32_t handleTypes; } VkExportMemoryAllocateInfo;
typedef struct { uint32_t sType; const void* pNext; VkImage image; VkBuffer buffer; } VkMemoryDedicatedAllocateInfo;
typedef struct { uint32_t sType; const void* pNext; VkDeviceMemory memory; uint32_t handleType; } VkMemoryGetFdInfoKHR;
typedef struct { VkDeviceSize srcOffset; VkDeviceSize dstOffset; VkDeviceSize size; } VkBufferCopy;
typedef struct { char extensionName[256]; uint32_t specVersion; } VkExtensionProperties;
typedef struct { uint32_t binding; uint32_t descriptorType; uint32_t descriptorCount; uint32_t stageFlags; const void* pImmutableSamplers; } VkDescriptorSetLayoutBinding;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; uint32_t bindingCount; const VkDescriptorSetLayoutBinding* pBindings; } VkDescriptorSetLayoutCreateInfo;
typedef struct { uint32_t type; uint32_t descriptorCount; } VkDescriptorPoolSize;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; uint32_t maxSets; uint32_t poolSizeCount; const VkDescriptorPoolSize* pPoolSizes; } VkDescriptorPoolCreateInfo;
typedef struct { uint32_t sType; const void* pNext; VkDescriptorPool descriptorPool; uint32_t descriptorSetCount; const VkDescriptorSetLayout* pSetLayouts; } VkDescriptorSetAllocateInfo;
typedef struct { VkBuffer buffer; VkDeviceSize offset; VkDeviceSize range; } VkDescriptorBufferInfo;
typedef struct { VkSampler sampler; VkImageView imageView; uint32_t imageLayout; } VkDescriptorImageInfo;
typedef struct { uint32_t sType; const void* pNext; VkDescriptorSet dstSet; uint32_t dstBinding; uint32_t dstArrayElement; uint32_t descriptorCount; uint32_t descriptorType; const VkDescriptorImageInfo* pImageInfo; const VkDescriptorBufferInfo* pBufferInfo; const void* pTexelBufferView; } VkWriteDescriptorSet;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; size_t codeSize; const uint32_t* pCode; } VkShaderModuleCreateInfo;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; uint32_t setLayoutCount; const VkDescriptorSetLayout* pSetLayouts; uint32_t pushConstantRangeCount; const void* pPushConstantRanges; } VkPipelineLayoutCreateInfo;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; uint32_t stage; VkShaderModule module; const char* pName; const void* pSpecializationInfo; } VkPipelineShaderStageCreateInfo;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; VkPipelineShaderStageCreateInfo stage; VkPipelineLayout layout; VkPipeline basePipelineHandle; int32_t basePipelineIndex; } VkComputePipelineCreateInfo;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; uint32_t queueFamilyIndex; } VkCommandPoolCreateInfo;
typedef struct { uint32_t sType; const void* pNext; VkCommandPool commandPool; uint32_t level; uint32_t commandBufferCount; } VkCommandBufferAllocateInfo;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; const void* pInheritanceInfo; } VkCommandBufferBeginInfo;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; } VkFenceCreateInfo;
typedef struct { uint32_t sType; const void* pNext; uint32_t waitSemaphoreCount; const void* pWaitSemaphores; const void* pWaitDstStageMask; uint32_t commandBufferCount; const VkCommandBuffer* pCommandBuffers; uint32_t signalSemaphoreCount; const void* pSignalSemaphores; } VkSubmitInfo;

typedef void* (*PFN_vkGetInstanceProcAddr)(VkInstance, const char*);
typedef void* (*PFN_vkGetDeviceProcAddr)(VkDevice, const char*);
typedef VkResult (*PFN_vkCreateInstance)(const VkInstanceCreateInfo*, const void*, VkInstance*);
typedef void (*PFN_vkDestroyInstance)(VkInstance, const void*);
typedef VkResult (*PFN_vkEnumeratePhysicalDevices)(VkInstance, uint32_t*, VkPhysicalDevice*);
typedef void (*PFN_vkGetPhysicalDeviceQueueFamilyProperties)(VkPhysicalDevice, uint32_t*, VkQueueFamilyProperties*);
typedef void (*PFN_vkGetPhysicalDeviceMemoryProperties)(VkPhysicalDevice, VkPhysicalDeviceMemoryProperties*);
typedef void (*PFN_vkGetPhysicalDeviceFeatures)(VkPhysicalDevice, VkPhysicalDeviceFeatures*);
typedef VkResult (*PFN_vkCreateDevice)(VkPhysicalDevice, const VkDeviceCreateInfo*, const void*, VkDevice*);
typedef void (*PFN_vkDestroyDevice)(VkDevice, const void*);
typedef void (*PFN_vkGetDeviceQueue)(VkDevice, uint32_t, uint32_t, VkQueue*);
typedef VkResult (*PFN_vkCreateBuffer)(VkDevice, const VkBufferCreateInfo*, const void*, VkBuffer*);
typedef void (*PFN_vkDestroyBuffer)(VkDevice, VkBuffer, const void*);
typedef void (*PFN_vkGetBufferMemoryRequirements)(VkDevice, VkBuffer, VkMemoryRequirements*);
typedef VkResult (*PFN_vkCreateImage)(VkDevice, const VkImageCreateInfo*, const void*, VkImage*);
typedef void (*PFN_vkDestroyImage)(VkDevice, VkImage, const void*);
typedef void (*PFN_vkGetImageMemoryRequirements)(VkDevice, VkImage, VkMemoryRequirements*);
typedef void (*PFN_vkGetImageSparseMemoryRequirements)(VkDevice, VkImage, uint32_t*, VkSparseImageMemoryRequirements*);
typedef VkResult (*PFN_vkBindImageMemory)(VkDevice, VkImage, VkDeviceMemory, VkDeviceSize);
typedef VkResult (*PFN_vkCreateImageView)(VkDevice, const VkImageViewCreateInfo*, const void*, VkImageView*);
typedef void (*PFN_vkDestroyImageView)(VkDevice, VkImageView, const void*);
typedef VkResult (*PFN_vkCreateSampler)(VkDevice, const VkSamplerCreateInfo*, const void*, VkSampler*);
typedef void (*PFN_vkDestroySampler)(VkDevice, VkSampler, const void*);
typedef VkResult (*PFN_vkAllocateMemory)(VkDevice, const VkMemoryAllocateInfo*, const void*, VkDeviceMemory*);
typedef void (*PFN_vkFreeMemory)(VkDevice, VkDeviceMemory, const void*);
typedef VkResult (*PFN_vkBindBufferMemory)(VkDevice, VkBuffer, VkDeviceMemory, VkDeviceSize);
typedef VkResult (*PFN_vkMapMemory)(VkDevice, VkDeviceMemory, VkDeviceSize, VkDeviceSize, VkFlags, void**);
typedef void (*PFN_vkUnmapMemory)(VkDevice, VkDeviceMemory);
typedef VkResult (*PFN_vkCreateDescriptorSetLayout)(VkDevice, const VkDescriptorSetLayoutCreateInfo*, const void*, VkDescriptorSetLayout*);
typedef void (*PFN_vkDestroyDescriptorSetLayout)(VkDevice, VkDescriptorSetLayout, const void*);
typedef VkResult (*PFN_vkCreateDescriptorPool)(VkDevice, const VkDescriptorPoolCreateInfo*, const void*, VkDescriptorPool*);
typedef void (*PFN_vkDestroyDescriptorPool)(VkDevice, VkDescriptorPool, const void*);
typedef VkResult (*PFN_vkAllocateDescriptorSets)(VkDevice, const VkDescriptorSetAllocateInfo*, VkDescriptorSet*);
typedef void (*PFN_vkUpdateDescriptorSets)(VkDevice, uint32_t, const VkWriteDescriptorSet*, uint32_t, const void*);
typedef tvdb_status_t (*PFN_vkFreeDescriptorSets)(VkDevice, VkDescriptorPool, uint32_t, const VkDescriptorSet*);
typedef VkResult (*PFN_vkCreateShaderModule)(VkDevice, const VkShaderModuleCreateInfo*, const void*, VkShaderModule*);
typedef void (*PFN_vkDestroyShaderModule)(VkDevice, VkShaderModule, const void*);
typedef VkResult (*PFN_vkCreatePipelineLayout)(VkDevice, const VkPipelineLayoutCreateInfo*, const void*, VkPipelineLayout*);
typedef void (*PFN_vkDestroyPipelineLayout)(VkDevice, VkPipelineLayout, const void*);
typedef VkResult (*PFN_vkCreateComputePipelines)(VkDevice, VkPipeline, uint32_t, const VkComputePipelineCreateInfo*, const void*, VkPipeline*);
typedef void (*PFN_vkDestroyPipeline)(VkDevice, VkPipeline, const void*);
typedef VkResult (*PFN_vkCreateCommandPool)(VkDevice, const VkCommandPoolCreateInfo*, const void*, VkCommandPool*);
typedef void (*PFN_vkDestroyCommandPool)(VkDevice, VkCommandPool, const void*);
typedef VkResult (*PFN_vkAllocateCommandBuffers)(VkDevice, const VkCommandBufferAllocateInfo*, VkCommandBuffer*);
typedef VkResult (*PFN_vkBeginCommandBuffer)(VkCommandBuffer, const VkCommandBufferBeginInfo*);
typedef VkResult (*PFN_vkEndCommandBuffer)(VkCommandBuffer);
typedef VkResult (*PFN_vkResetCommandBuffer)(VkCommandBuffer, VkFlags);
typedef void (*PFN_vkCmdBindPipeline)(VkCommandBuffer, uint32_t, VkPipeline);
typedef void (*PFN_vkCmdBindDescriptorSets)(VkCommandBuffer, uint32_t, VkPipelineLayout, uint32_t, uint32_t, const VkDescriptorSet*, uint32_t, const uint32_t*);
typedef void (*PFN_vkCmdDispatch)(VkCommandBuffer, uint32_t, uint32_t, uint32_t);
typedef void (*PFN_vkCmdPipelineBarrier)(VkCommandBuffer, VkFlags, VkFlags, VkFlags, uint32_t, const void*, uint32_t, const void*, uint32_t, const void*);
typedef void (*PFN_vkCmdCopyBufferToImage)(VkCommandBuffer, VkBuffer, VkImage, uint32_t, uint32_t, const VkBufferImageCopy*);
typedef void (*PFN_vkCmdCopyBuffer)(VkCommandBuffer, VkBuffer, VkBuffer, uint32_t, const VkBufferCopy*);
typedef tvdb_status_t (*PFN_vkFreeCommandBuffers)(VkDevice, VkCommandPool, uint32_t, const VkCommandBuffer*);
typedef VkResult (*PFN_vkEnumerateDeviceExtensionProperties)(VkPhysicalDevice, const char*, uint32_t*, VkExtensionProperties*);
typedef VkResult (*PFN_vkGetMemoryFdKHR)(VkDevice, const VkMemoryGetFdInfoKHR*, int*);
typedef VkResult (*PFN_vkCreateFence)(VkDevice, const VkFenceCreateInfo*, const void*, VkFence*);
typedef void (*PFN_vkDestroyFence)(VkDevice, VkFence, const void*);
typedef VkResult (*PFN_vkResetFences)(VkDevice, uint32_t, const VkFence*);
typedef VkResult (*PFN_vkGetFenceStatus)(VkDevice, VkFence);
typedef VkResult (*PFN_vkWaitForFences)(VkDevice, uint32_t, const VkFence*, VkBool32, uint64_t);
typedef VkResult (*PFN_vkQueueSubmit)(VkQueue, uint32_t, const VkSubmitInfo*, VkFence);
typedef VkResult (*PFN_vkQueueBindSparse)(VkQueue, uint32_t, const VkBindSparseInfo*, VkFence);
typedef VkResult (*PFN_vkDeviceWaitIdle)(VkDevice);

typedef struct {
  void* lib;
  PFN_vkGetInstanceProcAddr GetInstanceProcAddr;
  PFN_vkGetDeviceProcAddr GetDeviceProcAddr;
  PFN_vkCreateInstance CreateInstance;
  PFN_vkDestroyInstance DestroyInstance;
  PFN_vkEnumeratePhysicalDevices EnumeratePhysicalDevices;
  PFN_vkGetPhysicalDeviceQueueFamilyProperties GetPhysicalDeviceQueueFamilyProperties;
  PFN_vkGetPhysicalDeviceMemoryProperties GetPhysicalDeviceMemoryProperties;
  PFN_vkGetPhysicalDeviceFeatures GetPhysicalDeviceFeatures;
  PFN_vkCreateDevice CreateDevice;
  PFN_vkDestroyDevice DestroyDevice;
  PFN_vkGetDeviceQueue GetDeviceQueue;
  PFN_vkCreateBuffer CreateBuffer;
  PFN_vkDestroyBuffer DestroyBuffer;
  PFN_vkGetBufferMemoryRequirements GetBufferMemoryRequirements;
  PFN_vkCreateImage CreateImage;
  PFN_vkDestroyImage DestroyImage;
  PFN_vkGetImageMemoryRequirements GetImageMemoryRequirements;
  PFN_vkGetImageSparseMemoryRequirements GetImageSparseMemoryRequirements;
  PFN_vkBindImageMemory BindImageMemory;
  PFN_vkCreateImageView CreateImageView;
  PFN_vkDestroyImageView DestroyImageView;
  PFN_vkCreateSampler CreateSampler;
  PFN_vkDestroySampler DestroySampler;
  PFN_vkAllocateMemory AllocateMemory;
  PFN_vkFreeMemory FreeMemory;
  PFN_vkBindBufferMemory BindBufferMemory;
  PFN_vkMapMemory MapMemory;
  PFN_vkUnmapMemory UnmapMemory;
  PFN_vkCreateDescriptorSetLayout CreateDescriptorSetLayout;
  PFN_vkDestroyDescriptorSetLayout DestroyDescriptorSetLayout;
  PFN_vkCreateDescriptorPool CreateDescriptorPool;
  PFN_vkDestroyDescriptorPool DestroyDescriptorPool;
  PFN_vkAllocateDescriptorSets AllocateDescriptorSets;
  PFN_vkUpdateDescriptorSets UpdateDescriptorSets;
  PFN_vkFreeDescriptorSets FreeDescriptorSets;
  PFN_vkCreateShaderModule CreateShaderModule;
  PFN_vkDestroyShaderModule DestroyShaderModule;
  PFN_vkCreatePipelineLayout CreatePipelineLayout;
  PFN_vkDestroyPipelineLayout DestroyPipelineLayout;
  PFN_vkCreateComputePipelines CreateComputePipelines;
  PFN_vkDestroyPipeline DestroyPipeline;
  PFN_vkCreateCommandPool CreateCommandPool;
  PFN_vkDestroyCommandPool DestroyCommandPool;
  PFN_vkAllocateCommandBuffers AllocateCommandBuffers;
  PFN_vkBeginCommandBuffer BeginCommandBuffer;
  PFN_vkEndCommandBuffer EndCommandBuffer;
  PFN_vkResetCommandBuffer ResetCommandBuffer;
  PFN_vkCmdBindPipeline CmdBindPipeline;
  PFN_vkCmdBindDescriptorSets CmdBindDescriptorSets;
  PFN_vkCmdDispatch CmdDispatch;
  PFN_vkCmdPipelineBarrier CmdPipelineBarrier;
  PFN_vkCmdCopyBufferToImage CmdCopyBufferToImage;
  PFN_vkCmdCopyBuffer CmdCopyBuffer;
  PFN_vkFreeCommandBuffers FreeCommandBuffers;
  PFN_vkEnumerateDeviceExtensionProperties EnumerateDeviceExtensionProperties;
  PFN_vkGetMemoryFdKHR GetMemoryFdKHR;
  PFN_vkCreateFence CreateFence;
  PFN_vkDestroyFence DestroyFence;
  PFN_vkResetFences ResetFences;
  PFN_vkGetFenceStatus GetFenceStatus;
  PFN_vkWaitForFences WaitForFences;
  PFN_vkQueueSubmit QueueSubmit;
  PFN_vkQueueBindSparse QueueBindSparse;
  PFN_vkDeviceWaitIdle DeviceWaitIdle;
} tvdb_vk_table;

typedef struct {
  VkBuffer buffer;
  VkDeviceMemory memory;
  VkDeviceSize size;
  void* mapped;
} tvdb_vk_buffer;

typedef struct {
  VkImage image;
  VkDeviceMemory memory;
  VkImageView view;
  VkSampler sampler;
  uint32_t nx, ny, nz;
} tvdb_vk_image3d;

typedef struct {
  uint32_t x, y, z;
  VkOffset3D offset;
  VkExtent3D extent;
} tvdb_vk_sparse_page_region;

typedef struct {
  void* libcuda;
  void* libnvrtc;
  CUresult (*cuInit)(unsigned int);
  CUresult (*cuDeviceGetCount)(int*);
  CUresult (*cuDeviceGet)(CUdevice*, int);
  CUresult (*cuDeviceGetName)(char*, int, CUdevice);
  CUresult (*cuDeviceGetUuid)(uint8_t*, CUdevice);  // optional; CUuuid is 16 bytes
  CUresult (*cuCtxCreate)(CUcontext*, unsigned int, CUdevice);
  CUresult (*cuCtxDestroy)(CUcontext);
  CUresult (*cuCtxSynchronize)(void);
  CUresult (*cuMemAlloc)(CUdeviceptr*, size_t);
  CUresult (*cuMemFree)(CUdeviceptr);
  CUresult (*cuMemcpyHtoD)(CUdeviceptr, const void*, size_t);
  CUresult (*cuMemcpyDtoH)(void*, CUdeviceptr, size_t);
  CUresult (*cuMemsetD32)(CUdeviceptr, unsigned int, size_t);
  CUresult (*cuModuleLoadData)(CUmodule*, const void*);
  CUresult (*cuModuleUnload)(CUmodule);
  CUresult (*cuModuleGetFunction)(CUfunction*, CUmodule, const char*);
  CUresult (*cuLaunchKernel)(CUfunction, unsigned int, unsigned int, unsigned int,
                             unsigned int, unsigned int, unsigned int,
                             unsigned int, void*, void**, void**);
  CUresult (*cuGetErrorString)(CUresult, const char**);
  CUresult (*cuImportExternalMemory)(CUexternalMemory*, const CUDA_EXTERNAL_MEMORY_HANDLE_DESC*);
  CUresult (*cuExternalMemoryGetMappedBuffer)(CUdeviceptr*, CUexternalMemory, const CUDA_EXTERNAL_MEMORY_BUFFER_DESC*);
  CUresult (*cuDestroyExternalMemory)(CUexternalMemory);
  nvrtcResult (*nvrtcCreateProgram)(nvrtcProgram*, const char*, const char*, int,
                                    const char* const*, const char* const*);
  nvrtcResult (*nvrtcCompileProgram)(nvrtcProgram, int, const char* const*);
  nvrtcResult (*nvrtcGetPTXSize)(nvrtcProgram, size_t*);
  nvrtcResult (*nvrtcGetPTX)(nvrtcProgram, char*);
  nvrtcResult (*nvrtcGetProgramLogSize)(nvrtcProgram, size_t*);
  nvrtcResult (*nvrtcGetProgramLog)(nvrtcProgram, char*);
  nvrtcResult (*nvrtcDestroyProgram)(nvrtcProgram*);
  const char* (*nvrtcGetErrorString)(nvrtcResult);
} tvdb_cuda_table;

/* Cached compute pipeline objects, keyed on the SPIR-V blob and the descriptor
 * shape.
 *
 * tvdb_vk_dispatch used to build and tear down the shader module, pipeline
 * layout, descriptor-set layout, pipeline and descriptor pool on every single
 * call -- 28 create/destroy calls. Measured fixed cost of that churn: a
 * trivial 8^3 primitive took 2.075 ms wall, essentially all of it overhead
 * (a 64^3 one took 36.4 ms, so ~2 ms of every op is setup, not work).
 *
 * Only the pipeline-side objects are cached. Descriptor *sets* must still be
 * written per dispatch because the bound buffers differ, but
 * UpdateDescriptorSets is cheap. Nothing here adds new Vulkan ABI, which
 * matters: the device-local-buffer approach in the same area proved far
 * riskier than it looked. */
/* Per-dispatch descriptor bindings. This bound is load-bearing: the cache entry
 * below, the descriptor-set binding arrays and the dispatch descriptor all size
 * themselves from it, and a dispatch that exceeded it silently overwrote the
 * entry's shader handle (7 descriptors overflowed descriptor_types[6] by one
 * uint32 and corrupted the adjacent VkShaderModule, which surfaced as a driver
 * segfault rather than a clean error). */
#define TVDB_VK_MAX_DESCRIPTORS 8

/* In-flight deferred submissions per context. A batch larger than this drains the
 * oldest first, so memory stays bounded. */
#define TVDB_VK_PENDING_MAX 64

/* Grid size at which hoisting the transfer to a device-local working set beats
 * the two extra full-buffer copies. See the measurement table at the use site. */
#define TVDB_VK_DEVICE_STAGING_MIN_VOXELS ((size_t)131072)

typedef struct {
  const uint8_t *spv;
  uint32_t spv_len;
  uint32_t descriptor_count;
  uint32_t descriptor_types[TVDB_VK_MAX_DESCRIPTORS];
  VkShaderModule shader;
  VkDescriptorSetLayout set_layout;
  VkPipelineLayout pipeline_layout;
  VkPipeline pipeline;
} tvdb_vk_pipeline_entry;

#define TVDB_VK_PIPELINE_CACHE_MAX 128

/* Below this active count the hash map loses to a plain linear scan: the map
 * build and the extra keys/values buffers cost more than a short scan saves.
 * Measured crossover on RTX 5060 Ti, nq=65536 (linear -> hash):
 *   na=512  5.94 -> 7.35 ms (0.81x)
 *   na=4096 13.68 -> 8.10 ms (1.69x)
 *   na=32768 34.49 -> 9.92 ms (3.48x)
 *   na=262144 175.62 -> 45.73 ms (3.84x)
 */
#ifndef TVDB_INDEX_MAP_MIN_ACTIVE
#define TVDB_INDEX_MAP_MIN_ACTIVE 2048u
#endif
#ifndef TVDB_INDEX_MAP_FORCE_LINEAR
#define TVDB_INDEX_MAP_FORCE_LINEAR 0
#endif

/* Queue a kernel chain and wait once instead of waiting per dispatch. Only sound
 * when the host touches no mapped buffer between the dispatches it defers: a
 * chain that reads a counter off a mapped buffer to decide whether to iterate
 * again (signed flood fill) must not defer. Set to 0 to force a wait per
 * dispatch, which is how the deferred paths were A/B measured. */
/* Upper bound on the voxels one mesh_to_sdf dispatch may cover. The kernel is
 * O(voxels * faces), so a single dispatch over a 199^3 grid is millions of
 * threads each scanning every triangle -- long enough that the driver's watchdog
 * kills the context and the call comes back as VK_ERROR_DEVICE_LOST. Chunking z
 * into slabs keeps each dispatch short. 1M voxels x 32 faces is comfortably
 * inside a frame; raising it trades TDR margin for fewer launches. */
#ifndef TVDB_MESH_SDF_MAX_VOXELS_PER_DISPATCH
#define TVDB_MESH_SDF_MAX_VOXELS_PER_DISPATCH ((size_t)1048576)
#endif

#ifndef TVDB_VK_DEFERRED_SUBMIT
#define TVDB_VK_DEFERRED_SUBMIT 1
#endif

#define TVDB_GPU_DEFER_MAX 8
typedef struct {
  tvdb_vk_buffer bufs[6];
  unsigned int nbufs;
  void* host[6];
  size_t bytes[6];
  unsigned int nout;
  unsigned int output_binding[6];
} tvdb_gpu_deferred;

struct tvdb_gpu_context {
  tvdb_gpu_deferred deferred[TVDB_GPU_DEFER_MAX];
  unsigned int deferred_count;
  tvdb_gpu_backend_t backend;
  tvdb_gpu_resident_metrics_t resident_metrics;
  tvdb_vk_table vk;
  VkInstance instance;
  VkPhysicalDevice physical_device;
  VkDevice device;
  VkQueue queue;
  uint32_t queue_family;
  VkPhysicalDeviceMemoryProperties memory_props;
  int supports_sparse_3d_images;
  int supports_shader_float64;   // VkPhysicalDeviceFeatures.shaderFloat64
  int supports_sparse_aliased;   // sparseResidencyAliased: legal sparse memory aliasing
  int supports_external_memory;
  char device_name[128];
  uint8_t device_uuid[16];  // physical-device identity shared by Vulkan and CUDA
  int has_device_uuid;
  tvdb_vk_pipeline_entry pipeline_cache[TVDB_VK_PIPELINE_CACHE_MAX];
  uint32_t pipeline_cache_count;
  /* Reused across dispatches. Creating and destroying a descriptor pool and a
   * command pool per call was measured at 43% and 13% of the fixed per-op cost
   * on a trivial kernel (41.8 ms and 13.0 ms over 23 calls, against ~57 ms of
   * wall time). One generous pool of each kind per context removes that. */
  VkDescriptorPool desc_pool;
  VkCommandPool cmd_pool;
  /* Deferred submissions. A dispatch with defer_wait set returns as soon as the
   * work is queued; its fence and command buffer are parked here and drained by
   * the next non-deferred dispatch or by tvdb_vk_flush. This is what makes a
   * batch of many small dispatches (an iterative solver, a wavefront sweep) cost
   * one wait instead of one per dispatch.
   *
   * A bounded ring, not a single slot: a batch defers many dispatches before it
   * drains, and a single slot silently orphaned every earlier fence and command
   * buffer -- measured at ~0.4 MB of RSS per batch, caught by the lifetime gate
   * once mean curvature flow started deferring 4 dispatches in a row. When the
   * ring is full the oldest batch is drained, which bounds memory without
   * changing the one-wait-per-batch property. */
  VkFence pending_fence[TVDB_VK_PENDING_MAX];
  VkCommandBuffer pending_cmd[TVDB_VK_PENDING_MAX];
  VkDescriptorSet pending_set[TVDB_VK_PENDING_MAX];
  uint32_t pending_count;
  tvdb_cuda_table cuda;
  CUcontext cu_ctx;
  CUdevice cu_device;
  CUmodule cu_module;
};
struct tvdb_gpu_buffer { tvdb_vk_buffer vk; tvdb_gpu_context_t* ctx; tvdb_gpu_backend_t backend; CUdeviceptr cu; size_t size;
                         CUexternalMemory ext_mem; int imported; int resident; };
struct tvdb_gpu_dense_grid { tvdb_gpu_context_t* ctx; tvdb_gpu_buffer_t *values, *scratch[3]; tvdb_gpu_grid_desc_t desc; size_t bytes, count; };
typedef struct {
  size_t refs, count;
  uint32_t capacity;
  tvdb_gpu_buffer_t *coords, *map;
} tvdb_resident_topology;
struct tvdb_gpu_sparse_grid {
  tvdb_gpu_context_t* ctx;
  tvdb_resident_topology* topology;
  tvdb_gpu_buffer_t* values;
  float ox,oy,oz,voxel_size;
};
struct tvdb_gpu_vulkan_sparse_image3d {
  tvdb_gpu_context_t* ctx;
  tvdb_vk_image3d image;
  float ox, oy, oz, voxel_size;
  int nx, ny, nz;
  VkDescriptorSetLayout sample_layout;
  VkDescriptorPool sample_pool;
  VkDescriptorSet sample_set;
  VkPipelineLayout sample_pipeline_layout;
  VkPipeline sample_pipeline;
  VkCommandPool sample_command_pool;
  VkCommandBuffer sample_cmd;
  VkFence sample_fence;
  int sample_cmd_recorded;
  int sample_in_flight;
  tvdb_vk_buffer sample_points;
  tvdb_vk_buffer sample_output;
  tvdb_vk_buffer sample_params;
  size_t sample_capacity;
  int sample_descriptors_bound;
  uint32_t sample_group_x;
  VkBuffer sample_bound_points;
  VkBuffer sample_bound_output;
  VkBuffer sample_bound_params;
};
struct tvdb_gpu_vulkan_sample_batch {
  tvdb_gpu_context_t* ctx;
  tvdb_vk_buffer points;
  tvdb_vk_buffer output;
  tvdb_vk_buffer params;
  size_t count;
  size_t capacity;
  VkDescriptorPool descriptor_pool;
  VkDescriptorSet descriptor_set;
  VkCommandPool command_pool;
  VkCommandBuffer cmd;
  VkFence fence;
  const tvdb_gpu_vulkan_sparse_image3d_t* bound_image;
  uint32_t group_x;
  int cmd_recorded;
  int in_flight;
};

static void tvdb_gpu_set_error(tvdb_error_t* err, tvdb_status_t st, const char* msg) {
  if (!err) return;
  err->status = st;
  err->byte_offset = 0;
  err->grid_index = -1;
  if (msg) {
    snprintf(err->message, sizeof(err->message), "%s", msg);
  } else {
    err->message[0] = '\0';
  }
}

static void* tvdb_dyn_open(const char* name) {
#if defined(_WIN32)
  return (void*)LoadLibraryA(name);
#else
  return dlopen(name, RTLD_NOW | RTLD_LOCAL);
#endif
}

static void* tvdb_dyn_sym(void* lib, const char* name) {
#if defined(_WIN32)
  return (void*)GetProcAddress((HMODULE)lib, name);
#else
  return dlsym(lib, name);
#endif
}

static void tvdb_dyn_close(void* lib) {
  if (!lib) return;
#if defined(_WIN32)
  FreeLibrary((HMODULE)lib);
#else
  dlclose(lib);
#endif
}

static void* tvdb_load_first_library(const char* const* names, size_t count) {
  for (size_t i = 0; i < count; ++i) {
    void* lib = tvdb_dyn_open(names[i]);
    if (lib) return lib;
  }
  return NULL;
}

static void* tvdb_load_vulkan_library(tvdb_vk_table* vk) {
#if defined(_WIN32)
  const char* names[] = {"vulkan-1.dll"};
#elif defined(__APPLE__)
  const char* names[] = {"libvulkan.1.dylib", "libvulkan.dylib"};
#else
  const char* names[] = {"libvulkan.so.1", "libvulkan.so"};
#endif
  for (size_t i = 0; i < sizeof(names) / sizeof(names[0]); ++i) {
    void* lib = tvdb_dyn_open(names[i]);
    if (!lib) continue;
    vk->GetInstanceProcAddr = (PFN_vkGetInstanceProcAddr)tvdb_dyn_sym(lib, "vkGetInstanceProcAddr");
    vk->CreateInstance = (PFN_vkCreateInstance)tvdb_dyn_sym(lib, "vkCreateInstance");
    if (vk->GetInstanceProcAddr && vk->CreateInstance) {
      vk->lib = lib;
      return lib;
    }
    tvdb_dyn_close(lib);
  }
  return NULL;
}

static int tvdb_load_cuda_library(tvdb_cuda_table* cu) {
#if defined(_WIN32)
  const char* cuda_names[] = {"nvcuda.dll"};
  const char* nvrtc_names[] = {"nvrtc64_130_0.dll", "nvrtc64_120_0.dll", "nvrtc64_112_0.dll", "nvrtc64_102_0.dll"};
#elif defined(__APPLE__)
  const char* cuda_names[] = {"libcuda.dylib"};
  const char* nvrtc_names[] = {"libnvrtc.dylib"};
#else
  const char* cuda_names[] = {"libcuda.so.1", "libcuda.so"};
  const char* nvrtc_names[] = {"libnvrtc.so.13", "libnvrtc.so.12", "libnvrtc.so.11.2", "libnvrtc.so"};
#endif
  cu->libcuda = tvdb_load_first_library(cuda_names, sizeof(cuda_names) / sizeof(cuda_names[0]));
  if (!cu->libcuda) return 0;
  cu->libnvrtc = tvdb_load_first_library(nvrtc_names, sizeof(nvrtc_names) / sizeof(nvrtc_names[0]));
  if (!cu->libnvrtc) {
    tvdb_dyn_close(cu->libcuda);
    memset(cu, 0, sizeof(*cu));
    return 0;
  }
#define TVDB_CUDA_SYM(field, name) do { \
  cu->field = (void*)tvdb_dyn_sym(cu->libcuda, name); \
  if (!cu->field) goto fail; \
} while (0)
#define TVDB_NVRTC_SYM(field, name) do { \
  cu->field = (void*)tvdb_dyn_sym(cu->libnvrtc, name); \
  if (!cu->field) goto fail; \
} while (0)
  TVDB_CUDA_SYM(cuInit, "cuInit");
  TVDB_CUDA_SYM(cuDeviceGetCount, "cuDeviceGetCount");
  TVDB_CUDA_SYM(cuDeviceGet, "cuDeviceGet");
  TVDB_CUDA_SYM(cuDeviceGetName, "cuDeviceGetName");
  TVDB_CUDA_SYM(cuCtxCreate, "cuCtxCreate_v2");
  TVDB_CUDA_SYM(cuCtxDestroy, "cuCtxDestroy_v2");
  TVDB_CUDA_SYM(cuCtxSynchronize, "cuCtxSynchronize");
  TVDB_CUDA_SYM(cuMemAlloc, "cuMemAlloc_v2");
  TVDB_CUDA_SYM(cuMemFree, "cuMemFree_v2");
  TVDB_CUDA_SYM(cuMemcpyHtoD, "cuMemcpyHtoD_v2");
  TVDB_CUDA_SYM(cuMemcpyDtoH, "cuMemcpyDtoH_v2");
  TVDB_CUDA_SYM(cuMemsetD32, "cuMemsetD32_v2");
  TVDB_CUDA_SYM(cuModuleLoadData, "cuModuleLoadData");
  TVDB_CUDA_SYM(cuModuleUnload, "cuModuleUnload");
  TVDB_CUDA_SYM(cuModuleGetFunction, "cuModuleGetFunction");
  TVDB_CUDA_SYM(cuLaunchKernel, "cuLaunchKernel");
  cu->cuGetErrorString = (void*)tvdb_dyn_sym(cu->libcuda, "cuGetErrorString");
  cu->cuDeviceGetUuid = (void*)tvdb_dyn_sym(cu->libcuda, "cuDeviceGetUuid");
  // External-memory interop (optional; absent on very old drivers).
  cu->cuImportExternalMemory = (void*)tvdb_dyn_sym(cu->libcuda, "cuImportExternalMemory");
  cu->cuExternalMemoryGetMappedBuffer = (void*)tvdb_dyn_sym(cu->libcuda, "cuExternalMemoryGetMappedBuffer");
  cu->cuDestroyExternalMemory = (void*)tvdb_dyn_sym(cu->libcuda, "cuDestroyExternalMemory");
  TVDB_NVRTC_SYM(nvrtcCreateProgram, "nvrtcCreateProgram");
  TVDB_NVRTC_SYM(nvrtcCompileProgram, "nvrtcCompileProgram");
  TVDB_NVRTC_SYM(nvrtcGetPTXSize, "nvrtcGetPTXSize");
  TVDB_NVRTC_SYM(nvrtcGetPTX, "nvrtcGetPTX");
  TVDB_NVRTC_SYM(nvrtcGetProgramLogSize, "nvrtcGetProgramLogSize");
  TVDB_NVRTC_SYM(nvrtcGetProgramLog, "nvrtcGetProgramLog");
  TVDB_NVRTC_SYM(nvrtcDestroyProgram, "nvrtcDestroyProgram");
  cu->nvrtcGetErrorString = (void*)tvdb_dyn_sym(cu->libnvrtc, "nvrtcGetErrorString");
#undef TVDB_CUDA_SYM
#undef TVDB_NVRTC_SYM
  return 1;
fail:
  tvdb_dyn_close(cu->libnvrtc);
  tvdb_dyn_close(cu->libcuda);
  memset(cu, 0, sizeof(*cu));
  return 0;
}

static int tvdb_vk_ok(VkResult r, tvdb_error_t* err, const char* label) {
  if (r == VK_SUCCESS) return 1;
  char msg[160];
  snprintf(msg, sizeof(msg), "%s failed: %d", label, (int)r);
  tvdb_gpu_set_error(err, TVDB_ERROR_IO, msg);
  return 0;
}

#define TVDB_LOAD_INST(ctx, name) do { \
  (ctx)->vk.name = (PFN_vk##name)(ctx)->vk.GetInstanceProcAddr((ctx)->instance, "vk" #name); \
  if (!(ctx)->vk.name) { tvdb_gpu_set_error(err, TVDB_ERROR_IO, "missing Vulkan instance function: vk" #name); return TVDB_ERROR_IO; } \
} while (0)

#define TVDB_LOAD_DEV(ctx, name) do { \
  (ctx)->vk.name = (PFN_vk##name)(ctx)->vk.GetDeviceProcAddr((ctx)->device, "vk" #name); \
  if (!(ctx)->vk.name) { tvdb_gpu_set_error(err, TVDB_ERROR_IO, "missing Vulkan device function: vk" #name); return TVDB_ERROR_IO; } \
} while (0)

static tvdb_status_t tvdb_vk_load_instance_functions(tvdb_gpu_context_t* ctx, tvdb_error_t* err) {
  TVDB_LOAD_INST(ctx, DestroyInstance);
  TVDB_LOAD_INST(ctx, EnumeratePhysicalDevices);
  TVDB_LOAD_INST(ctx, GetPhysicalDeviceQueueFamilyProperties);
  TVDB_LOAD_INST(ctx, GetPhysicalDeviceMemoryProperties);
  TVDB_LOAD_INST(ctx, GetPhysicalDeviceFeatures);
  TVDB_LOAD_INST(ctx, EnumerateDeviceExtensionProperties);
  TVDB_LOAD_INST(ctx, CreateDevice);
  ctx->vk.GetDeviceProcAddr = (PFN_vkGetDeviceProcAddr)ctx->vk.GetInstanceProcAddr(ctx->instance, "vkGetDeviceProcAddr");
  if (!ctx->vk.GetDeviceProcAddr) {
    tvdb_gpu_set_error(err, TVDB_ERROR_IO, "missing Vulkan instance function: vkGetDeviceProcAddr");
    return TVDB_ERROR_IO;
  }
  return TVDB_OK;
}

static tvdb_status_t tvdb_vk_load_device_functions(tvdb_gpu_context_t* ctx, tvdb_error_t* err) {
  TVDB_LOAD_DEV(ctx, DestroyDevice); TVDB_LOAD_DEV(ctx, GetDeviceQueue);
  TVDB_LOAD_DEV(ctx, CreateBuffer); TVDB_LOAD_DEV(ctx, DestroyBuffer);
  TVDB_LOAD_DEV(ctx, GetBufferMemoryRequirements);
  TVDB_LOAD_DEV(ctx, CreateImage); TVDB_LOAD_DEV(ctx, DestroyImage);
  TVDB_LOAD_DEV(ctx, GetImageMemoryRequirements); TVDB_LOAD_DEV(ctx, GetImageSparseMemoryRequirements);
  TVDB_LOAD_DEV(ctx, BindImageMemory);
  TVDB_LOAD_DEV(ctx, CreateImageView); TVDB_LOAD_DEV(ctx, DestroyImageView);
  TVDB_LOAD_DEV(ctx, CreateSampler); TVDB_LOAD_DEV(ctx, DestroySampler);
  TVDB_LOAD_DEV(ctx, AllocateMemory);
  TVDB_LOAD_DEV(ctx, FreeMemory); TVDB_LOAD_DEV(ctx, BindBufferMemory);
  TVDB_LOAD_DEV(ctx, MapMemory); TVDB_LOAD_DEV(ctx, UnmapMemory);
  TVDB_LOAD_DEV(ctx, CreateDescriptorSetLayout); TVDB_LOAD_DEV(ctx, DestroyDescriptorSetLayout);
  TVDB_LOAD_DEV(ctx, CreateDescriptorPool); TVDB_LOAD_DEV(ctx, DestroyDescriptorPool);
  TVDB_LOAD_DEV(ctx, AllocateDescriptorSets); TVDB_LOAD_DEV(ctx, UpdateDescriptorSets); TVDB_LOAD_DEV(ctx, FreeDescriptorSets);
  TVDB_LOAD_DEV(ctx, CreateShaderModule); TVDB_LOAD_DEV(ctx, DestroyShaderModule);
  TVDB_LOAD_DEV(ctx, CreatePipelineLayout); TVDB_LOAD_DEV(ctx, DestroyPipelineLayout);
  TVDB_LOAD_DEV(ctx, CreateComputePipelines); TVDB_LOAD_DEV(ctx, DestroyPipeline);
  TVDB_LOAD_DEV(ctx, CreateCommandPool); TVDB_LOAD_DEV(ctx, DestroyCommandPool);
  TVDB_LOAD_DEV(ctx, AllocateCommandBuffers); TVDB_LOAD_DEV(ctx, BeginCommandBuffer);
  TVDB_LOAD_DEV(ctx, EndCommandBuffer); TVDB_LOAD_DEV(ctx, ResetCommandBuffer);
  TVDB_LOAD_DEV(ctx, CmdBindPipeline); TVDB_LOAD_DEV(ctx, CmdBindDescriptorSets);
  TVDB_LOAD_DEV(ctx, CmdDispatch); TVDB_LOAD_DEV(ctx, CmdPipelineBarrier);
  TVDB_LOAD_DEV(ctx, CmdCopyBufferToImage); TVDB_LOAD_DEV(ctx, CmdCopyBuffer); TVDB_LOAD_DEV(ctx, FreeCommandBuffers); TVDB_LOAD_DEV(ctx, CreateFence);
  TVDB_LOAD_DEV(ctx, DestroyFence); TVDB_LOAD_DEV(ctx, ResetFences);
  TVDB_LOAD_DEV(ctx, GetFenceStatus);
  TVDB_LOAD_DEV(ctx, WaitForFences); TVDB_LOAD_DEV(ctx, QueueSubmit);
  TVDB_LOAD_DEV(ctx, QueueBindSparse);
  TVDB_LOAD_DEV(ctx, DeviceWaitIdle);
  // Optional external-memory export function (only present when the extension
  // is enabled); non-fatal if absent.
  ctx->vk.GetMemoryFdKHR = (PFN_vkGetMemoryFdKHR)ctx->vk.GetDeviceProcAddr(ctx->device, "vkGetMemoryFdKHR");
  return TVDB_OK;
}

static uint32_t tvdb_vk_find_memory_type(const tvdb_gpu_context_t* ctx, uint32_t bits, uint32_t props) {
  for (uint32_t i = 0; i < ctx->memory_props.memoryTypeCount; ++i) {
    if ((bits & (1u << i)) && ((ctx->memory_props.memoryTypes[i].propertyFlags & props) == props)) {
      return i;
    }
  }
  return UINT32_MAX;
}

static VkDeviceSize tvdb_align_up_device_size(VkDeviceSize v, VkDeviceSize align) {
  if (align == 0) return v;
  return (v + align - 1u) / align * align;
}

static void tvdb_vk_destroy_buffer(tvdb_gpu_context_t* ctx, tvdb_vk_buffer* buf);

static tvdb_status_t tvdb_vk_create_buffer(tvdb_gpu_context_t* ctx, VkDeviceSize size,
                                           uint32_t usage, tvdb_vk_buffer* out,
                                           tvdb_error_t* err) {
  memset(out, 0, sizeof(*out));
  VkBufferCreateInfo bci;
  memset(&bci, 0, sizeof(bci));
  bci.sType = VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO;
  bci.size = size ? size : 4;
  bci.usage = usage;
  bci.sharingMode = VK_SHARING_MODE_EXCLUSIVE;
  if (!tvdb_vk_ok(ctx->vk.CreateBuffer(ctx->device, &bci, NULL, &out->buffer), err, "vkCreateBuffer")) goto failed;
  VkMemoryRequirements req;
  ctx->vk.GetBufferMemoryRequirements(ctx->device, out->buffer, &req);
  uint32_t mt = tvdb_vk_find_memory_type(ctx, req.memoryTypeBits, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT);
  if (mt == UINT32_MAX) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "no host-visible coherent Vulkan memory type");
    tvdb_vk_destroy_buffer(ctx, out);
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  VkMemoryAllocateInfo mai;
  memset(&mai, 0, sizeof(mai));
  mai.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
  mai.allocationSize = req.size;
  mai.memoryTypeIndex = mt;
  if (!tvdb_vk_ok(ctx->vk.AllocateMemory(ctx->device, &mai, NULL, &out->memory), err, "vkAllocateMemory")) goto failed;
  if (!tvdb_vk_ok(ctx->vk.BindBufferMemory(ctx->device, out->buffer, out->memory, 0), err, "vkBindBufferMemory")) goto failed;
  if (!tvdb_vk_ok(ctx->vk.MapMemory(ctx->device, out->memory, 0, size ? size : 4, 0, &out->mapped), err, "vkMapMemory")) goto failed;
  out->size = size ? size : 4;
  return TVDB_OK;
failed:
  tvdb_vk_destroy_buffer(ctx, out);
  return err ? err->status : TVDB_ERROR_IO;
}

static tvdb_status_t tvdb_vk_ensure_pools(tvdb_gpu_context_t* ctx, tvdb_error_t* err);

/* Create a DEVICE_LOCAL storage buffer used as a GPU-side working copy. The
 * host-visible buffer stays the CPU-facing side, so the readback idiom is
 * unchanged; the two are moved with vkCmdCopyBuffer.
 *
 * This is deliberately NOT a per-dispatch mirror. Mirroring every dispatch
 * copies in and out on each call, which measured as a regression on
 * output-bound kernels (sdf sphere 9.7 -> 11.9 ms, denseSSBO 29 -> 60 ms),
 * because there the result crosses PCIe once regardless. It pays off only when
 * the transfer can be hoisted out of a loop -- see tvdb_mcf_vk, which stages the
 * grid in once, iterates entirely in device memory, and stages out once. */
static tvdb_status_t tvdb_vk_create_device_buffer(tvdb_gpu_context_t* ctx, size_t size, tvdb_vk_buffer* out, tvdb_error_t* err) {
  memset(out, 0, sizeof(*out));
  VkBufferCreateInfo bci;
  memset(&bci, 0, sizeof(bci));
  bci.sType = VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO;
  bci.size = size ? size : 4;
  bci.usage = VK_BUFFER_USAGE_STORAGE_BUFFER_BIT | VK_BUFFER_USAGE_TRANSFER_SRC_BIT | VK_BUFFER_USAGE_TRANSFER_DST_BIT;
  bci.sharingMode = VK_SHARING_MODE_EXCLUSIVE;
  if (!tvdb_vk_ok(ctx->vk.CreateBuffer(ctx->device, &bci, NULL, &out->buffer), err, "vkCreateBuffer(device)")) goto failed;
  VkMemoryRequirements req;
  ctx->vk.GetBufferMemoryRequirements(ctx->device, out->buffer, &req);
  uint32_t mt = tvdb_vk_find_memory_type(ctx, req.memoryTypeBits, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT);
  if (mt == UINT32_MAX) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "no device-local Vulkan memory type");
    tvdb_vk_destroy_buffer(ctx, out);
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  VkMemoryAllocateInfo mai;
  memset(&mai, 0, sizeof(mai));
  mai.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
  mai.allocationSize = req.size;
  mai.memoryTypeIndex = mt;
  if (!tvdb_vk_ok(ctx->vk.AllocateMemory(ctx->device, &mai, NULL, &out->memory), err, "vkAllocateMemory(device)")) goto failed;
  if (!tvdb_vk_ok(ctx->vk.BindBufferMemory(ctx->device, out->buffer, out->memory, 0), err, "vkBindBufferMemory(device)")) goto failed;
  out->size = size ? size : 4;
  return TVDB_OK;
failed:
  tvdb_vk_destroy_buffer(ctx, out);
  return err ? err->status : TVDB_ERROR_IO;
}

/* One full-buffer copy, with the barriers that make it actually happen.
 *
 * The source and destination sides are spelled out rather than inferred. The
 * first version guessed from the copy's index ("copy 0 is a host write, the rest
 * are compute writes"), which is right only for a caller that happens to put its
 * host write first; a caller copying three host buffers into device memory got a
 * SHADER_WRITE/COMPUTE source scope on copies 1 and 2, which does not cover the
 * transfer at all. Two callers had been quietly getting away with it because
 * their barrier was redundant anyway.
 *
 * Each copy is bracketed:
 *   pre : (src_stage, src_access) -> (TRANSFER, TRANSFER_READ) on src
 *   copy
 *   post: (TRANSFER, TRANSFER_WRITE) -> (dst_stage, dst_access) on dst
 * so dst_access is the *consumer's* access mask (SHADER_READ for a compute
 * consumer, HOST_READ for the host), which is what the post barrier has to
 * name. */
typedef struct {
  VkBuffer src, dst;
  VkDeviceSize size;
  uint32_t src_stage;      /* producer stage */
  uint32_t src_access;     /* producer access mask */
  uint32_t dst_stage;      /* consumer stage */
  uint32_t dst_access;     /* consumer access mask */
  VkDeviceSize src_offset, dst_offset;
} tvdb_vk_copy;

/* Record `n` copies into a fresh command buffer, submit and wait. Used for the
 * stage-in and stage-out of a hoisted transfer, so the whole op pays two waits
 * rather than one per iteration. */
static tvdb_status_t tvdb_vk_run_copies(tvdb_gpu_context_t* ctx, const tvdb_vk_copy* copies, uint32_t n, tvdb_error_t* err) {
  if (!ctx->vk.CmdCopyBuffer || !ctx->vk.CmdPipelineBarrier) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "device lacks vkCmdCopyBuffer");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  tvdb_status_t ps = tvdb_vk_ensure_pools(ctx, err);
  if (ps != TVDB_OK) return ps;
  VkCommandBufferAllocateInfo cbai;
  memset(&cbai, 0, sizeof(cbai));
  cbai.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
  cbai.commandPool = ctx->cmd_pool;
  cbai.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
  cbai.commandBufferCount = 1;
  VkCommandBuffer cmd = VK_NULL_HANDLE;
  if (!tvdb_vk_ok(ctx->vk.AllocateCommandBuffers(ctx->device, &cbai, &cmd), err, "vkAllocateCommandBuffers"))
    return err ? err->status : TVDB_ERROR_IO;
  VkCommandBufferBeginInfo begin;
  memset(&begin, 0, sizeof(begin));
  begin.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;
  begin.flags = VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT;
  if (!tvdb_vk_ok(ctx->vk.BeginCommandBuffer(cmd, &begin), err, "vkBeginCommandBuffer")) goto fail;
  for (uint32_t i = 0; i < n; ++i) {
    const tvdb_vk_copy* c = &copies[i];
    VkBufferMemoryBarrier b;
    /* Producer -> transfer, on the source buffer. Without this the copy can read
     * stale contents: a host write is only automatically made available to the
     * transfer stage at submit, and a shader write is not made available at all. */
    memset(&b, 0, sizeof(b));
    b.sType = VK_STRUCTURE_TYPE_BUFFER_MEMORY_BARRIER;
    b.srcAccessMask = c->src_access;
    b.dstAccessMask = VK_ACCESS_TRANSFER_READ_BIT;
    b.srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
    b.dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
    b.buffer = c->src;
    b.offset = c->src_offset;
    b.size = c->size;
    ctx->vk.CmdPipelineBarrier(cmd, c->src_stage, VK_PIPELINE_STAGE_TRANSFER_BIT, 0,
                               0, NULL, 1, &b, 0, NULL);

    VkBufferCopy bc;
    bc.srcOffset = c->src_offset; bc.dstOffset = c->dst_offset; bc.size = c->size;
    ctx->vk.CmdCopyBuffer(cmd, c->src, c->dst, 1, &bc);

    /* Transfer -> consumer, on the destination buffer. */
    memset(&b, 0, sizeof(b));
    b.sType = VK_STRUCTURE_TYPE_BUFFER_MEMORY_BARRIER;
    b.srcAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;
    b.dstAccessMask = c->dst_access;
    b.srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
    b.dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
    b.buffer = c->dst;
    b.offset = c->dst_offset;
    b.size = c->size;
    ctx->vk.CmdPipelineBarrier(cmd, VK_PIPELINE_STAGE_TRANSFER_BIT, c->dst_stage, 0,
                               0, NULL, 1, &b, 0, NULL);
  }
  if (!tvdb_vk_ok(ctx->vk.EndCommandBuffer(cmd), err, "vkEndCommandBuffer")) goto fail;
  VkFenceCreateInfo fci;
  memset(&fci, 0, sizeof(fci));
  fci.sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO;
  VkFence fence = VK_NULL_HANDLE;
  if (!tvdb_vk_ok(ctx->vk.CreateFence(ctx->device, &fci, NULL, &fence), err, "vkCreateFence")) goto fail;
  {
    VkSubmitInfo si;
    memset(&si, 0, sizeof(si));
    si.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
    si.commandBufferCount = 1;
    si.pCommandBuffers = &cmd;
    if (!tvdb_vk_ok(ctx->vk.QueueSubmit(ctx->queue, 1, &si, fence), err, "vkQueueSubmit")) { ctx->vk.DestroyFence(ctx->device, fence, NULL); goto fail; }
  }
  if (!tvdb_vk_ok(ctx->vk.WaitForFences(ctx->device, 1, &fence, VK_TRUE, UINT64_MAX), err, "vkWaitForFences")) {
    ctx->vk.DestroyFence(ctx->device, fence, NULL); goto fail;
  }
  ctx->vk.DestroyFence(ctx->device, fence, NULL);
  if (ctx->vk.FreeCommandBuffers) ctx->vk.FreeCommandBuffers(ctx->device, ctx->cmd_pool, 1, &cmd);
  return TVDB_OK;
fail:
  if (cmd && ctx->vk.FreeCommandBuffers) ctx->vk.FreeCommandBuffers(ctx->device, ctx->cmd_pool, 1, &cmd);
  return err ? err->status : TVDB_ERROR_IO;
}

static void tvdb_vk_destroy_buffer(tvdb_gpu_context_t* ctx, tvdb_vk_buffer* buf) {
  if (!ctx || !ctx->device || !buf) return;
  if (buf->mapped) ctx->vk.UnmapMemory(ctx->device, buf->memory);
  if (buf->buffer) ctx->vk.DestroyBuffer(ctx->device, buf->buffer, NULL);
  if (buf->memory) ctx->vk.FreeMemory(ctx->device, buf->memory, NULL);
  memset(buf, 0, sizeof(*buf));
}

/* Build an open-addressing map from active ijk to first-seen index.
 *
 * Replaces the brute-force O(nq*na) shader scan with O(na) construction and
 * O(nq) probing. Slots hold 3 int32 keys plus one int32 value = (index + 1),
 * with 0 marking empty. Insertion runs on the host in increasing index order,
 * so the first insert into a slot wins and first-seen semantics match the CPU
 * reference exactly -- which is also why this is not built on the GPU: a
 * parallel insert cannot make that ordering guarantee without extra atomics,
 * and the write-then-compare ordering would leave a duplicate-key race.
 */
static tvdb_status_t tvdb_index_map_build(const int32_t* active, size_t na,
                                             int32_t** out_keys, int32_t** out_vals,
                                             uint32_t* out_cap, tvdb_error_t* err) {
  /* Round up to a power of two in 64-bit, then reject anything that would not
     survive being truncated to the uint32_t the rest of this table uses. Done in
     32 bits the shift at 2^31 wraps to 0 and `0 < want` stays true forever, so an
     active set above 2^30 voxels hung the process instead of returning an error. */
  size_t want = na * 2u + 2u;
  if (na > (size_t)(UINT32_MAX / 4u) || want > (size_t)UINT32_MAX) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                       "too many active voxels for the index map (limit 2^30)");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  uint32_t cap = 16;
  while ((size_t)cap < want) cap <<= 1;   /* keep load factor <= 0.5 */
  int32_t* keys = (int32_t*)calloc((size_t)cap * 3u, sizeof(int32_t));
  int32_t* vals = (int32_t*)calloc(cap, sizeof(int32_t));
  if (!keys || !vals) {
    free(keys); free(vals);
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM building index map");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  uint32_t mask = cap - 1u;
  for (size_t i = 0; i < na; ++i) {
    int32_t ix = active[3 * i + 0], iy = active[3 * i + 1], iz = active[3 * i + 2];
    uint32_t h = ((uint32_t)ix * 73856093u) ^ ((uint32_t)iy * 19349663u) ^ ((uint32_t)iz * 83492791u);
    uint32_t slot = h & mask;
    for (uint32_t probe = 0; probe < cap; ++probe) {
      if (vals[slot] == 0) {
        keys[slot * 3u + 0u] = ix; keys[slot * 3u + 1u] = iy; keys[slot * 3u + 2u] = iz;
        vals[slot] = (int32_t)i + 1;
        break;
      }
      if (keys[slot * 3u + 0u] == ix && keys[slot * 3u + 1u] == iy && keys[slot * 3u + 2u] == iz)
        break;                                     /* duplicate: first-seen wins */
      slot = (slot + 1u) & mask;
    }
  }
  *out_keys = keys; *out_vals = vals; *out_cap = cap;
  return TVDB_OK;
}

/* Interleaved (ix, iy, iz, v) form of the map, 4 x int32 per slot with v holding
 * first_seen_index + 1 and 0 meaning "empty". Interleaving keeps a slot's key and
 * its occupancy in one cache line, and keeps both probe kernels to a single
 * indexing base. Shared by the Vulkan and CUDA sparse-conv probe paths so the two
 * cannot drift apart. */
static tvdb_status_t tvdb_index_map_build4(const tvdb_sparse_grid* g,
                                           int32_t** out_map4, uint32_t* out_cap,
                                           tvdb_error_t* err) {
  int32_t* flat = (int32_t*)malloc(g->count * 3u * sizeof(int32_t));
  if (!flat) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  for (size_t i = 0; i < g->count; ++i) {
    flat[3*i+0] = g->coords[i].x; flat[3*i+1] = g->coords[i].y; flat[3*i+2] = g->coords[i].z;
  }
  int32_t* keys = NULL; int32_t* vals = NULL; uint32_t cap = 0;
  tvdb_status_t st = tvdb_index_map_build(flat, g->count, &keys, &vals, &cap, err);
  free(flat);
  if (st != TVDB_OK) return st;
  int32_t* map4 = (int32_t*)malloc((size_t)cap * 4u * sizeof(int32_t));
  if (!map4) { free(keys); free(vals); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  for (uint32_t s = 0; s < cap; ++s) {
    map4[4*s+0] = keys[3*s+0]; map4[4*s+1] = keys[3*s+1];
    map4[4*s+2] = keys[3*s+2]; map4[4*s+3] = vals[s];
  }
  free(keys); free(vals);
  *out_map4 = map4; *out_cap = cap;
  return TVDB_OK;
}


static void tvdb_vk_destroy_image3d(tvdb_gpu_context_t* ctx, tvdb_vk_image3d* img) {
  if (!ctx || !ctx->device || !img) return;
  if (img->sampler) ctx->vk.DestroySampler(ctx->device, img->sampler, NULL);
  if (img->view) ctx->vk.DestroyImageView(ctx->device, img->view, NULL);
  if (img->image) ctx->vk.DestroyImage(ctx->device, img->image, NULL);
  if (img->memory) ctx->vk.FreeMemory(ctx->device, img->memory, NULL);
  memset(img, 0, sizeof(*img));
}

static tvdb_status_t tvdb_vk_submit_one_time(tvdb_gpu_context_t* ctx,
                                             VkCommandBuffer* out_cmd,
                                             VkCommandPool* out_pool,
                                             VkFence* out_fence,
                                             tvdb_error_t* err) {
  VkCommandPoolCreateInfo cp;
  memset(&cp, 0, sizeof(cp));
  cp.sType = VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO;
  cp.flags = VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT;
  cp.queueFamilyIndex = ctx->queue_family;
  if (!tvdb_vk_ok(ctx->vk.CreateCommandPool(ctx->device, &cp, NULL, out_pool), err, "vkCreateCommandPool")) return err ? err->status : TVDB_ERROR_IO;
  VkCommandBufferAllocateInfo cbai;
  memset(&cbai, 0, sizeof(cbai));
  cbai.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
  cbai.commandPool = *out_pool;
  cbai.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
  cbai.commandBufferCount = 1;
  if (!tvdb_vk_ok(ctx->vk.AllocateCommandBuffers(ctx->device, &cbai, out_cmd), err, "vkAllocateCommandBuffers")) return err ? err->status : TVDB_ERROR_IO;
  VkFenceCreateInfo fci;
  memset(&fci, 0, sizeof(fci));
  fci.sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO;
  if (!tvdb_vk_ok(ctx->vk.CreateFence(ctx->device, &fci, NULL, out_fence), err, "vkCreateFence")) return err ? err->status : TVDB_ERROR_IO;
  VkCommandBufferBeginInfo begin;
  memset(&begin, 0, sizeof(begin));
  begin.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;
  begin.flags = VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT;
  if (!tvdb_vk_ok(ctx->vk.BeginCommandBuffer(*out_cmd, &begin), err, "vkBeginCommandBuffer")) return err ? err->status : TVDB_ERROR_IO;
  return TVDB_OK;
}

static tvdb_status_t tvdb_vk_end_submit_wait(tvdb_gpu_context_t* ctx,
                                             VkCommandBuffer cmd,
                                             VkCommandPool pool,
                                             VkFence fence,
                                             tvdb_error_t* err) {
  if (!tvdb_vk_ok(ctx->vk.EndCommandBuffer(cmd), err, "vkEndCommandBuffer")) return err ? err->status : TVDB_ERROR_IO;
  VkSubmitInfo si;
  memset(&si, 0, sizeof(si));
  si.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
  si.commandBufferCount = 1;
  si.pCommandBuffers = &cmd;
  if (!tvdb_vk_ok(ctx->vk.QueueSubmit(ctx->queue, 1, &si, fence), err, "vkQueueSubmit")) return err ? err->status : TVDB_ERROR_IO;
  if (!tvdb_vk_ok(ctx->vk.WaitForFences(ctx->device, 1, &fence, VK_TRUE, UINT64_MAX), err, "vkWaitForFences")) return err ? err->status : TVDB_ERROR_IO;
  ctx->vk.DestroyFence(ctx->device, fence, NULL);
  ctx->vk.DestroyCommandPool(ctx->device, pool, NULL);
  return TVDB_OK;
}

static tvdb_status_t tvdb_vk_bind_sparse_image3d_all_pages(tvdb_gpu_context_t* ctx,
                                                           tvdb_vk_image3d* out,
                                                           const VkMemoryRequirements* req,
                                                           tvdb_error_t* err) {
  if (!ctx->supports_sparse_3d_images) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "Vulkan sparse 3D image residency is unavailable on this context");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  uint32_t sparse_count = 0;
  ctx->vk.GetImageSparseMemoryRequirements(ctx->device, out->image, &sparse_count, NULL);
  if (sparse_count == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "Vulkan image has no sparse memory requirements");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  VkSparseImageMemoryRequirements* sparse_reqs =
      (VkSparseImageMemoryRequirements*)calloc(sparse_count, sizeof(*sparse_reqs));
  if (!sparse_reqs) {
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  ctx->vk.GetImageSparseMemoryRequirements(ctx->device, out->image, &sparse_count, sparse_reqs);
  const VkSparseImageMemoryRequirements* sr = NULL;
  for (uint32_t i = 0; i < sparse_count; ++i) {
    if (sparse_reqs[i].formatProperties.aspectMask & VK_IMAGE_ASPECT_COLOR_BIT) {
      sr = &sparse_reqs[i];
      break;
    }
  }
  if (!sr) sr = &sparse_reqs[0];

  uint32_t mt = tvdb_vk_find_memory_type(ctx, req->memoryTypeBits, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT);
  if (mt == UINT32_MAX) mt = tvdb_vk_find_memory_type(ctx, req->memoryTypeBits, 0);
  if (mt == UINT32_MAX) {
    free(sparse_reqs);
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "no Vulkan sparse image memory type");
    return TVDB_ERROR_UNIMPLEMENTED;
  }

  VkSparseImageMemoryBindInfo image_bind_info;
  VkSparseImageOpaqueMemoryBindInfo opaque_bind_info;
  VkSparseImageMemoryBind* binds = NULL;
  VkSparseMemoryBind opaque_bind;
  memset(&image_bind_info, 0, sizeof(image_bind_info));
  memset(&opaque_bind_info, 0, sizeof(opaque_bind_info));
  memset(&opaque_bind, 0, sizeof(opaque_bind));
  VkDeviceSize allocation_size = 0;

  if (sr->imageMipTailFirstLod == 0 && sr->imageMipTailSize > 0) {
    allocation_size = tvdb_align_up_device_size(sr->imageMipTailSize, req->alignment);
    opaque_bind.resourceOffset = sr->imageMipTailOffset;
    opaque_bind.size = sr->imageMipTailSize;
    opaque_bind.memoryOffset = 0;
    opaque_bind.flags = 0;
    opaque_bind_info.image = out->image;
    opaque_bind_info.bindCount = 1;
    opaque_bind_info.pBinds = &opaque_bind;
  } else {
    VkExtent3D g = sr->formatProperties.imageGranularity;
    if (g.width == 0 || g.height == 0 || g.depth == 0) {
      free(sparse_reqs);
      tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "invalid Vulkan sparse image granularity");
      return TVDB_ERROR_UNIMPLEMENTED;
    }
    uint32_t nx = (out->nx + g.width - 1u) / g.width;
    uint32_t ny = (out->ny + g.height - 1u) / g.height;
    uint32_t nz = (out->nz + g.depth - 1u) / g.depth;
    uint64_t bind_count64 = (uint64_t)nx * (uint64_t)ny * (uint64_t)nz;
    if (bind_count64 == 0 || bind_count64 > 1000000ull) {
      free(sparse_reqs);
      tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "unsupported Vulkan sparse image page count");
      return TVDB_ERROR_UNIMPLEMENTED;
    }
    uint32_t bind_count = (uint32_t)bind_count64;
    VkDeviceSize page_bytes = tvdb_align_up_device_size((VkDeviceSize)g.width * (VkDeviceSize)g.height * (VkDeviceSize)g.depth * sizeof(float), req->alignment);
    allocation_size = page_bytes * (VkDeviceSize)bind_count;
    binds = (VkSparseImageMemoryBind*)calloc(bind_count, sizeof(*binds));
    if (!binds) {
      free(sparse_reqs);
      tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
      return TVDB_ERROR_OUT_OF_MEMORY;
    }
    uint32_t k = 0;
    for (uint32_t z = 0; z < nz; ++z) {
      for (uint32_t y = 0; y < ny; ++y) {
        for (uint32_t x = 0; x < nx; ++x) {
          VkSparseImageMemoryBind* b = &binds[k];
          b->subresource.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
          b->subresource.mipLevel = 0;
          b->subresource.arrayLayer = 0;
          b->offset.x = (int32_t)(x * g.width);
          b->offset.y = (int32_t)(y * g.height);
          b->offset.z = (int32_t)(z * g.depth);
          b->extent.width = (x + 1u == nx) ? (out->nx - x * g.width) : g.width;
          b->extent.height = (y + 1u == ny) ? (out->ny - y * g.height) : g.height;
          b->extent.depth = (z + 1u == nz) ? (out->nz - z * g.depth) : g.depth;
          b->memoryOffset = page_bytes * (VkDeviceSize)k;
          ++k;
        }
      }
    }
    image_bind_info.image = out->image;
    image_bind_info.bindCount = bind_count;
    image_bind_info.pBinds = binds;
  }

  VkMemoryAllocateInfo mai;
  memset(&mai, 0, sizeof(mai));
  mai.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
  mai.allocationSize = allocation_size ? allocation_size : req->alignment;
  mai.memoryTypeIndex = mt;
  if (!tvdb_vk_ok(ctx->vk.AllocateMemory(ctx->device, &mai, NULL, &out->memory), err, "vkAllocateMemory(sparse image)")) {
    free(binds);
    free(sparse_reqs);
    return err ? err->status : TVDB_ERROR_IO;
  }
  if (binds) {
    for (uint32_t i = 0; i < image_bind_info.bindCount; ++i) binds[i].memory = out->memory;
  } else {
    opaque_bind.memory = out->memory;
  }

  VkFence fence = VK_NULL_HANDLE;
  VkFenceCreateInfo fci;
  memset(&fci, 0, sizeof(fci));
  fci.sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO;
  if (!tvdb_vk_ok(ctx->vk.CreateFence(ctx->device, &fci, NULL, &fence), err, "vkCreateFence(sparse)")) {
    free(binds);
    free(sparse_reqs);
    return err ? err->status : TVDB_ERROR_IO;
  }
  VkBindSparseInfo bsi;
  memset(&bsi, 0, sizeof(bsi));
  bsi.sType = VK_STRUCTURE_TYPE_BIND_SPARSE_INFO;
  if (binds) {
    bsi.imageBindCount = 1;
    bsi.pImageBinds = &image_bind_info;
  } else {
    bsi.imageOpaqueBindCount = 1;
    bsi.pImageOpaqueBinds = &opaque_bind_info;
  }
  tvdb_status_t st = TVDB_OK;
  if (!tvdb_vk_ok(ctx->vk.QueueBindSparse(ctx->queue, 1, &bsi, fence), err, "vkQueueBindSparse")) st = err ? err->status : TVDB_ERROR_IO;
  else if (!tvdb_vk_ok(ctx->vk.WaitForFences(ctx->device, 1, &fence, VK_TRUE, UINT64_MAX), err, "vkWaitForFences(sparse)")) st = err ? err->status : TVDB_ERROR_IO;
  ctx->vk.DestroyFence(ctx->device, fence, NULL);
  free(binds);
  free(sparse_reqs);
  return st;
}

static int tvdb_page_region_cmp(const void* a, const void* b) {
  const tvdb_vk_sparse_page_region* pa = (const tvdb_vk_sparse_page_region*)a;
  const tvdb_vk_sparse_page_region* pb = (const tvdb_vk_sparse_page_region*)b;
  if (pa->z != pb->z) return pa->z < pb->z ? -1 : 1;
  if (pa->y != pb->y) return pa->y < pb->y ? -1 : 1;
  if (pa->x != pb->x) return pa->x < pb->x ? -1 : 1;
  return 0;
}

static tvdb_status_t tvdb_vk_collect_sparse_active_pages(tvdb_gpu_context_t* ctx,
                                                         const tvdb_vk_image3d* img,
                                                         const tvdb_sparse_grid* sparse,
                                                         VkSparseImageMemoryRequirements* out_req,
                                                         tvdb_vk_sparse_page_region** regions_out,
                                                         uint32_t* region_count_out,
                                                         int* uses_mip_tail_out,
                                                         tvdb_error_t* err) {
  *regions_out = NULL;
  *region_count_out = 0;
  *uses_mip_tail_out = 0;
  uint32_t sparse_count = 0;
  ctx->vk.GetImageSparseMemoryRequirements(ctx->device, img->image, &sparse_count, NULL);
  if (sparse_count == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "Vulkan image has no sparse memory requirements");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  VkSparseImageMemoryRequirements* sparse_reqs =
      (VkSparseImageMemoryRequirements*)calloc(sparse_count, sizeof(*sparse_reqs));
  if (!sparse_reqs) {
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  ctx->vk.GetImageSparseMemoryRequirements(ctx->device, img->image, &sparse_count, sparse_reqs);
  VkSparseImageMemoryRequirements sr = sparse_reqs[0];
  for (uint32_t i = 0; i < sparse_count; ++i) {
    if (sparse_reqs[i].formatProperties.aspectMask & VK_IMAGE_ASPECT_COLOR_BIT) {
      sr = sparse_reqs[i];
      break;
    }
  }
  free(sparse_reqs);
  *out_req = sr;
  if (sr.imageMipTailFirstLod == 0 && sr.imageMipTailSize > 0) {
    *uses_mip_tail_out = 1;
    return TVDB_OK;
  }
  VkExtent3D g = sr.formatProperties.imageGranularity;
  if (g.width == 0 || g.height == 0 || g.depth == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "invalid Vulkan sparse image granularity");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  tvdb_vk_sparse_page_region* regions =
      (tvdb_vk_sparse_page_region*)calloc(sparse->count ? sparse->count : 1, sizeof(*regions));
  if (!regions) {
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  uint32_t count = 0;
  for (size_t i = 0; i < sparse->count; ++i) {
    int x = sparse->coords[i].x, y = sparse->coords[i].y, z = sparse->coords[i].z;
    if (x < 0 || y < 0 || z < 0 || x >= (int)img->nx || y >= (int)img->ny || z >= (int)img->nz) continue;
    regions[count].x = (uint32_t)x / g.width;
    regions[count].y = (uint32_t)y / g.height;
    regions[count].z = (uint32_t)z / g.depth;
    ++count;
  }
  if (count == 0) {
    *regions_out = regions;
    *region_count_out = 0;
    return TVDB_OK;
  }
  qsort(regions, count, sizeof(*regions), tvdb_page_region_cmp);
  uint32_t unique = 0;
  for (uint32_t i = 0; i < count; ++i) {
    if (unique == 0 || regions[i].x != regions[unique-1].x ||
        regions[i].y != regions[unique-1].y || regions[i].z != regions[unique-1].z) {
      regions[unique++] = regions[i];
    }
  }
  for (uint32_t i = 0; i < unique; ++i) {
    uint32_t ox = regions[i].x * g.width;
    uint32_t oy = regions[i].y * g.height;
    uint32_t oz = regions[i].z * g.depth;
    regions[i].offset.x = (int32_t)ox;
    regions[i].offset.y = (int32_t)oy;
    regions[i].offset.z = (int32_t)oz;
    regions[i].extent.width = (ox + g.width > img->nx) ? (img->nx - ox) : g.width;
    regions[i].extent.height = (oy + g.height > img->ny) ? (img->ny - oy) : g.height;
    regions[i].extent.depth = (oz + g.depth > img->nz) ? (img->nz - oz) : g.depth;
  }
  *regions_out = regions;
  *region_count_out = unique;
  return TVDB_OK;
}

static tvdb_status_t tvdb_vk_bind_sparse_image3d_regions(tvdb_gpu_context_t* ctx,
                                                         tvdb_vk_image3d* out,
                                                         const VkMemoryRequirements* req,
                                                         const VkSparseImageMemoryRequirements* sr,
                                                         const tvdb_vk_sparse_page_region* regions,
                                                         uint32_t region_count,
                                                         int uses_mip_tail,
                                                         int* out_all_bound,
                                                         tvdb_error_t* err) {
  *out_all_bound = 0;
  uint32_t mt = tvdb_vk_find_memory_type(ctx, req->memoryTypeBits, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT);
  if (mt == UINT32_MAX) mt = tvdb_vk_find_memory_type(ctx, req->memoryTypeBits, 0);
  if (mt == UINT32_MAX) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "no Vulkan sparse image memory type");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  VkDeviceSize allocation_size = 0;
  VkSparseImageMemoryBind* binds = NULL;
  uint32_t bind_count = 0;
  VkSparseMemoryBind opaque_bind;
  memset(&opaque_bind, 0, sizeof(opaque_bind));
  if (uses_mip_tail) {
    allocation_size = tvdb_align_up_device_size(sr->imageMipTailSize, req->alignment);
    opaque_bind.resourceOffset = sr->imageMipTailOffset;
    opaque_bind.size = sr->imageMipTailSize;
    *out_all_bound = 1;  // the mip tail backs the entire image
  } else {
    VkExtent3D g = sr->formatProperties.imageGranularity;
    VkDeviceSize page_bytes = tvdb_align_up_device_size((VkDeviceSize)g.width * (VkDeviceSize)g.height * (VkDeviceSize)g.depth * sizeof(float), req->alignment);
    uint32_t npx = (out->nx + g.width - 1) / g.width;
    uint32_t npy = (out->ny + g.height - 1) / g.height;
    uint32_t npz = (out->nz + g.depth - 1) / g.depth;
    uint64_t total_pages = (uint64_t)npx * (uint64_t)npy * (uint64_t)npz;
    // Background fallback: bind a single shared page to every page that holds no
    // active voxel, so sampling an unbound region returns the background value.
    // This aliases one physical page across many image regions, which is only
    // legal with the sparseResidencyAliased feature (+ SPARSE_ALIASED_BIT on the
    // image). Skip it otherwise (degrades to undefined unbound reads, as before),
    // and skip for absurd page counts so the bind list stays bounded.
    int use_bg = ctx->supports_sparse_aliased &&
                 (total_pages > (uint64_t)region_count) && (total_pages <= (uint64_t)(1u << 20));
    uint32_t unbound = use_bg ? (uint32_t)(total_pages - region_count) : 0u;
    uint32_t mem_pages = region_count + (use_bg ? 1u : 0u);
    VkDeviceSize bg_offset = page_bytes * (VkDeviceSize)region_count;
    allocation_size = page_bytes * (VkDeviceSize)(mem_pages ? mem_pages : 1u);
    bind_count = region_count + unbound;
    binds = (VkSparseImageMemoryBind*)calloc(bind_count ? bind_count : 1, sizeof(*binds));
    if (!binds) {
      tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
      return TVDB_ERROR_OUT_OF_MEMORY;
    }
    for (uint32_t i = 0; i < region_count; ++i) {
      binds[i].subresource.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
      binds[i].offset = regions[i].offset;
      binds[i].extent = regions[i].extent;
      binds[i].memoryOffset = page_bytes * (VkDeviceSize)i;
    }
    if (use_bg) {
      uint8_t* active = (uint8_t*)calloc((size_t)total_pages, 1);
      if (!active) { free(binds); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
      for (uint32_t i = 0; i < region_count; ++i)
        active[(((uint64_t)regions[i].z * npy) + regions[i].y) * npx + regions[i].x] = 1;
      uint32_t bi = region_count;
      for (uint32_t pz = 0; pz < npz; ++pz)
        for (uint32_t py = 0; py < npy; ++py)
          for (uint32_t px = 0; px < npx; ++px) {
            if (active[(((uint64_t)pz * npy) + py) * npx + px]) continue;
            uint32_t ox = px * g.width, oy = py * g.height, oz = pz * g.depth;
            binds[bi].subresource.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
            binds[bi].offset.x = (int32_t)ox; binds[bi].offset.y = (int32_t)oy; binds[bi].offset.z = (int32_t)oz;
            binds[bi].extent.width = (ox + g.width > out->nx) ? (out->nx - ox) : g.width;
            binds[bi].extent.height = (oy + g.height > out->ny) ? (out->ny - oy) : g.height;
            binds[bi].extent.depth = (oz + g.depth > out->nz) ? (out->nz - oz) : g.depth;
            binds[bi].memoryOffset = bg_offset;
            ++bi;
          }
      free(active);
      *out_all_bound = 1;  // every page is now backed (active pages + shared bg page)
    } else if (total_pages == (uint64_t)region_count) {
      *out_all_bound = 1;  // active pages already cover the whole image
    }
  }
  VkMemoryAllocateInfo mai;
  memset(&mai, 0, sizeof(mai));
  mai.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
  mai.allocationSize = allocation_size ? allocation_size : req->alignment;
  mai.memoryTypeIndex = mt;
  if (!tvdb_vk_ok(ctx->vk.AllocateMemory(ctx->device, &mai, NULL, &out->memory), err, "vkAllocateMemory(partial sparse image)")) {
    free(binds);
    return err ? err->status : TVDB_ERROR_IO;
  }
  for (uint32_t i = 0; i < bind_count; ++i) binds[i].memory = out->memory;
  opaque_bind.memory = out->memory;

  VkSparseImageMemoryBindInfo image_bind_info;
  VkSparseImageOpaqueMemoryBindInfo opaque_bind_info;
  memset(&image_bind_info, 0, sizeof(image_bind_info));
  memset(&opaque_bind_info, 0, sizeof(opaque_bind_info));
  image_bind_info.image = out->image;
  image_bind_info.bindCount = bind_count;
  image_bind_info.pBinds = binds;
  opaque_bind_info.image = out->image;
  opaque_bind_info.bindCount = uses_mip_tail ? 1u : 0u;
  opaque_bind_info.pBinds = uses_mip_tail ? &opaque_bind : NULL;

  VkFence fence = VK_NULL_HANDLE;
  VkFenceCreateInfo fci;
  memset(&fci, 0, sizeof(fci));
  fci.sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO;
  if (!tvdb_vk_ok(ctx->vk.CreateFence(ctx->device, &fci, NULL, &fence), err, "vkCreateFence(partial sparse)")) {
    free(binds);
    return err ? err->status : TVDB_ERROR_IO;
  }
  VkBindSparseInfo bsi;
  memset(&bsi, 0, sizeof(bsi));
  bsi.sType = VK_STRUCTURE_TYPE_BIND_SPARSE_INFO;
  if (uses_mip_tail) {
    bsi.imageOpaqueBindCount = 1;
    bsi.pImageOpaqueBinds = &opaque_bind_info;
  } else {
    bsi.imageBindCount = 1;
    bsi.pImageBinds = &image_bind_info;
  }
  tvdb_status_t st = TVDB_OK;
  if (!tvdb_vk_ok(ctx->vk.QueueBindSparse(ctx->queue, 1, &bsi, fence), err, "vkQueueBindSparse(partial)")) st = err ? err->status : TVDB_ERROR_IO;
  else if (!tvdb_vk_ok(ctx->vk.WaitForFences(ctx->device, 1, &fence, VK_TRUE, UINT64_MAX), err, "vkWaitForFences(partial sparse)")) st = err ? err->status : TVDB_ERROR_IO;
  ctx->vk.DestroyFence(ctx->device, fence, NULL);
  free(binds);
  return st;
}

static tvdb_status_t tvdb_vk_create_image3d_from_dense(tvdb_gpu_context_t* ctx,
                                                       const tvdb_dense_grid* grid,
                                                       int use_sparse_residency,
                                                       tvdb_vk_image3d* out,
                                                       tvdb_error_t* err) {
  memset(out, 0, sizeof(*out));
  out->nx = (uint32_t)grid->nx;
  out->ny = (uint32_t)grid->ny;
  out->nz = (uint32_t)grid->nz;

  VkImageCreateInfo ici;
  memset(&ici, 0, sizeof(ici));
  ici.sType = VK_STRUCTURE_TYPE_IMAGE_CREATE_INFO;
  if (use_sparse_residency) {
    if (!ctx->supports_sparse_3d_images) {
      tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "Vulkan sparse 3D image residency is unavailable on this context");
      return TVDB_ERROR_UNIMPLEMENTED;
    }
    ici.flags = VK_IMAGE_CREATE_SPARSE_BINDING_BIT | VK_IMAGE_CREATE_SPARSE_RESIDENCY_BIT;
  }
  ici.imageType = VK_IMAGE_TYPE_3D;
  ici.format = VK_FORMAT_R32_SFLOAT;
  ici.extent.width = out->nx;
  ici.extent.height = out->ny;
  ici.extent.depth = out->nz;
  ici.mipLevels = 1;
  ici.arrayLayers = 1;
  ici.samples = VK_SAMPLE_COUNT_1_BIT;
  ici.tiling = VK_IMAGE_TILING_OPTIMAL;
  ici.usage = VK_IMAGE_USAGE_TRANSFER_DST_BIT | VK_IMAGE_USAGE_SAMPLED_BIT;
  ici.sharingMode = VK_SHARING_MODE_EXCLUSIVE;
  ici.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
  if (!tvdb_vk_ok(ctx->vk.CreateImage(ctx->device, &ici, NULL, &out->image), err, "vkCreateImage")) return err ? err->status : TVDB_ERROR_IO;

  VkMemoryRequirements req;
  ctx->vk.GetImageMemoryRequirements(ctx->device, out->image, &req);
  if (use_sparse_residency) {
    tvdb_status_t sparse_st = tvdb_vk_bind_sparse_image3d_all_pages(ctx, out, &req, err);
    if (sparse_st != TVDB_OK) return sparse_st;
  } else {
    uint32_t mt = tvdb_vk_find_memory_type(ctx, req.memoryTypeBits, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT);
    if (mt == UINT32_MAX) mt = tvdb_vk_find_memory_type(ctx, req.memoryTypeBits, 0);
    if (mt == UINT32_MAX) {
      tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "no Vulkan image memory type");
      return TVDB_ERROR_UNIMPLEMENTED;
    }
    VkMemoryAllocateInfo mai;
    memset(&mai, 0, sizeof(mai));
    mai.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
    mai.allocationSize = req.size;
    mai.memoryTypeIndex = mt;
    if (!tvdb_vk_ok(ctx->vk.AllocateMemory(ctx->device, &mai, NULL, &out->memory), err, "vkAllocateMemory(image)")) return err ? err->status : TVDB_ERROR_IO;
    if (!tvdb_vk_ok(ctx->vk.BindImageMemory(ctx->device, out->image, out->memory, 0), err, "vkBindImageMemory")) return err ? err->status : TVDB_ERROR_IO;
  }

  tvdb_vk_buffer staging;
  tvdb_status_t st = tvdb_vk_create_buffer(ctx,
      (VkDeviceSize)((size_t)grid->nx * (size_t)grid->ny * (size_t)grid->nz * sizeof(float)),
      VK_BUFFER_USAGE_TRANSFER_SRC_BIT, &staging, err);
  if (st != TVDB_OK) return st;
  memcpy(staging.mapped, grid->data, (size_t)grid->nx * (size_t)grid->ny * (size_t)grid->nz * sizeof(float));

  VkCommandBuffer cmd = NULL;
  VkCommandPool pool = VK_NULL_HANDLE;
  VkFence fence = VK_NULL_HANDLE;
  st = tvdb_vk_submit_one_time(ctx, &cmd, &pool, &fence, err);
  if (st != TVDB_OK) goto done_staging;

  VkImageMemoryBarrier b0;
  memset(&b0, 0, sizeof(b0));
  b0.sType = VK_STRUCTURE_TYPE_IMAGE_MEMORY_BARRIER;
  b0.srcAccessMask = 0;
  b0.dstAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;
  b0.oldLayout = VK_IMAGE_LAYOUT_UNDEFINED;
  b0.newLayout = VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL;
  b0.srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
  b0.dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
  b0.image = out->image;
  b0.subresourceRange.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
  b0.subresourceRange.levelCount = 1;
  b0.subresourceRange.layerCount = 1;
  ctx->vk.CmdPipelineBarrier(cmd, VK_PIPELINE_STAGE_TOP_OF_PIPE_BIT, VK_PIPELINE_STAGE_TRANSFER_BIT,
                             0, 0, NULL, 0, NULL, 1, &b0);
  VkBufferImageCopy copy;
  memset(&copy, 0, sizeof(copy));
  copy.imageSubresource.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
  copy.imageSubresource.layerCount = 1;
  copy.imageExtent.width = out->nx;
  copy.imageExtent.height = out->ny;
  copy.imageExtent.depth = out->nz;
  ctx->vk.CmdCopyBufferToImage(cmd, staging.buffer, out->image,
                               VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL, 1, &copy);
  VkImageMemoryBarrier b1 = b0;
  b1.srcAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;
  b1.dstAccessMask = VK_ACCESS_SHADER_READ_BIT;
  b1.oldLayout = VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL;
  b1.newLayout = VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL;
  ctx->vk.CmdPipelineBarrier(cmd, VK_PIPELINE_STAGE_TRANSFER_BIT, VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                             0, 0, NULL, 0, NULL, 1, &b1);
  st = tvdb_vk_end_submit_wait(ctx, cmd, pool, fence, err);
  cmd = NULL; pool = VK_NULL_HANDLE; fence = VK_NULL_HANDLE;
  if (st != TVDB_OK) goto done_staging;

  VkImageViewCreateInfo ivci;
  memset(&ivci, 0, sizeof(ivci));
  ivci.sType = VK_STRUCTURE_TYPE_IMAGE_VIEW_CREATE_INFO;
  ivci.image = out->image;
  ivci.viewType = VK_IMAGE_VIEW_TYPE_3D;
  ivci.format = VK_FORMAT_R32_SFLOAT;
  ivci.subresourceRange.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
  ivci.subresourceRange.levelCount = 1;
  ivci.subresourceRange.layerCount = 1;
  if (!tvdb_vk_ok(ctx->vk.CreateImageView(ctx->device, &ivci, NULL, &out->view), err, "vkCreateImageView")) { st = err ? err->status : TVDB_ERROR_IO; goto done_staging; }

  VkSamplerCreateInfo sci;
  memset(&sci, 0, sizeof(sci));
  sci.sType = VK_STRUCTURE_TYPE_SAMPLER_CREATE_INFO;
  sci.magFilter = VK_FILTER_LINEAR;
  sci.minFilter = VK_FILTER_LINEAR;
  sci.mipmapMode = VK_SAMPLER_MIPMAP_MODE_NEAREST;
  sci.addressModeU = VK_SAMPLER_ADDRESS_MODE_CLAMP_TO_EDGE;
  sci.addressModeV = VK_SAMPLER_ADDRESS_MODE_CLAMP_TO_EDGE;
  sci.addressModeW = VK_SAMPLER_ADDRESS_MODE_CLAMP_TO_EDGE;
  sci.maxLod = 0.0f;
  sci.borderColor = VK_BORDER_COLOR_FLOAT_TRANSPARENT_BLACK;
  if (!tvdb_vk_ok(ctx->vk.CreateSampler(ctx->device, &sci, NULL, &out->sampler), err, "vkCreateSampler")) { st = err ? err->status : TVDB_ERROR_IO; goto done_staging; }
  st = TVDB_OK;

done_staging:
  if (fence) ctx->vk.DestroyFence(ctx->device, fence, NULL);
  if (pool) ctx->vk.DestroyCommandPool(ctx->device, pool, NULL);
  tvdb_vk_destroy_buffer(ctx, &staging);
  if (st != TVDB_OK) tvdb_vk_destroy_image3d(ctx, out);
  return st;
}

static tvdb_status_t tvdb_vk_create_sparse_image3d_from_sparse_grid(tvdb_gpu_context_t* ctx,
                                                                    const tvdb_sparse_grid* sparse,
                                                                    float background,
                                                                    int nx, int ny, int nz,
                                                                    tvdb_vk_image3d* out,
                                                                    tvdb_error_t* err) {
  memset(out, 0, sizeof(*out));
  if (!ctx->supports_sparse_3d_images) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "Vulkan sparse 3D image residency is unavailable on this context");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  out->nx = (uint32_t)nx;
  out->ny = (uint32_t)ny;
  out->nz = (uint32_t)nz;

  VkImageCreateInfo ici;
  memset(&ici, 0, sizeof(ici));
  ici.sType = VK_STRUCTURE_TYPE_IMAGE_CREATE_INFO;
  ici.flags = VK_IMAGE_CREATE_SPARSE_BINDING_BIT | VK_IMAGE_CREATE_SPARSE_RESIDENCY_BIT;
  // The background fallback aliases one physical page across all unbound pages,
  // which is only well-defined with SPARSE_ALIASED_BIT + the sparseResidencyAliased
  // feature. Request it when available so the fallback is spec-compliant.
  if (ctx->supports_sparse_aliased) ici.flags |= VK_IMAGE_CREATE_SPARSE_ALIASED_BIT;
  ici.imageType = VK_IMAGE_TYPE_3D;
  ici.format = VK_FORMAT_R32_SFLOAT;
  ici.extent.width = out->nx;
  ici.extent.height = out->ny;
  ici.extent.depth = out->nz;
  ici.mipLevels = 1;
  ici.arrayLayers = 1;
  ici.samples = VK_SAMPLE_COUNT_1_BIT;
  ici.tiling = VK_IMAGE_TILING_OPTIMAL;
  ici.usage = VK_IMAGE_USAGE_TRANSFER_DST_BIT | VK_IMAGE_USAGE_SAMPLED_BIT;
  ici.sharingMode = VK_SHARING_MODE_EXCLUSIVE;
  ici.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
  if (!tvdb_vk_ok(ctx->vk.CreateImage(ctx->device, &ici, NULL, &out->image), err, "vkCreateImage(partial sparse)")) return err ? err->status : TVDB_ERROR_IO;

  VkMemoryRequirements req;
  ctx->vk.GetImageMemoryRequirements(ctx->device, out->image, &req);
  VkSparseImageMemoryRequirements sparse_req;
  tvdb_vk_sparse_page_region* regions = NULL;
  uint32_t region_count = 0;
  int uses_mip_tail = 0;
  tvdb_status_t st = tvdb_vk_collect_sparse_active_pages(ctx, out, sparse, &sparse_req, &regions, &region_count, &uses_mip_tail, err);
  if (st != TVDB_OK) goto done_regions;
  if (!uses_mip_tail && region_count == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "sparse image upload has no active resident pages");
    st = TVDB_ERROR_INVALID_ARGUMENT;
    goto done_regions;
  }
  int all_bound = 0;
  st = tvdb_vk_bind_sparse_image3d_regions(ctx, out, &req, &sparse_req, regions, region_count, uses_mip_tail, &all_bound, err);
  if (st != TVDB_OK) goto done_regions;

  size_t voxel_count = (size_t)nx * (size_t)ny * (size_t)nz;
  tvdb_vk_buffer staging;
  st = tvdb_vk_create_buffer(ctx, (VkDeviceSize)(voxel_count * sizeof(float)),
                             VK_BUFFER_USAGE_TRANSFER_SRC_BIT, &staging, err);
  if (st != TVDB_OK) goto done_regions;
  float* sdata = (float*)staging.mapped;
  for (size_t i = 0; i < voxel_count; ++i) sdata[i] = background;
  for (size_t i = 0; i < sparse->count; ++i) {
    int x = sparse->coords[i].x, y = sparse->coords[i].y, z = sparse->coords[i].z;
    if (x >= 0 && y >= 0 && z >= 0 && x < nx && y < ny && z < nz) {
      sdata[(size_t)x + (size_t)nx * ((size_t)y + (size_t)ny * (size_t)z)] = sparse->values[i];
    }
  }

  VkCommandBuffer cmd = NULL;
  VkCommandPool pool = VK_NULL_HANDLE;
  VkFence fence = VK_NULL_HANDLE;
  st = tvdb_vk_submit_one_time(ctx, &cmd, &pool, &fence, err);
  if (st != TVDB_OK) goto done_staging;
  VkImageMemoryBarrier b0;
  memset(&b0, 0, sizeof(b0));
  b0.sType = VK_STRUCTURE_TYPE_IMAGE_MEMORY_BARRIER;
  b0.dstAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;
  b0.oldLayout = VK_IMAGE_LAYOUT_UNDEFINED;
  b0.newLayout = VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL;
  b0.srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
  b0.dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
  b0.image = out->image;
  b0.subresourceRange.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
  b0.subresourceRange.levelCount = 1;
  b0.subresourceRange.layerCount = 1;
  ctx->vk.CmdPipelineBarrier(cmd, VK_PIPELINE_STAGE_TOP_OF_PIPE_BIT, VK_PIPELINE_STAGE_TRANSFER_BIT,
                             0, 0, NULL, 0, NULL, 1, &b0);
  if (uses_mip_tail || all_bound) {
    // Every page is backed (mip tail, fully-active, or the shared background
    // page): one full-image copy writes real values to active pages and the
    // background value everywhere else (unbound pages alias one page, all
    // receiving the same background value, so the result is well-defined).
    VkBufferImageCopy copy;
    memset(&copy, 0, sizeof(copy));
    copy.imageSubresource.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
    copy.imageSubresource.layerCount = 1;
    copy.imageExtent.width = out->nx;
    copy.imageExtent.height = out->ny;
    copy.imageExtent.depth = out->nz;
    ctx->vk.CmdCopyBufferToImage(cmd, staging.buffer, out->image,
                                 VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL, 1, &copy);
  } else {
    VkBufferImageCopy* copies = (VkBufferImageCopy*)calloc(region_count, sizeof(*copies));
    if (!copies) {
      tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
      st = TVDB_ERROR_OUT_OF_MEMORY;
      goto done_cmd;
    }
    for (uint32_t i = 0; i < region_count; ++i) {
      copies[i].bufferOffset = ((VkDeviceSize)regions[i].offset.x +
          (VkDeviceSize)nx * ((VkDeviceSize)regions[i].offset.y + (VkDeviceSize)ny * (VkDeviceSize)regions[i].offset.z)) * sizeof(float);
      copies[i].bufferRowLength = (uint32_t)nx;
      copies[i].bufferImageHeight = (uint32_t)ny;
      copies[i].imageSubresource.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
      copies[i].imageSubresource.layerCount = 1;
      copies[i].imageOffset = regions[i].offset;
      copies[i].imageExtent = regions[i].extent;
    }
    ctx->vk.CmdCopyBufferToImage(cmd, staging.buffer, out->image,
                                 VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL, region_count, copies);
    free(copies);
  }
  VkImageMemoryBarrier b1 = b0;
  b1.srcAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;
  b1.dstAccessMask = VK_ACCESS_SHADER_READ_BIT;
  b1.oldLayout = VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL;
  b1.newLayout = VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL;
  ctx->vk.CmdPipelineBarrier(cmd, VK_PIPELINE_STAGE_TRANSFER_BIT, VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                             0, 0, NULL, 0, NULL, 1, &b1);
done_cmd:
  if (st == TVDB_OK) st = tvdb_vk_end_submit_wait(ctx, cmd, pool, fence, err);
  else {
    if (fence) ctx->vk.DestroyFence(ctx->device, fence, NULL);
    if (pool) ctx->vk.DestroyCommandPool(ctx->device, pool, NULL);
  }
  cmd = NULL; pool = VK_NULL_HANDLE; fence = VK_NULL_HANDLE;
  if (st != TVDB_OK) goto done_staging;

  VkImageViewCreateInfo ivci;
  memset(&ivci, 0, sizeof(ivci));
  ivci.sType = VK_STRUCTURE_TYPE_IMAGE_VIEW_CREATE_INFO;
  ivci.image = out->image;
  ivci.viewType = VK_IMAGE_VIEW_TYPE_3D;
  ivci.format = VK_FORMAT_R32_SFLOAT;
  ivci.subresourceRange.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
  ivci.subresourceRange.levelCount = 1;
  ivci.subresourceRange.layerCount = 1;
  if (!tvdb_vk_ok(ctx->vk.CreateImageView(ctx->device, &ivci, NULL, &out->view), err, "vkCreateImageView(partial sparse)")) { st = err ? err->status : TVDB_ERROR_IO; goto done_staging; }
  VkSamplerCreateInfo sci;
  memset(&sci, 0, sizeof(sci));
  sci.sType = VK_STRUCTURE_TYPE_SAMPLER_CREATE_INFO;
  sci.magFilter = VK_FILTER_LINEAR;
  sci.minFilter = VK_FILTER_LINEAR;
  sci.mipmapMode = VK_SAMPLER_MIPMAP_MODE_NEAREST;
  sci.addressModeU = VK_SAMPLER_ADDRESS_MODE_CLAMP_TO_EDGE;
  sci.addressModeV = VK_SAMPLER_ADDRESS_MODE_CLAMP_TO_EDGE;
  sci.addressModeW = VK_SAMPLER_ADDRESS_MODE_CLAMP_TO_EDGE;
  sci.maxLod = 0.0f;
  sci.borderColor = VK_BORDER_COLOR_FLOAT_TRANSPARENT_BLACK;
  if (!tvdb_vk_ok(ctx->vk.CreateSampler(ctx->device, &sci, NULL, &out->sampler), err, "vkCreateSampler(partial sparse)")) { st = err ? err->status : TVDB_ERROR_IO; goto done_staging; }

done_staging:
  tvdb_vk_destroy_buffer(ctx, &staging);
done_regions:
  free(regions);
  if (st != TVDB_OK) tvdb_vk_destroy_image3d(ctx, out);
  return st;
}

typedef struct {
  const uint8_t* spv;
  uint32_t spv_len;
  uint32_t descriptor_count;
  const tvdb_vk_buffer* buffers[TVDB_VK_MAX_DESCRIPTORS];
  const tvdb_vk_image3d* images[TVDB_VK_MAX_DESCRIPTORS];
  uint32_t descriptor_types[TVDB_VK_MAX_DESCRIPTORS];
  uint32_t group_x;
  uint32_t group_y;   /* 0 or 1 means 1 */
  uint32_t group_z;   /* 0 or 1 means 1 */
  /* Queue the work and return without waiting. The caller must not touch any
   * buffer the shader reads until the next non-deferred dispatch or an explicit
   * flush, so a batch of deferred dispatches may only share constant contents
   * (a uniform rewritten between iterations is not safe). */
  int defer_wait;
  /* Bind this descriptor set instead of allocating one and writing it. Lets a
   * loop that alternates between a fixed set of buffers allocate the sets once
   * and skip both the pool allocation and UpdateDescriptorSets per iteration.
   * Owned by the caller; not freed by the dispatch. */
  VkDescriptorSet preset_set;
  /* Dynamic offset applied to the first VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER_DYNAMIC
   * binding in the set, for presets that share one set across many parameter
   * slices. Must be a multiple of the device's minUniformBufferOffsetAlignment.
   * Only meaningful together with preset_set. */
  uint32_t dynamic_offset;
} tvdb_vk_dispatch_desc;

/* Wait for a deferred submission, if any, and release its fence and command
 * buffer. Called at the head of every non-deferred dispatch and by
 * tvdb_vk_flush, so a deferred batch is always drained before anything that
 * could reuse the resources. */
tvdb_status_t tvdb_vk_flush(tvdb_gpu_context_t* ctx, tvdb_error_t* err);

/* Create the shared descriptor and command pools on first use. Factored out of
 * the dispatch because a caller that pre-builds descriptor sets needs the pool
 * to exist before it ever reaches a dispatch. */
static tvdb_status_t tvdb_vk_ensure_pools(tvdb_gpu_context_t* ctx, tvdb_error_t* err) {
  if (!ctx->desc_pool) {
    VkDescriptorPoolSize ps[3];
    memset(ps, 0, sizeof(ps));
    ps[0].type = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; ps[0].descriptorCount = 256;
    ps[1].type = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;  ps[1].descriptorCount = 256;
    ps[2].type = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER; ps[2].descriptorCount = 64;
    VkDescriptorPoolCreateInfo dpci;
    memset(&dpci, 0, sizeof(dpci));
    dpci.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO;
    dpci.flags = VK_DESCRIPTOR_POOL_CREATE_FREE_DESCRIPTOR_SET_BIT;
    dpci.maxSets = 1024;
    dpci.poolSizeCount = 3;
    dpci.pPoolSizes = ps;
    if (!tvdb_vk_ok(ctx->vk.CreateDescriptorPool(ctx->device, &dpci, NULL, &ctx->desc_pool), err, "vkCreateDescriptorPool"))
      return err ? err->status : TVDB_ERROR_IO;
  }
  if (!ctx->cmd_pool) {
    VkCommandPoolCreateInfo cpi;
    memset(&cpi, 0, sizeof(cpi));
    cpi.sType = VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO;
    /* RESET lets the flag be set on the buffers; FREE is what lets a per-call
     * command buffer go back to the pool. Without it the pool grows without
     * bound, because Vulkan only reclaims command buffers on pool reset or
     * free -- measured at ~0.34 MB of RSS per dispatch. */
    cpi.flags = VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT | VK_COMMAND_POOL_CREATE_FREE_COMMAND_BUFFER_BIT;
    cpi.queueFamilyIndex = ctx->queue_family;
    if (!tvdb_vk_ok(ctx->vk.CreateCommandPool(ctx->device, &cpi, NULL, &ctx->cmd_pool), err, "vkCreateCommandPool"))
      return err ? err->status : TVDB_ERROR_IO;
  }
  return TVDB_OK;
}



/* Create a descriptor-set layout for `count` bindings. Split out of the dispatch
 * path so a caller that pre-builds descriptor sets gets a layout that matches
 * the cached pipeline's for the same shader and binding types. */
static tvdb_status_t tvdb_vk_make_layout(tvdb_gpu_context_t* ctx,
    const uint8_t* spv, uint32_t spv_len, uint32_t count, const uint32_t* types,
    VkDescriptorSetLayout* out, int* out_borrowed, tvdb_error_t* err) {
  for (uint32_t i = 0; i < ctx->pipeline_cache_count; ++i) {
    tvdb_vk_pipeline_entry* e = &ctx->pipeline_cache[i];
    if (e->spv != spv || e->spv_len != spv_len || e->descriptor_count != count) continue;
    uint32_t k, same = 1;
    for (k = 0; k < count; ++k) if (e->descriptor_types[k] != types[k]) { same = 0; break; }
    if (same) { *out = e->set_layout; if (out_borrowed) *out_borrowed = 1; return TVDB_OK; }
  }
  VkDescriptorSetLayoutBinding bindings[TVDB_VK_MAX_DESCRIPTORS];
  memset(bindings, 0, sizeof(bindings));
  for (uint32_t i = 0; i < count; ++i) {
    bindings[i].binding = i;
    bindings[i].descriptorCount = 1;
    bindings[i].descriptorType = types[i];
    bindings[i].stageFlags = VK_SHADER_STAGE_COMPUTE_BIT;
  }
  VkDescriptorSetLayoutCreateInfo dlci;
  memset(&dlci, 0, sizeof(dlci));
  dlci.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO;
  dlci.bindingCount = count;
  dlci.pBindings = bindings;
  if (!tvdb_vk_ok(ctx->vk.CreateDescriptorSetLayout(ctx->device, &dlci, NULL, out), err, "vkCreateDescriptorSetLayout"))
    return err ? err->status : TVDB_ERROR_IO;
  if (out_borrowed) *out_borrowed = 0;   /* created fresh; the caller owns it */
  return TVDB_OK;
}



/* Build a descriptor set that the caller owns and reuses. */
static tvdb_status_t tvdb_vk_make_set(tvdb_gpu_context_t* ctx, VkDescriptorSetLayout layout,
    const tvdb_vk_buffer* const* buffers, const uint32_t* types, uint32_t count,
    VkDescriptorSet* out, tvdb_error_t* err) {
  tvdb_status_t ps = tvdb_vk_ensure_pools(ctx, err);
  if (ps != TVDB_OK) return ps;
  VkDescriptorSetAllocateInfo dsai;
  memset(&dsai, 0, sizeof(dsai));
  dsai.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
  dsai.descriptorPool = ctx->desc_pool;
  dsai.descriptorSetCount = 1;
  dsai.pSetLayouts = &layout;
  if (!tvdb_vk_ok(ctx->vk.AllocateDescriptorSets(ctx->device, &dsai, out), err, "vkAllocateDescriptorSets"))
    return err ? err->status : TVDB_ERROR_IO;
  VkDescriptorBufferInfo infos[TVDB_VK_MAX_DESCRIPTORS];
  VkWriteDescriptorSet writes[TVDB_VK_MAX_DESCRIPTORS];
  memset(infos, 0, sizeof(infos));
  memset(writes, 0, sizeof(writes));
  for (uint32_t i = 0; i < count; ++i) {
    writes[i].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
    writes[i].dstSet = *out;
    writes[i].dstBinding = i;
    writes[i].descriptorCount = 1;
    writes[i].descriptorType = types[i];
    infos[i].buffer = buffers[i]->buffer;
    infos[i].offset = 0;
    infos[i].range = buffers[i]->size;
    writes[i].pBufferInfo = &infos[i];
  }
  ctx->vk.UpdateDescriptorSets(ctx->device, count, writes, 0, NULL);
  return TVDB_OK;
}

static tvdb_status_t tvdb_vk_drain_pending(tvdb_gpu_context_t* ctx, tvdb_error_t* err) {
  if (!ctx->pending_count) return TVDB_OK;
  /* One vkWaitForFences for the whole set, not one per fence: a blocking wait
   * costs ~2.4 ms whenever it actually has to block, so draining a batch of N
   * serially would give back most of what the deferred submit saved (measured
   * 153 ms -> 222 ms for 256 mean-curvature-flow iterations). Waiting on all of
   * them at once also matches the in-order queue: the last one completing
   * implies the earlier ones did. */
  VkFence fences[TVDB_VK_PENDING_MAX];
  uint32_t n = ctx->pending_count;
  for (uint32_t i = 0; i < n; ++i) fences[i] = ctx->pending_fence[i];
  tvdb_status_t st = TVDB_OK;
  if (!tvdb_vk_ok(ctx->vk.WaitForFences(ctx->device, n, fences, VK_TRUE, UINT64_MAX), err, "vkWaitForFences"))
    st = err ? err->status : TVDB_ERROR_IO;
  for (uint32_t i = 0; i < n; ++i) {
    VkCommandBuffer c = ctx->pending_cmd[i];
    /* A descriptor set is read at *execution* time, not record time, so a
     * deferred dispatch's set cannot be returned to the pool until its fence has
     * signalled. Freeing it right after the submit let the pool hand the same
     * memory to the next allocation while the dispatch was still in flight,
     * which is a spec violation and reads whichever bindings landed there. The
     * two deferred callers (mean curvature flow, fast sweeping) both pre-build
     * their sets, so this never fired for them -- it appears the moment the path
     * is generalised to an op that does not. */
    if (ctx->pending_set[i] != VK_NULL_HANDLE && ctx->vk.FreeDescriptorSets)
      ctx->vk.FreeDescriptorSets(ctx->device, ctx->desc_pool, 1, &ctx->pending_set[i]);
    if (c && ctx->vk.FreeCommandBuffers) ctx->vk.FreeCommandBuffers(ctx->device, ctx->cmd_pool, 1, &c);
    if (fences[i]) ctx->vk.DestroyFence(ctx->device, fences[i], NULL);
  }
  ctx->pending_count = 0;
  return st;
}

tvdb_status_t tvdb_vk_flush(tvdb_gpu_context_t* ctx, tvdb_error_t* err) {
  return tvdb_vk_drain_pending(ctx, err);
}

/* Look up, or create and cache, the compute pipeline for a shader and descriptor
   shape, and hand back the layout its descriptor set must be allocated from.
   A caller that pre-allocates a descriptor set has to allocate it from *this*
   layout, not from one it built itself: the set is bound with the pipeline's own
   pipeline layout, and although Vulkan permits binding a set from an "identically
   defined" layout, at least one shipping driver crashes on a set whose layout is a
   different object. So this is the single place that creates the layout, and both
   the dispatch and the pre-allocating callers (fast sweeping's dynamic-offset
   preset, mesh_to_sdf's per-slab sets) go through it. */
static tvdb_status_t tvdb_vk_get_pipeline(tvdb_gpu_context_t* ctx,
    const uint8_t* spv, uint32_t spv_len, uint32_t count, const uint32_t* types,
    tvdb_vk_pipeline_entry** out_pe, int* out_cached, tvdb_error_t* err) {
  tvdb_vk_pipeline_entry *pe = NULL;
  int cached = 0;
  for (uint32_t i = 0; i < ctx->pipeline_cache_count; ++i) {
    tvdb_vk_pipeline_entry *e = &ctx->pipeline_cache[i];
    if (e->spv != spv || e->spv_len != spv_len) continue;
    if (e->descriptor_count != count) continue;
    uint32_t k, same = 1;
    for (k = 0; k < count; ++k)
      if (e->descriptor_types[k] != types[k]) { same = 0; break; }
    if (same) { pe = e; cached = 1; break; }
  }
  if (!pe && ctx->pipeline_cache_count < TVDB_VK_PIPELINE_CACHE_MAX) {
    pe = &ctx->pipeline_cache[ctx->pipeline_cache_count++];
    cached = 1;
    memset(pe, 0, sizeof(*pe));
    pe->spv = spv;
    pe->spv_len = spv_len;
    pe->descriptor_count = count;
    for (uint32_t k = 0; k < count; ++k)
      pe->descriptor_types[k] = types[k];

    VkDescriptorSetLayoutBinding bindings[TVDB_VK_MAX_DESCRIPTORS];
    memset(bindings, 0, sizeof(bindings));
    for (uint32_t i = 0; i < count; ++i) {
      bindings[i].binding = i;
      bindings[i].descriptorCount = 1;
      bindings[i].descriptorType = types[i];
      bindings[i].stageFlags = VK_SHADER_STAGE_COMPUTE_BIT;
    }
    VkDescriptorSetLayoutCreateInfo dlci;
    memset(&dlci, 0, sizeof(dlci));
    dlci.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO;
    dlci.bindingCount = count;
    dlci.pBindings = bindings;
    if (!tvdb_vk_ok(ctx->vk.CreateDescriptorSetLayout(ctx->device, &dlci, NULL, &pe->set_layout), err, "vkCreateDescriptorSetLayout")) {
      ctx->pipeline_cache_count--;
      return err ? err->status : TVDB_ERROR_IO;
    }

    VkShaderModuleCreateInfo smci;
    memset(&smci, 0, sizeof(smci));
    smci.sType = VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO;
    smci.codeSize = spv_len;
    smci.pCode = (const uint32_t*)spv;
    if (!tvdb_vk_ok(ctx->vk.CreateShaderModule(ctx->device, &smci, NULL, &pe->shader), err, "vkCreateShaderModule")) {
      ctx->vk.DestroyDescriptorSetLayout(ctx->device, pe->set_layout, NULL);
      ctx->pipeline_cache_count--;
      return err ? err->status : TVDB_ERROR_IO;
    }

    VkPipelineLayoutCreateInfo plci;
    memset(&plci, 0, sizeof(plci));
    plci.sType = VK_STRUCTURE_TYPE_PIPELINE_LAYOUT_CREATE_INFO;
    plci.setLayoutCount = 1;
    plci.pSetLayouts = &pe->set_layout;
    if (!tvdb_vk_ok(ctx->vk.CreatePipelineLayout(ctx->device, &plci, NULL, &pe->pipeline_layout), err, "vkCreatePipelineLayout")) {
      ctx->vk.DestroyShaderModule(ctx->device, pe->shader, NULL);
      ctx->vk.DestroyDescriptorSetLayout(ctx->device, pe->set_layout, NULL);
      ctx->pipeline_cache_count--;
      return err ? err->status : TVDB_ERROR_IO;
    }

    VkComputePipelineCreateInfo cpci;
    memset(&cpci, 0, sizeof(cpci));
    cpci.sType = VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO;
    cpci.stage.sType = VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO;
    cpci.stage.stage = VK_SHADER_STAGE_COMPUTE_BIT;
    cpci.stage.module = pe->shader;
    cpci.stage.pName = "main";
    cpci.layout = pe->pipeline_layout;
    if (!tvdb_vk_ok(ctx->vk.CreateComputePipelines(ctx->device, VK_NULL_HANDLE, 1, &cpci, NULL, &pe->pipeline), err, "vkCreateComputePipelines")) {
      ctx->vk.DestroyPipelineLayout(ctx->device, pe->pipeline_layout, NULL);
      ctx->vk.DestroyShaderModule(ctx->device, pe->shader, NULL);
      ctx->vk.DestroyDescriptorSetLayout(ctx->device, pe->set_layout, NULL);
      ctx->pipeline_cache_count--;
      return err ? err->status : TVDB_ERROR_IO;
    }
  }
  if (!pe) {
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "GPU pipeline cache capacity exceeded");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  *out_pe = pe;
  if (out_cached) *out_cached = cached;
  return TVDB_OK;
}

static tvdb_status_t tvdb_vk_dispatch(tvdb_gpu_context_t* ctx, const tvdb_vk_dispatch_desc* d, tvdb_error_t* err) {
  if (!d->spv || d->spv_len == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "Vulkan SPIR-V blobs are unavailable; rebuild with glslangValidator or use generated include");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  if (d->descriptor_count > TVDB_VK_MAX_DESCRIPTORS) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "descriptor count exceeds TVDB_VK_MAX_DESCRIPTORS");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }

  /* A deferred batch must complete before this dispatch touches anything the
   * previous one may still be reading. */
  if (!d->defer_wait) {
    tvdb_status_t ps = tvdb_vk_drain_pending(ctx, err);
    if (ps != TVDB_OK) return ps;
  }

  /* Shared, lazily created once per context. */
  { tvdb_status_t ps = tvdb_vk_ensure_pools(ctx, err); if (ps != TVDB_OK) return ps; }

  /* Look for (or build) the cached pipeline for this shader and descriptor shape. */
  tvdb_vk_pipeline_entry *pe = NULL;
  int cached = 0;
  { tvdb_status_t ps = tvdb_vk_get_pipeline(ctx, d->spv, d->spv_len,
                                            d->descriptor_count, d->descriptor_types,
                                            &pe, &cached, err);
    if (ps != TVDB_OK) return ps; }

  VkDescriptorSetLayout layout = pe->set_layout;

  VkDescriptorPool pool = ctx->desc_pool;   /* shared; freed with the context */
  VkDescriptorSet set = d->preset_set ? d->preset_set : VK_NULL_HANDLE;
  if (!set) {
    VkDescriptorSetAllocateInfo dsai;
    memset(&dsai, 0, sizeof(dsai));
    dsai.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
    dsai.descriptorPool = pool;
    dsai.descriptorSetCount = 1;
    dsai.pSetLayouts = &layout;
    if (!tvdb_vk_ok(ctx->vk.AllocateDescriptorSets(ctx->device, &dsai, &set), err, "vkAllocateDescriptorSets")) goto fail_pool;

    VkDescriptorBufferInfo infos[TVDB_VK_MAX_DESCRIPTORS];
    VkDescriptorImageInfo image_infos[TVDB_VK_MAX_DESCRIPTORS];
    VkWriteDescriptorSet writes[TVDB_VK_MAX_DESCRIPTORS];
    memset(infos, 0, sizeof(infos));
    memset(image_infos, 0, sizeof(image_infos));
    memset(writes, 0, sizeof(writes));
    for (uint32_t i = 0; i < d->descriptor_count; ++i) {
      writes[i].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
      writes[i].dstSet = set;
      writes[i].dstBinding = i;
      writes[i].descriptorCount = 1;
      writes[i].descriptorType = d->descriptor_types[i];
      if (d->descriptor_types[i] == VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER) {
        image_infos[i].sampler = d->images[i]->sampler;
        image_infos[i].imageView = d->images[i]->view;
        image_infos[i].imageLayout = VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL;
        writes[i].pImageInfo = &image_infos[i];
      } else {
        infos[i].buffer = d->buffers[i]->buffer;
        infos[i].offset = 0;
        infos[i].range = d->buffers[i]->size;
        writes[i].pBufferInfo = &infos[i];
      }
    }
    ctx->vk.UpdateDescriptorSets(ctx->device, d->descriptor_count, writes, 0, NULL);
  }

  /* Shader module, pipeline layout and pipeline come from the cache above. */
  const VkShaderModule shader = pe->shader;
  const VkPipelineLayout pipeline_layout = pe->pipeline_layout;
  const VkPipeline pipeline = pe->pipeline;

  VkCommandPool cmd_pool = ctx->cmd_pool;  /* shared; freed with the context */
  VkCommandBuffer cmd = NULL;
  VkCommandBufferAllocateInfo cbai;
  memset(&cbai, 0, sizeof(cbai));
  cbai.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
  cbai.commandPool = cmd_pool;
  cbai.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
  cbai.commandBufferCount = 1;
  if (!tvdb_vk_ok(ctx->vk.AllocateCommandBuffers(ctx->device, &cbai, &cmd), err, "vkAllocateCommandBuffers")) goto fail_cmdpool;

  VkFence fence = VK_NULL_HANDLE;
  VkFenceCreateInfo fci;
  memset(&fci, 0, sizeof(fci));
  fci.sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO;
  if (!tvdb_vk_ok(ctx->vk.CreateFence(ctx->device, &fci, NULL, &fence), err, "vkCreateFence")) goto fail_cmdpool;

  VkCommandBufferBeginInfo begin;
  memset(&begin, 0, sizeof(begin));
  begin.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;
  if (!tvdb_vk_ok(ctx->vk.BeginCommandBuffer(cmd, &begin), err, "vkBeginCommandBuffer")) goto fail_fence;
  ctx->vk.CmdBindPipeline(cmd, VK_PIPELINE_BIND_POINT_COMPUTE, pipeline);
  { /* dynamicOffsetCount must equal the number of dynamic bindings in the set,
       * including when the offset itself is 0 (plane 0 of a preset sweep) -- a
       * count of 0 against a set holding a dynamic descriptor is invalid, and
       * at least one driver faults on it. So derive the count from the declared
       * descriptor types rather than from the offset's value. */
    uint32_t ndyn = 0;
    for (uint32_t i = 0; i < d->descriptor_count; ++i)
      if (d->descriptor_types[i] == VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER_DYNAMIC ||
          d->descriptor_types[i] == VK_DESCRIPTOR_TYPE_STORAGE_BUFFER_DYNAMIC) ndyn++;
    if (ndyn > 1) {
      tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                         "at most one dynamic descriptor binding is supported");
      goto fail_cmdpool;
    }
    const uint32_t dyn = d->dynamic_offset;
    ctx->vk.CmdBindDescriptorSets(cmd, VK_PIPELINE_BIND_POINT_COMPUTE, pipeline_layout,
                                  0, 1, &set, ndyn, ndyn ? &dyn : NULL); }

  /* Kernel chains that iterate (mean-curvature flow, the fast-sweeping planes)
   * dispatch repeatedly against the same buffers, so each dispatch has to make
   * the previous one's shader writes visible before it reads. Queue submission
   * only orders execution; it supplies no dependency between device writes and
   * later device reads, so without this the second iteration reads stale data.
   * The barrier costs nothing here because dispatch N+1 depends on N anyway. */
  {
    VkBufferMemoryBarrier bar[TVDB_VK_MAX_DESCRIPTORS];
    uint32_t nbar = 0;
    memset(bar, 0, sizeof(bar));
    for (uint32_t i = 0; i < d->descriptor_count; ++i) {
      if (d->descriptor_types[i] == VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER) continue;
      if (!d->buffers[i] || !d->buffers[i]->buffer) continue;
      bar[nbar].sType = VK_STRUCTURE_TYPE_BUFFER_MEMORY_BARRIER;
      bar[nbar].srcAccessMask = VK_ACCESS_SHADER_WRITE_BIT;
      bar[nbar].dstAccessMask = VK_ACCESS_SHADER_READ_BIT | VK_ACCESS_SHADER_WRITE_BIT;
      bar[nbar].srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
      bar[nbar].dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
      bar[nbar].buffer = d->buffers[i]->buffer;
      bar[nbar].offset = 0;
      bar[nbar].size = d->buffers[i]->size;   /* equivalent to VK_WHOLE_SIZE from offset 0 */
      nbar++;
    }
    if (nbar && ctx->vk.CmdPipelineBarrier)
      ctx->vk.CmdPipelineBarrier(cmd,
                                 VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
                                 VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT, 0,
                                 0, NULL, nbar, bar, 0, NULL);
  }

  ctx->vk.CmdDispatch(cmd, d->group_x, d->group_y ? d->group_y : 1u, d->group_z ? d->group_z : 1u);
  if (!tvdb_vk_ok(ctx->vk.EndCommandBuffer(cmd), err, "vkEndCommandBuffer")) goto fail_fence;
  VkSubmitInfo si;
  memset(&si, 0, sizeof(si));
  si.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
  si.commandBufferCount = 1;
  si.pCommandBuffers = &cmd;
  if (!tvdb_vk_ok(ctx->vk.QueueSubmit(ctx->queue, 1, &si, fence), err, "vkQueueSubmit")) goto fail_fence;
  if (d->defer_wait) {
    /* Hand ownership of the fence and command buffer to the context. A full
     * ring means a batch larger than the ring; drain it rather than growing. */
    if (ctx->pending_count == TVDB_VK_PENDING_MAX) {
      tvdb_status_t ps = tvdb_vk_drain_pending(ctx, err);
      if (ps != TVDB_OK) goto fail_fence;
    }
    ctx->pending_fence[ctx->pending_count] = fence;
    ctx->pending_cmd[ctx->pending_count] = cmd;
    /* Parked with the fence, not freed here: see tvdb_vk_drain_pending. */
    ctx->pending_set[ctx->pending_count] = d->preset_set ? VK_NULL_HANDLE : set;
    ctx->pending_count++;
    fence = VK_NULL_HANDLE;
    cmd = NULL;
    set = VK_NULL_HANDLE;
    if (!cached) {
      ctx->vk.DestroyPipeline(ctx->device, pipeline, NULL);
      ctx->vk.DestroyPipelineLayout(ctx->device, pipeline_layout, NULL);
      ctx->vk.DestroyShaderModule(ctx->device, shader, NULL);
      ctx->vk.DestroyDescriptorSetLayout(ctx->device, layout, NULL);
    }
    return TVDB_OK;
  }
  if (!tvdb_vk_ok(ctx->vk.WaitForFences(ctx->device, 1, &fence, VK_TRUE, UINT64_MAX), err, "vkWaitForFences")) goto fail_fence;

  ctx->vk.DestroyFence(ctx->device, fence, NULL);
  /* The pool belongs to the context, so the set and the command buffer go back
   * to it rather than the pool being destroyed. Both must happen on every
   * dispatch: the descriptor pool has a fixed maxSets, and skipping the return
   * exhausts it (measured VK_ERROR_OUT_OF_POOL_MEMORY after 85 calls of a 3-op
   * rotation); the command pool accumulates command buffers otherwise, at
   * ~0.34 MB of RSS per dispatch. */
  if (set != VK_NULL_HANDLE && !d->preset_set && ctx->vk.FreeDescriptorSets)
    ctx->vk.FreeDescriptorSets(ctx->device, pool, 1, &set);
  if (cmd != VK_NULL_HANDLE && ctx->vk.FreeCommandBuffers)
    ctx->vk.FreeCommandBuffers(ctx->device, cmd_pool, 1, &cmd);
  /* Shader module, pipeline layout, pipeline and descriptor-set layout live in
   * the context cache and are released with the context, not per call. */
  if (!cached) {
    ctx->vk.DestroyPipeline(ctx->device, pipeline, NULL);
    ctx->vk.DestroyPipelineLayout(ctx->device, pipeline_layout, NULL);
    ctx->vk.DestroyShaderModule(ctx->device, shader, NULL);
    ctx->vk.DestroyDescriptorSetLayout(ctx->device, layout, NULL);
  }
  return TVDB_OK;

fail_fence:
  if (fence) ctx->vk.DestroyFence(ctx->device, fence, NULL);
fail_cmdpool:
  /* cmd_pool is ctx->cmd_pool, owned by the context and released in
   * tvdb_gpu_context_destroy. Destroying it here would leave every later dispatch
   * allocating from a dead pool and double free it at context teardown, turning
   * one transient device error into undefined behaviour for the rest of the
   * context's life. Only free the command buffer this call allocated. */
  if (ctx->vk.FreeCommandBuffers && cmd != VK_NULL_HANDLE && cmd_pool != VK_NULL_HANDLE)
    ctx->vk.FreeCommandBuffers(ctx->device, cmd_pool, 1, &cmd);
fail_pool:
  if (set != VK_NULL_HANDLE && pool && ctx->vk.FreeDescriptorSets)
    ctx->vk.FreeDescriptorSets(ctx->device, pool, 1, &set);
  if (!cached) {
    if (pipeline) ctx->vk.DestroyPipeline(ctx->device, pipeline, NULL);
    if (pipeline_layout) ctx->vk.DestroyPipelineLayout(ctx->device, pipeline_layout, NULL);
    if (shader) ctx->vk.DestroyShaderModule(ctx->device, shader, NULL);
    if (layout) ctx->vk.DestroyDescriptorSetLayout(ctx->device, layout, NULL);
  }
  return err ? err->status : TVDB_ERROR_IO;
}

static const char kTvdbCudaSource[] =
"// ---- PDE stencils. Mirrors the CPU reference exactly: reads clamp at the\n"
"// grid edge, laplacian is (sum of 6 neighbours - 6*centre) * scale, and the\n"
"// central differences are (f(+1) - f(-1)) * scale with scale = 1/(2h).\n"
"__device__ __forceinline__ int tvdb_c_cl(int v, int n) { return v < 0 ? 0 : (v > n - 1 ? n - 1 : v); }\n"
"extern \"C\" __global__ void tvdb_cuda_stencil_scalar_scalar(const float* src, float* dst,\n"
"                                                          int nx, int ny, int nz, int op, float scale) {\n"
"  int ix = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  int iy = blockIdx.y * blockDim.y + threadIdx.y;\n"
"  int iz = blockIdx.z;\n"
"  if (ix >= nx || iy >= ny || iz >= nz) return;\n"
"  #define TVDB_C_AT(X, Y, Z) src[(size_t)(tvdb_c_cl((Z), nz) * ny + tvdb_c_cl((Y), ny)) * nx + tvdb_c_cl((X), nx)]\n"
"  float v;\n"
"  if (op == 0) {\n"
"    float s = TVDB_C_AT(ix-1, iy, iz) + TVDB_C_AT(ix+1, iy, iz)\n"
"            + TVDB_C_AT(ix, iy-1, iz) + TVDB_C_AT(ix, iy+1, iz)\n"
"            + TVDB_C_AT(ix, iy, iz-1) + TVDB_C_AT(ix, iy, iz+1);\n"
"    v = (s - 6.0f * TVDB_C_AT(ix, iy, iz)) * scale;\n"
"  } else if (op == 1) v = (TVDB_C_AT(ix+1, iy, iz) - TVDB_C_AT(ix-1, iy, iz)) * scale;\n"
"  else if (op == 2) v = (TVDB_C_AT(ix, iy+1, iz) - TVDB_C_AT(ix, iy-1, iz)) * scale;\n"
"  else v = (TVDB_C_AT(ix, iy, iz+1) - TVDB_C_AT(ix, iy, iz-1)) * scale;\n"
"  #undef TVDB_C_AT\n"
"  dst[(size_t)iz * ny * nx + (size_t)iy * nx + ix] = v;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_mean_curvature_flow(const float* src, float* dst,\n"
"                                                      int nx, int ny, int nz, float h, float dt) {\n"
"  int ix = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  int iy = blockIdx.y * blockDim.y + threadIdx.y;\n"
"  int iz = blockIdx.z;\n"
"  if (ix >= nx || iy >= ny || iz >= nz) return;\n"
"  size_t i = (size_t)iz * ny * nx + (size_t)iy * nx + ix;\n"
"  if (ix < 1 || iy < 1 || iz < 1 || ix > nx-2 || iy > ny-2 || iz > nz-2) { dst[i] = src[i]; return; }\n"
"  float h2 = h*h, i2h = 1.0f/(2.0f*h), i4h2 = 1.0f/(4.0f*h2);\n"
"  float c0 = src[i];\n"
"  float px = (src[i+1] - src[i-1]) * i2h;\n"
"  float py = (src[i+nx] - src[i-nx]) * i2h;\n"
"  int sl = nx*ny;\n"
"  float pz = (src[i+sl] - src[i-sl]) * i2h;\n"
"  float g2 = px*px + py*py + pz*pz;\n"
"  if (g2 < 1e-12f) { dst[i] = c0; return; }\n"
"  float pxx = (src[i+1] - 2.0f*c0 + src[i-1]) / h2;\n"
"  float pyy = (src[i+nx] - 2.0f*c0 + src[i-nx]) / h2;\n"
"  float pzz = (src[i+sl] - 2.0f*c0 + src[i-sl]) / h2;\n"
"  float pxy = (src[i+1+nx] - src[i-1+nx] - src[i+1-nx] + src[i-1-nx]) * i4h2;\n"
"  float pyz = (src[i+nx+sl] - src[i-nx+sl] - src[i+nx-sl] + src[i-nx-sl]) * i4h2;\n"
"  float pxz = (src[i+1+sl] - src[i-1+sl] - src[i+1-sl] + src[i-1-sl]) * i4h2;\n"
"  float num = pxx*(py*py + pz*pz) + pyy*(px*px + pz*pz) + pzz*(px*px + py*py)\n"
"            - 2.0f*(pxy*px*py + pyz*py*pz + pxz*px*pz);\n"
"  dst[i] = c0 + dt * (num / g2);\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_stencil_scalar_d(const double* src, double* dst,\n"
"                                                        int nx, int ny, int nz, int op, double scale) {\n"
"  int ix = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  int iy = blockIdx.y * blockDim.y + threadIdx.y;\n"
"  int iz = blockIdx.z;\n"
"  if (ix >= nx || iy >= ny || iz >= nz) return;\n"
"  #define TVDB_CD_AT(X, Y, Z) src[(size_t)(tvdb_c_cl((Z), nz) * ny + tvdb_c_cl((Y), ny)) * nx + tvdb_c_cl((X), nx)]\n"
"  double v;\n"
"  if (op == 0) {\n"
"    double t = TVDB_CD_AT(ix-1, iy, iz) + TVDB_CD_AT(ix+1, iy, iz)\n"
"            + TVDB_CD_AT(ix, iy-1, iz) + TVDB_CD_AT(ix, iy+1, iz)\n"
"            + TVDB_CD_AT(ix, iy, iz-1) + TVDB_CD_AT(ix, iy, iz+1);\n"
"    v = (t - 6.0 * TVDB_CD_AT(ix, iy, iz)) * scale;\n"
"  } else if (op == 1) v = (TVDB_CD_AT(ix+1, iy, iz) - TVDB_CD_AT(ix-1, iy, iz)) * scale;\n"
"  else if (op == 2) v = (TVDB_CD_AT(ix, iy+1, iz) - TVDB_CD_AT(ix, iy-1, iz)) * scale;\n"
"  else v = (TVDB_CD_AT(ix, iy, iz+1) - TVDB_CD_AT(ix, iy, iz-1)) * scale;\n"
"  #undef TVDB_CD_AT\n"
"  dst[(size_t)iz * ny * nx + (size_t)iy * nx + ix] = v;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_sample_d(const double* grid, const double* pts, double* out_values,\n"
"                                              int nx, int ny, int nz, double ox, double oy, double oz,\n"
"                                              double vs, size_t npts) {\n"
"  size_t idx = (size_t)blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (idx >= npts) return;\n"
"  double px = pts[3*idx], py = pts[3*idx+1], pz = pts[3*idx+2];\n"
"  double fxv = (px - ox) / vs - 0.5, fyv = (py - oy) / vs - 0.5, fzv = (pz - oz) / vs - 0.5;\n"
"  fxv=isnan(fxv)?0:(fxv < -1 ? -1 : (fxv >= nx ? nx-1 : fxv));\n"
"  fyv=isnan(fyv)?0:(fyv < -1 ? -1 : (fyv >= ny ? ny-1 : fyv));\n"
"  fzv=isnan(fzv)?0:(fzv < -1 ? -1 : (fzv >= nz ? nz-1 : fzv));\n"
"  int ix = (int)floor(fxv), iy = (int)floor(fyv), iz = (int)floor(fzv);\n"
"  double fx = fxv - (double)ix, fy = fyv - (double)iy, fz = fzv - (double)iz;\n"
"  #define TVDB_SD_F(X, Y, Z) grid[(size_t)(tvdb_c_cl((Z), nz) * ny + tvdb_c_cl((Y), ny)) * nx + tvdb_c_cl((X), nx)]\n"
"  double c000 = TVDB_SD_F(ix, iy, iz), c100 = TVDB_SD_F(ix+1, iy, iz);\n"
"  double c010 = TVDB_SD_F(ix, iy+1, iz), c110 = TVDB_SD_F(ix+1, iy+1, iz);\n"
"  double c001 = TVDB_SD_F(ix, iy, iz+1), c101 = TVDB_SD_F(ix+1, iy, iz+1);\n"
"  double c011 = TVDB_SD_F(ix, iy+1, iz+1), c111 = TVDB_SD_F(ix+1, iy+1, iz+1);\n"
"  #undef TVDB_SD_F\n"
"  double c00 = c000 * (1.0 - fx) + c100 * fx, c10 = c010 * (1.0 - fx) + c110 * fx;\n"
"  double c01 = c001 * (1.0 - fx) + c101 * fx, c11 = c011 * (1.0 - fx) + c111 * fx;\n"
"  double c0 = c00 * (1.0 - fy) + c10 * fy, c1 = c01 * (1.0 - fy) + c11 * fy;\n"
"  out_values[idx] = c0 * (1.0 - fz) + c1 * fz;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_csg_d(const double* a, const double* b, double* dst,\n"
"                                            int nx, int ny, int nz, int op) {\n"
"  int ix = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  int iy = blockIdx.y * blockDim.y + threadIdx.y;\n"
"  int iz = blockIdx.z;\n"
"  if (ix >= nx || iy >= ny || iz >= nz) return;\n"
"  size_t i = ((size_t)iz * ny + iy) * nx + ix;\n"
"  double va = a[i], vb = b[i];\n"
"  /* Comparison form, not fmin/fmax: the CPU twin is `va < vb ? va : vb`, and\n"
"   * the two disagree on signed zero, which a zero-crossing field reaches. */\n"
"  dst[i] = op == 0 ? (va < vb ? va : vb)\n"
"                  : (op == 1 ? (va > vb ? va : vb) : (va > -vb ? va : -vb));\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_stencil_scalar_vec(const float* src, float* dst,\n"
"                                                        int nx, int ny, int nz, int op, float scale,\n"
"                                                        float ox, float oy, float oz, float vs) {\n"
"  int ix = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  int iy = blockIdx.y * blockDim.y + threadIdx.y;\n"
"  int iz = blockIdx.z;\n"
"  if (ix >= nx || iy >= ny || iz >= nz) return;\n"
"  #define TVDB_C_AT(X, Y, Z) src[(size_t)(tvdb_c_cl((Z), nz) * ny + tvdb_c_cl((Y), ny)) * nx + tvdb_c_cl((X), nx)]\n"
"  float gx = (TVDB_C_AT(ix+1, iy, iz) - TVDB_C_AT(ix-1, iy, iz)) * scale;\n"
"  float gy = (TVDB_C_AT(ix, iy+1, iz) - TVDB_C_AT(ix, iy-1, iz)) * scale;\n"
"  float gz = (TVDB_C_AT(ix, iy, iz+1) - TVDB_C_AT(ix, iy, iz-1)) * scale;\n"
"  size_t i = 3u * ((size_t)iz * ny * nx + (size_t)iy * nx + ix);\n"
"  if (op == 1) {\n"
"    float d = TVDB_C_AT(ix, iy, iz);\n"
"    float px = ox + ((float)ix + 0.5f) * vs;\n"
"    float py = oy + ((float)iy + 0.5f) * vs;\n"
"    float pz = oz + ((float)iz + 0.5f) * vs;\n"
"    dst[i+0] = px - d*gx; dst[i+1] = py - d*gy; dst[i+2] = pz - d*gz;\n"
"    #undef TVDB_C_AT\n"
"    return;\n"
"  }\n"
"  #undef TVDB_C_AT\n"
"  dst[i+0] = gx; dst[i+1] = gy; dst[i+2] = gz;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_stencil_vec_scalar(const float* src, float* dst,\n"
"                                                        int nx, int ny, int nz, int op, float scale) {\n"
"  int ix = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  int iy = blockIdx.y * blockDim.y + threadIdx.y;\n"
"  int iz = blockIdx.z;\n"
"  if (ix >= nx || iy >= ny || iz >= nz) return;\n"
"  (void)op;\n"
"  #define TVDB_C_AT(X, Y, Z, C) src[3u * (((size_t)tvdb_c_cl((Z), nz) * ny + tvdb_c_cl((Y), ny)) * nx + tvdb_c_cl((X), nx)) + (C)]\n"
"  float dvx = (TVDB_C_AT(ix+1, iy, iz, 0) - TVDB_C_AT(ix-1, iy, iz, 0)) * scale;\n"
"  float dvy = (TVDB_C_AT(ix, iy+1, iz, 1) - TVDB_C_AT(ix, iy-1, iz, 1)) * scale;\n"
"  float dvz = (TVDB_C_AT(ix, iy, iz+1, 2) - TVDB_C_AT(ix, iy, iz-1, 2)) * scale;\n"
"  size_t oi = (size_t)iz * ny * nx + (size_t)iy * nx + ix;\n"
"  if (op == 1) {\n"
"    float x = TVDB_C_AT(ix, iy, iz, 0), y = TVDB_C_AT(ix, iy, iz, 1), z = TVDB_C_AT(ix, iy, iz, 2);\n"
"    dst[oi] = sqrtf(x*x + y*y + z*z);\n"
"    #undef TVDB_C_AT\n"
"    return;\n"
"  }\n"
"  #undef TVDB_C_AT\n"
"  dst[oi] = dvx + dvy + dvz;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_stencil_vec_vec(const float* src, float* dst,\n"
"                                                    int nx, int ny, int nz, int op, float scale) {\n"
"  int ix = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  int iy = blockIdx.y * blockDim.y + threadIdx.y;\n"
"  int iz = blockIdx.z;\n"
"  if (ix >= nx || iy >= ny || iz >= nz) return;\n"
"  (void)op;\n"
"  #define TVDB_C_AT(X, Y, Z, C) src[3u * (((size_t)tvdb_c_cl((Z), nz) * ny + tvdb_c_cl((Y), ny)) * nx + tvdb_c_cl((X), nx)) + (C)]\n"
"  float dvz_dy = (TVDB_C_AT(ix, iy+1, iz, 2) - TVDB_C_AT(ix, iy-1, iz, 2)) * scale;\n"
"  float dvy_dz = (TVDB_C_AT(ix, iy, iz+1, 1) - TVDB_C_AT(ix, iy, iz-1, 1)) * scale;\n"
"  float dvx_dz = (TVDB_C_AT(ix, iy, iz+1, 0) - TVDB_C_AT(ix, iy, iz-1, 0)) * scale;\n"
"  float dvz_dx = (TVDB_C_AT(ix+1, iy, iz, 2) - TVDB_C_AT(ix-1, iy, iz, 2)) * scale;\n"
"  float dvy_dx = (TVDB_C_AT(ix+1, iy, iz, 1) - TVDB_C_AT(ix-1, iy, iz, 1)) * scale;\n"
"  float dvx_dy = (TVDB_C_AT(ix, iy+1, iz, 0) - TVDB_C_AT(ix, iy-1, iz, 0)) * scale;\n"
"  size_t i = 3u * ((size_t)iz * ny * nx + (size_t)iy * nx + ix);\n"
"  if (op == 1) {\n"
"    float x = TVDB_C_AT(ix, iy, iz, 0), y = TVDB_C_AT(ix, iy, iz, 1), z = TVDB_C_AT(ix, iy, iz, 2);\n"
"    float m = sqrtf(x*x + y*y + z*z);\n"
"    #undef TVDB_C_AT\n"
"    if (m > 0.0f) { dst[i+0] = x/m; dst[i+1] = y/m; dst[i+2] = z/m; }\n"
"    else         { dst[i+0] = 0.0f; dst[i+1] = 0.0f; dst[i+2] = 0.0f; }\n"
"    return;\n"
"  }\n"
"  #undef TVDB_C_AT\n"
"  dst[i+0] = dvz_dy - dvy_dz;\n"
"  dst[i+1] = dvx_dz - dvz_dx;\n"
"  dst[i+2] = dvy_dx - dvx_dy;\n"
"}\n"
"struct tvdb_float4 { float x, y, z, w; };\n"
"struct tvdb_int4 { int x, y, z, w; };\n"
"extern \"C\" __global__ void tvdb_cuda_csg(const float* a, const float* b, float* out_values, unsigned int count, int op) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= count) return;\n"
"  float va = a[i];\n"
"  float vb = b[i];\n"
"  out_values[i] = op == 0 ? fminf(va, vb) : (op == 1 ? fmaxf(va, vb) : fmaxf(va, -vb));\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_sdf_sphere(float* out_values, int nx, int ny, int nz,\n"
"                                                 float ox, float oy, float oz, float vs,\n"
"                                                 float cx, float cy, float cz, float radius,\n"
"                                                 float background, unsigned int count) {\n"
"  unsigned int idx = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (idx >= count) return;\n"
"  int iz = (int)(idx / (unsigned int)(nx * ny));\n"
"  int rem = (int)(idx - (unsigned int)(iz * nx * ny));\n"
"  int iy = rem / nx;\n"
"  int ix = rem - iy * nx;\n"
"  float wx = ox + ((float)ix + 0.5f) * vs;\n"
"  float wy = oy + ((float)iy + 0.5f) * vs;\n"
"  float wz = oz + ((float)iz + 0.5f) * vs;\n"
"  float dx = wx - cx, dy = wy - cy, dz = wz - cz;\n"
"  float d = sqrtf(dx * dx + dy * dy + dz * dz) - radius;\n"
"  out_values[idx] = fminf(fmaxf(d, -background), background);\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_sdf_box(float* out_values, int nx, int ny, int nz,\n"
"                                              float ox, float oy, float oz, float vs,\n"
"                                              float cx, float cy, float cz,\n"
"                                              float hx, float hy, float hz,\n"
"                                              float background, unsigned int count) {\n"
"  unsigned int idx = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (idx >= count) return;\n"
"  int iz = (int)(idx / (unsigned int)(nx * ny));\n"
"  int rem = (int)(idx - (unsigned int)(iz * nx * ny));\n"
"  int iy = rem / nx;\n"
"  int ix = rem - iy * nx;\n"
"  float wx = ox + ((float)ix + 0.5f) * vs;\n"
"  float wy = oy + ((float)iy + 0.5f) * vs;\n"
"  float wz = oz + ((float)iz + 0.5f) * vs;\n"
"  float qx = fabsf(wx - cx) - hx;\n"
"  float qy = fabsf(wy - cy) - hy;\n"
"  float qz = fabsf(wz - cz) - hz;\n"
"  float oxv = fmaxf(qx, 0.0f), oyv = fmaxf(qy, 0.0f), ozv = fmaxf(qz, 0.0f);\n"
"  float outside = sqrtf(oxv * oxv + oyv * oyv + ozv * ozv);\n"
"  float inside = fminf(fmaxf(qx, fmaxf(qy, qz)), 0.0f);\n"
"  float d = outside + inside;\n"
"  out_values[idx] = fminf(fmaxf(d, -background), background);\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_sdf_torus(float* out_values, int nx, int ny, int nz,\n"
"                                                float ox, float oy, float oz, float vs,\n"
"                                                float cx, float cy, float cz,\n"
"                                                float major_radius, float minor_radius,\n"
"                                                float background, unsigned int count) {\n"
"  unsigned int idx = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (idx >= count) return;\n"
"  int iz = (int)(idx / (unsigned int)(nx * ny));\n"
"  int rem = (int)(idx - (unsigned int)(iz * nx * ny));\n"
"  int iy = rem / nx;\n"
"  int ix = rem - iy * nx;\n"
"  float wx = ox + ((float)ix + 0.5f) * vs;\n"
"  float wy = oy + ((float)iy + 0.5f) * vs;\n"
"  float wz = oz + ((float)iz + 0.5f) * vs;\n"
"  float dx = wx - cx, dy = wy - cy, dz = wz - cz;\n"
"  float qx = sqrtf(dx * dx + dz * dz) - major_radius;\n"
"  float d = sqrtf(qx * qx + dy * dy) - minor_radius;\n"
"  out_values[idx] = fminf(fmaxf(d, -background), background);\n"
"}\n"
"__device__ float tvdb_fetch(const float* grid, int nx, int ny, int nz, int x, int y, int z) {\n"
"  x = x < 0 ? 0 : (x >= nx ? nx - 1 : x);\n"
"  y = y < 0 ? 0 : (y >= ny ? ny - 1 : y);\n"
"  z = z < 0 ? 0 : (z >= nz ? nz - 1 : z);\n"
"  return grid[x + nx * (y + ny * z)];\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_sample(const float* grid, const tvdb_float4* pts, float* out_values,\n"
"                                             int nx, int ny, int nz, float ox, float oy, float oz, float vs,\n"
"                                             unsigned int count) {\n"
"  unsigned int idx = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (idx >= count) return;\n"
"  tvdb_float4 p = pts[idx];\n"
"  float fx = (p.x - ox) / vs - 0.5f;\n"
"  float fy = (p.y - oy) / vs - 0.5f;\n"
"  float fz = (p.z - oz) / vs - 0.5f;\n"
"  fx=isnan(fx)?0:(fx < -1 ? -1 : (fx >= nx ? nx-1 : fx));\n"
"  fy=isnan(fy)?0:(fy < -1 ? -1 : (fy >= ny ? ny-1 : fy));\n"
"  fz=isnan(fz)?0:(fz < -1 ? -1 : (fz >= nz ? nz-1 : fz));\n"
"  int ix = (int)floorf(fx); int iy = (int)floorf(fy); int iz = (int)floorf(fz);\n"
"  float tx = fx - (float)ix; float ty = fy - (float)iy; float tz = fz - (float)iz;\n"
"  float c000 = tvdb_fetch(grid, nx, ny, nz, ix, iy, iz);\n"
"  float c100 = tvdb_fetch(grid, nx, ny, nz, ix+1, iy, iz);\n"
"  float c010 = tvdb_fetch(grid, nx, ny, nz, ix, iy+1, iz);\n"
"  float c110 = tvdb_fetch(grid, nx, ny, nz, ix+1, iy+1, iz);\n"
"  float c001 = tvdb_fetch(grid, nx, ny, nz, ix, iy, iz+1);\n"
"  float c101 = tvdb_fetch(grid, nx, ny, nz, ix+1, iy, iz+1);\n"
"  float c011 = tvdb_fetch(grid, nx, ny, nz, ix, iy+1, iz+1);\n"
"  float c111 = tvdb_fetch(grid, nx, ny, nz, ix+1, iy+1, iz+1);\n"
"  float c00 = c000 + (c100 - c000) * tx;\n"
"  float c10 = c010 + (c110 - c010) * tx;\n"
"  float c01 = c001 + (c101 - c001) * tx;\n"
"  float c11 = c011 + (c111 - c011) * tx;\n"
"  float c0 = c00 + (c10 - c00) * ty;\n"
"  float c1 = c01 + (c11 - c01) * ty;\n"
"  out_values[idx] = c0 + (c1 - c0) * tz;\n"
"}\n"
"__device__ float tvdb_quad1(float v0, float v1, float v2, float w) {\n"
"  float a = 0.5f * (v0 + v2) - v1;\n"
"  float b = 0.5f * (v2 - v0);\n"
"  return w * (w * a + b) + v1;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_sample_quadratic(const float* grid, const tvdb_float4* pts, float* out_values,\n"
"                                             int nx, int ny, int nz, float ox, float oy, float oz, float vs,\n"
"                                             unsigned int count) {\n"
"  unsigned int idx = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (idx >= count) return;\n"
"  tvdb_float4 p = pts[idx];\n"
"  float cx = (p.x - ox) / vs - 0.5f;\n"
"  float cy = (p.y - oy) / vs - 0.5f;\n"
"  float cz = (p.z - oz) / vs - 0.5f;\n"
"  cx=isnan(cx)?0:(cx < -1 ? -1 : (cx >= nx ? nx-1 : cx));\n"
"  cy=isnan(cy)?0:(cy < -1 ? -1 : (cy >= ny ? ny-1 : cy));\n"
"  cz=isnan(cz)?0:(cz < -1 ? -1 : (cz >= nz ? nz-1 : cz));\n"
"  int ix = (int)floorf(cx); int iy = (int)floorf(cy); int iz = (int)floorf(cz);\n"
"  float tu = cx - (float)ix; float tv = cy - (float)iy; float tw = cz - (float)iz;\n"
"  float vx[3];\n"
"  for (int dx = 0; dx < 3; ++dx) {\n"
"    float vy[3];\n"
"    for (int dy = 0; dy < 3; ++dy) {\n"
"      float a = tvdb_fetch(grid, nx, ny, nz, ix - 1 + dx, iy - 1 + dy, iz - 1);\n"
"      float b = tvdb_fetch(grid, nx, ny, nz, ix - 1 + dx, iy - 1 + dy, iz);\n"
"      float cc = tvdb_fetch(grid, nx, ny, nz, ix - 1 + dx, iy - 1 + dy, iz + 1);\n"
"      vy[dy] = tvdb_quad1(a, b, cc, tw);\n"
"    }\n"
"    vx[dx] = tvdb_quad1(vy[0], vy[1], vy[2], tv);\n"
"  }\n"
"  out_values[idx] = tvdb_quad1(vx[0], vx[1], vx[2], tu);\n"
"}\n"
"__device__ float tvdb_sparse_lookup(const tvdb_int4* coords, const float* values, unsigned int count, long long x, long long y, long long z, float pad_value) {\n"
"  for (unsigned int i = 0; i < count; ++i) {\n"
"    tvdb_int4 c = coords[i];\n"
"    if (c.x == x && c.y == y && c.z == z) return values[i];\n"
"  }\n"
"  return pad_value;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_sparse_conv(const tvdb_int4* coords, const float* values, const float* kernel,\n"
"                                                  float* out_values, unsigned int count, int kx, int ky, int kz,\n"
"                                                  float pad_value) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= count) return;\n"
"  tvdb_int4 c = coords[i];\n"
"  int ax = kx / 2; int ay = ky / 2; int az = kz / 2;\n"
"  float acc = 0.0f;\n"
"  for (int dk = 0; dk < kz; ++dk) {\n"
"    for (int dj = 0; dj < ky; ++dj) {\n"
"      for (int di = 0; di < kx; ++di) {\n"
"        int ki = (dk * ky + dj) * kx + di;\n"
"        acc += kernel[ki] * tvdb_sparse_lookup(coords, values, count, (long long)c.x + di - ax, (long long)c.y + dj - ay, (long long)c.z + dk - az, pad_value);\n"
"      }\n"
"    }\n"
"  }\n"
"  out_values[i] = acc;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_sparse_conv_map(const int* map4, const tvdb_int4* coords,\n"
"                                                        const float* values, const float* kernel,\n"
"                                                        float* out_values, unsigned int count, int kx,\n"
"                                                        int ky, int kz, float pad_value,\n"
"                                                        unsigned int cap, unsigned int mask) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= count) return;\n"
"  tvdb_int4 c = coords[i];\n"
"  int ax = kx / 2, ay = ky / 2, az = kz / 2;\n"
"  float acc = 0.0f;\n"
"  for (int dk = 0; dk < kz; ++dk)\n"
"    for (int dj = 0; dj < ky; ++dj)\n"
"      for (int di = 0; di < kx; ++di) {\n"
"        long long qx = (long long)c.x + (di-ax), qy = (long long)c.y + (dj-ay), qz = (long long)c.z + (dk-az);\n"
"        if(qx < (-2147483647LL-1) || qx > 2147483647LL || qy < (-2147483647LL-1) || qy > 2147483647LL || qz < (-2147483647LL-1) || qz > 2147483647LL) { acc += kernel[(dk*ky+dj)*kx+di]*pad_value; continue; }\n"
"        unsigned int hh = ((unsigned int)qx * 73856093u) ^ ((unsigned int)qy * 19349663u)\n"
"                         ^ ((unsigned int)qz * 83492791u);\n"
"        unsigned int slot = hh & mask;\n"
"        float got = pad_value;\n"
"        for (unsigned int pr = 0; pr < cap; ++pr) {\n"
"          int v = map4[slot*4u+3u];\n"
"          if (v == 0) break;\n"
"          if (map4[slot*4u+0u] == qx && map4[slot*4u+1u] == qy && map4[slot*4u+2u] == qz) {\n"
"            got = values[v - 1];\n"
"            break;\n"
"          }\n"
"          slot = (slot + 1u) & mask;\n"
"        }\n"
"        acc += kernel[(dk*ky + dj)*kx + di] * got;\n"
"      }\n"
"  out_values[i] = acc;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_sparse_index_scatter(const tvdb_int4* coords, int* idx_grid,\n"
"    int bx, int by, int bz, int dx, int dy, int dz, unsigned int count) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= count) return;\n"
"  tvdb_int4 c = coords[i];\n"
"  int lx = c.x - bx, ly = c.y - by, lz = c.z - bz;\n"
"  int* cell=&idx_grid[(lz*dy+ly)*dx+lx]; int old=atomicCAS(cell,-1,(int)i); if(old>=0) atomicMin(cell,(int)i);\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_sparse_conv_dense(const tvdb_int4* coords, const float* values,\n"
"    const float* kernel, float* out_values, const int* idx_grid, unsigned int count, int kx, int ky, int kz,\n"
"    float pad_value, int bx, int by, int bz, int dx, int dy, int dz) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= count) return;\n"
"  tvdb_int4 c = coords[i];\n"
"  int ax = kx / 2, ay = ky / 2, az = kz / 2;\n"
"  float acc = 0.0f;\n"
"  for (int dk = 0; dk < kz; ++dk) {\n"
"    for (int dj = 0; dj < ky; ++dj) {\n"
"      for (int di = 0; di < kx; ++di) {\n"
"        int lx = (long long)c.x + di - ax - bx, ly = (long long)c.y + dj - ay - by, lz = (long long)c.z + dk - az - bz;\n"
"        float val;\n"
"        if (lx < 0 || lx >= dx || ly < 0 || ly >= dy || lz < 0 || lz >= dz) val = pad_value;\n"
"        else { int idx = idx_grid[(lz * dy + ly) * dx + lx]; val = idx >= 0 ? values[idx] : pad_value; }\n"
"        int ki = (dk * ky + dj) * kx + di;\n"
"        acc += kernel[ki] * val;\n"
"      }\n"
"    }\n"
"  }\n"
"  out_values[i] = acc;\n"
"}\n"
"__device__ int tvdb_active_index(const tvdb_int4* active, unsigned int na, long long x, long long y, long long z) {\n"
"  if(x < (-2147483647LL-1) || x > 2147483647LL || y < (-2147483647LL-1) || y > 2147483647LL || z < (-2147483647LL-1) || z > 2147483647LL) return -1;\n"
"  for (unsigned int i = 0; i < na; ++i) {\n"
"    tvdb_int4 c = active[i];\n"
"    if (c.x == x && c.y == y && c.z == z) return (int)i;\n"
"  }\n"
"  return -1;\n"
"}\n"
"__device__ __forceinline__ int tvdb_map_probe(const int* keys, const int* values,\n"
"                                             unsigned int cap, unsigned int mask,\n"
"                                             long long qx, long long qy, long long qz) {\n"
"  unsigned int h = ((unsigned int)qx * 73856093u) ^ ((unsigned int)qy * 19349663u)\n"
"                 ^ ((unsigned int)qz * 83492791u);\n"
"  unsigned int slot = h & mask;\n"
"  for (unsigned int p = 0; p < cap; ++p) {\n"
"    int v = values[slot];\n"
"    if (v == 0) return -1;\n"
"    if (keys[slot*3u+0u] == qx && keys[slot*3u+1u] == qy && keys[slot*3u+2u] == qz) return v - 1;\n"
"    slot = (slot + 1u) & mask;\n"
"  }\n"
"  return -1;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_index_probe(const int* keys, const int* values, int* out_index,\n"
"                                                  const int* query, unsigned int nq,\n"
"                                                  unsigned int cap, unsigned int mask) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= nq) return;\n"
"  out_index[i] = tvdb_map_probe(keys, values, cap, mask, query[3*i+0], query[3*i+1], query[3*i+2]);\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_points_in_grid_probe(const int* keys, const int* values, int* out_index,\n"
"                                                            const tvdb_float4* pts, unsigned int np,\n"
"                                                            unsigned int cap, unsigned int mask,\n"
"                                                            float vx, float vy, float vz,\n"
"                                                            float ox, float oy, float oz) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= np) return;\n"
"  tvdb_float4 p = pts[i];\n"
"  int qx = (int)floorf((p.x - ox) / vx);\n"
"  int qy = (int)floorf((p.y - oy) / vy);\n"
"  int qz = (int)floorf((p.z - oz) / vz);\n"
"  out_index[i] = tvdb_map_probe(keys, values, cap, mask, qx, qy, qz);\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_neighbor_counts_probe(const int* keys, const int* values,\n"
"                                                          int* out_counts, const tvdb_int4* act,\n"
"                                                          unsigned int na, int connectivity,\n"
"                                                          unsigned int cap, unsigned int mask) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= na) return;\n"
"  tvdb_int4 c = act[i];\n"
"  int cnt = 0;\n"
"  if (connectivity == 26) {\n"
"    for (int dz = -1; dz <= 1; ++dz)\n"
"      for (int dy = -1; dy <= 1; ++dy)\n"
"        for (int dx = -1; dx <= 1; ++dx) {\n"
"          if (dx == 0 && dy == 0 && dz == 0) continue;\n"
"          if (tvdb_map_probe(keys, values, cap, mask, (long long)c.x+dx, (long long)c.y+dy, (long long)c.z+dz) >= 0) ++cnt;\n"
"        }\n"
"  } else {\n"
"    const int o[6][3] = {{1,0,0},{-1,0,0},{0,1,0},{0,-1,0},{0,0,1},{0,0,-1}};\n"
"    for (int k = 0; k < 6; ++k)\n"
"      if (tvdb_map_probe(keys, values, cap, mask, (long long)c.x+o[k][0], (long long)c.y+o[k][1], (long long)c.z+o[k][2]) >= 0) ++cnt;\n"
"  }\n"
"  out_counts[i] = cnt;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_ijk_to_index(const tvdb_int4* active, const tvdb_int4* query,\n"
"                                                   int* out_index, unsigned int na, unsigned int nq) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= nq) return;\n"
"  tvdb_int4 q = query[i];\n"
"  out_index[i] = tvdb_active_index(active, na, q.x, q.y, q.z);\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_points_in_grid(const tvdb_int4* active, const tvdb_float4* pts,\n"
"                                                     int* out_index, unsigned int na, unsigned int np,\n"
"                                                     float vx, float vy, float vz, float ox, float oy, float oz) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= np) return;\n"
"  tvdb_float4 p = pts[i];\n"
"  int x = (int)floorf((p.x - ox) / vx);\n"
"  int y = (int)floorf((p.y - oy) / vy);\n"
"  int z = (int)floorf((p.z - oz) / vz);\n"
"  out_index[i] = tvdb_active_index(active, na, x, y, z);\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_neighbor_counts(const tvdb_int4* active, int* out_counts,\n"
"                                                      unsigned int na, int connectivity) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= na) return;\n"
"  tvdb_int4 c = active[i];\n"
"  int cnt = 0;\n"
"  if (connectivity == 26) {\n"
"    for (int dz = -1; dz <= 1; ++dz)\n"
"      for (int dy = -1; dy <= 1; ++dy)\n"
"        for (int dx = -1; dx <= 1; ++dx) {\n"
"          if (dx == 0 && dy == 0 && dz == 0) continue;\n"
"          if (tvdb_active_index(active, na, (long long)c.x + dx, (long long)c.y + dy, (long long)c.z + dz) >= 0) ++cnt;\n"
"        }\n"
"  } else {\n"
"    const int o[6][3] = {{1,0,0},{-1,0,0},{0,1,0},{0,-1,0},{0,0,1},{0,0,-1}};\n"
"    for (int t = 0; t < 6; ++t)\n"
"      if (tvdb_active_index(active, na, (long long)c.x + o[t][0], (long long)c.y + o[t][1], (long long)c.z + o[t][2]) >= 0) ++cnt;\n"
"  }\n"
"  out_counts[i] = cnt;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_morph(const float* in_data, float* out_data,\n"
"                                            int nx, int ny, int nz, int is_dilate) {\n"
"  unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  unsigned int total = (unsigned int)(nx * ny * nz);\n"
"  if (gid >= total) return;\n"
"  int iz = (int)(gid / (unsigned int)(nx * ny));\n"
"  int rem = (int)(gid - (unsigned int)(iz * nx * ny));\n"
"  int iy = rem / nx; int ix = rem - iy * nx;\n"
"  float r = in_data[gid];\n"
"  float xm = tvdb_fetch(in_data, nx, ny, nz, ix - 1, iy, iz);\n"
"  float xp = tvdb_fetch(in_data, nx, ny, nz, ix + 1, iy, iz);\n"
"  float ym = tvdb_fetch(in_data, nx, ny, nz, ix, iy - 1, iz);\n"
"  float yp = tvdb_fetch(in_data, nx, ny, nz, ix, iy + 1, iz);\n"
"  float zm = tvdb_fetch(in_data, nx, ny, nz, ix, iy, iz - 1);\n"
"  float zp = tvdb_fetch(in_data, nx, ny, nz, ix, iy, iz + 1);\n"
"  if (is_dilate != 0) {\n"
"    r = fminf(r, fminf(fminf(xm, xp), fminf(fminf(ym, yp), fminf(zm, zp))));\n"
"  } else {\n"
"    r = fmaxf(r, fmaxf(fmaxf(xm, xp), fmaxf(fmaxf(ym, yp), fmaxf(zm, zp))));\n"
"  }\n"
"  out_data[gid] = r;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_prune(float* data, unsigned int count,\n"
"                                            float background, float tolerance) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= count) return;\n"
"  if (fabsf(data[i] - background) <= tolerance) data[i] = background;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_coarsen(const float* in_data, float* out_data,\n"
"                                              int inx, int iny, int inz, int onx, int ony, int onz, int factor) {\n"
"  unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  unsigned int total = (unsigned int)(onx * ony * onz);\n"
"  if (gid >= total) return;\n"
"  int oz = (int)(gid / (unsigned int)(onx * ony));\n"
"  int rem = (int)(gid - (unsigned int)(oz * onx * ony));\n"
"  int oy = rem / onx; int ox = rem - oy * onx;\n"
"  float sum = 0.0f; int count = 0;\n"
"  for (int dz = 0; dz < factor; ++dz) { int sz = oz * factor + dz; if (sz >= inz) break;\n"
"    for (int dy = 0; dy < factor; ++dy) { int sy = oy * factor + dy; if (sy >= iny) break;\n"
"      for (int dx = 0; dx < factor; ++dx) { int sx = ox * factor + dx; if (sx >= inx) break;\n"
"        sum += in_data[(sz * iny + sy) * inx + sx]; ++count; } } }\n"
"  out_data[gid] = count > 0 ? sum / (float)count : 0.0f;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_refine(const float* in_data, float* out_data,\n"
"                                             int inx, int iny, int inz, int onx, int ony, int onz,\n"
"                                             float iox, float ioy, float ioz, float ivs,\n"
"                                             float oox, float ooy, float ooz, float ovs) {\n"
"  unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  unsigned int total = (unsigned int)(onx * ony * onz);\n"
"  if (gid >= total) return;\n"
"  int oz = (int)(gid / (unsigned int)(onx * ony));\n"
"  int rem = (int)(gid - (unsigned int)(oz * onx * ony));\n"
"  int oy = rem / onx; int ox = rem - oy * onx;\n"
"  float wx = oox + ((float)ox + 0.5f) * ovs;\n"
"  float wy = ooy + ((float)oy + 0.5f) * ovs;\n"
"  float wz = ooz + ((float)oz + 0.5f) * ovs;\n"
"  float fx = (wx - iox) / ivs - 0.5f;\n"
"  float fy = (wy - ioy) / ivs - 0.5f;\n"
"  float fz = (wz - ioz) / ivs - 0.5f;\n"
"  int ix = (int)floorf(fx), iy = (int)floorf(fy), iz = (int)floorf(fz);\n"
"  float tx = fx - (float)ix, ty = fy - (float)iy, tz = fz - (float)iz;\n"
"  float c000 = tvdb_fetch(in_data, inx, iny, inz, ix, iy, iz);\n"
"  float c100 = tvdb_fetch(in_data, inx, iny, inz, ix+1, iy, iz);\n"
"  float c010 = tvdb_fetch(in_data, inx, iny, inz, ix, iy+1, iz);\n"
"  float c110 = tvdb_fetch(in_data, inx, iny, inz, ix+1, iy+1, iz);\n"
"  float c001 = tvdb_fetch(in_data, inx, iny, inz, ix, iy, iz+1);\n"
"  float c101 = tvdb_fetch(in_data, inx, iny, inz, ix+1, iy, iz+1);\n"
"  float c011 = tvdb_fetch(in_data, inx, iny, inz, ix, iy+1, iz+1);\n"
"  float c111 = tvdb_fetch(in_data, inx, iny, inz, ix+1, iy+1, iz+1);\n"
"  float c00 = c000 + (c100 - c000) * tx; float c10 = c010 + (c110 - c010) * tx;\n"
"  float c01 = c001 + (c101 - c001) * tx; float c11 = c011 + (c111 - c011) * tx;\n"
"  float c0 = c00 + (c10 - c00) * ty; float c1 = c01 + (c11 - c01) * ty;\n"
"  out_data[gid] = c0 + (c1 - c0) * tz;\n"
"}\n"
"__device__ float tvdb_sample_world(const float* g, int nx, int ny, int nz,\n"
"                                    float ox, float oy, float oz, float vs, float wx, float wy, float wz) {\n"
"  float fx = (wx - ox) / vs - 0.5f, fy = (wy - oy) / vs - 0.5f, fz = (wz - oz) / vs - 0.5f;\n"
"  int ix = (int)floorf(fx), iy = (int)floorf(fy), iz = (int)floorf(fz);\n"
"  float tx = fx - ix, ty = fy - iy, tz = fz - iz;\n"
"  float c00 = tvdb_fetch(g,nx,ny,nz,ix,iy,iz)     + (tvdb_fetch(g,nx,ny,nz,ix+1,iy,iz)     - tvdb_fetch(g,nx,ny,nz,ix,iy,iz))     * tx;\n"
"  float c10 = tvdb_fetch(g,nx,ny,nz,ix,iy+1,iz)   + (tvdb_fetch(g,nx,ny,nz,ix+1,iy+1,iz)   - tvdb_fetch(g,nx,ny,nz,ix,iy+1,iz))   * tx;\n"
"  float c01 = tvdb_fetch(g,nx,ny,nz,ix,iy,iz+1)   + (tvdb_fetch(g,nx,ny,nz,ix+1,iy,iz+1)   - tvdb_fetch(g,nx,ny,nz,ix,iy,iz+1))   * tx;\n"
"  float c11 = tvdb_fetch(g,nx,ny,nz,ix,iy+1,iz+1) + (tvdb_fetch(g,nx,ny,nz,ix+1,iy+1,iz+1) - tvdb_fetch(g,nx,ny,nz,ix,iy+1,iz+1)) * tx;\n"
"  float c0 = c00 + (c10 - c00) * ty, c1 = c01 + (c11 - c01) * ty;\n"
"  return c0 + (c1 - c0) * tz;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_volume_render(const float* density, float* out_image,\n"
"    int nx, int ny, int nz, float ox, float oy, float oz, float vs,\n"
"    float lox, float loy, float loz, float hix, float hiy, float hiz,\n"
"    float ex, float ey, float ez, float fwx, float fwy, float fwz,\n"
"    float rx, float ry, float rz, float ux, float uy, float uz,\n"
"    float tan_half, float aspect, float sigma, float step, float background,\n"
"    int width, int height) {\n"
"  unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (gid >= (unsigned int)(width * height)) return;\n"
"  int px = (int)gid % width, py = (int)gid / width;\n"
"  float sx = (2.0f * ((float)px + 0.5f) / (float)width - 1.0f) * aspect * tan_half;\n"
"  float sy = (1.0f - 2.0f * ((float)py + 0.5f) / (float)height) * tan_half;\n"
"  float dx = fwx + sx*rx + sy*ux, dy = fwy + sx*ry + sy*uy, dz = fwz + sx*rz + sy*uz;\n"
"  float dl = sqrtf(dx*dx + dy*dy + dz*dz); if (dl > 0.0f) { dx/=dl; dy/=dl; dz/=dl; }\n"
"  float o[3] = {ex, ey, ez}, d[3] = {dx, dy, dz}, lo[3] = {lox, loy, loz}, hi[3] = {hix, hiy, hiz};\n"
"  float tmin = 0.0f, tmax = 1e30f; bool hit = true;\n"
"  for (int a = 0; a < 3; ++a) {\n"
"    if (fabsf(d[a]) < 1e-12f) { if (o[a] < lo[a] || o[a] > hi[a]) { hit = false; break; } }\n"
"    else { float inv = 1.0f / d[a]; float ta = (lo[a]-o[a])*inv, tb = (hi[a]-o[a])*inv;\n"
"      if (ta > tb) { float t = ta; ta = tb; tb = t; } if (ta > tmin) tmin = ta; if (tb < tmax) tmax = tb;\n"
"      if (tmin > tmax) { hit = false; break; } } }\n"
"  float transmit = 1.0f;\n"
"  if (hit && tmax > tmin) {\n"
"    for (float t = tmin + 0.5f*step; t < tmax && transmit > 1e-3f; t += step) {\n"
"      float wx = ex + t*dx, wy = ey + t*dy, wz = ez + t*dz;\n"
"      float den = tvdb_sample_world(density, nx, ny, nz, ox, oy, oz, vs, wx, wy, wz);\n"
"      if (den <= 0.0f) continue;\n"
"      float alpha = 1.0f - expf(-den * sigma * step);\n"
"      transmit *= (1.0f - alpha);\n"
"    }\n"
"  }\n"
"  float opacity = 1.0f - transmit;\n"
"  out_image[py * width + px] = opacity + transmit * background;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_ray_samples(const float* rays, float* out_points, float* out_t,\n"
"                                                  unsigned int n_rays, unsigned int n_samples) {\n"
"  unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  unsigned int total = n_rays * n_samples;\n"
"  if (gid >= total) return;\n"
"  unsigned int ri = gid / n_samples, si = gid - ri * n_samples;\n"
"  const float* r = rays + ri * 8u;\n"
"  float a = (n_samples == 1u) ? 0.0f : (float)si / (float)(n_samples - 1u);\n"
"  float t = r[3] + (r[7] - r[3]) * a;\n"
"  out_t[gid] = t;\n"
"  out_points[3*gid+0] = r[0] + t * r[4];\n"
"  out_points[3*gid+1] = r[1] + t * r[5];\n"
"  out_points[3*gid+2] = r[2] + t * r[6];\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_voxels_along_ray(const float* rays, int* out_voxels, int* out_counts,\n"
"    int nx, int ny, int nz, float ox, float oy, float oz, float vs, unsigned int n_rays, unsigned int cap) {\n"
"  unsigned int ri = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (ri >= n_rays) return;\n"
"  const float* r = rays + ri * 8u;\n"
"  float o[3] = {(r[0]-ox)/vs, (r[1]-oy)/vs, (r[2]-oz)/vs};\n"
"  float d[3] = {r[4]/vs, r[5]/vs, r[6]/vs};\n"
"  int dim[3] = {nx, ny, nz};\n"
"  float t0 = r[3], t1 = r[7]; bool hit = true;\n"
"  for (int a = 0; a < 3; ++a) {\n"
"    float hi = (float)dim[a];\n"
"    if (fabsf(d[a]) < 1e-30f) { if (o[a] < 0.0f || o[a] > hi) { hit = false; break; } continue; }\n"
"    float ta = (0.0f - o[a]) / d[a], tb = (hi - o[a]) / d[a];\n"
"    if (ta > tb) { float t = ta; ta = tb; tb = t; } if (ta > t0) t0 = ta; if (tb < t1) t1 = tb;\n"
"    if (t0 > t1) { hit = false; break; } }\n"
"  out_counts[ri] = 0;\n"
"  if (!hit) return;\n"
"  float ex = o[0] + t0*d[0], ey = o[1] + t0*d[1], ez = o[2] + t0*d[2];\n"
"  int ip[3] = {(int)floorf(ex), (int)floorf(ey), (int)floorf(ez)};\n"
"  int dm[3] = {nx, ny, nz};\n"
"  for (int a = 0; a < 3; ++a) { if (ip[a] < 0) ip[a] = 0; if (ip[a] >= dm[a]) ip[a] = dm[a]-1; }\n"
"  int s[3] = {d[0]>0.0f?1:(d[0]<0.0f?-1:0), d[1]>0.0f?1:(d[1]<0.0f?-1:0), d[2]>0.0f?1:(d[2]<0.0f?-1:0)};\n"
"  float tmax3[3], tdelta[3]; const float BIG = 1e30f;\n"
"  for (int a = 0; a < 3; ++a) {\n"
"    tmax3[a] = (s[a]!=0) ? (((float)ip[a] + (s[a]>0?1.0f:0.0f)) - o[a]) / d[a] : BIG;\n"
"    tdelta[a] = (s[a]!=0) ? fabsf(1.0f/d[a]) : BIG; }\n"
"  int written = 0;\n"
"  while (ip[0]>=0 && ip[0]<nx && ip[1]>=0 && ip[1]<ny && ip[2]>=0 && ip[2]<nz) {\n"
"    if ((unsigned int)written < cap) {\n"
"      unsigned int base = 3u * (ri * cap + (unsigned int)written);\n"
"      out_voxels[base+0] = ip[0]; out_voxels[base+1] = ip[1]; out_voxels[base+2] = ip[2]; ++written; }\n"
"    if (tmax3[0] < tmax3[1] && tmax3[0] < tmax3[2]) { ip[0]+=s[0]; tmax3[0]+=tdelta[0]; }\n"
"    else if (tmax3[1] < tmax3[2]) { ip[1]+=s[1]; tmax3[1]+=tdelta[1]; }\n"
"    else { ip[2]+=s[2]; tmax3[2]+=tdelta[2]; }\n"
"    if (tmax3[0] > t1 && tmax3[1] > t1 && tmax3[2] > t1) break;\n"
"  }\n"
"  out_counts[ri] = written;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_segments_along_ray(const float* g, const float* rays,\n"
"    float* out_pairs, int* out_counts, int nx, int ny, int nz, float ox, float oy, float oz, float vs,\n"
"    unsigned int n_rays, float isovalue, unsigned int step_count, unsigned int cap) {\n"
"  unsigned int ri = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (ri >= n_rays) return;\n"
"  const float* r = rays + ri * 8u;\n"
"  float ox0 = r[0], oy0 = r[1], oz0 = r[2], tmin = r[3];\n"
"  float dx = r[4], dy = r[5], dz = r[6], tmax = r[7];\n"
"  unsigned int pairs = 0; bool inside = false; float t_enter = 0.0f; float t_prev = tmin;\n"
"  float v_prev = tvdb_sample_world(g, nx, ny, nz, ox, oy, oz, vs, ox0+tmin*dx, oy0+tmin*dy, oz0+tmin*dz) - isovalue;\n"
"  if (v_prev < 0.0f) { inside = true; t_enter = tmin; }\n"
"  for (unsigned int i = 1u; i < step_count; ++i) {\n"
"    float a = (float)i / (float)(step_count - 1u);\n"
"    float t = tmin + (tmax - tmin) * a;\n"
"    float v = tvdb_sample_world(g, nx, ny, nz, ox, oy, oz, vs, ox0+t*dx, oy0+t*dy, oz0+t*dz) - isovalue;\n"
"    if (v_prev * v < 0.0f) {\n"
"      float frac = v_prev / (v_prev - v); float t_cross = t_prev + frac * (t - t_prev);\n"
"      if (!inside) { t_enter = t_cross; inside = true; }\n"
"      else { if (pairs < cap) { out_pairs[2u*(ri*cap+pairs)+0u] = t_enter; out_pairs[2u*(ri*cap+pairs)+1u] = t_cross; } ++pairs; inside = false; }\n"
"    }\n"
"    v_prev = v; t_prev = t;\n"
"  }\n"
"  if (inside) { if (pairs < cap) { out_pairs[2u*(ri*cap+pairs)+0u] = t_enter; out_pairs[2u*(ri*cap+pairs)+1u] = tmax; } ++pairs; }\n"
"  out_counts[ri] = (int)pairs;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_integrate_tsdf(float* tsdf, float* weights, const float* depth,\n"
"    int nx, int ny, int nz, float ox, float oy, float oz, float vs,\n"
"    float p0, float p1, float p2, float p3, float p4, float p5, float p6, float p7, float p8, float p9, float p10, float p11,\n"
"    float fx, float fy, float ccx, float ccy, int width, int height,\n"
"    float depth_min, float depth_max, float trunc_distance) {\n"
"  unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  unsigned int total = (unsigned int)(nx * ny * nz);\n"
"  if (gid >= total) return;\n"
"  int iz = (int)(gid / (unsigned int)(nx * ny));\n"
"  int rem = (int)(gid - (unsigned int)(iz * nx * ny));\n"
"  int iy = rem / nx; int ix = rem - iy * nx;\n"
"  float wx = ox + ((float)ix + 0.5f) * vs, wy = oy + ((float)iy + 0.5f) * vs, wz = oz + ((float)iz + 0.5f) * vs;\n"
"  float cx = p0*wx + p1*wy + p2*wz + p3;\n"
"  float cy = p4*wx + p5*wy + p6*wz + p7;\n"
"  float cz = p8*wx + p9*wy + p10*wz + p11;\n"
"  if (cz <= 0.0f) return;\n"
"  float u = fx * (cx / cz) + ccx, v = fy * (cy / cz) + ccy;\n"
"  int iu = (int)floorf(u + 0.5f), iv = (int)floorf(v + 0.5f);\n"
"  if (iu < 0 || iu >= width || iv < 0 || iv >= height) return;\n"
"  float d = depth[(size_t)iv * (size_t)width + (size_t)iu];\n"
"  if (!(d >= depth_min && d <= depth_max)) return;\n"
"  float sdf = d - cz;\n"
"  if (sdf < -trunc_distance) return;\n"
"  if (sdf > trunc_distance) sdf = trunc_distance;\n"
"  float w_old = weights[gid], t_old = tsdf[gid], w_new = w_old + 1.0f;\n"
"  tsdf[gid] = (t_old * w_old + sdf) / w_new;\n"
"  weights[gid] = w_new;\n"
"}\n"
"/* One partial per block, reduced in shared memory: this used to be a single\n"
" * wavefront of `nthreads` threads, which left the rest of the device idle on a\n"
" * large grid. A thread with an empty slice starts from the opposite infinities\n"
" * so it cannot drag min down or max up to 0. */\n"
"extern \"C\" __global__ void tvdb_cuda_stats(const float* data, float4* partials,\n"
"                                            unsigned int count, unsigned int ngroups) {\n"
"  __shared__ float4 sh[256];\n"
"  unsigned int lid = threadIdx.x;\n"
"  unsigned int stride = ngroups * 256u;\n"
"  float mn = 3.402823466e+38f, mx = -3.402823466e+38f, sum = 0.0f, sumsq = 0.0f;\n"
"  for (unsigned int i = blockIdx.x * 256u + lid; i < count; i += stride) {\n"
"    float v = data[i];\n"
"    mn = fminf(mn, v); mx = fmaxf(mx, v); sum += v; sumsq += v * v;\n"
"  }\n"
"  float4 p; p.x = mn; p.y = mx; p.z = sum; p.w = sumsq; sh[lid] = p;\n"
"  __syncthreads();\n"
"  for (unsigned int t = 128u; t > 0u; t >>= 1u) {\n"
"    if (lid < t) {\n"
"      float4 a = sh[lid], b = sh[lid + t];\n"
"      sh[lid] = make_float4(fminf(a.x,b.x), fmaxf(a.y,b.y), a.z+b.z, a.w+b.w);\n"
"    }\n"
"    __syncthreads();\n"
"  }\n"
"  if (lid == 0u) partials[blockIdx.x] = sh[0];\n"
"}\n"
"/* One partial per block (see tvdb_cuda_stats): max_err uses the same\n"
" * opposite-infinity sentinel so a thread that skipped every voxel outside the\n"
" * band cannot report a max error of 0. */\n"
"extern \"C\" __global__ void tvdb_cuda_levelset_check(const float* data, float4* partials,\n"
"    int nx, int ny, int nz, float inv2vs, float band_world, float tol, unsigned int count, unsigned int ngroups) {\n"
"  __shared__ float4 sh[256];\n"
"  unsigned int lid = threadIdx.x;\n"
"  unsigned int t = blockIdx.x * 256u + lid;\n"
"  int inx = nx - 2, iny = ny - 2; unsigned int sl = (unsigned int)(nx * ny);\n"
"  float sum_mag = 0.0f, max_err = 0.0f, bad = 0.0f, band = 0.0f;\n"
"  for (unsigned int m = t; m < count; m += ngroups * 256u) {\n"
"    int ix = (int)(m % (unsigned int)inx) + 1;\n"
"    unsigned int tmp = m / (unsigned int)inx;\n"
"    int iy = (int)(tmp % (unsigned int)iny) + 1;\n"
"    int iz = (int)(tmp / (unsigned int)iny) + 1;\n"
"    unsigned int c = (unsigned int)((iz * ny + iy) * nx + ix);\n"
"    if (band_world > 0.0f && fabsf(data[c]) > band_world) continue;\n"
"    float gx = (data[c + 1u] - data[c - 1u]) * inv2vs;\n"
"    float gy = (data[c + (unsigned int)nx] - data[c - (unsigned int)nx]) * inv2vs;\n"
"    float gz = (data[c + sl] - data[c - sl]) * inv2vs;\n"
"    float mag = sqrtf(gx*gx + gy*gy + gz*gz); float err = fabsf(mag - 1.0f);\n"
"    sum_mag += mag; if (err > max_err) max_err = err; if (err > tol) bad += 1.0f; band += 1.0f;\n"
"  }\n"
"  float4 p; p.x = sum_mag; p.y = (band > 0.0f) ? max_err : -3.402823466e+38f; p.z = bad; p.w = band;\n"
"  sh[lid] = p;\n"
"  __syncthreads();\n"
"  for (unsigned int s2 = 128u; s2 > 0u; s2 >>= 1u) {\n"
"    if (lid < s2) {\n"
"      float4 a = sh[lid], b = sh[lid + s2];\n"
"      sh[lid] = make_float4(a.x+b.x, fmaxf(a.y,b.y), a.z+b.z, a.w+b.w);\n"
"    }\n"
"    __syncthreads();\n"
"  }\n"
"  if (lid == 0u) partials[blockIdx.x] = sh[0];\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_flood(const float* data, const unsigned int* vis, unsigned int* next_vis, unsigned int* changed,\n"
"                                            int nx, int ny, int nz, float thresh) {\n"
"  unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  unsigned int total = (unsigned int)(nx * ny * nz);\n"
"  if (gid >= total) return;\n"
"  next_vis[gid]=vis[gid];\n"
"  if (vis[gid] != 0u) return;\n"
"  if (fabsf(data[gid]) < thresh) return;\n"
"  int iz = (int)(gid / (unsigned int)(nx * ny));\n"
"  int rem = (int)(gid - (unsigned int)(iz * nx * ny));\n"
"  int iy = rem / nx; int ix = rem - iy * nx;\n"
"  unsigned int sl = (unsigned int)(nx * ny);\n"
"  bool reached = false;\n"
"  if (ix > 0      && vis[gid - 1u] != 0u) reached = true;\n"
"  if (ix < nx - 1 && vis[gid + 1u] != 0u) reached = true;\n"
"  if (iy > 0      && vis[gid - (unsigned int)nx] != 0u) reached = true;\n"
"  if (iy < ny - 1 && vis[gid + (unsigned int)nx] != 0u) reached = true;\n"
"  if (iz > 0      && vis[gid - sl] != 0u) reached = true;\n"
"  if (iz < nz - 1 && vis[gid + sl] != 0u) reached = true;\n"
"  if (reached) { next_vis[gid] = 1u; atomicOr(changed,1u); }\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_splat(float* data, const tvdb_float4* pts, const float* vals,\n"
"    float* wdata, int nx, int ny, int nz, float ox, float oy, float oz, float vs,\n"
"    unsigned int count, int has_weights) {\n"
"  unsigned int p = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (p >= count) return;\n"
"  tvdb_float4 q = pts[p];\n"
"  float vx = (q.x - ox) / vs - 0.5f, vy = (q.y - oy) / vs - 0.5f, vz = (q.z - oz) / vs - 0.5f;\n"
"  if(isnan(vx) || vx < -1 || vx >= nx || isnan(vy) || vy < -1 || vy >= ny || isnan(vz) || vz < -1 || vz >= nz) return;\n"
"  int ix = (int)floorf(vx), iy = (int)floorf(vy), iz = (int)floorf(vz);\n"
"  float fx = vx - ix, fy = vy - iy, fz = vz - iz; float v = vals[p];\n"
"  for (int dz = 0; dz < 2; ++dz) { int z = iz + dz; if (z < 0 || z >= nz) continue; float wz = (dz==0)?(1.0f-fz):fz;\n"
"    for (int dy = 0; dy < 2; ++dy) { int y = iy + dy; if (y < 0 || y >= ny) continue; float wy = (dy==0)?(1.0f-fy):fy;\n"
"      for (int dx = 0; dx < 2; ++dx) { int x = ix + dx; if (x < 0 || x >= nx) continue; float wx = (dx==0)?(1.0f-fx):fx;\n"
"        float w = wx * wy * wz; unsigned int idx = (unsigned int)((z * ny + y) * nx + x);\n"
"        atomicAdd(&data[idx], w * v); if (has_weights) atomicAdd(&wdata[idx], w);\n"
"      } } }\n"
"}\n"
"__device__ void tvdb_quad_w3(float t, float* w) {\n"
"  w[0] = 0.5f * t * (t - 1.0f); w[1] = 1.0f - t * t; w[2] = 0.5f * t * (t + 1.0f);\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_splat_quadratic(float* data, const tvdb_float4* pts, const float* vals,\n"
"    float* wdata, int nx, int ny, int nz, float ox, float oy, float oz, float vs,\n"
"    unsigned int count, int has_weights) {\n"
"  unsigned int p = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (p >= count) return;\n"
"  tvdb_float4 q = pts[p];\n"
"  float cx = (q.x - ox) / vs - 0.5f, cy = (q.y - oy) / vs - 0.5f, cz = (q.z - oz) / vs - 0.5f;\n"
"  if(isnan(cx) || cx < -1 || cx >= nx + 1.0f || isnan(cy) || cy < -1 || cy >= ny + 1.0f || isnan(cz) || cz < -1 || cz >= nz + 1.0f) return;\n"
"  int ix = (int)floorf(cx), iy = (int)floorf(cy), iz = (int)floorf(cz);\n"
"  float tu = cx - ix, tv = cy - iy, tw = cz - iz; float v = vals[p];\n"
"  float wu[3], wv[3], ww[3]; tvdb_quad_w3(tu, wu); tvdb_quad_w3(tv, wv); tvdb_quad_w3(tw, ww);\n"
"  for (int dz = 0; dz < 3; ++dz) { int z = iz - 1 + dz; if (z < 0 || z >= nz) continue;\n"
"    for (int dy = 0; dy < 3; ++dy) { int y = iy - 1 + dy; if (y < 0 || y >= ny) continue;\n"
"      for (int dx = 0; dx < 3; ++dx) { int x = ix - 1 + dx; if (x < 0 || x >= nx) continue;\n"
"        float w = wu[dx] * wv[dy] * ww[dz]; unsigned int idx = (unsigned int)((z * ny + y) * nx + x);\n"
"        atomicAdd(&data[idx], w * v); if (has_weights) atomicAdd(&wdata[idx], w);\n"
"      } } }\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_gaussian_sh(const float* sh, const tvdb_float4* dirs, float* out_colors,\n"
"    unsigned int count, unsigned int degree, unsigned int K) {\n"
"  unsigned int g = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (g >= count) return;\n"
"  const float C0 = 0.28209479177387814f;\n"
"  const float C1 = 0.4886025119029199f;\n"
"  const float C2[5] = {1.0925484305920792f, -1.0925484305920792f, 0.31539156525252005f, -1.0925484305920792f, 0.5462742152960396f};\n"
"  const float C3[7] = {-0.5900435899266435f, 2.890611442640554f, -0.4570457994644658f, 0.3731763325901154f, -0.4570457994644658f, 1.445305721320277f, -0.5900435899266435f};\n"
"  tvdb_float4 dd = dirs[g]; float dx = dd.x, dy = dd.y, dz = dd.z;\n"
"  float len = sqrtf(dx*dx+dy*dy+dz*dz);\n"
"  if (len > 1e-8f) { dx/=len; dy/=len; dz/=len; } else { dx=dy=dz=0.0f; }\n"
"  unsigned int base = (g * K) * 3u;\n"
"  for (unsigned int c = 0u; c < 3u; ++c) {\n"
"    const float* s = sh + base + c; float r = C0 * s[0];\n"
"    if (degree >= 1u) {\n"
"      r += C1 * (-dy*s[3] + dz*s[6] - dx*s[9]);\n"
"      if (degree >= 2u) {\n"
"        float xx=dx*dx, yy=dy*dy, zz=dz*dz, xy=dx*dy, yz=dy*dz, xz=dx*dz;\n"
"        r += C2[0]*xy*s[12] + C2[1]*yz*s[15] + C2[2]*(2.0f*zz-xx-yy)*s[18] + C2[3]*xz*s[21] + C2[4]*(xx-yy)*s[24];\n"
"        if (degree >= 3u) {\n"
"          r += C3[0]*dy*(3.0f*xx-yy)*s[27] + C3[1]*xy*dz*s[30] + C3[2]*dy*(4.0f*zz-xx-yy)*s[33] + C3[3]*dz*(2.0f*zz-3.0f*xx-3.0f*yy)*s[36] + C3[4]*dx*(4.0f*zz-xx-yy)*s[39] + C3[5]*dz*(xx-yy)*s[42] + C3[6]*dx*(xx-3.0f*yy)*s[45];\n"
"        }\n"
"      }\n"
"    }\n"
"    r += 0.5f; out_colors[g*3u+c] = r > 0.0f ? r : 0.0f;\n"
"  }\n"
"}\n"
"__device__ float tvdb_fast_sqrt(float x) {\n"
"  unsigned int i = __float_as_uint(x); i = (i >> 1) + 0x1fbc0000u; return __uint_as_float(i);\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_gaussian_project(const float* gin, float* gout,\n"
"    const float* extr, float fx, float fy, float cx, float cy,\n"
"    float near, float far, float eps2d, unsigned int count) {\n"
"  unsigned int g = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (g >= count) return;\n"
"  unsigned int ib = g * 14u, ob = g * 11u;\n"
"  float mx = gin[ib+0u], my = gin[ib+1u], mz = gin[ib+2u];\n"
"  float qx = gin[ib+3u], qy = gin[ib+4u], qz = gin[ib+5u], qw = gin[ib+6u];\n"
"  float lsx = gin[ib+7u], lsy = gin[ib+8u], lsz = gin[ib+9u];\n"
"  float opac = gin[ib+10u];\n"
"  float pz = extr[2]*mx + extr[6]*my + extr[10]*mz + extr[14];\n"
"  if (pz <= near || pz >= far) { for (unsigned int k=0u;k<11u;++k) gout[ob+k]=0.0f; return; }\n"
"  float px = extr[0]*mx + extr[4]*my + extr[8]*mz + extr[12];\n"
"  float py = extr[1]*mx + extr[5]*my + extr[9]*mz + extr[13];\n"
"  float pw = extr[3]*mx + extr[7]*my + extr[11]*mz + extr[15];\n"
"  float cam_x = px / pw, cam_y = py / pw, inv_depth = 1.0f / pz;\n"
"  float x = fx*cam_x*inv_depth + cx, y = fy*cam_y*inv_depth + cy;\n"
"  float sx = exp2f(lsx), sy = exp2f(lsy), sz = exp2f(lsz);\n"
"  float sqx = sx*sx, sqy = sy*sy, sqz = sz*sz;\n"
"  float R0 = 1.0f-2.0f*(qy*qy+qz*qz), R1 = 2.0f*(qx*qy-qw*qz), R2 = 2.0f*(qx*qz+qw*qy);\n"
"  float R3 = 2.0f*(qx*qy+qw*qz), R4 = 1.0f-2.0f*(qx*qx+qz*qz), R5 = 2.0f*(qy*qz-qw*qx);\n"
"  float R6 = 2.0f*(qx*qz-qw*qy), R7 = 2.0f*(qy*qz+qw*qx), R8 = 1.0f-2.0f*(qx*qx+qy*qy);\n"
"  float rot00 = R0*R0*sqx + R1*R1*sqy + R2*R2*sqz;\n"
"  float rot01 = R0*R3*sqx + R1*R4*sqy + R2*R5*sqz;\n"
"  float rot02 = R0*R6*sqx + R1*R7*sqy + R2*R8*sqz;\n"
"  float rot12 = R3*R6*sqx + R4*R7*sqy + R5*R8*sqz;\n"
"  float inv_fx = 1.0f/fx, inv_fy = 1.0f/fy, d_x = x-cx, d_y = y-cy;\n"
"  float c2d0 = inv_fx*inv_fx*rot00 + d_x*d_x*inv_fx*inv_fx*inv_depth*inv_depth*rot02;\n"
"  float c2d1 = d_x*d_y*inv_fx*inv_fy*inv_depth*inv_depth*rot02;\n"
"  float c2d2 = inv_fy*inv_fy*rot01 + d_y*d_y*inv_fy*inv_fy*inv_depth*inv_depth*rot12;\n"
"  c2d0 += eps2d; c2d2 += eps2d;\n"
"  float conic_a, conic_b, conic_c, det = c2d0*c2d2 - c2d1*c2d1;\n"
"  if (det > 1e-10f) { float id = 1.0f/det; conic_a = c2d2*id; conic_b = -c2d1*id; conic_c = c2d0*id; }\n"
"  else { conic_a = 1.0f; conic_b = 0.0f; conic_c = 1.0f; }\n"
"  float eig_max = 0.5f*(conic_a + conic_c + tvdb_fast_sqrt((conic_a-conic_c)*(conic_a-conic_c) + 4.0f*conic_b*conic_b));\n"
"  float radius = (eig_max > 1e-10f) ? 3.0f*tvdb_fast_sqrt(1.0f/eig_max) : 0.0f;\n"
"  float opacity = 1.0f/(1.0f + exp2f(-opac));\n"
"  gout[ob+0u]=x; gout[ob+1u]=y; gout[ob+2u]=conic_a; gout[ob+3u]=conic_b; gout[ob+4u]=conic_c;\n"
"  gout[ob+5u]=opacity; gout[ob+6u]=pz; gout[ob+7u]=radius;\n"
"  gout[ob+8u]=gin[ib+11u]; gout[ob+9u]=gin[ib+12u]; gout[ob+10u]=gin[ib+13u];\n"
"}\n"
"struct TvdbAxpyParams { unsigned int n; float alpha; };\n"
"/* Elementwise binary scalar-grid ops: max, min, sum, product. Mirrors\n"
"   tinyvdb_gpu_comp.comp, including the use of the CPU's ternaries rather than\n"
"   fmax/fmin so the two agree on NaN. The host has already rejected a shape\n"
"   mismatch (the CPU ops leave `result` untouched there), so this indexes a, b\n"
"   and o in lockstep with no clamping. */\n"
"/* Dense filters + the single-node semi-Lagrangian advect, mirroring\n"
"   tinyvdb_gpu_filter.comp op for op. */\n"
"__device__ float tvdb_flt_at(const float* f,int ix,int iy,int iz,int nx,int ny,int nz){\n"
"  if(ix<0)ix=0; if(ix>nx-1)ix=nx-1;\n"
"  if(iy<0)iy=0; if(iy>ny-1)iy=ny-1;\n"
"  if(iz<0)iz=0; if(iz>nz-1)iz=nz-1;\n"
"  return f[(unsigned int)(iz*ny+iy)*nx+ix]; }\n"
"__device__ float tvdb_flt_sample(const float* f,float vx,float vy,float vz,int nx,int ny,int nz){\n"
"  vx=isnan(vx)?0:(vx < -1 ? -1 : (vx >= nx ? nx-1 : vx));\n"
"  vy=isnan(vy)?0:(vy < -1 ? -1 : (vy >= ny ? ny-1 : vy));\n"
"  vz=isnan(vz)?0:(vz < -1 ? -1 : (vz >= nz ? nz-1 : vz));\n"
"  int ix=(int)floorf(vx),iy=(int)floorf(vy),iz=(int)floorf(vz);\n"
"  float fx=vx-(float)ix, fy=vy-(float)iy, fz=vz-(float)iz;\n"
"  float c00=tvdb_flt_at(f,ix,iy,iz,nx,ny,nz)*(1-fx)+tvdb_flt_at(f,ix+1,iy,iz,nx,ny,nz)*fx;\n"
"  float c10=tvdb_flt_at(f,ix,iy+1,iz,nx,ny,nz)*(1-fx)+tvdb_flt_at(f,ix+1,iy+1,iz,nx,ny,nz)*fx;\n"
"  float c01=tvdb_flt_at(f,ix,iy,iz+1,nx,ny,nz)*(1-fx)+tvdb_flt_at(f,ix+1,iy,iz+1,nx,ny,nz)*fx;\n"
"  float c11=tvdb_flt_at(f,ix,iy+1,iz+1,nx,ny,nz)*(1-fx)+tvdb_flt_at(f,ix+1,iy+1,iz+1,nx,ny,nz)*fx;\n"
"  float c0=c00*(1-fy)+c10*fy, c1=c01*(1-fy)+c11*fy;\n"
"  return c0*(1-fz)+c1*fz; }\n"
"extern \"C\" __global__ void tvdb_cuda_filter(const float* in_v, float* out_v,\n"
"    const float* vel, const float* kern, const int* u) {\n"
"  /* Dims and scalars come from the bound uniform: {int dim[4]; int cfg[4];\n"
"     float inv_h; float dt; uint nvox;}. inv_h is u[8], dt is u[9]. */\n"
"  int nx=u[0], ny=u[1], nz=u[2];\n"
"  unsigned int n=(unsigned int)(nx*ny*nz);\n"
"  unsigned int i=(blockIdx.x+blockIdx.y*gridDim.x)*blockDim.x+threadIdx.x;\n"
"  if (i>=n) return;\n"
"  int op=u[3], axis=u[4], radius=u[5];\n"
"  float inv_h=0.0f, dt=0.0f; memcpy(&inv_h,&u[8],4); memcpy(&dt,&u[9],4);\n"
"  int ix=(int)(i%(unsigned int)nx); unsigned int rm=i/(unsigned int)nx;\n"
"  int iy=(int)(rm%(unsigned int)ny), iz=(int)(rm/(unsigned int)ny);\n"
"  if (op==0) { float acc=0.0f;\n"
"    for (int k=-radius;k<=radius;++k){ int sx=ix,sy=iy,sz=iz;\n"
"      if(axis==0) sx=ix+k; else if(axis==1) sy=iy+k; else sz=iz+k;\n"
"      acc+=kern[k+radius]*tvdb_flt_at(in_v,sx,sy,sz,nx,ny,nz); }\n"
"    out_v[i]=acc; return; }\n"
"  if (op==3) {\n"
"    /* Rank count, exactly as the GLSL: the k-th smallest is any j with\n"
"       below[j] <= k < at_or_below[j]. Order independent, so it matches the\n"
"       CPU's quickselect bit for bit on finite input. r <= 2 is enforced by the\n"
"       host, so 125 floats of private storage is the worst case. */\n"
"    int rr=radius;\n"
"    int n=(2*rr+1)*(2*rr+1)*(2*rr+1), k=n/2;\n"
"    float win[125]; int m=0;\n"
"    for (int dz=-rr;dz<=rr;++dz) for (int dy=-rr;dy<=rr;++dy) for (int dx=-rr;dx<=rr;++dx)\n"
"      win[m++]=tvdb_flt_at(in_v,ix+dx,iy+dy,iz+dz,nx,ny,nz);\n"
"    for (int j=0;j<n;++j){ int below=0, le=0;\n"
"      for (int q=0;q<n;++q){ if (win[q]<win[j]) ++below; if (!(win[j]<win[q])) ++le; }\n"
"      if (below<=k && k<le) { out_v[i]=win[j]; return; } }\n"
"    out_v[i]=win[0]; return; }\n"
"  if (op==1) { float c=tvdb_flt_at(in_v,ix,iy,iz,nx,ny,nz);\n"
"    float s=tvdb_flt_at(in_v,ix-1,iy,iz,nx,ny,nz)+tvdb_flt_at(in_v,ix+1,iy,iz,nx,ny,nz)\n"
"           +tvdb_flt_at(in_v,ix,iy-1,iz,nx,ny,nz)+tvdb_flt_at(in_v,ix,iy+1,iz,nx,ny,nz)\n"
"           +tvdb_flt_at(in_v,ix,iy,iz-1,nx,ny,nz)+tvdb_flt_at(in_v,ix,iy,iz+1,nx,ny,nz);\n"
"    out_v[i]=c+0.125f*(s-6.0f*c); return; }\n"
"  unsigned int vb=i*3u;\n"
"  float bx=(float)ix-dt*vel[vb+0u]*inv_h;\n"
"  float by=(float)iy-dt*vel[vb+1u]*inv_h;\n"
"  float bz=(float)iz-dt*vel[vb+2u]*inv_h;\n"
"  out_v[i]=tvdb_flt_sample(in_v,bx,by,bz,nx,ny,nz); }\n"
"/* Semi-Lagrangian advection, mirroring tinyvdb_gpu_advect.comp op for op. */\n"
"__device__ float tvdb_adv_at(const float* f, int ix, int iy, int iz, int nx, int ny, int nz) {\n"
"  if (ix < 0) ix = 0; if (ix > nx-1) ix = nx-1;\n"
"  if (iy < 0) iy = 0; if (iy > ny-1) iy = ny-1;\n"
"  if (iz < 0) iz = 0; if (iz > nz-1) iz = nz-1;\n"
"  return f[(unsigned int)(iz*ny+iy)*nx+ix]; }\n"
"__device__ float tvdb_adv_vat(const float* v, int ix, int iy, int iz, int c, int nx, int ny, int nz) {\n"
"  if (ix < 0) ix = 0; if (ix > nx-1) ix = nx-1;\n"
"  if (iy < 0) iy = 0; if (iy > ny-1) iy = ny-1;\n"
"  if (iz < 0) iz = 0; if (iz > nz-1) iz = nz-1;\n"
"  return v[((unsigned int)(iz*ny+iy)*nx+ix)*3u+(unsigned int)c]; }\n"
"__device__ float tvdb_adv_sample(const float* f, float vx, float vy, float vz, int nx, int ny, int nz) {\n"
"  vx=isnan(vx)?0:(vx < -1 ? -1 : (vx >= nx ? nx-1 : vx));\n"
"  vy=isnan(vy)?0:(vy < -1 ? -1 : (vy >= ny ? ny-1 : vy));\n"
"  vz=isnan(vz)?0:(vz < -1 ? -1 : (vz >= nz ? nz-1 : vz));\n"
"  int ix=(int)floorf(vx), iy=(int)floorf(vy), iz=(int)floorf(vz);\n"
"  float fx=vx-(float)ix, fy=vy-(float)iy, fz=vz-(float)iz;\n"
"  float c000=tvdb_adv_at(f,ix,iy,iz,nx,ny,nz),     c100=tvdb_adv_at(f,ix+1,iy,iz,nx,ny,nz);\n"
"  float c010=tvdb_adv_at(f,ix,iy+1,iz,nx,ny,nz),   c110=tvdb_adv_at(f,ix+1,iy+1,iz,nx,ny,nz);\n"
"  float c001=tvdb_adv_at(f,ix,iy,iz+1,nx,ny,nz),   c101=tvdb_adv_at(f,ix+1,iy,iz+1,nx,ny,nz);\n"
"  float c011=tvdb_adv_at(f,ix,iy+1,iz+1,nx,ny,nz), c111=tvdb_adv_at(f,ix+1,iy+1,iz+1,nx,ny,nz);\n"
"  float c00=c000*(1.0f-fx)+c100*fx, c10=c010*(1.0f-fx)+c110*fx;\n"
"  float c01=c001*(1.0f-fx)+c101*fx, c11=c011*(1.0f-fx)+c111*fx;\n"
"  float c0=c00*(1.0f-fy)+c10*fy,   c1=c01*(1.0f-fy)+c11*fy;\n"
"  return c0*(1.0f-fz)+c1*fz; }\n"
"__device__ void tvdb_adv_svec(const float* v, float vx, float vy, float vz, float* o, int nx, int ny, int nz) {\n"
"  vx=isnan(vx)?0:(vx < -1 ? -1 : (vx >= nx ? nx-1 : vx));\n"
"  vy=isnan(vy)?0:(vy < -1 ? -1 : (vy >= ny ? ny-1 : vy));\n"
"  vz=isnan(vz)?0:(vz < -1 ? -1 : (vz >= nz ? nz-1 : vz));\n"
"  int ix=(int)floorf(vx), iy=(int)floorf(vy), iz=(int)floorf(vz);\n"
"  float fx=vx-(float)ix, fy=vy-(float)iy, fz=vz-(float)iz;\n"
"  for (int c=0;c<3;++c) {\n"
"    float c00=tvdb_adv_vat(v,ix,iy,iz,c,nx,ny,nz)*(1-fx)+tvdb_adv_vat(v,ix+1,iy,iz,c,nx,ny,nz)*fx;\n"
"    float c10=tvdb_adv_vat(v,ix,iy+1,iz,c,nx,ny,nz)*(1-fx)+tvdb_adv_vat(v,ix+1,iy+1,iz,c,nx,ny,nz)*fx;\n"
"    float c01=tvdb_adv_vat(v,ix,iy,iz+1,c,nx,ny,nz)*(1-fx)+tvdb_adv_vat(v,ix+1,iy,iz+1,c,nx,ny,nz)*fx;\n"
"    float c11=tvdb_adv_vat(v,ix,iy+1,iz+1,c,nx,ny,nz)*(1-fx)+tvdb_adv_vat(v,ix+1,iy+1,iz+1,c,nx,ny,nz)*fx;\n"
"    float c0=c00*(1-fy)+c10*fy, c1=c01*(1-fy)+c11*fy;\n"
"    o[c]=c0*(1-fz)+c1*fz; } }\n"
"__device__ void tvdb_adv_bt(const float* v, float dt, int order, float inv_h,\n"
"                            float px, float py, float pz, float* b, int nx, int ny, int nz) {\n"
"  float g[3], s[3]; tvdb_adv_svec(v,px,py,pz,s,nx,ny,nz);\n"
"  g[0]=-s[0]*inv_h; g[1]=-s[1]*inv_h; g[2]=-s[2]*inv_h;\n"
"  if (order<=1) { b[0]=px+dt*g[0]; b[1]=py+dt*g[1]; b[2]=pz+dt*g[2]; return; }\n"
"  if (order==2) { tvdb_adv_svec(v,px+0.5f*dt*g[0],py+0.5f*dt*g[1],pz+0.5f*dt*g[2],s,nx,ny,nz);\n"
"    b[0]=px-dt*s[0]*inv_h; b[1]=py-dt*s[1]*inv_h; b[2]=pz-dt*s[2]*inv_h; return; }\n"
"  float g2[3]; tvdb_adv_svec(v,px+0.5f*dt*g[0],py+0.5f*dt*g[1],pz+0.5f*dt*g[2],s,nx,ny,nz);\n"
"  g2[0]=-s[0]*inv_h; g2[1]=-s[1]*inv_h; g2[2]=-s[2]*inv_h;\n"
"  if (order==3) { float g3[3];\n"
"    tvdb_adv_svec(v,px-dt*g[0]+2.0f*dt*g2[0],py-dt*g[1]+2.0f*dt*g2[1],pz-dt*g[2]+2.0f*dt*g2[2],s,nx,ny,nz);\n"
"    g3[0]=-s[0]*inv_h; g3[1]=-s[1]*inv_h; g3[2]=-s[2]*inv_h;\n"
"    b[0]=px+dt*(g[0]+4.0f*g2[0]+g3[0])/6.0f; b[1]=py+dt*(g[1]+4.0f*g2[1]+g3[1])/6.0f;\n"
"    b[2]=pz+dt*(g[2]+4.0f*g2[2]+g3[2])/6.0f; return; }\n"
"  float g3[3], g4[3];\n"
"  tvdb_adv_svec(v,px+0.5f*dt*g2[0],py+0.5f*dt*g2[1],pz+0.5f*dt*g2[2],s,nx,ny,nz);\n"
"  g3[0]=-s[0]*inv_h; g3[1]=-s[1]*inv_h; g3[2]=-s[2]*inv_h;\n"
"  tvdb_adv_svec(v,px+dt*g3[0],py+dt*g3[1],pz+dt*g3[2],s,nx,ny,nz);\n"
"  g4[0]=-s[0]*inv_h; g4[1]=-s[1]*inv_h; g4[2]=-s[2]*inv_h;\n"
"  b[0]=px+dt*(g[0]+2.0f*g2[0]+2.0f*g3[0]+g4[0])/6.0f; b[1]=py+dt*(g[1]+2.0f*g2[1]+2.0f*g3[1]+g4[1])/6.0f;\n"
"  b[2]=pz+dt*(g[2]+2.0f*g2[2]+2.0f*g3[2]+g4[2])/6.0f; }\n"
"__device__ void tvdb_adv_mm(const float* f, float bx, float by, float bz,\n"
"                            float* mn, float* mx, int nx, int ny, int nz) {\n"
"  bx=isnan(bx)?0:(bx < -1 ? -1 : (bx >= nx ? nx-1 : bx));\n"
"  by=isnan(by)?0:(by < -1 ? -1 : (by >= ny ? ny-1 : by));\n"
"  bz=isnan(bz)?0:(bz < -1 ? -1 : (bz >= nz ? nz-1 : bz));\n"
"  int ix=(int)floorf(bx), iy=(int)floorf(by), iz=(int)floorf(bz);\n"
"  *mn=3.4e38f; *mx=-3.4e38f;\n"
"  for (int dz=0;dz<2;++dz) for (int dy=0;dy<2;++dy) for (int dx=0;dx<2;++dx) {\n"
"    float s=tvdb_adv_at(f,ix+dx,iy+dy,iz+dz,nx,ny,nz);\n"
"    if (s<*mn) *mn=s; if (s>*mx) *mx=s; } }\n"
"/* The grid dims come from the bound uniform, not from extra parameters: the\n"
"   dispatch spec binds exactly six and a seventh would read whatever followed in\n"
"   the argument list, which cuLaunchKernel reports as `invalid argument`. */\n"
"extern \"C\" __global__ void tvdb_cuda_advect(const float* field, const float* vel,\n"
"    const float* phat, const float* pstar, float* out_v, const int* u) {\n"
"  int nx = u[0], ny = u[1], nz = u[2];\n"
"  unsigned int i = (blockIdx.x+blockIdx.y*gridDim.x)*blockDim.x+threadIdx.x;\n"
"  unsigned int n = (unsigned int)(nx*ny*nz);\n"
"  if (i >= n) return;\n"
"  int op=u[3], order=u[4], clampf=u[5], ix=(int)(i%(unsigned int)nx);\n"
"  unsigned int rm=i/(unsigned int)nx; int iy=(int)(rm%(unsigned int)ny), iz=(int)(rm/(unsigned int)ny);\n"
"  /* The uniform is {int dim[4]; int cfg[4]; float inv_h; float dt; uint nvox;}, so\n"
"     inv_h is u[8] and dt is u[9]. Reading u[6]/u[7] picks up cfg[2]/cfg[3], both\n"
"     zero -- which makes the backtrace a no-op and the kernel silently return\n"
"     the un-advected field, a ~5e-2 difference on a field of scale 1.2 that\n"
"     looks like a plausible small error rather than a total failure to advect. */\n"
"  float inv_h=0.0f, dt=0.0f; memcpy(&inv_h,&u[8],4); memcpy(&dt,&u[9],4);\n"
"  float b[3];\n"
"  if (op==0) { tvdb_adv_bt(vel,dt,order,inv_h,(float)ix,(float)iy,(float)iz,b,nx,ny,nz);\n"
"    out_v[i]=tvdb_adv_sample(field,b[0],b[1],b[2],nx,ny,nz); return; }\n"
"  if (op==1) { float val=phat[i]+0.5f*(field[i]-pstar[i]);\n"
"    if (clampf) { tvdb_adv_bt(vel,dt,order,inv_h,(float)ix,(float)iy,(float)iz,b,nx,ny,nz);\n"
"      float mn,mx; tvdb_adv_mm(field,b[0],b[1],b[2],&mn,&mx,nx,ny,nz);\n"
"      if (val<mn) val=mn; else if (val>mx) val=mx; }\n"
"    out_v[i]=val; return; }\n"
"  if (op==2) { out_v[i]=field[i]+0.5f*(field[i]-pstar[i]); return; }\n"
"  tvdb_adv_bt(vel,dt,order,inv_h,(float)ix,(float)iy,(float)iz,b,nx,ny,nz);\n"
"  float mn,mx; tvdb_adv_mm(field,b[0],b[1],b[2],&mn,&mx,nx,ny,nz);\n"
"  float vv=out_v[i]; if (vv<mn) vv=mn; else if (vv>mx) vv=mx; out_v[i]=vv; }\n"
"extern \"C\" __global__ void tvdb_cuda_comp(const float* a, const float* b, float* o,\n"
"                                          const int* u) {\n"
"  /* n is derived from the uniform rather than passed: the dispatch spec binds\n"
"     only the four declared bindings, so a fifth kernel parameter would read\n"
"     whatever followed in the argument list. */\n"
"  unsigned int n = (unsigned int)(u[0] * u[1] * u[2]);\n"
"  unsigned int i = (blockIdx.x+blockIdx.y*gridDim.x) * blockDim.x + threadIdx.x;\n"
"  if (i >= n) return;\n"
"  float av = a[i], bv = b[i], r;\n"
"  if (u[3] == 0)      r = (av > bv) ? av : bv;\n"
"  else if (u[3] == 1) r = (av < bv) ? av : bv;\n"
"  else if (u[3] == 2) r = av + bv;\n"
"  else                r = av * bv;\n"
"  o[i] = r;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_axpy(const float* x, const float* y, float* o, const TvdbAxpyParams* u) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= u->n) return;\n"
"  o[i] = u->alpha * x[i] + y[i];\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_mcmc_relocation(const float* gin, const float* B,\n"
"    float* new_op, float* new_scale, unsigned int count, unsigned int nmax) {\n"
"  unsigned int g = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (g >= count) return;\n"
"  unsigned int b = g * 5u; float op = gin[b];\n"
"  int ratio = (int)gin[b + 4u]; if (ratio < 1) ratio = 1; if (ratio > (int)nmax) ratio = (int)nmax;\n"
"  float nop = 1.0f - powf(1.0f - op, 1.0f / (float)ratio); new_op[g] = nop;\n"
"  float denom = 0.0f;\n"
"  for (int i = 1; i <= ratio; ++i) for (int k = 0; k <= i - 1; ++k) {\n"
"    float sign = (k & 1) ? -1.0f : 1.0f;\n"
"    denom += B[(unsigned int)(i - 1) * nmax + (unsigned int)k] * (sign / sqrtf((float)(k + 1))) * powf(nop, (float)(k + 1));\n"
"  }\n"
"  float coeff = (denom != 0.0f) ? (op / denom) : 1.0f;\n"
"  new_scale[g*3u+0u] = coeff * gin[b+1u]; new_scale[g*3u+1u] = coeff * gin[b+2u]; new_scale[g*3u+2u] = coeff * gin[b+3u];\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_mcmc_noise(const float* gin, float* out_means,\n"
"    unsigned int count, float lr) {\n"
"  unsigned int g = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (g >= count) return; unsigned int b = g * 14u;\n"
"  float mx = gin[b+0u], my = gin[b+1u], mz = gin[b+2u];\n"
"  float qx = gin[b+3u], qy = gin[b+4u], qz = gin[b+5u], qw = gin[b+6u];\n"
"  float lsx = gin[b+7u], lsy = gin[b+8u], lsz = gin[b+9u];\n"
"  float opl = gin[b+10u]; float rx = gin[b+11u], ry = gin[b+12u], rz = gin[b+13u];\n"
"  float op = 1.0f/(1.0f+expf(-opl)); float gate = 1.0f/(1.0f+expf(-100.0f*(0.005f-op)));\n"
"  float sx = expf(lsx), sy = expf(lsy), sz = expf(lsz); float sqx = sx*sx, sqy = sy*sy, sqz = sz*sz;\n"
"  float ql = sqrtf(qx*qx+qy*qy+qz*qz+qw*qw); if (ql > 1e-8f) { qx/=ql; qy/=ql; qz/=ql; qw/=ql; }\n"
"  float R0 = 1.0f-2.0f*(qy*qy+qz*qz), R1 = 2.0f*(qx*qy-qw*qz), R2 = 2.0f*(qx*qz+qw*qy);\n"
"  float R3 = 2.0f*(qx*qy+qw*qz), R4 = 1.0f-2.0f*(qx*qx+qz*qz), R5 = 2.0f*(qy*qz-qw*qx);\n"
"  float R6 = 2.0f*(qx*qz-qw*qy), R7 = 2.0f*(qy*qz+qw*qx), R8 = 1.0f-2.0f*(qx*qx+qy*qy);\n"
"  float c00 = R0*R0*sqx+R1*R1*sqy+R2*R2*sqz, c01 = R0*R3*sqx+R1*R4*sqy+R2*R5*sqz, c02 = R0*R6*sqx+R1*R7*sqy+R2*R8*sqz;\n"
"  float c11 = R3*R3*sqx+R4*R4*sqy+R5*R5*sqz, c12 = R3*R6*sqx+R4*R7*sqy+R5*R8*sqz, c22 = R6*R6*sqx+R7*R7*sqy+R8*R8*sqz;\n"
"  float gx = rx*gate*lr, gy = ry*gate*lr, gz = rz*gate*lr;\n"
"  out_means[g*3u+0u] = mx + (c00*gx+c01*gy+c02*gz);\n"
"  out_means[g*3u+1u] = my + (c01*gx+c11*gy+c12*gz);\n"
"  out_means[g*3u+2u] = mz + (c02*gx+c12*gy+c22*gz);\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_points_to_mask(float* mask, const tvdb_float4* pts,\n"
"    int nx, int ny, int nz, float ox, float oy, float oz, float vs, unsigned int count) {\n"
"  unsigned int p = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (p >= count) return;\n"
"  tvdb_float4 q = pts[p];\n"
"  int ix = (int)floorf((q.x - ox) / vs);\n"
"  int iy = (int)floorf((q.y - oy) / vs);\n"
"  int iz = (int)floorf((q.z - oz) / vs);\n"
"  if (ix < 0 || ix >= nx || iy < 0 || iy >= ny || iz < 0 || iz >= nz) return;\n"
"  mask[(iz * ny + iy) * nx + ix] = 1.0f;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_voxelize_mark(unsigned int* occ, const tvdb_float4* pts,\n"
"    int dx, int dy, int dz, int bx, int by, int bz, float vx, float vy, float vz,\n"
"    float ox, float oy, float oz, unsigned int count) {\n"
"  unsigned int p = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (p >= count) return;\n"
"  tvdb_float4 q = pts[p];\n"
"  int ix = (int)floorf((q.x - ox) / vx) - bx;\n"
"  int iy = (int)floorf((q.y - oy) / vy) - by;\n"
"  int iz = (int)floorf((q.z - oz) / vz) - bz;\n"
"  if (ix < 0 || ix >= dx || iy < 0 || iy >= dy || iz < 0 || iz >= dz) return;\n"
"  occ[(iz * dy + iy) * dx + ix] = 1u;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_voxelize_compact(const unsigned int* occ, unsigned int* counter,\n"
"    int* out_coords, int dx, int dy, int dz, int bx, int by, int bz, unsigned int cap) {\n"
"  unsigned int v = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  unsigned int total = (unsigned int)(dx * dy * dz);\n"
"  if (v >= total) return;\n"
"  if (occ[v] == 0u) return;\n"
"  int lz = (int)(v / (unsigned int)(dx * dy));\n"
"  int rem = (int)(v - (unsigned int)(lz * dx * dy));\n"
"  int ly = rem / dx; int lx = rem - ly * dx;\n"
"  unsigned int slot = atomicAdd(counter, 1u);\n"
"  if (slot < cap) { out_coords[3u*slot+0u] = lx + bx; out_coords[3u*slot+1u] = ly + by; out_coords[3u*slot+2u] = lz + bz; }\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_hash_insert(unsigned int* state, volatile int* keys, const tvdb_float4* pts,\n"
"    float vx, float vy, float vz, float ox, float oy, float oz, unsigned int count, unsigned int cap, unsigned int mask) {\n"
"  unsigned int p = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (p >= count) return;\n"
"  tvdb_float4 q = pts[p];\n"
"  int ix = (int)floorf((q.x - ox) / vx);\n"
"  int iy = (int)floorf((q.y - oy) / vy);\n"
"  int iz = (int)floorf((q.z - oz) / vz);\n"
"  unsigned int h = ((unsigned int)ix * 73856093u) ^ ((unsigned int)iy * 19349663u) ^ ((unsigned int)iz * 83492791u);\n"
"  unsigned int slot = h & mask;\n"
"  for (unsigned int probe = 0u; probe < cap; ++probe) {\n"
"    unsigned int prev = atomicCAS(&state[slot], 0u, 1u);\n"
"    if (prev == 0u) { keys[slot*3u+0u]=ix; keys[slot*3u+1u]=iy; keys[slot*3u+2u]=iz; __threadfence(); atomicExch(&state[slot], 2u); return; }\n"
"    if (prev == 2u) { __threadfence(); if (keys[slot*3u+0u]==ix && keys[slot*3u+1u]==iy && keys[slot*3u+2u]==iz) return; }\n"
"    slot = (slot + 1u) & mask;\n"
"  }\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_hash_compact(const unsigned int* state, const int* keys,\n"
"    unsigned int* counter, int* out_coords, unsigned int cap) {\n"
"  unsigned int s = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (s >= cap) return;\n"
"  if (state[s] != 2u) return;\n"
"  unsigned int idx = atomicAdd(counter, 1u);\n"
"  if (idx >= cap) return;\n"
"  out_coords[3u*idx+0u] = keys[s*3u+0u]; out_coords[3u*idx+1u] = keys[s*3u+1u]; out_coords[3u*idx+2u] = keys[s*3u+2u];\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_sparse_mark(unsigned int* occ, float* val, const tvdb_int4* coords,\n"
"    const float* invals, int dx, int dy, int dz, int bx, int by, int bz, unsigned int count) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= count) return;\n"
"  tvdb_int4 c = coords[i];\n"
"  int lx = c.x - bx, ly = c.y - by, lz = c.z - bz;\n"
"  unsigned int lin = (unsigned int)((lz * dy + ly) * dx + lx);\n"
"  occ[lin] = 1u; val[lin] = invals[i];\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_sparse_erode(const unsigned int* occ, const float* val,\n"
"    unsigned int* counter, int* outd, int dx, int dy, int dz, int bx, int by, int bz, unsigned int cap) {\n"
"  unsigned int v = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  unsigned int total = (unsigned int)(dx * dy * dz);\n"
"  if (v >= total) return;\n"
"  if (occ[v] == 0u) return;\n"
"  int lz = (int)(v / (unsigned int)(dx * dy));\n"
"  int rem = (int)(v - (unsigned int)(lz * dx * dy));\n"
"  int ly = rem / dx; int lx = rem - ly * dx;\n"
"  const int N[6][3] = {{1,0,0},{-1,0,0},{0,1,0},{0,-1,0},{0,0,1},{0,0,-1}};\n"
"  float r = val[v]; bool keep = true;\n"
"  for (int n = 0; n < 6; ++n) {\n"
"    int mx = lx + N[n][0], my = ly + N[n][1], mz = lz + N[n][2];\n"
"    if (mx < 0 || mx >= dx || my < 0 || my >= dy || mz < 0 || mz >= dz) { keep = false; break; }\n"
"    unsigned int m = (unsigned int)((mz * dy + my) * dx + mx);\n"
"    if (occ[m] == 0u) { keep = false; break; }\n"
"    if (val[m] > r) r = val[m];\n"
"  }\n"
"  if (!keep) return;\n"
"  unsigned int slot = atomicAdd(counter, 1u);\n"
"  if (slot < cap) { outd[4u*slot+0u]=lx+bx; outd[4u*slot+1u]=ly+by; outd[4u*slot+2u]=lz+bz; outd[4u*slot+3u]=__float_as_int(r); }\n"
"}\n"
"__device__ void tvdb_atomic_min_f(float* addr, float val) {\n"
"  int* a = (int*)addr; int old = atomicCAS(a,0,0), assumed;\n"
"  do { assumed = old; if (__int_as_float(assumed) <= val) break; old = atomicCAS(a, assumed, __float_as_int(val)); } while (assumed != old);\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_sparse_dilate_scatter(float* v2, unsigned int* outocc,\n"
"    const tvdb_int4* coords, const float* invals, int dx, int dy, int dz, int bx, int by, int bz, unsigned int count) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= count) return;\n"
"  tvdb_int4 c = coords[i]; int cx = c.x - bx, cy = c.y - by, cz = c.z - bz; float vs = invals[i];\n"
"  const int O[7][3] = {{0,0,0},{1,0,0},{-1,0,0},{0,1,0},{0,-1,0},{0,0,1},{0,0,-1}};\n"
"  for (int k = 0; k < 7; ++k) {\n"
"    int qx = cx+O[k][0], qy = cy+O[k][1], qz = cz+O[k][2];\n"
"    if(qx<0 || qx>=dx || qy<0 || qy>=dy || qz<0 || qz>=dz) continue;\n"
"    unsigned int lin = (unsigned int)((qz * dy + qy) * dx + qx);\n"
"    tvdb_atomic_min_f(&v2[lin], vs); atomicOr(&outocc[lin],1u);\n"
"  }\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_sparse_finalize(const float* val, const unsigned int* outocc,\n"
"    unsigned int* counter, int* outd, int dx, int dy, int dz, int bx, int by, int bz, unsigned int cap) {\n"
"  unsigned int v = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  unsigned int total = (unsigned int)(dx * dy * dz);\n"
"  if (v >= total) return;\n"
"  if (outocc[v] == 0u) return;\n"
"  int lz = (int)(v / (unsigned int)(dx * dy));\n"
"  int rem = (int)(v - (unsigned int)(lz * dx * dy));\n"
"  int ly = rem / dx; int lx = rem - ly * dx;\n"
"  unsigned int slot = atomicAdd(counter, 1u);\n"
"  if (slot < cap) { outd[4u*slot+0u]=lx+bx; outd[4u*slot+1u]=ly+by; outd[4u*slot+2u]=lz+bz; outd[4u*slot+3u]=__float_as_int(val[v]); }\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_merge_scatter(float* outv, const float* src,\n"
"    int snx, int sny, int snz, int onx, int ony, int onz, int offx, int offy, int offz, unsigned int count) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= count) return;\n"
"  int iz = (int)(i / (unsigned int)(snx * sny));\n"
"  int rem = (int)(i - (unsigned int)(iz * snx * sny));\n"
"  int iy = rem / snx; int ix = rem - iy * snx;\n"
"  int ox = ix + offx, oy = iy + offy, oz = iz + offz;\n"
"  if (ox < 0 || oy < 0 || oz < 0 || ox >= onx || oy >= ony || oz >= onz) return;\n"
"  tvdb_atomic_min_f(&outv[(oz * ony + oy) * onx + ox], src[i]);\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_active_coords(const float* data, unsigned int* counter, int* outd,\n"
"    int nx, int ny, int nz, float background, float tolerance, unsigned int cap) {\n"
"  unsigned int v = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  unsigned int total = (unsigned int)(nx * ny * nz);\n"
"  if (v >= total) return;\n"
"  float val = data[v];\n"
"  if (fabsf(val - background) <= tolerance) return;\n"
"  int iz = (int)(v / (unsigned int)(nx * ny));\n"
"  int rem = (int)(v - (unsigned int)(iz * nx * ny));\n"
"  int iy = rem / nx; int ix = rem - iy * nx;\n"
"  unsigned int slot = atomicAdd(counter, 1u);\n"
"  if (slot < cap) { outd[4u*slot+0u]=ix; outd[4u*slot+1u]=iy; outd[4u*slot+2u]=iz; outd[4u*slot+3u]=__float_as_int(val); }\n"
"}\n"
"/* One partial per block, reduced in shared memory (see tvdb_cuda_stats). */\n"
"extern \"C\" __global__ void tvdb_cuda_checksum(const unsigned int* data, unsigned int* partials,\n"
"                                               unsigned int count, unsigned int ngroups) {\n"
"  __shared__ unsigned int sh[256];\n"
"  unsigned int lid = threadIdx.x;\n"
"  unsigned int s = 0u;\n"
"  for (unsigned int i = blockIdx.x * 256u + lid; i < count; i += ngroups * 256u) {\n"
"    unsigned int h = data[i] ^ (i * 2654435761u); h *= 2654435761u; h ^= h >> 15; s += h;\n"
"  }\n"
"  sh[lid] = s;\n"
"  __syncthreads();\n"
"  for (unsigned int t = 128u; t > 0u; t >>= 1u) {\n"
"    if (lid < t) sh[lid] += sh[lid + t];\n"
"    __syncthreads();\n"
"  }\n"
"  if (lid == 0u) partials[blockIdx.x] = sh[0];\n"
"}\n"
"__device__ void tvdb_tri_closest(const float* p, const float* a, const float* b, const float* c, float* o) {\n"
"  float ab[3]={b[0]-a[0],b[1]-a[1],b[2]-a[2]}, ac[3]={c[0]-a[0],c[1]-a[1],c[2]-a[2]}, ap[3]={p[0]-a[0],p[1]-a[1],p[2]-a[2]};\n"
"  float d1=ab[0]*ap[0]+ab[1]*ap[1]+ab[2]*ap[2], d2=ac[0]*ap[0]+ac[1]*ap[1]+ac[2]*ap[2];\n"
"  if (d1<=0.0f && d2<=0.0f) { o[0]=a[0];o[1]=a[1];o[2]=a[2]; return; }\n"
"  float bp[3]={p[0]-b[0],p[1]-b[1],p[2]-b[2]};\n"
"  float d3=ab[0]*bp[0]+ab[1]*bp[1]+ab[2]*bp[2], d4=ac[0]*bp[0]+ac[1]*bp[1]+ac[2]*bp[2];\n"
"  if (d3>=0.0f && d4<=d3) { o[0]=b[0];o[1]=b[1];o[2]=b[2]; return; }\n"
"  float vc=d1*d4-d3*d2;\n"
"  if (vc<=0.0f && d1>=0.0f && d3<=0.0f) { float v=d1/(d1-d3); o[0]=a[0]+ab[0]*v;o[1]=a[1]+ab[1]*v;o[2]=a[2]+ab[2]*v; return; }\n"
"  float cp[3]={p[0]-c[0],p[1]-c[1],p[2]-c[2]};\n"
"  float d5=ab[0]*cp[0]+ab[1]*cp[1]+ab[2]*cp[2], d6=ac[0]*cp[0]+ac[1]*cp[1]+ac[2]*cp[2];\n"
"  if (d6>=0.0f && d5<=d6) { o[0]=c[0];o[1]=c[1];o[2]=c[2]; return; }\n"
"  float vb=d5*d2-d1*d6;\n"
"  if (vb<=0.0f && d2>=0.0f && d6<=0.0f) { float w=d2/(d2-d6); o[0]=a[0]+ac[0]*w;o[1]=a[1]+ac[1]*w;o[2]=a[2]+ac[2]*w; return; }\n"
"  float va=d3*d6-d5*d4;\n"
"  if (va<=0.0f && (d4-d3)>=0.0f && (d5-d6)>=0.0f) { float w=(d4-d3)/((d4-d3)+(d5-d6)); o[0]=b[0]+(c[0]-b[0])*w;o[1]=b[1]+(c[1]-b[1])*w;o[2]=b[2]+(c[2]-b[2])*w; return; }\n"
"  float denom=1.0f/(va+vb+vc); float vbn=vb*denom, vcn=vc*denom;\n"
"  o[0]=a[0]+ab[0]*vbn+ac[0]*vcn; o[1]=a[1]+ab[1]*vbn+ac[1]*vcn; o[2]=a[2]+ab[2]*vbn+ac[2]*vcn;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_mesh_to_sdf(const float* verts, const float* normals, float* out_sdf,\n"
"    int nx, int ny, int nz, float ox, float oy, float oz, float vs, float band, unsigned int face_count,\n"
"    int z_begin, int z_count) {\n"
"  /* One slab of z slices per launch, matching the Vulkan shader. Each thread\n"
"     writes its true global voxel index, so the slabs compose to exactly the\n"
"     same field as a single launch over the whole grid. */\n"
"  unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  unsigned int slice = (unsigned int)(nx * ny);\n"
"  if (slice == 0u) return;\n"
"  if (gid >= slice * (unsigned int)z_count) return;\n"
"  int iz = z_begin + (int)(gid / slice);\n"
"  int rem = (int)(gid - (unsigned int)(iz - z_begin) * slice);\n"
"  int iy=rem/nx; int ix=rem-iy*nx;\n"
"  float p[3]={ox+((float)ix+0.5f)*vs, oy+((float)iy+0.5f)*vs, oz+((float)iz+0.5f)*vs};\n"
"  float best=1e30f, bcp[3]={0,0,0}, bn[3]={0,0,0};\n"
"  for (unsigned int f=0; f<face_count; ++f) {\n"
"    const float* a=&verts[9u*f]; const float* b=&verts[9u*f+3u]; const float* c=&verts[9u*f+6u];\n"
"    float q[3]; tvdb_tri_closest(p,a,b,c,q);\n"
"    float dx=p[0]-q[0],dy=p[1]-q[1],dz=p[2]-q[2]; float dsq=dx*dx+dy*dy+dz*dz;\n"
"    if (dsq<best) { best=dsq; bcp[0]=q[0];bcp[1]=q[1];bcp[2]=q[2]; bn[0]=normals[3u*f];bn[1]=normals[3u*f+1u];bn[2]=normals[3u*f+2u]; }\n"
"  }\n"
"  float dist=sqrtf(best);\n"
"  float s=((p[0]-bcp[0])*bn[0]+(p[1]-bcp[1])*bn[1]+(p[2]-bcp[2])*bn[2])>=0.0f?1.0f:-1.0f;\n"
"  float v=s*dist; if (v>band) v=band; if (v<-band) v=-band;\n"
"  out_sdf[(unsigned int)((iz*ny + iy)*nx + ix)]=v;\n"
"}\n"
"__device__ void tvdb_mc_interp(float iso, const float* p1, const float* p2, float v1, float v2, float* o) {\n"
"  if(fmaxf(fabsf(iso),fmaxf(fabsf(v1),fabsf(v2)))>1e30f){const float scale=5.421010862427522e-20f;iso*=scale;v1*=scale;v2*=scale;} float numerator=iso-v1,delta=v2-v1;\n"
"  float mu=fminf(1.0f,fmaxf(0.0f,numerator/delta)); o[0]=p1[0]+mu*(p2[0]-p1[0]); o[1]=p1[1]+mu*(p2[1]-p1[1]); o[2]=p1[2]+mu*(p2[2]-p1[2]);\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_marching_cubes_resident(const float* grid,const int* tables,float* out_verts,int* tri_counts,const int* u) {\n"
"  int nx=u[0],ny=u[1],nz=u[2];\n"
"  const float* f=(const float*)u;\n"
"  float ox=f[4],oy=f[5],oz=f[6],vs=f[7],isovalue=f[8];\n"
"  unsigned int cell_count=(unsigned int)u[9];\n"
"  unsigned int gid = (blockIdx.x+blockIdx.y*gridDim.x) * blockDim.x + threadIdx.x;\n"
"  if (gid >= cell_count) return;\n"
"  const int CN[8][3]={{0,0,0},{1,0,0},{1,1,0},{0,1,0},{0,0,1},{1,0,1},{1,1,1},{0,1,1}};\n"
"  const int EA[12]={0,1,2,3,4,5,6,7,0,1,2,3}; const int EB[12]={1,2,3,0,5,6,7,4,4,5,6,7};\n"
"  int cnx=nx-1, cny=ny-1;\n"
"  int cz=(int)(gid/(unsigned int)(cnx*cny)); int rem=(int)(gid-(unsigned int)(cz*cnx*cny)); int cy=rem/cnx; int cx=rem-cy*cnx;\n"
"  float val[8]; int gc[8][3]; int cube=0;\n"
"  for (int i=0;i<8;++i){ gc[i][0]=cx+CN[i][0]; gc[i][1]=cy+CN[i][1]; gc[i][2]=cz+CN[i][2];\n"
"    val[i]=grid[(gc[i][2]*ny+gc[i][1])*nx+gc[i][0]]; if (val[i]<isovalue) cube|=(1<<i); }\n"
"  int edges=tables[cube]; if(u[10]==0) { int count=0; for(int i=0;i<16 && tables[256+cube*16+i]!=-1;i+=3)++count;tri_counts[gid]=count;return; }\n"
"  if(edges==0)return;\n"
"  float ev[12][3];\n"
"  for (int e=0;e<12;++e){ if((edges&(1<<e))==0) continue; int a=EA[e],b=EB[e];\n"
"    float pa[3]={ox+((float)gc[a][0]+0.5f)*vs, oy+((float)gc[a][1]+0.5f)*vs, oz+((float)gc[a][2]+0.5f)*vs};\n"
"    float pb[3]={ox+((float)gc[b][0]+0.5f)*vs, oy+((float)gc[b][1]+0.5f)*vs, oz+((float)gc[b][2]+0.5f)*vs};\n"
"    tvdb_mc_interp(isovalue,pa,pb,val[a],val[b],ev[e]); }\n"
"  int tc=0;\n"
"  for (int i=0;i<16 && tables[256+cube*16+i]!=-1; i+=3){\n"
"    int e0=tables[256+cube*16+i],e1=tables[256+cube*16+i+1],e2=tables[256+cube*16+i+2];\n"
"    unsigned int base=((unsigned int)tri_counts[gid]+(unsigned int)tc)*9u;\n"
"    out_verts[base+0]=ev[e0][0];out_verts[base+1]=ev[e0][1];out_verts[base+2]=ev[e0][2];\n"
"    out_verts[base+3]=ev[e1][0];out_verts[base+4]=ev[e1][1];out_verts[base+5]=ev[e1][2];\n"
"    out_verts[base+6]=ev[e2][0];out_verts[base+7]=ev[e2][1];out_verts[base+8]=ev[e2][2]; ++tc; }\n"
"\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_scan(unsigned int* data,unsigned int* blocks,const unsigned int* u) {\n"
" if((blockIdx.x+blockIdx.y*gridDim.x)>=(u[0]+127u)/128u)return;\n"
"  unsigned int i=(blockIdx.x+blockIdx.y*gridDim.x)*128u+threadIdx.x,l=threadIdx.x,b=(blockIdx.x+blockIdx.y*gridDim.x);\n"
"  if(u[1]==1u){if(i<u[0])data[i]+=blocks[b];return;}\n"
"  __shared__ unsigned int scan[128];scan[l]=i<u[0]?data[i]:0u;__syncthreads();\n"
"  for(unsigned int s=1;s<128;s<<=1){unsigned int v=l>=s?scan[l-s]:0u;__syncthreads();scan[l]+=v;__syncthreads();}\n"
"  if(i<u[0])data[i]=l==0?0:scan[l-1];\n"
"  if(l==127)blocks[b]=scan[l];\n"
"}\n"
"__device__ float tvdb_strided_lookup(const tvdb_int4* in_data, unsigned int n_in, long long x, long long y, long long z, float pad) {\n"
"  for (unsigned int i=0;i<n_in;++i){ tvdb_int4 c=in_data[i]; if(c.x==x&&c.y==y&&c.z==z) return __int_as_float(c.w); }\n"
"  return pad;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_sparse_conv_strided(const tvdb_int4* in_data, const tvdb_int4* out_coords,\n"
"    const float* kernel, float* out_values, unsigned int n_in, unsigned int n_out, int kx, int ky, int kz,\n"
"    int stride, float pad_value) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= n_out) return;\n"
"  tvdb_int4 oc = out_coords[i];\n"
"  int ax=kx/2, ay=ky/2, az=kz/2; float acc=0.0f;\n"
"  for (int dk=0;dk<kz;++dk) for (int dj=0;dj<ky;++dj) for (int di=0;di<kx;++di){\n"
"    int ki=(dk*ky+dj)*kx+di;\n"
"    acc += kernel[ki]*tvdb_strided_lookup(in_data, n_in, (long long)oc.x*stride+di-ax, (long long)oc.y*stride+dj-ay, (long long)oc.z*stride+dk-az, pad_value);\n"
"  }\n"
"  out_values[i]=acc;\n"
"}\n"
"__device__ void tvdb_atomic_add_f(float* addr, float val) {\n"
"  int* a=(int*)addr; int old=atomicCAS(a,0,0), assumed;\n"
"  do { assumed=old; old=atomicCAS(a, assumed, __float_as_int(__int_as_float(assumed)+val)); } while (assumed!=old);\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_conv_transpose_scatter(float* v2, unsigned int* occ,\n"
"    const tvdb_int4* in_data, const float* kernel, int dx, int dy, int dz, int bx, int by, int bz,\n"
"    int kx, int ky, int kz, int stride, unsigned int n_in) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= n_in) return;\n"
"  tvdb_int4 c = in_data[i]; float v = __int_as_float(c.w);\n"
"  int ax=kx/2, ay=ky/2, az=kz/2;\n"
"  for (int dk=0;dk<kz;++dk) for (int dj=0;dj<ky;++dj) for (int di=0;di<kx;++di){\n"
"    int ki=(dk*ky+dj)*kx+di;\n"
"    long long ox=(long long)c.x*stride+di-ax-bx, oy=(long long)c.y*stride+dj-ay-by, oz=(long long)c.z*stride+dk-az-bz;\n"
"    unsigned int lin=(unsigned int)((oz*dy+oy)*dx+ox);\n"
"    tvdb_atomic_add_f(&v2[lin], kernel[ki]*v); atomicOr(&occ[lin],1u);\n"
"  }\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_gaussian_forward(const float* gauss, const tvdb_int4* entries,\n"
"    float* out_image, float* out_aux, unsigned int W, unsigned int H, unsigned int NF, unsigned int TS,\n"
"    unsigned int num_entries, float alpha_threshold, float bg0, float bg1, float bg2) {\n"
"  unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (gid >= W*H) return;\n"
"  int px = (int)(gid % W), py = (int)(gid / W);\n"
"  int my_tx = px/(int)TS, my_ty = py/(int)TS;\n"
"  float bg[3] = {bg0,bg1,bg2}; float img[3]; for (unsigned int f=0;f<NF;++f) img[f]=bg[f];\n"
"  float a_acc = 0.0f; int last = -1;\n"
"  for (unsigned int e=0;e<num_entries;++e){ tvdb_int4 ent=entries[e];\n"
"    if (ent.y!=my_tx || ent.z!=my_ty) continue;\n"
"    unsigned int g=(unsigned int)ent.x*12u;\n"
"    float dx=(float)px-gauss[g+0], dy=(float)py-gauss[g+1];\n"
"    float sigma=0.5f*(gauss[g+2]*dx*dx + 2.0f*gauss[g+3]*dx*dy + gauss[g+4]*dy*dy);\n"
"    if (sigma>10.0f) continue;\n"
"    float ga=gauss[g+5]*expf(-sigma); if (ga<alpha_threshold) continue;\n"
"    float T=1.0f-a_acc; if (T<0.001f) continue;\n"
"    a_acc += ga*T; for (unsigned int f=0;f<NF;++f) img[f]+=gauss[g+8+f]*ga*T; last=ent.x;\n"
"  }\n"
"  for (unsigned int f=0;f<NF;++f) out_image[gid*NF+f]=img[f];\n"
"  out_aux[gid*2u+0u]=a_acc; out_aux[gid*2u+1u]=__int_as_float(last);\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_gaussian_backward(const float* gauss, const tvdb_int4* entries,\n"
"    const float* pixel, float* grad, unsigned int W, unsigned int H, unsigned int F, unsigned int TS,\n"
"    unsigned int num_entries, float alpha_threshold, int has_dLdA, float bg0, float bg1, float bg2) {\n"
"  unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (gid >= W*H) return;\n"
"  int px=(int)(gid%W), py=(int)(gid/W); int my_tx=px/(int)TS, my_ty=py/(int)TS;\n"
"  unsigned int stride=F+2u, base=gid*stride; float bg[3]={bg0,bg1,bg2};\n"
"  float Tfin=1.0f-pixel[base+F]; if (Tfin<0.0f) Tfin=0.0f;\n"
"  float Tc=Tfin; float Sc[3]; for (unsigned int f=0;f<F;++f) Sc[f]=Tfin*bg[f];\n"
"  float dLdA = has_dLdA ? pixel[base+F+1u] : 0.0f;\n"
"  for (unsigned int e=num_entries; e>0u; --e){ tvdb_int4 ent=entries[e-1u];\n"
"    if (ent.y!=my_tx || ent.z!=my_ty) continue;\n"
"    unsigned int g=(unsigned int)ent.x*12u;\n"
"    float a_c=gauss[g+2],b_c=gauss[g+3],c_c=gauss[g+4],opac=gauss[g+5];\n"
"    float dx=(float)px-gauss[g+0], dy=(float)py-gauss[g+1];\n"
"    float sigma=0.5f*(a_c*dx*dx+2.0f*b_c*dx*dy+c_c*dy*dy); if (sigma>10.0f) continue;\n"
"    float G=expf(-sigma); float alpha=opac*G; if (alpha<alpha_threshold) continue;\n"
"    float one_m=1.0f-alpha; if (one_m<1e-7f) one_m=1e-7f; float T_pre=Tc/one_m; if (T_pre<0.001f) continue;\n"
"    unsigned int gb=(unsigned int)ent.x*(6u+F); float w=T_pre*alpha; float dotCf=0.0f,dotCS=0.0f;\n"
"    for (unsigned int f=0;f<F;++f){ float dLdCf=pixel[base+f]; float feat=gauss[g+8u+f]; dotCf+=dLdCf*feat; dotCS+=dLdCf*Sc[f]; tvdb_atomic_add_f(&grad[gb+6u+f], dLdCf*w); }\n"
"    float dL_dalpha=T_pre*dotCf - dotCS/one_m; if (has_dLdA) dL_dalpha += dLdA*Tfin/one_m;\n"
"    tvdb_atomic_add_f(&grad[gb+5u], dL_dalpha*G); float dL_dsigma=-alpha*dL_dalpha;\n"
"    tvdb_atomic_add_f(&grad[gb+0u], dL_dsigma*-(a_c*dx+b_c*dy));\n"
"    tvdb_atomic_add_f(&grad[gb+1u], dL_dsigma*-(b_c*dx+c_c*dy));\n"
"    tvdb_atomic_add_f(&grad[gb+2u], dL_dsigma*0.5f*dx*dx);\n"
"    tvdb_atomic_add_f(&grad[gb+3u], dL_dsigma*dx*dy);\n"
"    tvdb_atomic_add_f(&grad[gb+4u], dL_dsigma*0.5f*dy*dy);\n"
"    for (unsigned int f=0;f<F;++f) Sc[f]+=w*gauss[g+8u+f]; Tc=T_pre;\n"
"  }\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_ssim(const float* a, const float* b, const float* win, float* ssim,\n"
"    int W, int H, int C, int R, float c1, float c2) {\n"
"  unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (gid >= (unsigned int)(W*H)) return;\n"
"  int px=(int)gid%W, py=(int)gid/W; int win_n=2*R+1; float ssim_sum=0.0f;\n"
"  for (int c=0;c<C;++c){ float ma=0,mb=0,maa=0,mbb=0,mab=0;\n"
"    for (int dy=-R;dy<=R;++dy) for (int dx=-R;dx<=R;++dx){\n"
"      int qx=px+dx; if(qx<0)qx=0; if(qx>=W)qx=W-1; int qy=py+dy; if(qy<0)qy=0; if(qy>=H)qy=H-1;\n"
"      float wgt=win[(dy+R)*win_n+(dx+R)]; float va=a[(qy*W+qx)*C+c], vb=b[(qy*W+qx)*C+c];\n"
"      ma+=wgt*va; mb+=wgt*vb; maa+=wgt*va*va; mbb+=wgt*vb*vb; mab+=wgt*va*vb;\n"
"    }\n"
"    float va2=maa-ma*ma, vb2=mbb-mb*mb, vab=mab-ma*mb;\n"
"    float num=(2.0f*ma*mb+c1)*(2.0f*vab+c2); float den=(ma*ma+mb*mb+c1)*(va2+vb2+c2);\n"
"    ssim_sum += num/den;\n"
"  }\n"
"  ssim[gid] = ssim_sum/(float)C;\n"
"}\n"
"__device__ float tvdb_batched_lookup(const tvdb_int4* in_data, int lo, int hi, int x, int y, int z, float pad) {\n"
"  for (int j=lo;j<hi;++j){ tvdb_int4 c=in_data[j]; if(c.x==x&&c.y==y&&c.z==z) return __int_as_float(c.w); }\n"
"  return pad;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_sparse_conv_batched(const tvdb_int4* in_data, const int* range,\n"
"    const float* kernel, float* out_values, unsigned int total, int kx, int ky, int kz, float pad_value) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= total) return;\n"
"  int lo=range[2u*i+0u], hi=range[2u*i+1u]; tvdb_int4 c=in_data[i];\n"
"  int ax=kx/2, ay=ky/2, az=kz/2; float acc=0.0f;\n"
"  for (int dk=0;dk<kz;++dk) for (int dj=0;dj<ky;++dj) for (int di=0;di<kx;++di){\n"
"    int ki=(dk*ky+dj)*kx+di;\n"
"    acc += kernel[ki]*tvdb_batched_lookup(in_data, lo, hi, (long long)c.x+di-ax, (long long)c.y+dj-ay, (long long)c.z+dk-az, pad_value);\n"
"  }\n"
"  out_values[i]=acc;\n"
"}\n"
"__device__ double tvdb_measure_count(const float* src, int nx, int ny, int nz,\n"
"                                    unsigned int i, unsigned int n, int op) {\n"
"  if (op == 1) { if (src[i] < 0.0f) return 1.0; return 0.0; }\n"
"  unsigned int unx=(unsigned int)nx, uny=(unsigned int)ny;\n"
"  unsigned int ix=i%unx; unsigned int rem=i/unx; unsigned int iy=rem%uny; unsigned int iz=rem/uny;\n"
"  float c=src[i]; double a=0.0;\n"
"  if (ix+1u<unx) { float v=src[i+1u];            if ((c<0.0f)!=(v<0.0f)) a+=1.0; }\n"
"  if (iy+1u<uny) { float v=src[i+unx];           if ((c<0.0f)!=(v<0.0f)) a+=1.0; }\n"
"  if (iz+1u<(unsigned int)nz) { float v=src[i+unx*uny]; if ((c<0.0f)!=(v<0.0f)) a+=1.0; }\n"
"  return a;\n"
"}\n"
"__device__ double tvdb_measure_count_d(const double* src, int nx, int ny, int nz,\n"
"                                      unsigned int i, unsigned int n, int op) {\n"
"  if (op == 1) { if (src[i] < 0.0) return 1.0; return 0.0; }\n"
"  unsigned int unx=(unsigned int)nx, uny=(unsigned int)ny;\n"
"  unsigned int ix=i%unx; unsigned int rem=i/unx; unsigned int iy=rem%uny; unsigned int iz=rem/uny;\n"
"  double c=src[i]; double a=0.0;\n"
"  if (ix+1u<unx) { double v=src[i+1u];            if ((c<0.0)!=(v<0.0)) a+=1.0; }\n"
"  if (iy+1u<uny) { double v=src[i+unx];           if ((c<0.0)!=(v<0.0)) a+=1.0; }\n"
"  if (iz+1u<(unsigned int)nz) { double v=src[i+unx*uny]; if ((c<0.0)!=(v<0.0)) a+=1.0; }\n"
"  return a;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_measure(const float* src, double* partials,\n"
"                                                int nx, int ny, int nz, unsigned int n,\n"
"                                                unsigned int ngroups, int op) {\n"
"  __shared__ double sdata[256];\n"
"  unsigned int gid = blockIdx.x*blockDim.x+threadIdx.x;\n"
"  unsigned int lid = threadIdx.x;\n"
"  double acc = 0.0;\n"
"  unsigned int stride = ngroups*blockDim.x;\n"
"  for (unsigned int i=gid; i<n; i+=stride) acc += tvdb_measure_count(src,nx,ny,nz,i,n,op);\n"
"  sdata[lid]=acc; __syncthreads();\n"
"  for (unsigned int s=128u; s>0u; s>>=1u) { if (lid<s) sdata[lid]+=sdata[lid+s]; __syncthreads(); }\n"
"  if (lid==0u) partials[blockIdx.x]=sdata[0];\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_measure_d(const double* src, double* partials,\n"
"                                                  int nx, int ny, int nz, unsigned int n,\n"
"                                                  unsigned int ngroups, int op) {\n"
"  __shared__ double sdata[256];\n"
"  unsigned int gid = blockIdx.x*blockDim.x+threadIdx.x;\n"
"  unsigned int lid = threadIdx.x;\n"
"  double acc = 0.0;\n"
"  unsigned int stride = ngroups*blockDim.x;\n"
"  for (unsigned int i=gid; i<n; i+=stride) acc += tvdb_measure_count_d(src,nx,ny,nz,i,n,op);\n"
"  sdata[lid]=acc; __syncthreads();\n"
"  for (unsigned int s=128u; s>0u; s>>=1u) { if (lid<s) sdata[lid]+=sdata[lid+s]; __syncthreads(); }\n"
"  if (lid==0u) partials[blockIdx.x]=sdata[0];\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_measure_sum(const double* partials, double* out,\n"
"                                                    unsigned int ngroups) {\n"
"  __shared__ double sdata[256];\n"
"  unsigned int gid=blockIdx.x*blockDim.x+threadIdx.x, lid=threadIdx.x;\n"
"  double acc=0.0;\n"
"  for (unsigned int i=gid; i<ngroups; i+=256u) acc+=partials[i];\n"
"  sdata[lid]=acc; __syncthreads();\n"
"  for (unsigned int s=128u; s>0u; s>>=1u) { if (lid<s) sdata[lid]+=sdata[lid+s]; __syncthreads(); }\n"
"  if (lid==0u) out[0]=sdata[0];\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_stencil_scalar_scalar_resident(const float* src,float* dst,const int* u) {\n"
"int nx=u[0],ny=u[1],nz=u[2],op=u[3];float scale;memcpy(&scale,u+4,4);\n"
"\n"
"  int ix = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  int iy = blockIdx.y * blockDim.y + threadIdx.y;\n"
"  int iz = blockIdx.z;\n"
"  if (ix >= nx || iy >= ny || iz >= nz) return;\n"
"  #define TVDB_C_AT(X, Y, Z) src[(size_t)(tvdb_c_cl((Z), nz) * ny + tvdb_c_cl((Y), ny)) * nx + tvdb_c_cl((X), nx)]\n"
"  float v;\n"
"  if (op == 0) {\n"
"    float s = TVDB_C_AT(ix-1, iy, iz) + TVDB_C_AT(ix+1, iy, iz)\n"
"            + TVDB_C_AT(ix, iy-1, iz) + TVDB_C_AT(ix, iy+1, iz)\n"
"            + TVDB_C_AT(ix, iy, iz-1) + TVDB_C_AT(ix, iy, iz+1);\n"
"    v = (s - 6.0f * TVDB_C_AT(ix, iy, iz)) * scale;\n"
"  } else if (op == 1) v = (TVDB_C_AT(ix+1, iy, iz) - TVDB_C_AT(ix-1, iy, iz)) * scale;\n"
"  else if (op == 2) v = (TVDB_C_AT(ix, iy+1, iz) - TVDB_C_AT(ix, iy-1, iz)) * scale;\n"
"  else v = (TVDB_C_AT(ix, iy, iz+1) - TVDB_C_AT(ix, iy, iz-1)) * scale;\n"
"  #undef TVDB_C_AT\n"
"  dst[(size_t)iz * ny * nx + (size_t)iy * nx + ix] = v;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_stencil_scalar_d_resident(const double* src,double* dst,const int* u) {\n"
"int nx=u[0],ny=u[1],nz=u[2],op=u[3];double scale;memcpy(&scale,u+4,8);\n"
"\n"
"  int ix = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  int iy = blockIdx.y * blockDim.y + threadIdx.y;\n"
"  int iz = blockIdx.z;\n"
"  if (ix >= nx || iy >= ny || iz >= nz) return;\n"
"  #define TVDB_CD_AT(X, Y, Z) src[(size_t)(tvdb_c_cl((Z), nz) * ny + tvdb_c_cl((Y), ny)) * nx + tvdb_c_cl((X), nx)]\n"
"  double v;\n"
"  if (op == 0) {\n"
"    double t = TVDB_CD_AT(ix-1, iy, iz) + TVDB_CD_AT(ix+1, iy, iz)\n"
"            + TVDB_CD_AT(ix, iy-1, iz) + TVDB_CD_AT(ix, iy+1, iz)\n"
"            + TVDB_CD_AT(ix, iy, iz-1) + TVDB_CD_AT(ix, iy, iz+1);\n"
"    v = (t - 6.0 * TVDB_CD_AT(ix, iy, iz)) * scale;\n"
"  } else if (op == 1) v = (TVDB_CD_AT(ix+1, iy, iz) - TVDB_CD_AT(ix-1, iy, iz)) * scale;\n"
"  else if (op == 2) v = (TVDB_CD_AT(ix, iy+1, iz) - TVDB_CD_AT(ix, iy-1, iz)) * scale;\n"
"  else v = (TVDB_CD_AT(ix, iy, iz+1) - TVDB_CD_AT(ix, iy, iz-1)) * scale;\n"
"  #undef TVDB_CD_AT\n"
"  dst[(size_t)iz * ny * nx + (size_t)iy * nx + ix] = v;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_stencil_scalar_vec_resident(const float* src,float* dst,const int* u) {\n"
"int nx=u[0],ny=u[1],nz=u[2],op=u[3];const float* f=(const float*)u;float scale=f[4],ox=f[8],oy=f[9],oz=f[10],vs=f[11];\n"
"\n"
"  int ix = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  int iy = blockIdx.y * blockDim.y + threadIdx.y;\n"
"  int iz = blockIdx.z;\n"
"  if (ix >= nx || iy >= ny || iz >= nz) return;\n"
"  #define TVDB_C_AT(X, Y, Z) src[(size_t)(tvdb_c_cl((Z), nz) * ny + tvdb_c_cl((Y), ny)) * nx + tvdb_c_cl((X), nx)]\n"
"  float gx = (TVDB_C_AT(ix+1, iy, iz) - TVDB_C_AT(ix-1, iy, iz)) * scale;\n"
"  float gy = (TVDB_C_AT(ix, iy+1, iz) - TVDB_C_AT(ix, iy-1, iz)) * scale;\n"
"  float gz = (TVDB_C_AT(ix, iy, iz+1) - TVDB_C_AT(ix, iy, iz-1)) * scale;\n"
"  size_t i = 3u * ((size_t)iz * ny * nx + (size_t)iy * nx + ix);\n"
"  if (op == 1) {\n"
"    float d = TVDB_C_AT(ix, iy, iz);\n"
"    float px = ox + ((float)ix + 0.5f) * vs;\n"
"    float py = oy + ((float)iy + 0.5f) * vs;\n"
"    float pz = oz + ((float)iz + 0.5f) * vs;\n"
"    dst[i+0] = px - d*gx; dst[i+1] = py - d*gy; dst[i+2] = pz - d*gz;\n"
"    #undef TVDB_C_AT\n"
"    return;\n"
"  }\n"
"  #undef TVDB_C_AT\n"
"  dst[i+0] = gx; dst[i+1] = gy; dst[i+2] = gz;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_stencil_vec_scalar_resident(const float* src,float* dst,const int* u) {\n"
"int nx=u[0],ny=u[1],nz=u[2],op=u[3];float scale;memcpy(&scale,u+4,4);\n"
"\n"
"  int ix = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  int iy = blockIdx.y * blockDim.y + threadIdx.y;\n"
"  int iz = blockIdx.z;\n"
"  if (ix >= nx || iy >= ny || iz >= nz) return;\n"
"  (void)op;\n"
"  #define TVDB_C_AT(X, Y, Z, C) src[3u * (((size_t)tvdb_c_cl((Z), nz) * ny + tvdb_c_cl((Y), ny)) * nx + tvdb_c_cl((X), nx)) + (C)]\n"
"  float dvx = (TVDB_C_AT(ix+1, iy, iz, 0) - TVDB_C_AT(ix-1, iy, iz, 0)) * scale;\n"
"  float dvy = (TVDB_C_AT(ix, iy+1, iz, 1) - TVDB_C_AT(ix, iy-1, iz, 1)) * scale;\n"
"  float dvz = (TVDB_C_AT(ix, iy, iz+1, 2) - TVDB_C_AT(ix, iy, iz-1, 2)) * scale;\n"
"  size_t oi = (size_t)iz * ny * nx + (size_t)iy * nx + ix;\n"
"  if (op == 1) {\n"
"    float x = TVDB_C_AT(ix, iy, iz, 0), y = TVDB_C_AT(ix, iy, iz, 1), z = TVDB_C_AT(ix, iy, iz, 2);\n"
"    dst[oi] = sqrtf(x*x + y*y + z*z);\n"
"    #undef TVDB_C_AT\n"
"    return;\n"
"  }\n"
"  #undef TVDB_C_AT\n"
"  dst[oi] = dvx + dvy + dvz;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_stencil_vec_vec_resident(const float* src,float* dst,const int* u) {\n"
"int nx=u[0],ny=u[1],nz=u[2],op=u[3];float scale;memcpy(&scale,u+4,4);\n"
"\n"
"  int ix = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  int iy = blockIdx.y * blockDim.y + threadIdx.y;\n"
"  int iz = blockIdx.z;\n"
"  if (ix >= nx || iy >= ny || iz >= nz) return;\n"
"  (void)op;\n"
"  #define TVDB_C_AT(X, Y, Z, C) src[3u * (((size_t)tvdb_c_cl((Z), nz) * ny + tvdb_c_cl((Y), ny)) * nx + tvdb_c_cl((X), nx)) + (C)]\n"
"  float dvz_dy = (TVDB_C_AT(ix, iy+1, iz, 2) - TVDB_C_AT(ix, iy-1, iz, 2)) * scale;\n"
"  float dvy_dz = (TVDB_C_AT(ix, iy, iz+1, 1) - TVDB_C_AT(ix, iy, iz-1, 1)) * scale;\n"
"  float dvx_dz = (TVDB_C_AT(ix, iy, iz+1, 0) - TVDB_C_AT(ix, iy, iz-1, 0)) * scale;\n"
"  float dvz_dx = (TVDB_C_AT(ix+1, iy, iz, 2) - TVDB_C_AT(ix-1, iy, iz, 2)) * scale;\n"
"  float dvy_dx = (TVDB_C_AT(ix+1, iy, iz, 1) - TVDB_C_AT(ix-1, iy, iz, 1)) * scale;\n"
"  float dvx_dy = (TVDB_C_AT(ix, iy+1, iz, 0) - TVDB_C_AT(ix, iy-1, iz, 0)) * scale;\n"
"  size_t i = 3u * ((size_t)iz * ny * nx + (size_t)iy * nx + ix);\n"
"  if (op == 1) {\n"
"    float x = TVDB_C_AT(ix, iy, iz, 0), y = TVDB_C_AT(ix, iy, iz, 1), z = TVDB_C_AT(ix, iy, iz, 2);\n"
"    float m = sqrtf(x*x + y*y + z*z);\n"
"    #undef TVDB_C_AT\n"
"    if (m > 0.0f) { dst[i+0] = x/m; dst[i+1] = y/m; dst[i+2] = z/m; }\n"
"    else         { dst[i+0] = 0.0f; dst[i+1] = 0.0f; dst[i+2] = 0.0f; }\n"
"    return;\n"
"  }\n"
"  #undef TVDB_C_AT\n"
"  dst[i+0] = dvz_dy - dvy_dz;\n"
"  dst[i+1] = dvx_dz - dvz_dx;\n"
"  dst[i+2] = dvy_dx - dvx_dy;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_csg_resident(const float* a,const float* b,float* out_values,const int* u) {\n"
"unsigned int count=(unsigned int)u[0];int op=u[1];\n"
"\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= count) return;\n"
"  float va = a[i];\n"
"  float vb = b[i];\n"
"  out_values[i] = op == 0 ? fminf(va, vb) : (op == 1 ? fmaxf(va, vb) : fmaxf(va, -vb));\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_csg_d_resident(const double* a,const double* b,double* dst,const int* u) {\n"
"int nx=u[0],ny=u[1],nz=u[2],op=u[3];\n"
"\n"
"  int ix = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  int iy = blockIdx.y * blockDim.y + threadIdx.y;\n"
"  int iz = blockIdx.z;\n"
"  if (ix >= nx || iy >= ny || iz >= nz) return;\n"
"  size_t i = ((size_t)iz * ny + iy) * nx + ix;\n"
"  double va = a[i], vb = b[i];\n"
"  /* Comparison form, not fmin/fmax: the CPU twin is `va < vb ? va : vb`, and\n"
"   * the two disagree on signed zero, which a zero-crossing field reaches. */\n"
"  dst[i] = op == 0 ? (va < vb ? va : vb)\n"
"                  : (op == 1 ? (va > vb ? va : vb) : (va > -vb ? va : -vb));\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_morph_resident(const float* in_data,float* out_data,const int* u) {\n"
"int nx=u[0],ny=u[1],nz=u[2],is_dilate=u[4];\n"
"\n"
"  unsigned int gid = (blockIdx.x+blockIdx.y*gridDim.x) * blockDim.x + threadIdx.x;\n"
"  unsigned int total = (unsigned int)(nx * ny * nz);\n"
"  if (gid >= total) return;\n"
"  int iz = (int)(gid / (unsigned int)(nx * ny));\n"
"  int rem = (int)(gid - (unsigned int)(iz * nx * ny));\n"
"  int iy = rem / nx; int ix = rem - iy * nx;\n"
"  float r = in_data[gid];\n"
"  float xm = tvdb_fetch(in_data, nx, ny, nz, ix - 1, iy, iz);\n"
"  float xp = tvdb_fetch(in_data, nx, ny, nz, ix + 1, iy, iz);\n"
"  float ym = tvdb_fetch(in_data, nx, ny, nz, ix, iy - 1, iz);\n"
"  float yp = tvdb_fetch(in_data, nx, ny, nz, ix, iy + 1, iz);\n"
"  float zm = tvdb_fetch(in_data, nx, ny, nz, ix, iy, iz - 1);\n"
"  float zp = tvdb_fetch(in_data, nx, ny, nz, ix, iy, iz + 1);\n"
"  if (is_dilate != 0) {\n"
"    r = fminf(r, fminf(fminf(xm, xp), fminf(fminf(ym, yp), fminf(zm, zp))));\n"
"  } else {\n"
"    r = fmaxf(r, fmaxf(fmaxf(xm, xp), fmaxf(fmaxf(ym, yp), fmaxf(zm, zp))));\n"
"  }\n"
"  out_data[gid] = r;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_coarsen_resident(const float* in_data,float* out_data,const int* u) {\n"
"int inx=u[0],iny=u[1],inz=u[2],onx=u[4],ony=u[5],onz=u[6],factor=u[8];\n"
"\n"
"  unsigned int gid = (blockIdx.x+blockIdx.y*gridDim.x) * blockDim.x + threadIdx.x;\n"
"  unsigned int total = (unsigned int)(onx * ony * onz);\n"
"  if (gid >= total) return;\n"
"  int oz = (int)(gid / (unsigned int)(onx * ony));\n"
"  int rem = (int)(gid - (unsigned int)(oz * onx * ony));\n"
"  int oy = rem / onx; int ox = rem - oy * onx;\n"
"  float sum = 0.0f; int count = 0;\n"
"  for (int dz = 0; dz < factor; ++dz) { int sz = oz * factor + dz; if (sz >= inz) break;\n"
"    for (int dy = 0; dy < factor; ++dy) { int sy = oy * factor + dy; if (sy >= iny) break;\n"
"      for (int dx = 0; dx < factor; ++dx) { int sx = ox * factor + dx; if (sx >= inx) break;\n"
"        sum += in_data[(sz * iny + sy) * inx + sx]; ++count; } } }\n"
"  out_data[gid] = count > 0 ? sum / (float)count : 0.0f;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_refine_resident(const float* in_data,float* out_data,const int* u) {\n"
"int inx=u[0],iny=u[1],inz=u[2],onx=u[4],ony=u[5],onz=u[6];const float* f=(const float*)u;float iox=f[8],ioy=f[9],ioz=f[10],oox=f[12],ooy=f[13],ooz=f[14],ivs=f[16],ovs=f[17];\n"
"\n"
"  unsigned int gid = (blockIdx.x+blockIdx.y*gridDim.x) * blockDim.x + threadIdx.x;\n"
"  unsigned int total = (unsigned int)(onx * ony * onz);\n"
"  if (gid >= total) return;\n"
"  int oz = (int)(gid / (unsigned int)(onx * ony));\n"
"  int rem = (int)(gid - (unsigned int)(oz * onx * ony));\n"
"  int oy = rem / onx; int ox = rem - oy * onx;\n"
"  float wx = oox + ((float)ox + 0.5f) * ovs;\n"
"  float wy = ooy + ((float)oy + 0.5f) * ovs;\n"
"  float wz = ooz + ((float)oz + 0.5f) * ovs;\n"
"  float fx = (wx - iox) / ivs - 0.5f;\n"
"  float fy = (wy - ioy) / ivs - 0.5f;\n"
"  float fz = (wz - ioz) / ivs - 0.5f;\n"
"  int ix = (int)floorf(fx), iy = (int)floorf(fy), iz = (int)floorf(fz);\n"
"  float tx = fx - (float)ix, ty = fy - (float)iy, tz = fz - (float)iz;\n"
"  float c000 = tvdb_fetch(in_data, inx, iny, inz, ix, iy, iz);\n"
"  float c100 = tvdb_fetch(in_data, inx, iny, inz, ix+1, iy, iz);\n"
"  float c010 = tvdb_fetch(in_data, inx, iny, inz, ix, iy+1, iz);\n"
"  float c110 = tvdb_fetch(in_data, inx, iny, inz, ix+1, iy+1, iz);\n"
"  float c001 = tvdb_fetch(in_data, inx, iny, inz, ix, iy, iz+1);\n"
"  float c101 = tvdb_fetch(in_data, inx, iny, inz, ix+1, iy, iz+1);\n"
"  float c011 = tvdb_fetch(in_data, inx, iny, inz, ix, iy+1, iz+1);\n"
"  float c111 = tvdb_fetch(in_data, inx, iny, inz, ix+1, iy+1, iz+1);\n"
"  float c00 = c000 + (c100 - c000) * tx; float c10 = c010 + (c110 - c010) * tx;\n"
"  float c01 = c001 + (c101 - c001) * tx; float c11 = c011 + (c111 - c011) * tx;\n"
"  float c0 = c00 + (c10 - c00) * ty; float c1 = c01 + (c11 - c01) * ty;\n"
"  out_data[gid] = c0 + (c1 - c0) * tz;\n"
"}\n"
"typedef unsigned int uint;\n"
"__device__ double tvdb_rp_read_rhs(uint i,const unsigned int* rhs,const int* u){return u[9]!=0?__longlong_as_double(((unsigned long long)rhs[2u*i+1u]<<32)|rhs[2u*i]):double(__uint_as_float(rhs[i]));}\n"
"__device__ double tvdb_rp_read_x(uint i,const unsigned int* initial,const int* u){return u[9]!=0?__longlong_as_double(((unsigned long long)initial[2u*i+1u]<<32)|initial[2u*i]):double(__uint_as_float(initial[i]));}\n"
"__device__ double tvdb_rp_rounded(double v,const int* u){return u[8]!=0?v:double(float(v));}\n"
"__device__ bool tvdb_rp_work_double(int slot,const int* u){return slot==8 || u[9]!=0 || (u[8]!=0 && slot<6);}\n"
"__device__ uint tvdb_rp_work_index(int slot,uint i,const int* u){\n"
"    uint base=uint(slot);\n"
"    if(u[9]!=0)base*=2u;\n"
"    else if(u[8]!=0)base=slot<6?base*2u:base+6u;\n"
"    return base*uint(u[3])+i*(tvdb_rp_work_double(slot,u)?2u:1u);\n"
"}\n"
"__device__ double tvdb_rp_load_work(int slot,uint i,const unsigned int* work,const int* u){\n"
"    uint at=tvdb_rp_work_index(slot,i,u);\n"
"    return tvdb_rp_work_double(slot,u)?((const double*)work)[at/2u]:double(((const float*)work)[at]);\n"
"}\n"
"__device__ void tvdb_rp_store_work(int slot,uint i,double v,unsigned int* work,const int* u){\n"
"    uint at=tvdb_rp_work_index(slot,i,u);\n"
"    if(tvdb_rp_work_double(slot,u))((double*)work)[at/2u]=v;\n"
"    else ((float*)work)[at]=float(v);\n"
"}\n"
"__device__ double tvdb_rp_positive(uint i,int slot,const unsigned int* work,const int* u){\n"
"    uint nx=uint(u[0]),ny=uint(u[1]),plane=nx*ny;\n"
"    uint x=i%nx,y=(i/nx)%ny,z=i/plane;\n"
"    double c=tvdb_rp_load_work(slot,i,work,u),v=0.0;\n"
"    if(x>0u)v+=c-tvdb_rp_load_work(slot,i-1u,work,u);if(x+1u<nx)v+=c-tvdb_rp_load_work(slot,i+1u,work,u);\n"
"    if(y>0u)v+=c-tvdb_rp_load_work(slot,i-nx,work,u);if(y+1u<ny)v+=c-tvdb_rp_load_work(slot,i+nx,work,u);\n"
"    if(z>0u)v+=c-tvdb_rp_load_work(slot,i-plane,work,u);if(z+1u<uint(u[2]))v+=c-tvdb_rp_load_work(slot,i+plane,work,u);\n"
"    return v/((const double*)(u+12))[0];\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_resident_poisson(const unsigned int* rhs,const unsigned int* initial,unsigned int* work,const double* ri,double* ro,unsigned int* output_data,const int* u){\n"
" __shared__ double sums[512];\n"
"    uint i=((blockIdx.x+blockIdx.y*gridDim.x)*blockDim.x+threadIdx.x),n=uint(u[3]),lane=threadIdx.x;\n"
"    int op=u[4];\n"
"    if(op>=90){\n"
"        if((blockIdx.x+blockIdx.y*gridDim.x)>=(uint(op==100?u[10]:u[3])+127u)/128u)return;\n"
"        double a=0.0,b=0.0,c=0.0,d=0.0;\n"
"        if(op==100){if(i<uint(u[10])){a=ri[4u*i];b=ri[4u*i+1u];c=ri[4u*i+2u];d=ri[4u*i+3u];}}\n"
"        else if(i<n){\n"
"            if(op==91){a=tvdb_rp_read_rhs(i,rhs,u);b=fabs(a);c=tvdb_rp_read_x(i,initial,u);d=(isnan(a)||isinf(a)||isnan(c)||isinf(c))?1.0:0.0;}\n"
"            else {double v=tvdb_rp_load_work(u[5],i,work,u),w=tvdb_rp_load_work(u[6],i,work,u);a=v*w;b=v;c=fabs(v);d=(isnan(v)||isinf(v)||isnan(w)||isinf(w))?1.0:0.0;}\n"
"        }\n"
"        sums[lane]=a;sums[128u+lane]=b;sums[256u+lane]=c;sums[384u+lane]=d;__syncthreads();\n"
"        for(uint step=64u;step>0u;step/=2u){if(lane<step)for(uint k=0u;k<4u;++k)sums[128u*k+lane]+=sums[128u*k+lane+step];__syncthreads();}\n"
"        if(lane==0u)for(uint k=0u;k<4u;++k)ro[4u*(blockIdx.x+blockIdx.y*gridDim.x)+k]=sums[128u*k];return;\n"
"    }\n"
"    if(i>=n)return;\n"
"    int a=u[5],b=u[6],dst=u[7];\n"
"    if(op==0){tvdb_rp_store_work(0,i,tvdb_rp_rounded(tvdb_rp_read_x(i,initial,u)-((const double*)(u+12))[3],u),work,u);tvdb_rp_store_work(1,i,tvdb_rp_rounded(-tvdb_rp_read_rhs(i,rhs,u)+((const double*)(u+12))[1],u),work,u);tvdb_rp_store_work(6,i,tvdb_rp_read_x(i,initial,u),work,u);}\n"
"    if(op==1)tvdb_rp_store_work(dst,i,tvdb_rp_rounded(tvdb_rp_positive(i,a,work,u),u),work,u);\n"
"    if(op==2){double v=(u[11]!=0?-tvdb_rp_read_rhs(i,rhs,u)+((const double*)(u+12))[3]:tvdb_rp_load_work(1,i,work,u))-tvdb_rp_positive(i,a,work,u);tvdb_rp_store_work(dst,i,u[11]!=0?v:tvdb_rp_rounded(v,u),work,u);}\n"
"    if(op==3)tvdb_rp_store_work(dst,i,tvdb_rp_rounded(((const double*)(u+12))[1]*tvdb_rp_load_work(a,i,work,u)+((const double*)(u+12))[2]*tvdb_rp_load_work(b,i,work,u),u),work,u);\n"
"    if(op==4){uint nx=uint(u[0]),ny=uint(u[1]),x=i%nx,y=(i/nx)%ny,z=i/(nx*ny);\n"
"        int degree=int(x>0u)+int(x+1u<nx)+int(y>0u)+int(y+1u<ny)+int(z>0u)+int(z+1u<uint(u[2]));\n"
"        tvdb_rp_store_work(dst,i,degree>0?tvdb_rp_rounded(tvdb_rp_load_work(a,i,work,u)*((const double*)(u+12))[0]/double(degree),u):0.0,work,u);}\n"
"    if(op==5)tvdb_rp_store_work(dst,i,tvdb_rp_rounded(tvdb_rp_load_work(a,i,work,u)-((const double*)(u+12))[1],u),work,u);\n"
"    if(op==6){double v=tvdb_rp_load_work(a,i,work,u)+((const double*)(u+12))[3];tvdb_rp_store_work(dst,i,u[9]!=0?v:double(float(v)),work,u);}\n"
"    if(op==7){double v=tvdb_rp_load_work(a,i,work,u);if(u[9]!=0){unsigned long long bits=__double_as_longlong(v);output_data[2u*i]=(unsigned int)bits;output_data[2u*i+1u]=(unsigned int)(bits>>32);}else output_data[i]=__float_as_uint(float(v));}\n"
"    if(op==8)tvdb_rp_store_work(dst,i,tvdb_rp_load_work(a,i,work,u),work,u);\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_resident_map(const int* coords,unsigned int* slots,const unsigned int* u) {\n"
"    unsigned int i=((blockIdx.x+blockIdx.y*gridDim.x)*blockDim.x+threadIdx.x);\n"
"    if(u[2]==0u){if(i<u[1])slots[i]=0u;return;}\n"
"    if(i>=u[0])return;\n"
"    int x=coords[3u*i],y=coords[3u*i+1u],z=coords[3u*i+2u];\n"
"    unsigned int at=(((unsigned int)(x))*73856093u ^ ((unsigned int)(y))*19349663u ^ ((unsigned int)(z))*83492791u)&(u[1]-1u);\n"
"    for(unsigned int p=0u;p<u[1];++p) {\n"
"        unsigned int old=atomicCAS(&slots[at],0u,i+1u);\n"
"        if(old==0u){slots[u[1]+i]=0u;return;}\n"
"        unsigned int j=old-1u;\n"
"        if(coords[3u*j]==x && coords[3u*j+1u]==y && coords[3u*j+2u]==z){slots[u[1]+i]=atomicExch(&slots[at],i+1u);return;}\n"
"        at=(at+1u)&(u[1]-1u);\n"
"    }\n"
"}\n"
"__device__ bool tvdb_rs_add_ok(int a,int b,int& v) {\n"
"    if((b>0 && a>2147483647-b)||(b<0 && a<(-2147483647-1)-b))return false;\n"
"    v=a+b;return true;\n"
"}\n"
"__device__ bool tvdb_rs_mul_ok(int a,int b,int& v) {\n"
"    if(a>2147483647/b || a<(-2147483647-1)/b)return false;\n"
"    v=a*b;return true;\n"
"}\n"
"__device__ int tvdb_rs_lookup(int x,int y,int z,const int* coords,const unsigned int* slots,const int* u) {\n"
"    unsigned int at=(((unsigned int)(x))*73856093u ^ ((unsigned int)(y))*19349663u ^ ((unsigned int)(z))*83492791u)&(((unsigned int)(u[3]))-1u);\n"
"    for(unsigned int p=0u;p<((unsigned int)(u[3]));++p){unsigned int v=slots[at];if(v==0u)return -1;\n"
"        unsigned int j=v-1u;if(coords[3u*j]==x && coords[3u*j+1u]==y && coords[3u*j+2u]==z){unsigned int first=j;for(unsigned int q=slots[((unsigned int)(u[3]))+j];q!=0u;q=slots[((unsigned int)(u[3]))+q-1u])first=min(first,q-1u);return int(first);}\n"
"        at=(at+1u)&(((unsigned int)(u[3]))-1u);}\n"
"    return -1;\n"
"}\n"
"__device__ float tvdb_rs_transpose_value(int x,int y,int z,const int* coords,const float* values,const unsigned int* slots,const int* u) {\n"
"    unsigned int at=(((unsigned int)(x))*73856093u ^ ((unsigned int)(y))*19349663u ^ ((unsigned int)(z))*83492791u)&(((unsigned int)(u[3]))-1u);\n"
"    for(unsigned int p=0u;p<((unsigned int)(u[3]));++p){unsigned int v=slots[at];if(v==0u)return 0.0;\n"
"        unsigned int j=v-1u;if(coords[3u*j]==x && coords[3u*j+1u]==y && coords[3u*j+2u]==z){\n"
"            float sum=0.0;for(unsigned int q=v;q!=0u;q=slots[((unsigned int)(u[3]))+q-1u])sum+=values[q-1u];return sum;}\n"
"        at=(at+1u)&(((unsigned int)(u[3]))-1u);}\n"
"    return 0.0;\n"
"}\n"
"__device__ bool tvdb_rs_keep(unsigned int i,int x,int y,int z,const int* coords,const unsigned int* slots,const int* u) {\n"
"    if(tvdb_rs_lookup(x,y,z,coords,slots,u)!=int(i))return false;\n"
"    if(u[12]==4)for(int k=0;k<6;++k){int a=x,b=y,c=z,t=0;\n"
"        int d=(k%2==0)?-1:1;\n"
"        if(k/2==0){if(!tvdb_rs_add_ok(a,d,t))return false;a=t;}\n"
"        if(k/2==1){if(!tvdb_rs_add_ok(b,d,t))return false;b=t;}\n"
"        if(k/2==2){if(!tvdb_rs_add_ok(c,d,t))return false;c=t;}\n"
"        if(tvdb_rs_lookup(a,b,c,coords,slots,u)<0)return false;}\n"
"    return true;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_resident_sparse(const int* coords,const float* values,const unsigned int* slots,int* oc,float* ov,const float* weights,unsigned int* flags,const int* u) {\n"
"    unsigned int i=((blockIdx.x+blockIdx.y*gridDim.x)*blockDim.x+threadIdx.x);\n"
"    if(u[0]==4){if(i<=((unsigned int)(u[2])))flags[i]=0u;return;}\n"
"    if(i>=((unsigned int)(u[2])))return;\n"
"    if(u[0]==5 || u[0]==6){\n"
"        bool selected=fabsf(values[i]-((const float*)u)[8])>((const float*)u)[9];\n"
"        if(u[0]==5){flags[i]=selected?1u:0u;return;}\n"
"        if(selected){unsigned int j=flags[i];oc[3u*j]=int(i%((unsigned int)(u[4])));oc[3u*j+1u]=int((i/((unsigned int)(u[4])))%((unsigned int)(u[5])));oc[3u*j+2u]=int(i/((unsigned int)(u[4]*u[5])));ov[j]=values[i];}return;\n"
"    }\n"
"    if(u[0]==7){int x=int(i%((unsigned int)(u[4]))),y=int((i/((unsigned int)(u[4])))%((unsigned int)(u[5]))),z=int(i/((unsigned int)(u[4]*u[5])));\n"
"        int j=tvdb_rs_lookup(x,y,z,coords,slots,u);ov[i]=j<0?((const float*)u)[8]:values[j];return;}\n"
"    if(u[0]==8){\n"
"        float x=floorf((weights[3u*i]-((const float*)u)[8])/((const float*)u)[11]),y=floorf((weights[3u*i+1u]-((const float*)u)[9])/((const float*)u)[11]),z=floorf((weights[3u*i+2u]-((const float*)u)[10])/((const float*)u)[11]);\n"
"        if(isnan(x)||isnan(y)||isnan(z)||x< -2147483648.0||x>=2147483648.0||y< -2147483648.0||y>=2147483648.0||z< -2147483648.0||z>=2147483648.0){atomicOr(&flags[((unsigned int)(u[2]))],1u);return;}\n"
"        oc[3u*i]=int(x);oc[3u*i+1u]=int(y);oc[3u*i+2u]=int(z);ov[i]=1.0;return;\n"
"    }\n"
"    int kind=u[12];\n"
"    if(u[0]==0){\n"
"        unsigned int copies=kind==2?((unsigned int)(u[4]*u[5]*u[6])):kind==3?7u:1u;\n"
"        unsigned int src=i/copies,tap=i%copies;\n"
"        int x=coords[3u*src],y=coords[3u*src+1u],z=coords[3u*src+2u];bool good=true;int t;\n"
"        if(kind==1){int s=u[7]; x=x/s-(x%s<0?1:0);y=y/s-(y%s<0?1:0);z=z/s-(z%s<0?1:0);}\n"
"        if(kind==2){int dx=int(tap%((unsigned int)(u[4])))-u[4]/2;\n"
"          int dy=int((tap/((unsigned int)(u[4])))%((unsigned int)(u[5])))-u[5]/2;\n"
"          int dz=int(tap/((unsigned int)(u[4]*u[5])))-u[6]/2;\n"
"          good=tvdb_rs_mul_ok(x,u[7],t);if(good)good=tvdb_rs_add_ok(t,dx,x);\n"
"          good=good && tvdb_rs_mul_ok(y,u[7],t);if(good)good=tvdb_rs_add_ok(t,dy,y);\n"
"          good=good && tvdb_rs_mul_ok(z,u[7],t);if(good)good=tvdb_rs_add_ok(t,dz,z);\n"
"        }\n"
"        if(kind==3 && tap>0u){int d=(tap%2u==1u)?1:-1;\n"
"          if(tap<=2u)good=tvdb_rs_add_ok(x,d,x);else if(tap<=4u)good=tvdb_rs_add_ok(y,d,y);else good=tvdb_rs_add_ok(z,d,z);}\n"
"        if(!good && kind==3){x=coords[3u*src];y=coords[3u*src+1u];z=coords[3u*src+2u];}\n"
"        else if(!good)atomicOr(&flags[((unsigned int)(u[2]))],1u);\n"
"        oc[3u*i]=x;oc[3u*i+1u]=y;oc[3u*i+2u]=z;return;\n"
"    }\n"
"    if(u[0]==1 || u[0]==2){int x=coords[3u*i],y=coords[3u*i+1u],z=coords[3u*i+2u];bool selected=tvdb_rs_keep(i,x,y,z,coords,slots,u);\n"
"        if(u[0]==1){flags[i]=selected?1u:0u;return;}\n"
"        if(selected){unsigned int j=flags[i];oc[3u*j]=x;oc[3u*j+1u]=y;oc[3u*j+2u]=z;}return;\n"
"    }\n"
"    int x=oc[3u*i],y=oc[3u*i+1u],z=oc[3u*i+2u];\n"
"    if(kind==3 || kind==4){int j=tvdb_rs_lookup(x,y,z,coords,slots,u);float v=j<0?((const float*)u)[8]:values[j];\n"
"        for(int k=0;k<6;++k){int a=x,b=y,c=z,t=0;int d=(k%2==0)?-1:1;bool good=true;\n"
"          if(k/2==0){good=tvdb_rs_add_ok(a,d,t);a=t;}if(k/2==1){good=tvdb_rs_add_ok(b,d,t);b=t;}if(k/2==2){good=tvdb_rs_add_ok(c,d,t);c=t;}\n"
"          int q=good?tvdb_rs_lookup(a,b,c,coords,slots,u):-1;if(q>=0){float f=values[q];v=kind==4?(f>v?f:v):(f<v?f:v);}}\n"
"        ov[i]=v;return;\n"
"    }\n"
"    float sum=0.0;\n"
"    for(int kz=0;kz<u[6];++kz)for(int ky=0;ky<u[5];++ky)for(int kx=0;kx<u[4];++kx){\n"
"        int a=x,b=y,c=z,t=0;bool good=true;\n"
"        int dx=kx-u[4]/2,dy=ky-u[5]/2,dz=kz-u[6]/2;\n"
"        if(kind==2){good=tvdb_rs_add_ok(x,-dx,a) && tvdb_rs_add_ok(y,-dy,b) && tvdb_rs_add_ok(z,-dz,c);\n"
"          if(!good || a%u[7]!=0 || b%u[7]!=0 || c%u[7]!=0)continue;\n"
"          a/=u[7];b/=u[7];c/=u[7];\n"
"        }else {if(kind==1){good=tvdb_rs_mul_ok(x,u[7],a)&&tvdb_rs_mul_ok(y,u[7],b)&&tvdb_rs_mul_ok(z,u[7],c);}\n"
"          good=good && tvdb_rs_add_ok(a,dx,t);a=t;good=good && tvdb_rs_add_ok(b,dy,t);b=t;good=good && tvdb_rs_add_ok(c,dz,t);c=t;}\n"
"        int j=good?tvdb_rs_lookup(a,b,c,coords,slots,u):-1;\n"
"        float v=kind==2?(good?tvdb_rs_transpose_value(a,b,c,coords,values,slots,u):0.0):(j<0?((const float*)u)[8]:values[j]);\n"
"        sum+=weights[(kz*u[5]+ky)*u[4]+kx]*v;\n"
"    }\n"
"    ov[i]=sum;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_stats_resident(const float* data,float4* partials,const unsigned int* u) {\n"
"unsigned int count=u[0],ngroups=u[1];\n"
"\n"
"  __shared__ float4 sh[256];\n"
"  unsigned int lid = threadIdx.x;\n"
"  unsigned int stride = ngroups * 256u;\n"
"  float mn = 3.402823466e+38f, mx = -3.402823466e+38f, sum = 0.0f, sumsq = 0.0f;\n"
"  for (unsigned int i = blockIdx.x * 256u + lid; i < count; i += stride) {\n"
"    float v = data[i];\n"
"    mn = fminf(mn, v); mx = fmaxf(mx, v); sum += v; sumsq += v * v;\n"
"  }\n"
"  float4 p; p.x = mn; p.y = mx; p.z = sum; p.w = sumsq; sh[lid] = p;\n"
"  __syncthreads();\n"
"  for (unsigned int t = 128u; t > 0u; t >>= 1u) {\n"
"    if (lid < t) {\n"
"      float4 a = sh[lid], b = sh[lid + t];\n"
"      sh[lid] = make_float4(fminf(a.x,b.x), fmaxf(a.y,b.y), a.z+b.z, a.w+b.w);\n"
"    }\n"
"    __syncthreads();\n"
"  }\n"
"  if (lid == 0u) partials[blockIdx.x] = sh[0];\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_checksum_resident(const unsigned int* data,unsigned int* partials,const unsigned int* u) {\n"
"unsigned int count=u[0],ngroups=u[1];\n"
"\n"
"  __shared__ unsigned int sh[256];\n"
"  unsigned int lid = threadIdx.x;\n"
"  unsigned int s = 0u;\n"
"  for (unsigned int i = blockIdx.x * 256u + lid; i < count; i += ngroups * 256u) {\n"
"    unsigned int h = data[i] ^ (i * 2654435761u); h *= 2654435761u; h ^= h >> 15; s += h;\n"
"  }\n"
"  sh[lid] = s;\n"
"  __syncthreads();\n"
"  for (unsigned int t = 128u; t > 0u; t >>= 1u) {\n"
"    if (lid < t) sh[lid] += sh[lid + t];\n"
"    __syncthreads();\n"
"  }\n"
"  if (lid == 0u) partials[blockIdx.x] = sh[0];\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_levelset_check_resident(const float* data,float4* partials,const int* u) {\n"
"int nx=u[0],ny=u[1],nz=u[2];float inv2vs=((const float*)u)[4],band_world=((const float*)u)[5],tol=((const float*)u)[6];unsigned int count=u[8],ngroups=u[9];\n"
"\n"
"  __shared__ float4 sh[256];\n"
"  unsigned int lid = threadIdx.x;\n"
"  unsigned int t = blockIdx.x * 256u + lid;\n"
"  int inx = nx - 2, iny = ny - 2; unsigned int sl = (unsigned int)(nx * ny);\n"
"  float sum_mag = 0.0f, max_err = 0.0f, bad = 0.0f, band = 0.0f;\n"
"  for (unsigned int m = t; m < count; m += ngroups * 256u) {\n"
"    int ix = (int)(m % (unsigned int)inx) + 1;\n"
"    unsigned int tmp = m / (unsigned int)inx;\n"
"    int iy = (int)(tmp % (unsigned int)iny) + 1;\n"
"    int iz = (int)(tmp / (unsigned int)iny) + 1;\n"
"    unsigned int c = (unsigned int)((iz * ny + iy) * nx + ix);\n"
"    if (band_world > 0.0f && fabsf(data[c]) > band_world) continue;\n"
"    float gx = (data[c + 1u] - data[c - 1u]) * inv2vs;\n"
"    float gy = (data[c + (unsigned int)nx] - data[c - (unsigned int)nx]) * inv2vs;\n"
"    float gz = (data[c + sl] - data[c - sl]) * inv2vs;\n"
"    float mag = sqrtf(gx*gx + gy*gy + gz*gz); float err = fabsf(mag - 1.0f);\n"
"    sum_mag += mag; if (err > max_err) max_err = err; if (err > tol) bad += 1.0f; band += 1.0f;\n"
"  }\n"
"  float4 p; p.x = sum_mag; p.y = (band > 0.0f) ? max_err : -3.402823466e+38f; p.z = bad; p.w = band;\n"
"  sh[lid] = p;\n"
"  __syncthreads();\n"
"  for (unsigned int s2 = 128u; s2 > 0u; s2 >>= 1u) {\n"
"    if (lid < s2) {\n"
"      float4 a = sh[lid], b = sh[lid + s2];\n"
"      sh[lid] = make_float4(a.x+b.x, fmaxf(a.y,b.y), a.z+b.z, a.w+b.w);\n"
"    }\n"
"    __syncthreads();\n"
"  }\n"
"  if (lid == 0u) partials[blockIdx.x] = sh[0];\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_measure_resident(const float* src,double* partials,const int* u) {\n"
"int nx=u[0],ny=u[1],nz=u[2],op=u[3];unsigned int n=u[4],ngroups=u[6];\n"
"\n"
"  __shared__ double sdata[256];\n"
"  if(u[5]){double a=0;for(unsigned int i=threadIdx.x;i<ngroups;i+=256u)a+=partials[i];sdata[threadIdx.x]=a;__syncthreads();\n"
"    for(unsigned int t=128;t;t/=2){if(threadIdx.x<t)sdata[threadIdx.x]+=sdata[threadIdx.x+t];__syncthreads();}\n"
"    if(threadIdx.x==0)partials[0]=sdata[0];return;}\n"
"\n"
"  unsigned int gid = blockIdx.x*blockDim.x+threadIdx.x;\n"
"  unsigned int lid = threadIdx.x;\n"
"  double acc = 0.0;\n"
"  unsigned int stride = ngroups*blockDim.x;\n"
"  for (unsigned int i=gid; i<n; i+=stride) acc += tvdb_measure_count(src,nx,ny,nz,i,n,op);\n"
"  sdata[lid]=acc; __syncthreads();\n"
"  for (unsigned int s=128u; s>0u; s>>=1u) { if (lid<s) sdata[lid]+=sdata[lid+s]; __syncthreads(); }\n"
"  if (lid==0u) partials[blockIdx.x]=sdata[0];\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_measure_d_resident(const double* src,double* partials,const int* u) {\n"
"int nx=u[0],ny=u[1],nz=u[2],op=u[3];unsigned int n=u[4],ngroups=u[6];\n"
"\n"
"  __shared__ double sdata[256];\n"
"  if(u[5]){double a=0;for(unsigned int i=threadIdx.x;i<ngroups;i+=256u)a+=partials[i];sdata[threadIdx.x]=a;__syncthreads();\n"
"    for(unsigned int t=128;t;t/=2){if(threadIdx.x<t)sdata[threadIdx.x]+=sdata[threadIdx.x+t];__syncthreads();}\n"
"    if(threadIdx.x==0)partials[0]=sdata[0];return;}\n"
"\n"
"  unsigned int gid = blockIdx.x*blockDim.x+threadIdx.x;\n"
"  unsigned int lid = threadIdx.x;\n"
"  double acc = 0.0;\n"
"  unsigned int stride = ngroups*blockDim.x;\n"
"  for (unsigned int i=gid; i<n; i+=stride) acc += tvdb_measure_count_d(src,nx,ny,nz,i,n,op);\n"
"  sdata[lid]=acc; __syncthreads();\n"
"  for (unsigned int s=128u; s>0u; s>>=1u) { if (lid<s) sdata[lid]+=sdata[lid+s]; __syncthreads(); }\n"
"  if (lid==0u) partials[blockIdx.x]=sdata[0];\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_resident_reduce(const unsigned int* input_data,unsigned int* result,const unsigned int* u){\n"
" __shared__ float a[256],b[256],c[256],d[256];__shared__ unsigned int sums[256];\n"
"    uint lane=threadIdx.x;\n"
"    if(u[1]==2u){uint s=0u;for(uint i=lane;i<u[0];i+=256u)s+=input_data[i];sums[lane]=s;__syncthreads();\n"
"      for(uint k=128u;k>0u;k/=2u){if(lane<k)sums[lane]+=sums[lane+k];__syncthreads();}if(lane==0u)result[0]=sums[0];return;}\n"
"    float x=u[1]==0u?3.402823466e+38:0.0,y=-3.402823466e+38,z=0.0,w=0.0;\n"
"    for(uint i=lane;i<u[0];i+=256u){float v=__uint_as_float(input_data[4u*i]);\n"
"      x=u[1]==0u?fminf(x,v):x+v;y=fmaxf(y,__uint_as_float(input_data[4u*i+1u]));\n"
"      z+=__uint_as_float(input_data[4u*i+2u]);w+=__uint_as_float(input_data[4u*i+3u]);}\n"
"    a[lane]=x;b[lane]=y;c[lane]=z;d[lane]=w;__syncthreads();\n"
"    for(uint k=128u;k>0u;k/=2u){if(lane<k){a[lane]=u[1]==0u?fminf(a[lane],a[lane+k]):a[lane]+a[lane+k];b[lane]=fmaxf(b[lane],b[lane+k]);c[lane]+=c[lane+k];d[lane]+=d[lane+k];}__syncthreads();}\n"
"    if(lane==0u){result[0]=__float_as_uint(a[0]);result[1]=__float_as_uint(b[0]);result[2]=__float_as_uint(c[0]);result[3]=__float_as_uint(d[0]);}\n"
"}\n"

;

static void tvdb_cuda_set_error(tvdb_gpu_context_t* ctx, tvdb_error_t* err,
                                tvdb_status_t st, const char* label, CUresult r) {
  char msg[512];
  const char* cuda_msg = NULL;
  if (ctx && ctx->cuda.cuGetErrorString) ctx->cuda.cuGetErrorString(r, &cuda_msg);
  if (cuda_msg) snprintf(msg, sizeof(msg), "%s failed: %s (%d)", label, cuda_msg, r);
  else snprintf(msg, sizeof(msg), "%s failed: %d", label, r);
  tvdb_gpu_set_error(err, st, msg);
}

static int tvdb_cuda_ok(tvdb_gpu_context_t* ctx, tvdb_error_t* err, const char* label, CUresult r) {
  if (r == CUDA_SUCCESS) return 1;
  tvdb_cuda_set_error(ctx, err, TVDB_ERROR_IO, label, r);
  return 0;
}

static tvdb_status_t tvdb_cuda_get_module(tvdb_gpu_context_t* ctx, CUmodule* module, tvdb_error_t* err) {
  if (ctx->cu_module) {
    *module = ctx->cu_module;
    return TVDB_OK;
  }
  nvrtcProgram prog = NULL;
  nvrtcResult nr = ctx->cuda.nvrtcCreateProgram(&prog, kTvdbCudaSource, "tinyvdb_gpu.cu", 0, NULL, NULL);
  if (nr != NVRTC_SUCCESS) {
    tvdb_gpu_set_error(err, TVDB_ERROR_IO, "nvrtcCreateProgram failed");
    return TVDB_ERROR_IO;
  }
  const char* opts[] = {"--std=c++11"};
  nr = ctx->cuda.nvrtcCompileProgram(prog, 1, opts);
  if (nr != NVRTC_SUCCESS) {
    size_t log_size = 0;
    ctx->cuda.nvrtcGetProgramLogSize(prog, &log_size);
    char* log = (char*)calloc(log_size ? log_size : 1, 1);
    if (log) ctx->cuda.nvrtcGetProgramLog(prog, log);
    tvdb_gpu_set_error(err, TVDB_ERROR_IO, log ? log : "nvrtcCompileProgram failed");
    free(log);
    ctx->cuda.nvrtcDestroyProgram(&prog);
    return TVDB_ERROR_IO;
  }
  size_t ptx_size = 0;
  nr = ctx->cuda.nvrtcGetPTXSize(prog, &ptx_size);
  if (nr != NVRTC_SUCCESS || ptx_size == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_IO, "nvrtcGetPTXSize failed");
    ctx->cuda.nvrtcDestroyProgram(&prog);
    return TVDB_ERROR_IO;
  }
  char* ptx = (char*)malloc(ptx_size);
  if (!ptx) {
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
    ctx->cuda.nvrtcDestroyProgram(&prog);
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  nr = ctx->cuda.nvrtcGetPTX(prog, ptx);
  ctx->cuda.nvrtcDestroyProgram(&prog);
  if (nr != NVRTC_SUCCESS) {
    free(ptx);
    tvdb_gpu_set_error(err, TVDB_ERROR_IO, "nvrtcGetPTX failed");
    return TVDB_ERROR_IO;
  }
  CUresult cr = ctx->cuda.cuModuleLoadData(&ctx->cu_module, ptx);
  free(ptx);
  if (!tvdb_cuda_ok(ctx, err, "cuModuleLoadData", cr)) return err ? err->status : TVDB_ERROR_IO;
  *module = ctx->cu_module;
  return TVDB_OK;
}

static tvdb_status_t tvdb_cuda_alloc_copy_in(tvdb_gpu_context_t* ctx, CUdeviceptr* dst,
                                             const void* src, size_t size, tvdb_error_t* err) {
  if (!tvdb_cuda_ok(ctx, err, "cuMemAlloc", ctx->cuda.cuMemAlloc(dst, size ? size : 4))) return err ? err->status : TVDB_ERROR_IO;
  if (src && size) {
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyHtoD", ctx->cuda.cuMemcpyHtoD(*dst, src, size))) {
      ctx->cuda.cuMemFree(*dst);
      *dst = 0;
      return err ? err->status : TVDB_ERROR_IO;
    }
  }
  return TVDB_OK;
}

size_t tvdb_gpu_enumerate_devices(tvdb_gpu_backend_t backend, tvdb_gpu_device_info_t* devices, size_t capacity) {
  size_t n = 0;
  if (backend == TVDB_GPU_BACKEND_AUTO || backend == TVDB_GPU_BACKEND_VULKAN) {
    tvdb_vk_table vk;
    memset(&vk, 0, sizeof(vk));
    if (tvdb_load_vulkan_library(&vk)) {
      if (devices && n < capacity) {
        memset(&devices[n], 0, sizeof(devices[n]));
        devices[n].backend = TVDB_GPU_BACKEND_VULKAN;
        devices[n].available = 1;
        devices[n].supports_sparse_3d_images = 0;
        snprintf(devices[n].name, sizeof(devices[n].name), "Vulkan runtime");
      }
      ++n;
      tvdb_dyn_close(vk.lib);
    }
  }
  if (backend == TVDB_GPU_BACKEND_AUTO || backend == TVDB_GPU_BACKEND_CUDA) {
    tvdb_cuda_table cu;
    memset(&cu, 0, sizeof(cu));
    if (tvdb_load_cuda_library(&cu)) {
      if (devices && n < capacity) {
        memset(&devices[n], 0, sizeof(devices[n]));
        devices[n].backend = TVDB_GPU_BACKEND_CUDA;
        devices[n].available = 1;
        snprintf(devices[n].name, sizeof(devices[n].name), "CUDA driver + NVRTC runtime");
      }
      ++n;
      tvdb_dyn_close(cu.libnvrtc);
      tvdb_dyn_close(cu.libcuda);
    }
  }
  return n;
}

static tvdb_status_t tvdb_cuda_context_create(uint32_t device_index,
                                              tvdb_gpu_context_t** out,
                                              tvdb_error_t* err) {
  tvdb_gpu_context_t* ctx = (tvdb_gpu_context_t*)calloc(1, sizeof(*ctx));
  if (!ctx) {
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  ctx->backend = TVDB_GPU_BACKEND_CUDA;
  if (!tvdb_load_cuda_library(&ctx->cuda)) {
    free(ctx);
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "CUDA driver and NVRTC runtime libraries not found");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  if (!tvdb_cuda_ok(ctx, err, "cuInit", ctx->cuda.cuInit(0))) goto fail;
  int count = 0;
  if (!tvdb_cuda_ok(ctx, err, "cuDeviceGetCount", ctx->cuda.cuDeviceGetCount(&count))) goto fail;
  if (count <= 0 || device_index >= (uint32_t)count) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "requested CUDA device not found");
    goto fail;
  }
  if (!tvdb_cuda_ok(ctx, err, "cuDeviceGet", ctx->cuda.cuDeviceGet(&ctx->cu_device, (int)device_index))) goto fail;
  ctx->cuda.cuDeviceGetName(ctx->device_name, (int)sizeof(ctx->device_name), ctx->cu_device);
  if (ctx->device_name[0] == '\0') {
    snprintf(ctx->device_name, sizeof(ctx->device_name), "CUDA device %u", device_index);
  }
  if (ctx->cuda.cuDeviceGetUuid && ctx->cuda.cuDeviceGetUuid(ctx->device_uuid, ctx->cu_device) == CUDA_SUCCESS)
    ctx->has_device_uuid = 1;
  if (!tvdb_cuda_ok(ctx, err, "cuCtxCreate", ctx->cuda.cuCtxCreate(&ctx->cu_ctx, 0, ctx->cu_device))) goto fail;
  *out = ctx;
  return TVDB_OK;
fail:
  tvdb_gpu_context_destroy(ctx);
  return err ? err->status : TVDB_ERROR_IO;
}

static tvdb_status_t tvdb_vulkan_context_create(uint32_t device_index,
                                                tvdb_gpu_context_t** out,
                                                tvdb_error_t* err) {
  tvdb_gpu_context_t* ctx = (tvdb_gpu_context_t*)calloc(1, sizeof(*ctx));
  if (!ctx) {
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  ctx->backend = TVDB_GPU_BACKEND_VULKAN;
  if (!tvdb_load_vulkan_library(&ctx->vk)) {
    free(ctx);
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "Vulkan loader not found");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  VkApplicationInfo ai;
  memset(&ai, 0, sizeof(ai));
  ai.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
  ai.pApplicationName = "tinyvdb_gpu";
  // Request Vulkan 1.1 when the loader supports it: external-memory interop
  // (VK_KHR_external_memory and its capabilities instance extension) is core in
  // 1.1, which the opaque-fd export path below relies on. Fall back to 1.0 on
  // older loaders so context creation still succeeds.
  ai.apiVersion = VK_API_VERSION_1_0;
  {
    VkResult (*enum_ver)(uint32_t*) = (VkResult(*)(uint32_t*))ctx->vk.GetInstanceProcAddr(NULL, "vkEnumerateInstanceVersion");
    uint32_t loader_ver = 0;
    if (enum_ver && enum_ver(&loader_ver) == VK_SUCCESS && loader_ver >= VK_API_VERSION_1_1)
      ai.apiVersion = VK_API_VERSION_1_1;
  }
  VkInstanceCreateInfo ici;
  memset(&ici, 0, sizeof(ici));
  ici.sType = VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO;
  ici.pApplicationInfo = &ai;
  if (!tvdb_vk_ok(ctx->vk.CreateInstance(&ici, NULL, &ctx->instance), err, "vkCreateInstance")) goto fail;
  if (tvdb_vk_load_instance_functions(ctx, err) != TVDB_OK) goto fail;
  uint32_t count = 0;
  if (!tvdb_vk_ok(ctx->vk.EnumeratePhysicalDevices(ctx->instance, &count, NULL), err, "vkEnumeratePhysicalDevices")) goto fail;
  if (count == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "no Vulkan physical devices");
    goto fail;
  }
  VkPhysicalDevice* pds = (VkPhysicalDevice*)calloc(count, sizeof(VkPhysicalDevice));
  if (!pds) {
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
    goto fail;
  }
  ctx->vk.EnumeratePhysicalDevices(ctx->instance, &count, pds);
  uint32_t seen_compute = 0;
  uint32_t selected_queue_flags = 0;
  for (uint32_t p = 0; p < count && !ctx->physical_device; ++p) {
    uint32_t qcount = 0;
    ctx->vk.GetPhysicalDeviceQueueFamilyProperties(pds[p], &qcount, NULL);
    VkQueueFamilyProperties* qprops = (VkQueueFamilyProperties*)calloc(qcount ? qcount : 1, sizeof(*qprops));
    if (!qprops) continue;
    ctx->vk.GetPhysicalDeviceQueueFamilyProperties(pds[p], &qcount, qprops);
    for (uint32_t q = 0; q < qcount; ++q) {
      if (qprops[q].queueFlags & VK_QUEUE_COMPUTE_BIT) {
        if (seen_compute == device_index) {
          ctx->physical_device = pds[p];
          ctx->queue_family = q;
          selected_queue_flags = qprops[q].queueFlags;
          break;
        }
        ++seen_compute;
      }
    }
    free(qprops);
  }
  free(pds);
  if (!ctx->physical_device) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "requested Vulkan compute device not found");
    goto fail;
  }
  VkPhysicalDeviceFeatures features;
  memset(&features, 0, sizeof(features));
  ctx->vk.GetPhysicalDeviceFeatures(ctx->physical_device, &features);
  ctx->supports_sparse_3d_images =
      (features.sparseBinding && features.sparseResidencyImage3D &&
       (selected_queue_flags & VK_QUEUE_SPARSE_BINDING_BIT)) ? 1 : 0;
  /* Optional in core Vulkan. When it is absent an fp64 shader will not load, so
   * the fp64 ops must report UNIMPLEMENTED rather than silently running in fp32:
   * a caller who asked for double precision would get different answers with no
   * indication. */
  ctx->supports_shader_float64 = features.shaderFloat64 ? 1 : 0;
  ctx->supports_sparse_aliased =
      (ctx->supports_sparse_3d_images && features.sparseResidencyAliased) ? 1 : 0;
  ctx->vk.GetPhysicalDeviceMemoryProperties(ctx->physical_device, &ctx->memory_props);
  {
    /* Core in Vulkan 1.1; the KHR alias covers 1.0 instances exposing it. */
    PFN_vkGetPhysicalDeviceProperties2 get_props2 = (PFN_vkGetPhysicalDeviceProperties2)
        ctx->vk.GetInstanceProcAddr(ctx->instance, "vkGetPhysicalDeviceProperties2");
    if (!get_props2)
      get_props2 = (PFN_vkGetPhysicalDeviceProperties2)
          ctx->vk.GetInstanceProcAddr(ctx->instance, "vkGetPhysicalDeviceProperties2KHR");
    if (get_props2) {
      VkPhysicalDeviceIDProperties idp;
      VkPhysicalDeviceProperties2 p2;
      memset(&idp, 0, sizeof(idp));
      memset(&p2, 0, sizeof(p2));
      idp.sType = VK_STRUCTURE_TYPE_PHYSICAL_DEVICE_ID_PROPERTIES;
      p2.sType = VK_STRUCTURE_TYPE_PHYSICAL_DEVICE_PROPERTIES_2;
      p2.pNext = &idp;
      get_props2(ctx->physical_device, &p2);
      memcpy(ctx->device_uuid, idp.deviceUUID, sizeof(ctx->device_uuid));
      ctx->has_device_uuid = 1;
    }
  }
  float prio = 1.0f;
  VkDeviceQueueCreateInfo qci;
  memset(&qci, 0, sizeof(qci));
  qci.sType = VK_STRUCTURE_TYPE_DEVICE_QUEUE_CREATE_INFO;
  qci.queueFamilyIndex = ctx->queue_family;
  qci.queueCount = 1;
  qci.pQueuePriorities = &prio;
  VkDeviceCreateInfo dci;
  VkPhysicalDeviceFeatures enabled_features;
  memset(&enabled_features, 0, sizeof(enabled_features));
  if (ctx->supports_sparse_3d_images) {
    enabled_features.sparseBinding = VK_TRUE;
    enabled_features.sparseResidencyImage3D = VK_TRUE;
    if (ctx->supports_sparse_aliased) enabled_features.sparseResidencyAliased = VK_TRUE;
  }
  memset(&dci, 0, sizeof(dci));
  dci.sType = VK_STRUCTURE_TYPE_DEVICE_CREATE_INFO;
  dci.queueCreateInfoCount = 1;
  dci.pQueueCreateInfos = &qci;
  dci.pEnabledFeatures = &enabled_features;
  // Enable external-memory extensions for cross-API (Vulkan<->CUDA) interop when
  // the device advertises them; harmless to skip if unsupported.
  const char* all_ext[2] = { "VK_KHR_external_memory", "VK_KHR_external_memory_fd" };
  const char* enabled_ext[2];
  uint32_t enabled_ext_count = 0;
  int have_ext_fd = 0;
  {
    uint32_t ext_count = 0;
    ctx->vk.EnumerateDeviceExtensionProperties(ctx->physical_device, NULL, &ext_count, NULL);
    if (ext_count > 0 && ext_count < 4096) {
      VkExtensionProperties* props = (VkExtensionProperties*)calloc(ext_count, sizeof(VkExtensionProperties));
      if (props) {
        ctx->vk.EnumerateDeviceExtensionProperties(ctx->physical_device, NULL, &ext_count, props);
        for (uint32_t e = 0; e < 2; ++e) {
          for (uint32_t i = 0; i < ext_count; ++i) {
            if (strcmp(props[i].extensionName, all_ext[e]) == 0) {
              enabled_ext[enabled_ext_count++] = all_ext[e];
              if (e == 1) have_ext_fd = 1;
              break;
            }
          }
        }
        free(props);
      }
    }
  }
  // VK_KHR_external_memory_fd (which provides vkGetMemoryFdKHR) is the essential
  // one; its base VK_KHR_external_memory is core under Vulkan 1.1 and may not be
  // separately advertised, so enable whichever are present.
  if (have_ext_fd) {
    dci.enabledExtensionCount = enabled_ext_count;
    dci.ppEnabledExtensionNames = enabled_ext;
    ctx->supports_external_memory = 1;
  }
  if (!tvdb_vk_ok(ctx->vk.CreateDevice(ctx->physical_device, &dci, NULL, &ctx->device), err, "vkCreateDevice")) goto fail;
  if (tvdb_vk_load_device_functions(ctx, err) != TVDB_OK) goto fail;
  ctx->vk.GetDeviceQueue(ctx->device, ctx->queue_family, 0, &ctx->queue);
  snprintf(ctx->device_name, sizeof(ctx->device_name), "Vulkan compute device %u", device_index);
  *out = ctx;
  return TVDB_OK;
fail:
  tvdb_gpu_context_destroy(ctx);
  return err ? err->status : TVDB_ERROR_IO;
}

tvdb_status_t tvdb_gpu_context_create(tvdb_gpu_backend_t backend, uint32_t device_index,
                                      tvdb_gpu_context_t** out, tvdb_error_t* err) {
  if (!out) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "NULL output context");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  *out = NULL;
  if (backend == TVDB_GPU_BACKEND_VULKAN) {
    return tvdb_vulkan_context_create(device_index, out, err);
  }
  if (backend == TVDB_GPU_BACKEND_CUDA) {
    return tvdb_cuda_context_create(device_index, out, err);
  }
  if (backend != TVDB_GPU_BACKEND_AUTO) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "unknown GPU backend");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }

  tvdb_error_t first_err;
  memset(&first_err, 0, sizeof(first_err));
  tvdb_status_t st = tvdb_vulkan_context_create(device_index, out, &first_err);
  if (st == TVDB_OK) return TVDB_OK;
  st = tvdb_cuda_context_create(device_index, out, err);
  if (st == TVDB_OK) return TVDB_OK;
  if (err && err->message[0] == '\0') *err = first_err;
  return err ? err->status : st;
}

void tvdb_gpu_context_destroy(tvdb_gpu_context_t* ctx) {
  if (!ctx) return;
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    if (ctx->cu_module && ctx->cuda.cuModuleUnload) ctx->cuda.cuModuleUnload(ctx->cu_module);
    if (ctx->cu_ctx && ctx->cuda.cuCtxDestroy) ctx->cuda.cuCtxDestroy(ctx->cu_ctx);
    tvdb_dyn_close(ctx->cuda.libnvrtc);
    tvdb_dyn_close(ctx->cuda.libcuda);
  } else {
    if (ctx->device && ctx->vk.DeviceWaitIdle) ctx->vk.DeviceWaitIdle(ctx->device);
    if (ctx->device) tvdb_gpu_dispatch_flush(ctx, NULL);
    /* Release the cached pipelines before the device goes away. */
    for (uint32_t i = 0; i < ctx->pipeline_cache_count; ++i) {
      tvdb_vk_pipeline_entry *e = &ctx->pipeline_cache[i];
      if (ctx->device) {
        if (e->pipeline && ctx->vk.DestroyPipeline) ctx->vk.DestroyPipeline(ctx->device, e->pipeline, NULL);
        if (e->pipeline_layout && ctx->vk.DestroyPipelineLayout) ctx->vk.DestroyPipelineLayout(ctx->device, e->pipeline_layout, NULL);
        if (e->shader && ctx->vk.DestroyShaderModule) ctx->vk.DestroyShaderModule(ctx->device, e->shader, NULL);
        if (e->set_layout && ctx->vk.DestroyDescriptorSetLayout) ctx->vk.DestroyDescriptorSetLayout(ctx->device, e->set_layout, NULL);
      }
    }
    ctx->pipeline_cache_count = 0;
    if (ctx->device) {
      /* Best effort: the device is going away, so a failed wait must not abort
       * teardown, but the objects still need releasing. */
      while (ctx->pending_count) {
        uint32_t i = ctx->pending_count - 1;
        VkFence f = ctx->pending_fence[i];
        VkCommandBuffer c = ctx->pending_cmd[i];
        ctx->pending_count--;
        if (f) {
          tvdb_vk_ok(ctx->vk.WaitForFences(ctx->device, 1, &f, VK_TRUE, UINT64_MAX), NULL, "vkWaitForFences");
          ctx->vk.DestroyFence(ctx->device, f, NULL);
        }
        if (c && ctx->vk.FreeCommandBuffers)
          ctx->vk.FreeCommandBuffers(ctx->device, ctx->cmd_pool, 1, &c);
      }
    }
    if (ctx->device && ctx->cmd_pool && ctx->vk.DestroyCommandPool) ctx->vk.DestroyCommandPool(ctx->device, ctx->cmd_pool, NULL);
    if (ctx->device && ctx->desc_pool && ctx->vk.DestroyDescriptorPool) ctx->vk.DestroyDescriptorPool(ctx->device, ctx->desc_pool, NULL);
    ctx->cmd_pool = VK_NULL_HANDLE;
    ctx->desc_pool = VK_NULL_HANDLE;
    if (ctx->device && ctx->vk.DestroyDevice) ctx->vk.DestroyDevice(ctx->device, NULL);
    if (ctx->instance && ctx->vk.DestroyInstance) ctx->vk.DestroyInstance(ctx->instance, NULL);
    tvdb_dyn_close(ctx->vk.lib);
  }
  free(ctx);
}

/* Whether this build has GPU SPIR-V at all.
 *
 * The shaders are either compiled by glslangValidator at build time, or supplied
 * as the pre-generated fallback include whose arrays are all zero-length. A
 * context still creates fine in the second case and every op then returns
 * UNIMPLEMENTED, which is a legitimate outcome but not a test failure -- so
 * callers that want to skip rather than fail need to be able to tell the two
 * apart. Checking one blob would be enough in practice since the fallback is all
 * or nothing, but a spread of representatives is used so a partially populated
 * build reports the truth instead of claiming to be fine. */
int tvdb_gpu_spirv_available(void) {
  static const uint32_t* probe[] = {
    &kTvdbGpuStencilScalarScalarSpv_len, &kTvdbGpuSdfSphereSpv_len,
    &kTvdbGpuSampleSpv_len,              &kTvdbGpuMorphSpv_len,
    &kTvdbGpuMarchingCubesSpv_len,        &kTvdbGpuMeshToSdfSpv_len,
    &kTvdbGpuCsgSpv_len,                  &kTvdbGpuIjkToIndexSpv_len,
  };
  for (size_t i = 0; i < sizeof(probe) / sizeof(probe[0]); ++i)
    if (*probe[i] == 0u) return 0;
  return 1;
}

tvdb_status_t tvdb_gpu_context_info(const tvdb_gpu_context_t* ctx, tvdb_gpu_context_info_t* out, tvdb_error_t* err) {
  if (!ctx || !out) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "NULL argument");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  memset(out, 0, sizeof(*out));
  out->backend = ctx->backend;
  out->supports_sparse_3d_images = ctx->supports_sparse_3d_images;
  snprintf(out->device_name, sizeof(out->device_name), "%s", ctx->device_name);
  return TVDB_OK;
}

static int tvdb_dense_same_shape(const tvdb_dense_grid* a, const tvdb_dense_grid* b, const tvdb_dense_grid* c) {
  return a && b && c && a->data && b->data && c->data &&
         a->nx == b->nx && a->ny == b->ny && a->nz == b->nz &&
         a->nx == c->nx && a->ny == c->ny && a->nz == c->nz;
}

static int tvdb_gpu_make_sphere_grid(float radius, const float center[3],
                                     float voxel_size, float half_width,
                                     tvdb_dense_grid* out, float* bg_out) {
  if (!center || !out || radius <= 0.0f || voxel_size <= 0.0f) return 0;
  float hw = half_width > 0.0f ? half_width : 3.0f;
  float bg = hw * voxel_size;
  float ext = radius + bg;
  int n[3];
  float lo[3];
  for (int a = 0; a < 3; ++a) {
    lo[a] = center[a] - ext;
    float hi = center[a] + ext;
    float span = hi - lo[a];
    n[a] = (int)ceilf(span / voxel_size) + 1;
    if (n[a] < 1) n[a] = 1;
  }
  tvdb_dense_grid_init(out, n[0], n[1], n[2]);
  if (!out->data) return 0;
  out->voxel_size = voxel_size;
  out->ox = lo[0] - 0.5f * voxel_size;
  out->oy = lo[1] - 0.5f * voxel_size;
  out->oz = lo[2] - 0.5f * voxel_size;
  if (bg_out) *bg_out = bg;
  return 1;
}

static int tvdb_gpu_make_box_grid(const float half_extents[3], const float center[3],
                                  float voxel_size, float half_width,
                                  tvdb_dense_grid* out, float* bg_out) {
  if (!half_extents || !center || !out || voxel_size <= 0.0f) return 0;
  if (half_extents[0] <= 0.0f || half_extents[1] <= 0.0f || half_extents[2] <= 0.0f) return 0;
  float hw = half_width > 0.0f ? half_width : 3.0f;
  float bg = hw * voxel_size;
  int n[3];
  float lo[3];
  for (int a = 0; a < 3; ++a) {
    lo[a] = center[a] - half_extents[a] - bg;
    float hi = center[a] + half_extents[a] + bg;
    float span = hi - lo[a];
    n[a] = (int)ceilf(span / voxel_size) + 1;
    if (n[a] < 1) n[a] = 1;
  }
  tvdb_dense_grid_init(out, n[0], n[1], n[2]);
  if (!out->data) return 0;
  out->voxel_size = voxel_size;
  out->ox = lo[0] - 0.5f * voxel_size;
  out->oy = lo[1] - 0.5f * voxel_size;
  out->oz = lo[2] - 0.5f * voxel_size;
  if (bg_out) *bg_out = bg;
  return 1;
}

static int tvdb_gpu_make_torus_grid(float major_radius, float minor_radius,
                                    const float center[3], float voxel_size,
                                    float half_width, tvdb_dense_grid* out,
                                    float* bg_out) {
  if (!center || !out || major_radius <= 0.0f || minor_radius <= 0.0f || voxel_size <= 0.0f) return 0;
  float hw = half_width > 0.0f ? half_width : 3.0f;
  float bg = hw * voxel_size;
  float ext_xz = major_radius + minor_radius + bg;
  float ext_y = minor_radius + bg;
  float lo[3] = {center[0] - ext_xz, center[1] - ext_y, center[2] - ext_xz};
  float hi[3] = {center[0] + ext_xz, center[1] + ext_y, center[2] + ext_xz};
  int n[3];
  for (int a = 0; a < 3; ++a) {
    float span = hi[a] - lo[a];
    n[a] = (int)ceilf(span / voxel_size) + 1;
    if (n[a] < 1) n[a] = 1;
  }
  tvdb_dense_grid_init(out, n[0], n[1], n[2]);
  if (!out->data) return 0;
  out->voxel_size = voxel_size;
  out->ox = lo[0] - 0.5f * voxel_size;
  out->oy = lo[1] - 0.5f * voxel_size;
  out->oz = lo[2] - 0.5f * voxel_size;
  if (bg_out) *bg_out = bg;
  return 1;
}

static tvdb_status_t tvdb_cuda_csg_dense(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* a,
                                         const tvdb_dense_grid* b, int op,
                                         tvdb_dense_grid* out, tvdb_error_t* err) {
  size_t n = (size_t)a->nx * (size_t)a->ny * (size_t)a->nz;
  CUmodule module = NULL;
  CUfunction fn = NULL;
  CUdeviceptr da = 0, db = 0, dout = 0;
  tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
  if (st != TVDB_OK) return st;
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_csg"))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &da, a->data, n * sizeof(float), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &db, b->data, n * sizeof(float), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, n * sizeof(float), err)) != TVDB_OK) goto done;
  unsigned int count = (unsigned int)n;
  void* args[] = {&da, &db, &dout, &count, &op};
  unsigned int block = 256;
  unsigned int grid = (count + block - 1u) / block;
  if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out->data, dout, n * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  st = TVDB_OK;
done:
  if (dout) ctx->cuda.cuMemFree(dout);
  if (db) ctx->cuda.cuMemFree(db);
  if (da) ctx->cuda.cuMemFree(da);
  return st;
}

static tvdb_status_t tvdb_cuda_sdf_sphere_dense(tvdb_gpu_context_t* ctx,
                                                float radius,
                                                const float center[3],
                                                float background,
                                                tvdb_dense_grid* out,
                                                tvdb_error_t* err) {
  size_t n = (size_t)out->nx * (size_t)out->ny * (size_t)out->nz;
  CUmodule module = NULL;
  CUfunction fn = NULL;
  CUdeviceptr dout = 0;
  tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
  if (st != TVDB_OK) return st;
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_sdf_sphere"))) {
    st = err ? err->status : TVDB_ERROR_IO;
    goto done;
  }
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, n * sizeof(float), err)) != TVDB_OK) goto done;
  int nx = out->nx, ny = out->ny, nz = out->nz;
  float ox = out->ox, oy = out->oy, oz = out->oz, vs = out->voxel_size;
  float cx = center[0], cy = center[1], cz = center[2];
  unsigned int count = (unsigned int)n;
  void* args[] = {&dout, &nx, &ny, &nz, &ox, &oy, &oz, &vs,
                  &cx, &cy, &cz, &radius, &background, &count};
  unsigned int block = 256;
  unsigned int grid = (count + block - 1u) / block;
  if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) {
    st = err ? err->status : TVDB_ERROR_IO;
    goto done;
  }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) {
    st = err ? err->status : TVDB_ERROR_IO;
    goto done;
  }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out->data, dout, n * sizeof(float)))) {
    st = err ? err->status : TVDB_ERROR_IO;
    goto done;
  }
  st = TVDB_OK;
done:
  if (dout) ctx->cuda.cuMemFree(dout);
  return st;
}

static tvdb_status_t tvdb_cuda_sdf_box_dense(tvdb_gpu_context_t* ctx,
                                             const float half_extents[3],
                                             const float center[3],
                                             float background,
                                             tvdb_dense_grid* out,
                                             tvdb_error_t* err) {
  size_t n = (size_t)out->nx * (size_t)out->ny * (size_t)out->nz;
  CUmodule module = NULL;
  CUfunction fn = NULL;
  CUdeviceptr dout = 0;
  tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
  if (st != TVDB_OK) return st;
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_sdf_box"))) {
    st = err ? err->status : TVDB_ERROR_IO;
    goto done;
  }
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, n * sizeof(float), err)) != TVDB_OK) goto done;
  int nx = out->nx, ny = out->ny, nz = out->nz;
  float ox = out->ox, oy = out->oy, oz = out->oz, vs = out->voxel_size;
  float cx = center[0], cy = center[1], cz = center[2];
  float hx = half_extents[0], hy = half_extents[1], hz = half_extents[2];
  unsigned int count = (unsigned int)n;
  void* args[] = {&dout, &nx, &ny, &nz, &ox, &oy, &oz, &vs,
                  &cx, &cy, &cz, &hx, &hy, &hz, &background, &count};
  unsigned int block = 256;
  unsigned int grid = (count + block - 1u) / block;
  if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) {
    st = err ? err->status : TVDB_ERROR_IO;
    goto done;
  }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) {
    st = err ? err->status : TVDB_ERROR_IO;
    goto done;
  }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out->data, dout, n * sizeof(float)))) {
    st = err ? err->status : TVDB_ERROR_IO;
    goto done;
  }
  st = TVDB_OK;
done:
  if (dout) ctx->cuda.cuMemFree(dout);
  return st;
}

static tvdb_status_t tvdb_cuda_sdf_torus_dense(tvdb_gpu_context_t* ctx,
                                               float major_radius,
                                               float minor_radius,
                                               const float center[3],
                                               float background,
                                               tvdb_dense_grid* out,
                                               tvdb_error_t* err) {
  size_t n = (size_t)out->nx * (size_t)out->ny * (size_t)out->nz;
  CUmodule module = NULL;
  CUfunction fn = NULL;
  CUdeviceptr dout = 0;
  tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
  if (st != TVDB_OK) return st;
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_sdf_torus"))) {
    st = err ? err->status : TVDB_ERROR_IO;
    goto done;
  }
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, n * sizeof(float), err)) != TVDB_OK) goto done;
  int nx = out->nx, ny = out->ny, nz = out->nz;
  float ox = out->ox, oy = out->oy, oz = out->oz, vs = out->voxel_size;
  float cx = center[0], cy = center[1], cz = center[2];
  unsigned int count = (unsigned int)n;
  void* args[] = {&dout, &nx, &ny, &nz, &ox, &oy, &oz, &vs,
                  &cx, &cy, &cz, &major_radius, &minor_radius, &background, &count};
  unsigned int block = 256;
  unsigned int grid = (count + block - 1u) / block;
  if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) {
    st = err ? err->status : TVDB_ERROR_IO;
    goto done;
  }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) {
    st = err ? err->status : TVDB_ERROR_IO;
    goto done;
  }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out->data, dout, n * sizeof(float)))) {
    st = err ? err->status : TVDB_ERROR_IO;
    goto done;
  }
  st = TVDB_OK;
done:
  if (dout) ctx->cuda.cuMemFree(dout);
  return st;
}

static tvdb_status_t tvdb_cuda_sample_dense_kernel(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid_in,
                                            const tvdb_vec3f* pts, size_t n,
                                            float* out_values, const char* kernel_name, tvdb_error_t* err) {
  size_t voxels = (size_t)grid_in->nx * (size_t)grid_in->ny * (size_t)grid_in->nz;
  CUmodule module = NULL;
  CUfunction fn = NULL;
  CUdeviceptr dg = 0, dp = 0, dout = 0;
  float* p4 = NULL;
  tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
  if (st != TVDB_OK) return st;
  p4 = (float*)calloc(n ? n : 1, 4u * sizeof(float));
  if (!p4) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); st = TVDB_ERROR_OUT_OF_MEMORY; goto done; }
  for (size_t i = 0; i < n; ++i) {
    p4[4*i+0] = pts[i].x; p4[4*i+1] = pts[i].y; p4[4*i+2] = pts[i].z; p4[4*i+3] = 0.0f;
  }
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, kernel_name))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dg, grid_in->data, voxels * sizeof(float), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dp, p4, n * 4u * sizeof(float), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, n * sizeof(float), err)) != TVDB_OK) goto done;
  int nx = grid_in->nx, ny = grid_in->ny, nz = grid_in->nz;
  float ox = grid_in->ox, oy = grid_in->oy, oz = grid_in->oz, vs = grid_in->voxel_size;
  unsigned int count = (unsigned int)n;
  void* args[] = {&dg, &dp, &dout, &nx, &ny, &nz, &ox, &oy, &oz, &vs, &count};
  unsigned int block = 128;
  unsigned int grid_blocks = (count + block - 1u) / block;
  if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid_blocks, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out_values, dout, n * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  st = TVDB_OK;
done:
  free(p4);
  if (dout) ctx->cuda.cuMemFree(dout);
  if (dp) ctx->cuda.cuMemFree(dp);
  if (dg) ctx->cuda.cuMemFree(dg);
  return st;
}

static tvdb_status_t tvdb_cuda_sample_dense(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid_in,
                                            const tvdb_vec3f* pts, size_t n,
                                            float* out_values, tvdb_error_t* err) {
  return tvdb_cuda_sample_dense_kernel(ctx, grid_in, pts, n, out_values, "tvdb_cuda_sample", err);
}

static tvdb_status_t tvdb_cuda_sample_quadratic_dense(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid_in,
                                            const tvdb_vec3f* pts, size_t n,
                                            float* out_values, tvdb_error_t* err) {
  return tvdb_cuda_sample_dense_kernel(ctx, grid_in, pts, n, out_values, "tvdb_cuda_sample_quadratic", err);
}

static tvdb_status_t tvdb_cuda_sparse_conv(tvdb_gpu_context_t* ctx, const tvdb_sparse_grid* in,
                                           const float* kernel, int kx, int ky, int kz,
                                           float pad_value, tvdb_sparse_grid* out,
                                           tvdb_error_t* err) {
  CUmodule module = NULL;
  CUfunction fn = NULL;
  CUdeviceptr dc = 0, dv = 0, dk = 0, dout = 0;
  int32_t* c4 = NULL;
  tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
  if (st != TVDB_OK) return st;
  c4 = (int32_t*)calloc(in->count ? in->count : 1, 4u * sizeof(int32_t));
  if (!c4) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); st = TVDB_ERROR_OUT_OF_MEMORY; goto done; }
  for (size_t i = 0; i < in->count; ++i) {
    c4[4*i+0] = in->coords[i].x; c4[4*i+1] = in->coords[i].y; c4[4*i+2] = in->coords[i].z; c4[4*i+3] = 0;
    out->coords[i] = in->coords[i];
  }
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_sparse_conv"))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dc, c4, in->count * 4u * sizeof(int32_t), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dv, in->values, in->count * sizeof(float), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dk, kernel, (size_t)kx * (size_t)ky * (size_t)kz * sizeof(float), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, in->count * sizeof(float), err)) != TVDB_OK) goto done;
  unsigned int count = (unsigned int)in->count;
  void* args[] = {&dc, &dv, &dk, &dout, &count, &kx, &ky, &kz, &pad_value};
  unsigned int block = 128;
  unsigned int grid = (count + block - 1u) / block;
  if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out->values, dout, in->count * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  out->count = in->count;
  st = TVDB_OK;
done:
  free(c4);
  if (dout) ctx->cuda.cuMemFree(dout);
  if (dk) ctx->cuda.cuMemFree(dk);
  if (dv) ctx->cuda.cuMemFree(dv);
  if (dc) ctx->cuda.cuMemFree(dc);
  return st;
}

// Near-dense CUDA conv: build a dense bbox-local index grid (O(1) tap lookups)
// instead of the brute-force per-tap scan. Same result, much faster when the
// active set nearly fills its bounding box.
/* Map-probed sparse convolution for CUDA, the twin of the Vulkan
 * sparse_conv_map path. Reached when the active set's bbox does not fit a dense
 * index grid, where the alternative is a per-tap scan of the whole active set. */
static tvdb_status_t tvdb_cuda_sparse_conv_map(tvdb_gpu_context_t* ctx, const tvdb_sparse_grid* in,
                                               const float* kernel, int kx, int ky, int kz,
                                               float pad_value, tvdb_sparse_grid* out, tvdb_error_t* err) {
  CUmodule module = NULL; CUfunction f = NULL;
  CUdeviceptr dmap = 0, dc = 0, dv = 0, dk = 0, dout = 0;
  int32_t* map4 = NULL;
  int32_t* c4 = NULL;
  uint32_t cap = 0;
  tvdb_status_t st = tvdb_index_map_build4(in, &map4, &cap, err);
  if (st != TVDB_OK) return st;
  c4 = (int32_t*)calloc(in->count, 4u * sizeof(int32_t));
  if (!c4) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); st = TVDB_ERROR_OUT_OF_MEMORY; goto done; }
  for (size_t i = 0; i < in->count; ++i) {
    c4[4*i+0] = in->coords[i].x; c4[4*i+1] = in->coords[i].y; c4[4*i+2] = in->coords[i].z; c4[4*i+3] = 0;
    out->coords[i] = in->coords[i];
  }
  if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto done;
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction",
        ctx->cuda.cuModuleGetFunction(&f, module, "tvdb_cuda_sparse_conv_map"))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dmap, map4, (size_t)cap * 4u * sizeof(int32_t), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dc, c4, in->count * 4u * sizeof(int32_t), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dv, in->values, in->count * sizeof(float), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dk, kernel, (size_t)kx * (size_t)ky * (size_t)kz * sizeof(float), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, in->count * sizeof(float), err)) != TVDB_OK) goto done;
  {
    unsigned int count = (unsigned int)in->count, ucap = cap, umask = cap - 1u, block = 128;
    void* args[] = {&dmap, &dc, &dv, &dk, &dout, &count, &kx, &ky, &kz, &pad_value, &ucap, &umask};
    unsigned int grid = (count + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(f, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out->values, dout, in->count * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  out->count = in->count;
  st = TVDB_OK;
done:
  free(c4); free(map4);
  if (dout) ctx->cuda.cuMemFree(dout);
  if (dk) ctx->cuda.cuMemFree(dk);
  if (dv) ctx->cuda.cuMemFree(dv);
  if (dc) ctx->cuda.cuMemFree(dc);
  if (dmap) ctx->cuda.cuMemFree(dmap);
  return st;
}

static tvdb_status_t tvdb_cuda_sparse_conv_dense(tvdb_gpu_context_t* ctx, const tvdb_sparse_grid* in,
                                                 const float* kernel, int kx, int ky, int kz,
                                                 float pad_value, const int32_t bbmin[3], const int32_t dims[3],
                                                 size_t volume, tvdb_sparse_grid* out, tvdb_error_t* err) {
  CUmodule module = NULL;
  CUfunction fscatter = NULL, fconv = NULL;
  CUdeviceptr dc = 0, dv = 0, dk = 0, dout = 0, didx = 0;
  int32_t* c4 = NULL;
  tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
  if (st != TVDB_OK) return st;
  if (!ctx->cuda.cuMemsetD32) { tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "cuMemsetD32 unavailable"); return TVDB_ERROR_UNIMPLEMENTED; }
  c4 = (int32_t*)calloc(in->count ? in->count : 1, 4u * sizeof(int32_t));
  if (!c4) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); st = TVDB_ERROR_OUT_OF_MEMORY; goto done; }
  for (size_t i = 0; i < in->count; ++i) {
    c4[4*i+0] = in->coords[i].x; c4[4*i+1] = in->coords[i].y; c4[4*i+2] = in->coords[i].z; c4[4*i+3] = 0;
    out->coords[i] = in->coords[i];
  }
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fscatter, module, "tvdb_cuda_sparse_index_scatter"))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fconv, module, "tvdb_cuda_sparse_conv_dense"))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dc, c4, in->count * 4u * sizeof(int32_t), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dv, in->values, in->count * sizeof(float), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dk, kernel, (size_t)kx * (size_t)ky * (size_t)kz * sizeof(float), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, in->count * sizeof(float), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &didx, NULL, volume * sizeof(int32_t), err)) != TVDB_OK) goto done;
  if (!tvdb_cuda_ok(ctx, err, "cuMemsetD32", ctx->cuda.cuMemsetD32(didx, 0xFFFFFFFFu, volume))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  {
    unsigned int count = (unsigned int)in->count, block = 128;
    int bx = bbmin[0], by = bbmin[1], bz = bbmin[2], dx = dims[0], dy = dims[1], dz = dims[2];
    void* sargs[] = {&dc, &didx, &bx, &by, &bz, &dx, &dy, &dz, &count};
    unsigned int gs = (count + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fscatter, gs, 1, 1, block, 1, 1, 0, NULL, sargs, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
    void* cargs[] = {&dc, &dv, &dk, &dout, &didx, &count, &kx, &ky, &kz, &pad_value, &bx, &by, &bz, &dx, &dy, &dz};
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fconv, gs, 1, 1, block, 1, 1, 0, NULL, cargs, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out->values, dout, in->count * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  out->count = in->count;
  st = TVDB_OK;
done:
  free(c4);
  if (didx) ctx->cuda.cuMemFree(didx);
  if (dout) ctx->cuda.cuMemFree(dout);
  if (dk) ctx->cuda.cuMemFree(dk);
  if (dv) ctx->cuda.cuMemFree(dv);
  if (dc) ctx->cuda.cuMemFree(dc);
  return st;
}

static tvdb_status_t tvdb_gpu_csg_dense_impl(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* a,
                                 const tvdb_dense_grid* b, int op,
                                 tvdb_dense_grid* out, tvdb_error_t* err) {
  if (!ctx || !tvdb_dense_same_shape(a, b, out) || op < 0 || op > 2) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid dense CSG arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    return tvdb_cuda_csg_dense(ctx, a, b, op, out, err);
  }
  size_t n = (size_t)a->nx * (size_t)a->ny * (size_t)a->nz;
  tvdb_vk_buffer ba, bb, bo, bp;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &ba, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bb, err)) != TVDB_OK) goto done_a;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto done_b;
  if ((st = tvdb_vk_create_buffer(ctx, 16, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bp, err)) != TVDB_OK) goto done_o;
  memcpy(ba.mapped, a->data, n * sizeof(float));
  memcpy(bb.mapped, b->data, n * sizeof(float));
  uint32_t params[4] = {(uint32_t)n, (uint32_t)op, 0, 0};
  memcpy(bp.mapped, params, sizeof(params));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuCsgSpv; d.spv_len = kTvdbGpuCsgSpv_len; d.descriptor_count = 4;
  d.buffers[0] = &ba; d.buffers[1] = &bb; d.buffers[2] = &bo; d.buffers[3] = &bp;
  d.descriptor_types[0] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((n + 255u) / 256u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(out->data, bo.mapped, n * sizeof(float));
  tvdb_vk_destroy_buffer(ctx, &bp);
done_o: tvdb_vk_destroy_buffer(ctx, &bo);
done_b: tvdb_vk_destroy_buffer(ctx, &bb);
done_a: tvdb_vk_destroy_buffer(ctx, &ba);
  return st;
}

static tvdb_status_t tvdb_vk_sdf_sphere_dense(tvdb_gpu_context_t* ctx,
                                              float radius,
                                              const float center[3],
                                              float background,
                                              tvdb_dense_grid* out,
                                              tvdb_error_t* err) {
  size_t n = (size_t)out->nx * (size_t)out->ny * (size_t)out->nz;
  tvdb_vk_buffer bo, bp;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, 64, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bp, err)) != TVDB_OK) goto done_o;
  struct { int32_t dim[4]; float ov[4]; float cr[4]; float bc[4]; } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = out->nx; par.dim[1] = out->ny; par.dim[2] = out->nz;
  par.dim[3] = (int32_t)n;
  par.ov[0] = out->ox; par.ov[1] = out->oy; par.ov[2] = out->oz; par.ov[3] = out->voxel_size;
  par.cr[0] = center[0]; par.cr[1] = center[1]; par.cr[2] = center[2]; par.cr[3] = radius;
  par.bc[0] = background;
  memcpy(bp.mapped, &par, sizeof(par));

  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuSdfSphereSpv;
  d.spv_len = kTvdbGpuSdfSphereSpv_len;
  d.descriptor_count = 2;
  d.buffers[0] = &bo;
  d.buffers[1] = &bp;
  d.descriptor_types[0] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((n + 255u) / 256u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(out->data, bo.mapped, n * sizeof(float));
  tvdb_vk_destroy_buffer(ctx, &bp);
done_o:
  tvdb_vk_destroy_buffer(ctx, &bo);
  return st;
}

static tvdb_status_t tvdb_vk_sdf_box_dense(tvdb_gpu_context_t* ctx,
                                           const float half_extents[3],
                                           const float center[3],
                                           float background,
                                           tvdb_dense_grid* out,
                                           tvdb_error_t* err) {
  size_t n = (size_t)out->nx * (size_t)out->ny * (size_t)out->nz;
  tvdb_vk_buffer bo, bp;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, 64, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bp, err)) != TVDB_OK) goto done_o;
  struct { int32_t dim[4]; float ov[4]; float cp[4]; float hb[4]; } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = out->nx; par.dim[1] = out->ny; par.dim[2] = out->nz; par.dim[3] = (int32_t)n;
  par.ov[0] = out->ox; par.ov[1] = out->oy; par.ov[2] = out->oz; par.ov[3] = out->voxel_size;
  par.cp[0] = center[0]; par.cp[1] = center[1]; par.cp[2] = center[2];
  par.hb[0] = half_extents[0]; par.hb[1] = half_extents[1]; par.hb[2] = half_extents[2]; par.hb[3] = background;
  memcpy(bp.mapped, &par, sizeof(par));

  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuSdfBoxSpv;
  d.spv_len = kTvdbGpuSdfBoxSpv_len;
  d.descriptor_count = 2;
  d.buffers[0] = &bo;
  d.buffers[1] = &bp;
  d.descriptor_types[0] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((n + 255u) / 256u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(out->data, bo.mapped, n * sizeof(float));
  tvdb_vk_destroy_buffer(ctx, &bp);
done_o:
  tvdb_vk_destroy_buffer(ctx, &bo);
  return st;
}

static tvdb_status_t tvdb_vk_sdf_torus_dense(tvdb_gpu_context_t* ctx,
                                             float major_radius,
                                             float minor_radius,
                                             const float center[3],
                                             float background,
                                             tvdb_dense_grid* out,
                                             tvdb_error_t* err) {
  size_t n = (size_t)out->nx * (size_t)out->ny * (size_t)out->nz;
  tvdb_vk_buffer bo, bp;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, 64, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bp, err)) != TVDB_OK) goto done_o;
  struct { int32_t dim[4]; float ov[4]; float cm[4]; float mb[4]; } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = out->nx; par.dim[1] = out->ny; par.dim[2] = out->nz; par.dim[3] = (int32_t)n;
  par.ov[0] = out->ox; par.ov[1] = out->oy; par.ov[2] = out->oz; par.ov[3] = out->voxel_size;
  par.cm[0] = center[0]; par.cm[1] = center[1]; par.cm[2] = center[2]; par.cm[3] = major_radius;
  par.mb[0] = minor_radius; par.mb[1] = background;
  memcpy(bp.mapped, &par, sizeof(par));

  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuSdfTorusSpv;
  d.spv_len = kTvdbGpuSdfTorusSpv_len;
  d.descriptor_count = 2;
  d.buffers[0] = &bo;
  d.buffers[1] = &bp;
  d.descriptor_types[0] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((n + 255u) / 256u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(out->data, bo.mapped, n * sizeof(float));
  tvdb_vk_destroy_buffer(ctx, &bp);
done_o:
  tvdb_vk_destroy_buffer(ctx, &bo);
  return st;
}

tvdb_status_t tvdb_gpu_level_set_sphere(tvdb_gpu_context_t* ctx,
                                        float radius,
                                        const float center[3],
                                        float voxel_size,
                                        float half_width,
                                        tvdb_dense_grid* out,
                                        tvdb_error_t* err) {
  if (!ctx || !center || !out || radius <= 0.0f || voxel_size <= 0.0f) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid GPU sphere SDF arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  memset(out, 0, sizeof(*out));
  float background = 0.0f;
  if (!tvdb_gpu_make_sphere_grid(radius, center, voxel_size, half_width, out, &background)) {
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "failed to allocate GPU sphere SDF grid");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  tvdb_status_t st = TVDB_OK;
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    st = tvdb_cuda_sdf_sphere_dense(ctx, radius, center, background, out, err);
  } else {
    st = tvdb_vk_sdf_sphere_dense(ctx, radius, center, background, out, err);
  }
  if (st != TVDB_OK) {
    tvdb_dense_grid_free(out);
    memset(out, 0, sizeof(*out));
  }
  return st;
}

tvdb_status_t tvdb_gpu_level_set_box(tvdb_gpu_context_t* ctx,
                                     const float half_extents[3],
                                     const float center[3],
                                     float voxel_size,
                                     float half_width,
                                     tvdb_dense_grid* out,
                                     tvdb_error_t* err) {
  if (!ctx || !half_extents || !center || !out || voxel_size <= 0.0f ||
      half_extents[0] <= 0.0f || half_extents[1] <= 0.0f || half_extents[2] <= 0.0f) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid GPU box SDF arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  memset(out, 0, sizeof(*out));
  float background = 0.0f;
  if (!tvdb_gpu_make_box_grid(half_extents, center, voxel_size, half_width, out, &background)) {
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "failed to allocate GPU box SDF grid");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  tvdb_status_t st = TVDB_OK;
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    st = tvdb_cuda_sdf_box_dense(ctx, half_extents, center, background, out, err);
  } else {
    st = tvdb_vk_sdf_box_dense(ctx, half_extents, center, background, out, err);
  }
  if (st != TVDB_OK) {
    tvdb_dense_grid_free(out);
    memset(out, 0, sizeof(*out));
  }
  return st;
}

tvdb_status_t tvdb_gpu_level_set_torus(tvdb_gpu_context_t* ctx,
                                       float major_radius,
                                       float minor_radius,
                                       const float center[3],
                                       float voxel_size,
                                       float half_width,
                                       tvdb_dense_grid* out,
                                       tvdb_error_t* err) {
  if (!ctx || !center || !out || major_radius <= 0.0f || minor_radius <= 0.0f || voxel_size <= 0.0f) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid GPU torus SDF arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  memset(out, 0, sizeof(*out));
  float background = 0.0f;
  if (!tvdb_gpu_make_torus_grid(major_radius, minor_radius, center, voxel_size, half_width, out, &background)) {
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "failed to allocate GPU torus SDF grid");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  tvdb_status_t st = TVDB_OK;
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    st = tvdb_cuda_sdf_torus_dense(ctx, major_radius, minor_radius, center, background, out, err);
  } else {
    st = tvdb_vk_sdf_torus_dense(ctx, major_radius, minor_radius, center, background, out, err);
  }
  if (st != TVDB_OK) {
    tvdb_dense_grid_free(out);
    memset(out, 0, sizeof(*out));
  }
  return st;
}

tvdb_status_t tvdb_gpu_sample_trilinear_dense_batch(tvdb_gpu_context_t* ctx,
                                                    const tvdb_dense_grid* grid,
                                                    const tvdb_vec3f* pts,
                                                    size_t n,
                                                    float* out_values,
                                                    tvdb_error_t* err) {
  if (!ctx || !grid || !tvdb_gpu_shape_valid(grid->nx,grid->ny,grid->nz,grid->voxel_size,grid->data,sizeof(float)) ||
      !isfinite(grid->ox) || !isfinite(grid->oy) || !isfinite(grid->oz) || n > INT_MAX || !pts || !out_values) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid sample arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  for(size_t i=0;i<n;++i) {
    if(!isfinite(pts[i].x) || !isfinite(pts[i].y) || !isfinite(pts[i].z)) {
      tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"nonfinite sample point");
      return TVDB_ERROR_INVALID_ARGUMENT;
    }
  }
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    return tvdb_cuda_sample_dense(ctx, grid, pts, n, out_values, err);
  }
  size_t voxels = (size_t)grid->nx * (size_t)grid->ny * (size_t)grid->nz;
  tvdb_vk_buffer bg, bpnts, bo, bpar;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, voxels * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bg, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, n * 4u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bpnts, err)) != TVDB_OK) goto done_g;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto done_pnts;
  if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bpar, err)) != TVDB_OK) goto done_o;
  memcpy(bg.mapped, grid->data, voxels * sizeof(float));
  float* p4 = (float*)bpnts.mapped;
  for (size_t i = 0; i < n; ++i) {
    p4[4*i+0] = pts[i].x; p4[4*i+1] = pts[i].y; p4[4*i+2] = pts[i].z; p4[4*i+3] = 0.0f;
  }
  struct { int32_t dim[4]; float ov[4]; uint32_t count; uint32_t pad[3]; } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = grid->nx; par.dim[1] = grid->ny; par.dim[2] = grid->nz;
  par.ov[0] = grid->ox; par.ov[1] = grid->oy; par.ov[2] = grid->oz; par.ov[3] = grid->voxel_size;
  par.count = (uint32_t)n;
  memcpy(bpar.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuSampleSpv; d.spv_len = kTvdbGpuSampleSpv_len; d.descriptor_count = 4;
  d.buffers[0] = &bg; d.buffers[1] = &bpnts; d.buffers[2] = &bo; d.buffers[3] = &bpar;
  d.descriptor_types[0] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((n + 127u) / 128u);
  /* Read-heavy: 8 taps per query, so binding the grid device-local beats
   * the kernel pulling trilinear corners over PCIe. */
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(out_values, bo.mapped, n * sizeof(float));
  tvdb_vk_destroy_buffer(ctx, &bpar);
done_o: tvdb_vk_destroy_buffer(ctx, &bo);
done_pnts: tvdb_vk_destroy_buffer(ctx, &bpnts);
done_g: tvdb_vk_destroy_buffer(ctx, &bg);
  return st;
}

tvdb_status_t tvdb_gpu_sample_quadratic_dense_batch(tvdb_gpu_context_t* ctx,
                                                    const tvdb_dense_grid* grid,
                                                    const tvdb_vec3f* pts,
                                                    size_t n,
                                                    float* out_values,
                                                    tvdb_error_t* err) {
  if (!ctx || !grid || !tvdb_gpu_shape_valid(grid->nx,grid->ny,grid->nz,grid->voxel_size,grid->data,sizeof(float)) ||
      !isfinite(grid->ox) || !isfinite(grid->oy) || !isfinite(grid->oz) || n > INT_MAX || !pts || !out_values) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid quadratic sample arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (n == 0) return TVDB_OK;
  for(size_t i=0;i<n;++i) {
    if(!isfinite(pts[i].x) || !isfinite(pts[i].y) || !isfinite(pts[i].z)) {
      tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"nonfinite sample point");
      return TVDB_ERROR_INVALID_ARGUMENT;
    }
  }
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    return tvdb_cuda_sample_quadratic_dense(ctx, grid, pts, n, out_values, err);
  }
  size_t voxels = (size_t)grid->nx * (size_t)grid->ny * (size_t)grid->nz;
  tvdb_vk_buffer bg, bpnts, bo, bpar;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, voxels * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bg, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, n * 4u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bpnts, err)) != TVDB_OK) goto qdone_g;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto qdone_pnts;
  if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bpar, err)) != TVDB_OK) goto qdone_o;
  memcpy(bg.mapped, grid->data, voxels * sizeof(float));
  float* p4 = (float*)bpnts.mapped;
  for (size_t i = 0; i < n; ++i) {
    p4[4*i+0] = pts[i].x; p4[4*i+1] = pts[i].y; p4[4*i+2] = pts[i].z; p4[4*i+3] = 0.0f;
  }
  struct { int32_t dim[4]; float ov[4]; uint32_t count; uint32_t pad[3]; } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = grid->nx; par.dim[1] = grid->ny; par.dim[2] = grid->nz;
  par.ov[0] = grid->ox; par.ov[1] = grid->oy; par.ov[2] = grid->oz; par.ov[3] = grid->voxel_size;
  par.count = (uint32_t)n;
  memcpy(bpar.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuSampleQuadraticSpv; d.spv_len = kTvdbGpuSampleQuadraticSpv_len; d.descriptor_count = 4;
  d.buffers[0] = &bg; d.buffers[1] = &bpnts; d.buffers[2] = &bo; d.buffers[3] = &bpar;
  d.descriptor_types[0] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((n + 127u) / 128u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(out_values, bo.mapped, n * sizeof(float));
  tvdb_vk_destroy_buffer(ctx, &bpar);
qdone_o: tvdb_vk_destroy_buffer(ctx, &bo);
qdone_pnts: tvdb_vk_destroy_buffer(ctx, &bpnts);
qdone_g: tvdb_vk_destroy_buffer(ctx, &bg);
  return st;
}

static tvdb_status_t tvdb_vk_sample_dense_image3d(tvdb_gpu_context_t* ctx,
                                                  const tvdb_dense_grid* grid,
                                                  const tvdb_vec3f* pts,
                                                  size_t n,
                                                  float* out_values,
                                                  int use_sparse_residency,
                                                  tvdb_error_t* err) {
  if (!ctx || ctx->backend != TVDB_GPU_BACKEND_VULKAN) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "Vulkan image3D sampling requires a Vulkan context");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  if (!grid || !grid->data || !pts || !out_values || grid->nx <= 0 || grid->ny <= 0 || grid->nz <= 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid image3D sample arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_vk_image3d image;
  tvdb_vk_buffer bpnts, bo, bpar;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_image3d_from_dense(ctx, grid, use_sparse_residency, &image, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, n * 4u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bpnts, err)) != TVDB_OK) goto done_image;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto done_pnts;
  if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bpar, err)) != TVDB_OK) goto done_o;
  float* p4 = (float*)bpnts.mapped;
  for (size_t i = 0; i < n; ++i) {
    p4[4*i+0] = pts[i].x; p4[4*i+1] = pts[i].y; p4[4*i+2] = pts[i].z; p4[4*i+3] = 0.0f;
  }
  struct { int32_t dim[4]; float ov[4]; uint32_t count; uint32_t pad[3]; } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = grid->nx; par.dim[1] = grid->ny; par.dim[2] = grid->nz;
  par.ov[0] = grid->ox; par.ov[1] = grid->oy; par.ov[2] = grid->oz; par.ov[3] = grid->voxel_size;
  par.count = (uint32_t)n;
  memcpy(bpar.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuSampleImageSpv; d.spv_len = kTvdbGpuSampleImageSpv_len; d.descriptor_count = 4;
  d.images[0] = &image; d.buffers[1] = &bpnts; d.buffers[2] = &bo; d.buffers[3] = &bpar;
  d.descriptor_types[0] = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER;
  d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((n + 127u) / 128u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(out_values, bo.mapped, n * sizeof(float));
  tvdb_vk_destroy_buffer(ctx, &bpar);
done_o: tvdb_vk_destroy_buffer(ctx, &bo);
done_pnts: tvdb_vk_destroy_buffer(ctx, &bpnts);
done_image: tvdb_vk_destroy_image3d(ctx, &image);
  return st;
}

static tvdb_status_t tvdb_vk_sample_existing_image3d(tvdb_gpu_context_t* ctx,
                                                     const tvdb_vk_image3d* image,
                                                     float ox, float oy, float oz,
                                                     float voxel_size,
                                                     const tvdb_vec3f* pts,
                                                     size_t n,
                                                     float* out_values,
                                                     tvdb_error_t* err) {
  if (!ctx || ctx->backend != TVDB_GPU_BACKEND_VULKAN || !image || !image->image) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid persistent image3D sample arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (!pts || !out_values) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid persistent image3D sample buffers");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_vk_buffer bpnts, bo, bpar;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, n * 4u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bpnts, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto done_pnts;
  if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bpar, err)) != TVDB_OK) goto done_o;
  float* p4 = (float*)bpnts.mapped;
  for (size_t i = 0; i < n; ++i) {
    p4[4*i+0] = pts[i].x; p4[4*i+1] = pts[i].y; p4[4*i+2] = pts[i].z; p4[4*i+3] = 0.0f;
  }
  struct { int32_t dim[4]; float ov[4]; uint32_t count; uint32_t pad[3]; } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = (int32_t)image->nx; par.dim[1] = (int32_t)image->ny; par.dim[2] = (int32_t)image->nz;
  par.ov[0] = ox; par.ov[1] = oy; par.ov[2] = oz; par.ov[3] = voxel_size;
  par.count = (uint32_t)n;
  memcpy(bpar.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuSampleImageSpv; d.spv_len = kTvdbGpuSampleImageSpv_len; d.descriptor_count = 4;
  d.images[0] = image; d.buffers[1] = &bpnts; d.buffers[2] = &bo; d.buffers[3] = &bpar;
  d.descriptor_types[0] = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER;
  d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((n + 127u) / 128u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(out_values, bo.mapped, n * sizeof(float));
  tvdb_vk_destroy_buffer(ctx, &bpar);
done_o: tvdb_vk_destroy_buffer(ctx, &bo);
done_pnts: tvdb_vk_destroy_buffer(ctx, &bpnts);
  return st;
}

static void tvdb_vk_destroy_sparse_image3d_dispatch(tvdb_gpu_vulkan_sparse_image3d_t* image) {
  if (!image || !image->ctx) return;
  tvdb_gpu_context_t* ctx = image->ctx;
  /* submit/destroy is a legal sequence, so an outstanding submit may still be
   * reading the buffers and holding the command buffer. Wait before releasing
   * any of it -- the same rule the deferred-dispatch path already follows at
   * tvdb_vk_drain_pending. */
  if (image->sample_in_flight && image->sample_fence && ctx->vk.WaitForFences) {
    ctx->vk.WaitForFences(ctx->device, 1, &image->sample_fence, VK_TRUE, UINT64_MAX);
    image->sample_in_flight = 0;
  }
  tvdb_vk_destroy_buffer(ctx, &image->sample_params);
  tvdb_vk_destroy_buffer(ctx, &image->sample_output);
  tvdb_vk_destroy_buffer(ctx, &image->sample_points);
  if (image->sample_fence) ctx->vk.DestroyFence(ctx->device, image->sample_fence, NULL);
  if (image->sample_command_pool) ctx->vk.DestroyCommandPool(ctx->device, image->sample_command_pool, NULL);
  if (image->sample_pipeline) ctx->vk.DestroyPipeline(ctx->device, image->sample_pipeline, NULL);
  if (image->sample_pipeline_layout) ctx->vk.DestroyPipelineLayout(ctx->device, image->sample_pipeline_layout, NULL);
  if (image->sample_pool) ctx->vk.DestroyDescriptorPool(ctx->device, image->sample_pool, NULL);
  if (image->sample_layout) ctx->vk.DestroyDescriptorSetLayout(ctx->device, image->sample_layout, NULL);
  image->sample_fence = VK_NULL_HANDLE;
  image->sample_command_pool = VK_NULL_HANDLE;
  image->sample_cmd = NULL;
  image->sample_pipeline = VK_NULL_HANDLE;
  image->sample_pipeline_layout = VK_NULL_HANDLE;
  image->sample_pool = VK_NULL_HANDLE;
  image->sample_set = VK_NULL_HANDLE;
  image->sample_layout = VK_NULL_HANDLE;
  image->sample_cmd_recorded = 0;
  image->sample_in_flight = 0;
  image->sample_capacity = 0;
  image->sample_descriptors_bound = 0;
  image->sample_group_x = 0;
  image->sample_bound_points = VK_NULL_HANDLE;
  image->sample_bound_output = VK_NULL_HANDLE;
  image->sample_bound_params = VK_NULL_HANDLE;
}

static tvdb_status_t tvdb_vk_create_sparse_image3d_dispatch(tvdb_gpu_vulkan_sparse_image3d_t* image,
                                                            tvdb_error_t* err) {
  tvdb_gpu_context_t* ctx = image->ctx;
  if (!kTvdbGpuSampleImageSpv || kTvdbGpuSampleImageSpv_len == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "Vulkan image sampler SPIR-V blob is unavailable");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  VkDescriptorSetLayoutBinding bindings[4];
  memset(bindings, 0, sizeof(bindings));
  bindings[0].binding = 0; bindings[0].descriptorCount = 1; bindings[0].descriptorType = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER; bindings[0].stageFlags = VK_SHADER_STAGE_COMPUTE_BIT;
  bindings[1].binding = 1; bindings[1].descriptorCount = 1; bindings[1].descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; bindings[1].stageFlags = VK_SHADER_STAGE_COMPUTE_BIT;
  bindings[2].binding = 2; bindings[2].descriptorCount = 1; bindings[2].descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; bindings[2].stageFlags = VK_SHADER_STAGE_COMPUTE_BIT;
  bindings[3].binding = 3; bindings[3].descriptorCount = 1; bindings[3].descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER; bindings[3].stageFlags = VK_SHADER_STAGE_COMPUTE_BIT;
  VkDescriptorSetLayoutCreateInfo dlci;
  memset(&dlci, 0, sizeof(dlci));
  dlci.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO;
  dlci.bindingCount = 4;
  dlci.pBindings = bindings;
  if (!tvdb_vk_ok(ctx->vk.CreateDescriptorSetLayout(ctx->device, &dlci, NULL, &image->sample_layout), err, "vkCreateDescriptorSetLayout(persistent sample)")) goto fail;

  VkDescriptorPoolSize pool_sizes[3];
  memset(pool_sizes, 0, sizeof(pool_sizes));
  pool_sizes[0].type = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; pool_sizes[0].descriptorCount = 2;
  pool_sizes[1].type = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER; pool_sizes[1].descriptorCount = 1;
  pool_sizes[2].type = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER; pool_sizes[2].descriptorCount = 1;
  VkDescriptorPoolCreateInfo dpci;
  memset(&dpci, 0, sizeof(dpci));
  dpci.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO;
  dpci.maxSets = 1;
  dpci.poolSizeCount = 3;
  dpci.pPoolSizes = pool_sizes;
  if (!tvdb_vk_ok(ctx->vk.CreateDescriptorPool(ctx->device, &dpci, NULL, &image->sample_pool), err, "vkCreateDescriptorPool(persistent sample)")) goto fail;
  VkDescriptorSetAllocateInfo dsai;
  memset(&dsai, 0, sizeof(dsai));
  dsai.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
  dsai.descriptorPool = image->sample_pool;
  dsai.descriptorSetCount = 1;
  dsai.pSetLayouts = &image->sample_layout;
  if (!tvdb_vk_ok(ctx->vk.AllocateDescriptorSets(ctx->device, &dsai, &image->sample_set), err, "vkAllocateDescriptorSets(persistent sample)")) goto fail;

  VkShaderModule shader = VK_NULL_HANDLE;
  VkShaderModuleCreateInfo smci;
  memset(&smci, 0, sizeof(smci));
  smci.sType = VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO;
  smci.codeSize = kTvdbGpuSampleImageSpv_len;
  smci.pCode = (const uint32_t*)kTvdbGpuSampleImageSpv;
  if (!tvdb_vk_ok(ctx->vk.CreateShaderModule(ctx->device, &smci, NULL, &shader), err, "vkCreateShaderModule(persistent sample)")) goto fail;
  VkPipelineLayoutCreateInfo plci;
  memset(&plci, 0, sizeof(plci));
  plci.sType = VK_STRUCTURE_TYPE_PIPELINE_LAYOUT_CREATE_INFO;
  plci.setLayoutCount = 1;
  plci.pSetLayouts = &image->sample_layout;
  if (!tvdb_vk_ok(ctx->vk.CreatePipelineLayout(ctx->device, &plci, NULL, &image->sample_pipeline_layout), err, "vkCreatePipelineLayout(persistent sample)")) {
    ctx->vk.DestroyShaderModule(ctx->device, shader, NULL);
    goto fail;
  }
  VkComputePipelineCreateInfo cpci;
  memset(&cpci, 0, sizeof(cpci));
  cpci.sType = VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO;
  cpci.stage.sType = VK_STRUCTURE_TYPE_PIPELINE_SHADER_STAGE_CREATE_INFO;
  cpci.stage.stage = VK_SHADER_STAGE_COMPUTE_BIT;
  cpci.stage.module = shader;
  cpci.stage.pName = "main";
  cpci.layout = image->sample_pipeline_layout;
  int ok = tvdb_vk_ok(ctx->vk.CreateComputePipelines(ctx->device, VK_NULL_HANDLE, 1, &cpci, NULL, &image->sample_pipeline), err, "vkCreateComputePipelines(persistent sample)");
  ctx->vk.DestroyShaderModule(ctx->device, shader, NULL);
  if (!ok) goto fail;

  VkCommandPoolCreateInfo cmdpool;
  memset(&cmdpool, 0, sizeof(cmdpool));
  cmdpool.sType = VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO;
  cmdpool.flags = VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT;
  cmdpool.queueFamilyIndex = ctx->queue_family;
  if (!tvdb_vk_ok(ctx->vk.CreateCommandPool(ctx->device, &cmdpool, NULL, &image->sample_command_pool), err, "vkCreateCommandPool(persistent sample)")) goto fail;
  VkCommandBufferAllocateInfo cbai;
  memset(&cbai, 0, sizeof(cbai));
  cbai.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
  cbai.commandPool = image->sample_command_pool;
  cbai.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
  cbai.commandBufferCount = 1;
  if (!tvdb_vk_ok(ctx->vk.AllocateCommandBuffers(ctx->device, &cbai, &image->sample_cmd), err, "vkAllocateCommandBuffers(persistent sample)")) goto fail;
  VkFenceCreateInfo fci;
  memset(&fci, 0, sizeof(fci));
  fci.sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO;
  if (!tvdb_vk_ok(ctx->vk.CreateFence(ctx->device, &fci, NULL, &image->sample_fence), err, "vkCreateFence(persistent sample)")) goto fail;
  return TVDB_OK;

fail:
  tvdb_vk_destroy_sparse_image3d_dispatch(image);
  return err ? err->status : TVDB_ERROR_IO;
}

static tvdb_status_t tvdb_vk_sparse_image3d_ensure_sample_workspace(tvdb_gpu_vulkan_sparse_image3d_t* image,
                                                                    size_t n,
                                                                    tvdb_error_t* err) {
  tvdb_gpu_context_t* ctx = image->ctx;
  size_t cap = n ? n : 1;
  if (image->sample_capacity >= cap && image->sample_descriptors_bound &&
      image->sample_bound_points == image->sample_points.buffer &&
      image->sample_bound_output == image->sample_output.buffer &&
      image->sample_bound_params == image->sample_params.buffer) return TVDB_OK;
  if (image->sample_capacity < cap) {
    tvdb_vk_destroy_buffer(ctx, &image->sample_params);
    tvdb_vk_destroy_buffer(ctx, &image->sample_output);
    tvdb_vk_destroy_buffer(ctx, &image->sample_points);
    image->sample_capacity = 0;
    image->sample_descriptors_bound = 0;
    tvdb_status_t st;
    if ((st = tvdb_vk_create_buffer(ctx, cap * 4u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &image->sample_points, err)) != TVDB_OK) return st;
    if ((st = tvdb_vk_create_buffer(ctx, cap * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &image->sample_output, err)) != TVDB_OK) return st;
    if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &image->sample_params, err)) != TVDB_OK) return st;
    image->sample_capacity = cap;
  }

  VkDescriptorImageInfo image_info;
  VkDescriptorBufferInfo buffer_infos[3];
  VkWriteDescriptorSet writes[4];
  memset(&image_info, 0, sizeof(image_info));
  memset(buffer_infos, 0, sizeof(buffer_infos));
  memset(writes, 0, sizeof(writes));
  image_info.sampler = image->image.sampler;
  image_info.imageView = image->image.view;
  image_info.imageLayout = VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL;
  buffer_infos[0].buffer = image->sample_points.buffer; buffer_infos[0].range = image->sample_points.size;
  buffer_infos[1].buffer = image->sample_output.buffer; buffer_infos[1].range = image->sample_output.size;
  buffer_infos[2].buffer = image->sample_params.buffer; buffer_infos[2].range = image->sample_params.size;
  writes[0].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET; writes[0].dstSet = image->sample_set; writes[0].dstBinding = 0; writes[0].descriptorCount = 1; writes[0].descriptorType = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER; writes[0].pImageInfo = &image_info;
  writes[1].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET; writes[1].dstSet = image->sample_set; writes[1].dstBinding = 1; writes[1].descriptorCount = 1; writes[1].descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; writes[1].pBufferInfo = &buffer_infos[0];
  writes[2].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET; writes[2].dstSet = image->sample_set; writes[2].dstBinding = 2; writes[2].descriptorCount = 1; writes[2].descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; writes[2].pBufferInfo = &buffer_infos[1];
  writes[3].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET; writes[3].dstSet = image->sample_set; writes[3].dstBinding = 3; writes[3].descriptorCount = 1; writes[3].descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER; writes[3].pBufferInfo = &buffer_infos[2];
  ctx->vk.UpdateDescriptorSets(ctx->device, 4, writes, 0, NULL);
  image->sample_descriptors_bound = 1;
  image->sample_bound_points = image->sample_points.buffer;
  image->sample_bound_output = image->sample_output.buffer;
  image->sample_bound_params = image->sample_params.buffer;
  return TVDB_OK;
}

static int tvdb_vk_sparse_image3d_bind_sample_buffers(tvdb_gpu_vulkan_sparse_image3d_t* image,
                                                      const tvdb_vk_buffer* points,
                                                      const tvdb_vk_buffer* output,
                                                      const tvdb_vk_buffer* params) {
  if (image->sample_descriptors_bound &&
      image->sample_bound_points == points->buffer &&
      image->sample_bound_output == output->buffer &&
      image->sample_bound_params == params->buffer) {
    return 0;
  }
  tvdb_gpu_context_t* ctx = image->ctx;
  VkDescriptorImageInfo image_info;
  VkDescriptorBufferInfo buffer_infos[3];
  VkWriteDescriptorSet writes[4];
  memset(&image_info, 0, sizeof(image_info));
  memset(buffer_infos, 0, sizeof(buffer_infos));
  memset(writes, 0, sizeof(writes));
  image_info.sampler = image->image.sampler;
  image_info.imageView = image->image.view;
  image_info.imageLayout = VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL;
  buffer_infos[0].buffer = points->buffer; buffer_infos[0].range = points->size;
  buffer_infos[1].buffer = output->buffer; buffer_infos[1].range = output->size;
  buffer_infos[2].buffer = params->buffer; buffer_infos[2].range = params->size;
  writes[0].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET; writes[0].dstSet = image->sample_set; writes[0].dstBinding = 0; writes[0].descriptorCount = 1; writes[0].descriptorType = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER; writes[0].pImageInfo = &image_info;
  writes[1].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET; writes[1].dstSet = image->sample_set; writes[1].dstBinding = 1; writes[1].descriptorCount = 1; writes[1].descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; writes[1].pBufferInfo = &buffer_infos[0];
  writes[2].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET; writes[2].dstSet = image->sample_set; writes[2].dstBinding = 2; writes[2].descriptorCount = 1; writes[2].descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; writes[2].pBufferInfo = &buffer_infos[1];
  writes[3].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET; writes[3].dstSet = image->sample_set; writes[3].dstBinding = 3; writes[3].descriptorCount = 1; writes[3].descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER; writes[3].pBufferInfo = &buffer_infos[2];
  ctx->vk.UpdateDescriptorSets(ctx->device, 4, writes, 0, NULL);
  image->sample_descriptors_bound = 1;
  image->sample_bound_points = points->buffer;
  image->sample_bound_output = output->buffer;
  image->sample_bound_params = params->buffer;
  return 1;
}

static tvdb_status_t tvdb_vk_sparse_image3d_submit_sample(tvdb_gpu_vulkan_sparse_image3d_t* image,
                                                          uint32_t group_x,
                                                          int descriptors_changed,
                                                          int wait,
                                                          tvdb_error_t* err) {
  tvdb_gpu_context_t* ctx = image->ctx;
  if (image->sample_in_flight) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "persistent sample dispatch already in flight");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (!tvdb_vk_ok(ctx->vk.ResetFences(ctx->device, 1, &image->sample_fence), err, "vkResetFences(persistent sample)")) return err ? err->status : TVDB_ERROR_IO;
  if (!image->sample_cmd_recorded || image->sample_group_x != group_x || descriptors_changed) {
    if (image->sample_cmd_recorded) {
      if (!tvdb_vk_ok(ctx->vk.ResetCommandBuffer(image->sample_cmd, 0), err, "vkResetCommandBuffer(persistent sample)")) return err ? err->status : TVDB_ERROR_IO;
    }
    VkCommandBufferBeginInfo begin;
    memset(&begin, 0, sizeof(begin));
    begin.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;
    if (!tvdb_vk_ok(ctx->vk.BeginCommandBuffer(image->sample_cmd, &begin), err, "vkBeginCommandBuffer(persistent sample)")) return err ? err->status : TVDB_ERROR_IO;
    ctx->vk.CmdBindPipeline(image->sample_cmd, VK_PIPELINE_BIND_POINT_COMPUTE, image->sample_pipeline);
    ctx->vk.CmdBindDescriptorSets(image->sample_cmd, VK_PIPELINE_BIND_POINT_COMPUTE, image->sample_pipeline_layout, 0, 1, &image->sample_set, 0, NULL);
    ctx->vk.CmdDispatch(image->sample_cmd, group_x, 1, 1);
    if (!tvdb_vk_ok(ctx->vk.EndCommandBuffer(image->sample_cmd), err, "vkEndCommandBuffer(persistent sample)")) return err ? err->status : TVDB_ERROR_IO;
    image->sample_cmd_recorded = 1;
    image->sample_group_x = group_x;
  }
  VkSubmitInfo si;
  memset(&si, 0, sizeof(si));
  si.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
  si.commandBufferCount = 1;
  si.pCommandBuffers = &image->sample_cmd;
  if (!tvdb_vk_ok(ctx->vk.QueueSubmit(ctx->queue, 1, &si, image->sample_fence), err, "vkQueueSubmit(persistent sample)")) return err ? err->status : TVDB_ERROR_IO;
  image->sample_in_flight = 1;
  if (wait) {
    if (!tvdb_vk_ok(ctx->vk.WaitForFences(ctx->device, 1, &image->sample_fence, VK_TRUE, UINT64_MAX), err, "vkWaitForFences(persistent sample)")) return err ? err->status : TVDB_ERROR_IO;
    image->sample_in_flight = 0;
  }
  return TVDB_OK;
}

static void tvdb_vk_destroy_sample_batch_dispatch(tvdb_gpu_vulkan_sample_batch_t* batch) {
  if (!batch || !batch->ctx) return;
  tvdb_gpu_context_t* ctx = batch->ctx;
  /* Same rule as the single-image path: a submit without a matching wait must not
   * have its fence, command pool or buffers destroyed underneath it. */
  if (batch->in_flight && batch->fence && ctx->vk.WaitForFences) {
    ctx->vk.WaitForFences(ctx->device, 1, &batch->fence, VK_TRUE, UINT64_MAX);
    batch->in_flight = 0;
  }
  if (batch->fence) ctx->vk.DestroyFence(ctx->device, batch->fence, NULL);
  if (batch->command_pool) ctx->vk.DestroyCommandPool(ctx->device, batch->command_pool, NULL);
  if (batch->descriptor_pool) ctx->vk.DestroyDescriptorPool(ctx->device, batch->descriptor_pool, NULL);
  batch->fence = VK_NULL_HANDLE;
  batch->command_pool = VK_NULL_HANDLE;
  batch->cmd = NULL;
  batch->descriptor_pool = VK_NULL_HANDLE;
  batch->descriptor_set = VK_NULL_HANDLE;
  batch->bound_image = NULL;
  batch->group_x = 0;
  batch->cmd_recorded = 0;
  batch->in_flight = 0;
}

static tvdb_status_t tvdb_vk_sample_batch_ensure_dispatch(tvdb_gpu_vulkan_sparse_image3d_t* image,
                                                          tvdb_gpu_vulkan_sample_batch_t* batch,
                                                          tvdb_error_t* err) {
  tvdb_gpu_context_t* ctx = batch->ctx;
  if (batch->descriptor_set && batch->cmd && batch->fence) return TVDB_OK;
  tvdb_vk_destroy_sample_batch_dispatch(batch);
  VkDescriptorPoolSize pool_sizes[3];
  memset(pool_sizes, 0, sizeof(pool_sizes));
  pool_sizes[0].type = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; pool_sizes[0].descriptorCount = 2;
  pool_sizes[1].type = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER; pool_sizes[1].descriptorCount = 1;
  pool_sizes[2].type = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER; pool_sizes[2].descriptorCount = 1;
  VkDescriptorPoolCreateInfo dpci;
  memset(&dpci, 0, sizeof(dpci));
  dpci.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO;
  dpci.maxSets = 1;
  dpci.poolSizeCount = 3;
  dpci.pPoolSizes = pool_sizes;
  if (!tvdb_vk_ok(ctx->vk.CreateDescriptorPool(ctx->device, &dpci, NULL, &batch->descriptor_pool), err, "vkCreateDescriptorPool(batch sample)")) goto fail;
  VkDescriptorSetAllocateInfo dsai;
  memset(&dsai, 0, sizeof(dsai));
  dsai.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
  dsai.descriptorPool = batch->descriptor_pool;
  dsai.descriptorSetCount = 1;
  dsai.pSetLayouts = &image->sample_layout;
  if (!tvdb_vk_ok(ctx->vk.AllocateDescriptorSets(ctx->device, &dsai, &batch->descriptor_set), err, "vkAllocateDescriptorSets(batch sample)")) goto fail;

  VkCommandPoolCreateInfo cpci;
  memset(&cpci, 0, sizeof(cpci));
  cpci.sType = VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO;
  cpci.flags = VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT;
  cpci.queueFamilyIndex = ctx->queue_family;
  if (!tvdb_vk_ok(ctx->vk.CreateCommandPool(ctx->device, &cpci, NULL, &batch->command_pool), err, "vkCreateCommandPool(batch sample)")) goto fail;
  VkCommandBufferAllocateInfo cbai;
  memset(&cbai, 0, sizeof(cbai));
  cbai.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
  cbai.commandPool = batch->command_pool;
  cbai.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
  cbai.commandBufferCount = 1;
  if (!tvdb_vk_ok(ctx->vk.AllocateCommandBuffers(ctx->device, &cbai, &batch->cmd), err, "vkAllocateCommandBuffers(batch sample)")) goto fail;
  VkFenceCreateInfo fci;
  memset(&fci, 0, sizeof(fci));
  fci.sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO;
  if (!tvdb_vk_ok(ctx->vk.CreateFence(ctx->device, &fci, NULL, &batch->fence), err, "vkCreateFence(batch sample)")) goto fail;
  return TVDB_OK;
fail:
  tvdb_vk_destroy_sample_batch_dispatch(batch);
  return err ? err->status : TVDB_ERROR_IO;
}

static void tvdb_vk_sample_batch_update_descriptors(tvdb_gpu_vulkan_sparse_image3d_t* image,
                                                    tvdb_gpu_vulkan_sample_batch_t* batch) {
  tvdb_gpu_context_t* ctx = batch->ctx;
  VkDescriptorImageInfo image_info;
  VkDescriptorBufferInfo buffer_infos[3];
  VkWriteDescriptorSet writes[4];
  memset(&image_info, 0, sizeof(image_info));
  memset(buffer_infos, 0, sizeof(buffer_infos));
  memset(writes, 0, sizeof(writes));
  image_info.sampler = image->image.sampler;
  image_info.imageView = image->image.view;
  image_info.imageLayout = VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL;
  buffer_infos[0].buffer = batch->points.buffer; buffer_infos[0].range = batch->points.size;
  buffer_infos[1].buffer = batch->output.buffer; buffer_infos[1].range = batch->output.size;
  buffer_infos[2].buffer = batch->params.buffer; buffer_infos[2].range = batch->params.size;
  writes[0].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET; writes[0].dstSet = batch->descriptor_set; writes[0].dstBinding = 0; writes[0].descriptorCount = 1; writes[0].descriptorType = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER; writes[0].pImageInfo = &image_info;
  writes[1].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET; writes[1].dstSet = batch->descriptor_set; writes[1].dstBinding = 1; writes[1].descriptorCount = 1; writes[1].descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; writes[1].pBufferInfo = &buffer_infos[0];
  writes[2].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET; writes[2].dstSet = batch->descriptor_set; writes[2].dstBinding = 2; writes[2].descriptorCount = 1; writes[2].descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; writes[2].pBufferInfo = &buffer_infos[1];
  writes[3].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET; writes[3].dstSet = batch->descriptor_set; writes[3].dstBinding = 3; writes[3].descriptorCount = 1; writes[3].descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER; writes[3].pBufferInfo = &buffer_infos[2];
  ctx->vk.UpdateDescriptorSets(ctx->device, 4, writes, 0, NULL);
}

static tvdb_status_t tvdb_vk_sample_batch_submit(tvdb_gpu_vulkan_sparse_image3d_t* image,
                                                 tvdb_gpu_vulkan_sample_batch_t* batch,
                                                 int wait,
                                                 tvdb_error_t* err) {
  tvdb_gpu_context_t* ctx = batch->ctx;
  if (batch->in_flight) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "sample batch dispatch already in flight");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_status_t st = tvdb_vk_sample_batch_ensure_dispatch(image, batch, err);
  if (st != TVDB_OK) return st;
  uint32_t group_x = (uint32_t)((batch->count + 127u) / 128u);
  if (batch->bound_image != image) {
    tvdb_vk_sample_batch_update_descriptors(image, batch);
    batch->cmd_recorded = 0;
    batch->bound_image = image;
  }
  if (!tvdb_vk_ok(ctx->vk.ResetFences(ctx->device, 1, &batch->fence), err, "vkResetFences(batch sample)")) return err ? err->status : TVDB_ERROR_IO;
  if (!batch->cmd_recorded || batch->group_x != group_x) {
    if (batch->cmd_recorded) {
      if (!tvdb_vk_ok(ctx->vk.ResetCommandBuffer(batch->cmd, 0), err, "vkResetCommandBuffer(batch sample)")) return err ? err->status : TVDB_ERROR_IO;
    }
    VkCommandBufferBeginInfo begin;
    memset(&begin, 0, sizeof(begin));
    begin.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;
    if (!tvdb_vk_ok(ctx->vk.BeginCommandBuffer(batch->cmd, &begin), err, "vkBeginCommandBuffer(batch sample)")) return err ? err->status : TVDB_ERROR_IO;
    ctx->vk.CmdBindPipeline(batch->cmd, VK_PIPELINE_BIND_POINT_COMPUTE, image->sample_pipeline);
    ctx->vk.CmdBindDescriptorSets(batch->cmd, VK_PIPELINE_BIND_POINT_COMPUTE, image->sample_pipeline_layout, 0, 1, &batch->descriptor_set, 0, NULL);
    ctx->vk.CmdDispatch(batch->cmd, group_x, 1, 1);
    if (!tvdb_vk_ok(ctx->vk.EndCommandBuffer(batch->cmd), err, "vkEndCommandBuffer(batch sample)")) return err ? err->status : TVDB_ERROR_IO;
    batch->cmd_recorded = 1;
    batch->group_x = group_x;
  }
  VkSubmitInfo si;
  memset(&si, 0, sizeof(si));
  si.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
  si.commandBufferCount = 1;
  si.pCommandBuffers = &batch->cmd;
  if (!tvdb_vk_ok(ctx->vk.QueueSubmit(ctx->queue, 1, &si, batch->fence), err, "vkQueueSubmit(batch sample)")) return err ? err->status : TVDB_ERROR_IO;
  batch->in_flight = 1;
  if (wait) {
    if (!tvdb_vk_ok(ctx->vk.WaitForFences(ctx->device, 1, &batch->fence, VK_TRUE, UINT64_MAX), err, "vkWaitForFences(batch sample)")) return err ? err->status : TVDB_ERROR_IO;
    batch->in_flight = 0;
  }
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_sample_trilinear_dense_batch_vulkan_image3d(tvdb_gpu_context_t* ctx,
                                                                   const tvdb_dense_grid* grid,
                                                                   const tvdb_vec3f* pts,
                                                                   size_t n,
                                                                   float* out_values,
                                                                   tvdb_error_t* err) {
  return tvdb_vk_sample_dense_image3d(ctx, grid, pts, n, out_values, 0, err);
}

tvdb_status_t tvdb_gpu_sample_trilinear_dense_batch_vulkan_sparse_image3d(tvdb_gpu_context_t* ctx,
                                                                          const tvdb_dense_grid* grid,
                                                                          const tvdb_vec3f* pts,
                                                                          size_t n,
                                                                          float* out_values,
                                                                          tvdb_error_t* err) {
  return tvdb_vk_sample_dense_image3d(ctx, grid, pts, n, out_values, 1, err);
}

tvdb_status_t tvdb_gpu_sample_trilinear_sparse_vulkan_sparse_image3d(tvdb_gpu_context_t* ctx,
                                                                     const tvdb_sparse_grid* sparse,
                                                                     float background,
                                                                     int nx, int ny, int nz,
                                                                     const tvdb_vec3f* pts,
                                                                     size_t n,
                                                                     float* out_values,
                                                                     tvdb_error_t* err) {
  if (!ctx || ctx->backend != TVDB_GPU_BACKEND_VULKAN) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "Vulkan sparse image3D sampling requires a Vulkan context");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  if (!sparse || !sparse->coords || !sparse->values || nx <= 0 || ny <= 0 || nz <= 0 || !pts || !out_values) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid sparse image3D sample arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_vk_image3d image;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_sparse_image3d_from_sparse_grid(ctx, sparse, background, nx, ny, nz, &image, err)) != TVDB_OK) return st;
  st = tvdb_vk_sample_existing_image3d(ctx, &image, sparse->ox, sparse->oy, sparse->oz,
                                       sparse->voxel_size, pts, n, out_values, err);
  tvdb_vk_destroy_image3d(ctx, &image);
  return st;
}

tvdb_status_t tvdb_gpu_vulkan_sparse_image3d_create(tvdb_gpu_context_t* ctx,
                                                    const tvdb_sparse_grid* sparse,
                                                    float background,
                                                    int nx, int ny, int nz,
                                                    tvdb_gpu_vulkan_sparse_image3d_t** out,
                                                    tvdb_error_t* err) {
  if (!out) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "NULL output sparse image");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  *out = NULL;
  if (!ctx || ctx->backend != TVDB_GPU_BACKEND_VULKAN) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "persistent sparse image requires a Vulkan context");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  if (!sparse) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "NULL sparse grid");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_gpu_vulkan_sparse_image3d_t* img =
      (tvdb_gpu_vulkan_sparse_image3d_t*)calloc(1, sizeof(*img));
  if (!img) {
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  img->ctx = ctx;
  img->ox = sparse->ox; img->oy = sparse->oy; img->oz = sparse->oz;
  img->voxel_size = sparse->voxel_size;
  img->nx = nx; img->ny = ny; img->nz = nz;
  tvdb_status_t st = tvdb_vk_create_sparse_image3d_from_sparse_grid(ctx, sparse, background,
                                                                    nx, ny, nz, &img->image, err);
  if (st != TVDB_OK) {
    free(img);
    return st;
  }
  st = tvdb_vk_create_sparse_image3d_dispatch(img, err);
  if (st != TVDB_OK) {
    tvdb_vk_destroy_image3d(ctx, &img->image);
    free(img);
    return st;
  }
  *out = img;
  return TVDB_OK;
}

void tvdb_gpu_vulkan_sparse_image3d_destroy(tvdb_gpu_vulkan_sparse_image3d_t* image) {
  if (!image) return;
  tvdb_vk_destroy_sparse_image3d_dispatch(image);
  tvdb_vk_destroy_image3d(image->ctx, &image->image);
  free(image);
}

tvdb_status_t tvdb_gpu_vulkan_sparse_image3d_sample(tvdb_gpu_vulkan_sparse_image3d_t* image,
                                                    const tvdb_vec3f* pts,
                                                    size_t n,
                                                    float* out_values,
                                                    tvdb_error_t* err) {
  if (!image) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "NULL persistent sparse image");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_gpu_context_t* ctx = image->ctx;
  if (!pts || !out_values) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid persistent sparse image sample buffers");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (n == 0) return TVDB_OK;
  tvdb_status_t st = tvdb_vk_sparse_image3d_ensure_sample_workspace(image, n, err);
  if (st != TVDB_OK) return st;
  float* p4 = (float*)image->sample_points.mapped;
  for (size_t i = 0; i < n; ++i) {
    p4[4*i+0] = pts[i].x; p4[4*i+1] = pts[i].y; p4[4*i+2] = pts[i].z; p4[4*i+3] = 0.0f;
  }
  struct { int32_t dim[4]; float ov[4]; uint32_t count; uint32_t pad[3]; } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = image->nx; par.dim[1] = image->ny; par.dim[2] = image->nz;
  par.ov[0] = image->ox; par.ov[1] = image->oy; par.ov[2] = image->oz; par.ov[3] = image->voxel_size;
  par.count = (uint32_t)n;
  memcpy(image->sample_params.mapped, &par, sizeof(par));

  st = tvdb_vk_sparse_image3d_submit_sample(image, (uint32_t)((n + 127u) / 128u), 0, 1, err);
  if (st != TVDB_OK) return st;
  memcpy(out_values, image->sample_output.mapped, n * sizeof(float));
  return TVDB_OK;
}

static void tvdb_vk_fill_point_buffer(tvdb_vk_buffer* buf, const tvdb_vec3f* pts, size_t n) {
  float* p4 = (float*)buf->mapped;
  for (size_t i = 0; i < n; ++i) {
    p4[4*i+0] = pts[i].x;
    p4[4*i+1] = pts[i].y;
    p4[4*i+2] = pts[i].z;
    p4[4*i+3] = 0.0f;
  }
}

tvdb_status_t tvdb_gpu_vulkan_sample_batch_create(tvdb_gpu_context_t* ctx,
                                                  const tvdb_vec3f* pts,
                                                  size_t n,
                                                  tvdb_gpu_vulkan_sample_batch_t** out,
                                                  tvdb_error_t* err) {
  if (!out) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "NULL output sample batch");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  *out = NULL;
  if (!ctx || ctx->backend != TVDB_GPU_BACKEND_VULKAN || !pts) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid Vulkan sample batch arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_gpu_vulkan_sample_batch_t* batch =
      (tvdb_gpu_vulkan_sample_batch_t*)calloc(1, sizeof(*batch));
  if (!batch) {
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  batch->ctx = ctx;
  tvdb_status_t st = tvdb_gpu_vulkan_sample_batch_update_points(batch, pts, n, err);
  if (st != TVDB_OK) {
    tvdb_gpu_vulkan_sample_batch_destroy(batch);
    return st;
  }
  *out = batch;
  return TVDB_OK;
}

void tvdb_gpu_vulkan_sample_batch_destroy(tvdb_gpu_vulkan_sample_batch_t* batch) {
  if (!batch) return;
  tvdb_gpu_context_t* ctx = batch->ctx;
  tvdb_vk_destroy_sample_batch_dispatch(batch);
  tvdb_vk_destroy_buffer(ctx, &batch->params);
  tvdb_vk_destroy_buffer(ctx, &batch->output);
  tvdb_vk_destroy_buffer(ctx, &batch->points);
  free(batch);
}

tvdb_status_t tvdb_gpu_vulkan_sample_batch_update_points(tvdb_gpu_vulkan_sample_batch_t* batch,
                                                         const tvdb_vec3f* pts,
                                                         size_t n,
                                                         tvdb_error_t* err) {
  if (!batch || !batch->ctx || !pts) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid sample batch update arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_gpu_context_t* ctx = batch->ctx;
  size_t cap = n ? n : 1;
  if (batch->capacity < cap) {
    tvdb_vk_destroy_sample_batch_dispatch(batch);
    tvdb_vk_destroy_buffer(ctx, &batch->params);
    tvdb_vk_destroy_buffer(ctx, &batch->output);
    tvdb_vk_destroy_buffer(ctx, &batch->points);
    batch->capacity = 0;
    tvdb_status_t st;
    if ((st = tvdb_vk_create_buffer(ctx, cap * 4u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &batch->points, err)) != TVDB_OK) return st;
    if ((st = tvdb_vk_create_buffer(ctx, cap * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &batch->output, err)) != TVDB_OK) return st;
    if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &batch->params, err)) != TVDB_OK) return st;
    batch->capacity = cap;
  }
  batch->count = n;
  tvdb_vk_fill_point_buffer(&batch->points, pts, n);
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_vulkan_sparse_image3d_sample_batch(tvdb_gpu_vulkan_sparse_image3d_t* image,
                                                          tvdb_gpu_vulkan_sample_batch_t* batch,
                                                          tvdb_error_t* err) {
  if (!image || !batch || image->ctx != batch->ctx) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid sparse image sample batch arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (batch->count == 0) return TVDB_OK;
  struct { int32_t dim[4]; float ov[4]; uint32_t count; uint32_t pad[3]; } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = image->nx; par.dim[1] = image->ny; par.dim[2] = image->nz;
  par.ov[0] = image->ox; par.ov[1] = image->oy; par.ov[2] = image->oz; par.ov[3] = image->voxel_size;
  par.count = (uint32_t)batch->count;
  memcpy(batch->params.mapped, &par, sizeof(par));
  return tvdb_vk_sample_batch_submit(image, batch, 1, err);
}

tvdb_status_t tvdb_gpu_vulkan_sparse_image3d_sample_batch_submit(tvdb_gpu_vulkan_sparse_image3d_t* image,
                                                                 tvdb_gpu_vulkan_sample_batch_t* batch,
                                                                 tvdb_error_t* err) {
  if (!image || !batch || image->ctx != batch->ctx) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid sparse image async sample batch arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (batch->count == 0) return TVDB_OK;
  struct { int32_t dim[4]; float ov[4]; uint32_t count; uint32_t pad[3]; } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = image->nx; par.dim[1] = image->ny; par.dim[2] = image->nz;
  par.ov[0] = image->ox; par.ov[1] = image->oy; par.ov[2] = image->oz; par.ov[3] = image->voxel_size;
  par.count = (uint32_t)batch->count;
  memcpy(batch->params.mapped, &par, sizeof(par));
  return tvdb_vk_sample_batch_submit(image, batch, 0, err);
}

tvdb_status_t tvdb_gpu_vulkan_sample_batch_poll(tvdb_gpu_vulkan_sample_batch_t* batch,
                                                int* done,
                                                tvdb_error_t* err) {
  if (!batch || !done) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid sample batch poll arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (!batch->in_flight) {
    *done = 1;
    return TVDB_OK;
  }
  VkResult r = batch->ctx->vk.GetFenceStatus(batch->ctx->device, batch->fence);
  if (r == VK_SUCCESS) {
    batch->in_flight = 0;
    *done = 1;
    return TVDB_OK;
  }
  if (r == VK_NOT_READY) {
    *done = 0;
    return TVDB_OK;
  }
  tvdb_vk_ok(r, err, "vkGetFenceStatus(batch sample)");
  return err ? err->status : TVDB_ERROR_IO;
}

tvdb_status_t tvdb_gpu_vulkan_sample_batch_wait(tvdb_gpu_vulkan_sample_batch_t* batch,
                                                tvdb_error_t* err) {
  if (!batch) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "NULL sample batch wait");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (!batch->in_flight) return TVDB_OK;
  if (!tvdb_vk_ok(batch->ctx->vk.WaitForFences(batch->ctx->device, 1, &batch->fence, VK_TRUE, UINT64_MAX), err, "vkWaitForFences(batch async sample)")) return err ? err->status : TVDB_ERROR_IO;
  batch->in_flight = 0;
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_vulkan_sample_batch_readback(tvdb_gpu_vulkan_sample_batch_t* batch,
                                                    float* out_values,
                                                    size_t n,
                                                    tvdb_error_t* err) {
  if (!batch || !out_values || n > batch->count) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid sample batch readback arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  memcpy(out_values, batch->output.mapped, n * sizeof(float));
  return TVDB_OK;
}

// Near-dense Vulkan conv: dense bbox-local index grid for O(1) tap lookups.
static tvdb_status_t tvdb_vk_sparse_conv_dense(tvdb_gpu_context_t* ctx, const tvdb_sparse_grid* in,
                                               const float* kernel, int kx, int ky, int kz,
                                               float pad_value, const int32_t bbmin[3], const int32_t dims[3],
                                               size_t volume, tvdb_sparse_grid* out, tvdb_error_t* err) {
  tvdb_vk_buffer bc, bv, bk, bo, bidx, bus, buc;
  tvdb_status_t st;
  size_t kvol = (size_t)kx * (size_t)ky * (size_t)kz;
  if ((st = tvdb_vk_create_buffer(ctx, in->count * 4u * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bc, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, in->count * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bv, err)) != TVDB_OK) goto dd_c;
  if ((st = tvdb_vk_create_buffer(ctx, kvol * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bk, err)) != TVDB_OK) goto dd_v;
  if ((st = tvdb_vk_create_buffer(ctx, in->count * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto dd_k;
  if ((st = tvdb_vk_create_buffer(ctx, volume * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bidx, err)) != TVDB_OK) goto dd_o;
  if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bus, err)) != TVDB_OK) goto dd_idx;
  if ((st = tvdb_vk_create_buffer(ctx, 80, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &buc, err)) != TVDB_OK) goto dd_us;
  {
    int32_t* c4 = (int32_t*)bc.mapped;
    for (size_t i = 0; i < in->count; ++i) {
      c4[4*i+0] = in->coords[i].x; c4[4*i+1] = in->coords[i].y; c4[4*i+2] = in->coords[i].z; c4[4*i+3] = 0;
      out->coords[i] = in->coords[i];
    }
  }
  memcpy(bv.mapped, in->values, in->count * sizeof(float));
  memcpy(bk.mapped, kernel, kvol * sizeof(float));
  memset(bidx.mapped, 0xFF, volume * sizeof(int32_t));  // all -1
  struct { int32_t bbmin[4]; int32_t dims[4]; uint32_t count; uint32_t pad[3]; } spar;
  memset(&spar, 0, sizeof(spar));
  spar.bbmin[0]=bbmin[0]; spar.bbmin[1]=bbmin[1]; spar.bbmin[2]=bbmin[2];
  spar.dims[0]=dims[0]; spar.dims[1]=dims[1]; spar.dims[2]=dims[2];
  spar.count=(uint32_t)in->count;
  memcpy(bus.mapped, &spar, sizeof(spar));
  struct { int32_t bbmin[4]; int32_t dims[4]; int32_t kdim[4]; float misc[4]; uint32_t count; uint32_t pad[3]; } cpar;
  memset(&cpar, 0, sizeof(cpar));
  cpar.bbmin[0]=bbmin[0]; cpar.bbmin[1]=bbmin[1]; cpar.bbmin[2]=bbmin[2];
  cpar.dims[0]=dims[0]; cpar.dims[1]=dims[1]; cpar.dims[2]=dims[2];
  cpar.kdim[0]=kx; cpar.kdim[1]=ky; cpar.kdim[2]=kz; cpar.misc[0]=pad_value; cpar.count=(uint32_t)in->count;
  memcpy(buc.mapped, &cpar, sizeof(cpar));
  {
    tvdb_vk_dispatch_desc ds;
    memset(&ds, 0, sizeof(ds));
    ds.spv = kTvdbGpuSparseIndexScatterSpv; ds.spv_len = kTvdbGpuSparseIndexScatterSpv_len; ds.descriptor_count = 3;
    ds.buffers[0]=&bc; ds.buffers[1]=&bidx; ds.buffers[2]=&bus;
    ds.descriptor_types[0]=ds.descriptor_types[1]=VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    ds.descriptor_types[2]=VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    ds.group_x = (uint32_t)((in->count + 127u) / 128u);
    /* Deferred: the scatter writes bidx and the conv reads it, so the two are
     * dependent. Submitting the first one without waiting cost a full blocking
     * fence here and another for the second. Queueing it and draining once at the
     * end is the pattern erode/dilate and the transpose conv already use, and
     * the uniform contents are constant across both dispatches. */
    ds.defer_wait = TVDB_VK_DEFERRED_SUBMIT;
    st = tvdb_vk_dispatch(ctx, &ds, err);
  }
  if (st == TVDB_OK) {
    tvdb_vk_dispatch_desc dc;
    memset(&dc, 0, sizeof(dc));
    dc.spv = kTvdbGpuSparseConvDenseSpv; dc.spv_len = kTvdbGpuSparseConvDenseSpv_len; dc.descriptor_count = 6;
    dc.buffers[0]=&bc; dc.buffers[1]=&bv; dc.buffers[2]=&bk; dc.buffers[3]=&bo; dc.buffers[4]=&bidx; dc.buffers[5]=&buc;
    for (int i = 0; i < 5; ++i) dc.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    dc.descriptor_types[5] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    dc.group_x = (uint32_t)((in->count + 127u) / 128u);
    st = tvdb_vk_dispatch(ctx, &dc, err);
  }
  if (st == TVDB_OK) st = tvdb_vk_flush(ctx, err);
  if (st == TVDB_OK) { memcpy(out->values, bo.mapped, in->count * sizeof(float)); out->count = in->count; }
  tvdb_vk_destroy_buffer(ctx, &buc);
dd_us: tvdb_vk_destroy_buffer(ctx, &bus);
dd_idx: tvdb_vk_destroy_buffer(ctx, &bidx);
dd_o: tvdb_vk_destroy_buffer(ctx, &bo);
dd_k: tvdb_vk_destroy_buffer(ctx, &bk);
dd_v: tvdb_vk_destroy_buffer(ctx, &bv);
dd_c: tvdb_vk_destroy_buffer(ctx, &bc);
  return st;
}

// Active-set ijk bbox; returns the volume (or 0 on overflow/degenerate).
static size_t tvdb_sparse_bbox(const tvdb_sparse_grid* in, int32_t bbmin[3], int32_t dims[3]) {
  bbmin[0]=bbmin[1]=bbmin[2]=0; dims[0]=dims[1]=dims[2]=1;
  if (in->count == 0) return 0;
  int32_t mn[3], mx[3];
  mn[0]=mx[0]=in->coords[0].x; mn[1]=mx[1]=in->coords[0].y; mn[2]=mx[2]=in->coords[0].z;
  for (size_t i = 1; i < in->count; ++i) {
    int32_t v[3] = { in->coords[i].x, in->coords[i].y, in->coords[i].z };
    for (int a = 0; a < 3; ++a) { if (v[a] < mn[a]) mn[a] = v[a]; if (v[a] > mx[a]) mx[a] = v[a]; }
  }
  long long vol = 1;
  for (int a = 0; a < 3; ++a) {
    bbmin[a] = mn[a];
    long long d = (long long)mx[a] - mn[a] + 1;
    if (d <= 0 || d > 400000000 || vol > 400000000 / d) return 0;
    dims[a] = (int32_t)d;
    vol *= d;
    if (vol <= 0 || vol > (long long)400000000) return 0;  // too large for dense index grid
  }
  return (size_t)vol;
}

static tvdb_status_t tvdb_gpu_sparse_conv3d_impl(tvdb_gpu_context_t* ctx, const tvdb_sparse_grid* in,
                                     const float* kernel, int kx, int ky, int kz,
                                     float pad_value, tvdb_sparse_grid* out,
                                     tvdb_error_t* err) {
  if (!ctx || !in || !kernel || !out || kx <= 0 || ky <= 0 || kz <= 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid sparse conv arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  out->count = 0; out->voxel_size = in->voxel_size; out->ox = in->ox; out->oy = in->oy; out->oz = in->oz;
  if (!tvdb_sparse_grid_reserve(out, in->count)) {
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  if (in->count == 0) return TVDB_OK;
  // Near-dense fast path: when the active set's bbox fits a dense index grid,
  // O(1) tap lookups beat the brute-force O(active) scan. Falls back otherwise.
  int32_t bbmin[3], dims[3];
  size_t volume = tvdb_sparse_bbox(in, bbmin, dims);
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    if (volume && ctx->cuda.cuMemsetD32)
      return tvdb_cuda_sparse_conv_dense(ctx, in, kernel, kx, ky, kz, pad_value, bbmin, dims, volume, out, err);
    /* Without a usable dense index grid the fallback would be the O(count^2 *
     * kx*ky*kz) scan, so use the same host-built map as Vulkan rather than
     * leaving CUDA on the brute-force path. */
    if (!TVDB_INDEX_MAP_FORCE_LINEAR && in->count >= TVDB_INDEX_MAP_MIN_ACTIVE)
      return tvdb_cuda_sparse_conv_map(ctx, in, kernel, kx, ky, kz, pad_value, out, err);
    return tvdb_cuda_sparse_conv(ctx, in, kernel, kx, ky, kz, pad_value, out, err);
  }
  if (volume) {
    return tvdb_vk_sparse_conv_dense(ctx, in, kernel, kx, ky, kz, pad_value, bbmin, dims, volume, out, err);
  }
  /* Brute force is O(count^2 * kx*ky*kz) because every tap scans the active
   * set. Above the same crossover measured for ijk_to_index, probe a host-built
   * map instead: O(count * kx*ky*kz). */
  if (!TVDB_INDEX_MAP_FORCE_LINEAR && in->count >= TVDB_INDEX_MAP_MIN_ACTIVE) {
    int32_t* map4 = NULL; uint32_t cap = 0;
    tvdb_status_t st = tvdb_index_map_build4(in, &map4, &cap, err);
    if (st != TVDB_OK) return st;

    tvdb_vk_buffer bmap, bkc, bv2, bo2, bp2, bmp;
    memset(&bmap, 0, sizeof(bmap)); memset(&bkc, 0, sizeof(bkc)); memset(&bv2, 0, sizeof(bv2));
    memset(&bo2, 0, sizeof(bo2)); memset(&bp2, 0, sizeof(bp2)); memset(&bmp, 0, sizeof(bmp));
    if ((st = tvdb_vk_create_buffer(ctx, (size_t)cap * 4u * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bmap, err)) != TVDB_OK) goto sc_freemap2;
    if ((st = tvdb_vk_create_buffer(ctx, in->count * 4u * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bkc, err)) != TVDB_OK) goto sc_done_map;
    if ((st = tvdb_vk_create_buffer(ctx, in->count * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bv2, err)) != TVDB_OK) goto sc_done_c;
    if ((st = tvdb_vk_create_buffer(ctx, (size_t)kx*(size_t)ky*(size_t)kz * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo2, err)) != TVDB_OK) goto sc_done_v;
    if ((st = tvdb_vk_create_buffer(ctx, in->count * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bp2, err)) != TVDB_OK) goto sc_done_kk;
    if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bmp, err)) != TVDB_OK) goto sc_done_o;
    memcpy(bmap.mapped, map4, (size_t)cap * 4u * sizeof(int32_t));
    free(map4); map4 = NULL;
    { int32_t* c4 = (int32_t*)bkc.mapped;
      for (size_t i = 0; i < in->count; ++i) {
        c4[4*i+0] = in->coords[i].x; c4[4*i+1] = in->coords[i].y; c4[4*i+2] = in->coords[i].z; c4[4*i+3] = 0;
        out->coords[i] = in->coords[i];
      } }
    memcpy(bv2.mapped, in->values, in->count * sizeof(float));
    memcpy(bo2.mapped, kernel, (size_t)kx*(size_t)ky*(size_t)kz * sizeof(float));
    /* std140 alignment: the shader declares an ivec4 kdim, which must start at
     * offset 16. A plain int32_t[4] would land at offset 12 and the shader
     * would read a garbage kernel size. */
    struct { uint32_t count; uint32_t cap; uint32_t mask; uint32_t align_pad; int32_t kdim[4]; float pad_value; uint32_t pad0[3]; } par;
    memset(&par, 0, sizeof(par));
    par.count = (uint32_t)in->count; par.cap = cap; par.mask = cap - 1u;
    par.kdim[0] = kx; par.kdim[1] = ky; par.kdim[2] = kz; par.pad_value = pad_value;
    memcpy(bmp.mapped, &par, sizeof(par));
    tvdb_vk_dispatch_desc d2;
    memset(&d2, 0, sizeof(d2));
    d2.spv = kTvdbGpuSparseConvMapSpv; d2.spv_len = kTvdbGpuSparseConvMapSpv_len; d2.descriptor_count = 6;
    d2.buffers[0] = &bmap; d2.buffers[1] = &bkc; d2.buffers[2] = &bv2;
    d2.buffers[3] = &bo2; d2.buffers[4] = &bp2; d2.buffers[5] = &bmp;
    for (int i = 0; i < 5; ++i) d2.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    d2.descriptor_types[5] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    d2.group_x = (uint32_t)((in->count + 127u) / 128u);
    st = tvdb_vk_dispatch(ctx, &d2, err);
    if (st == TVDB_OK) {
      memcpy(out->values, bp2.mapped, in->count * sizeof(float));
      out->count = in->count;
    }
    tvdb_vk_destroy_buffer(ctx, &bmp);
  sc_done_o: tvdb_vk_destroy_buffer(ctx, &bp2);
  sc_done_kk: tvdb_vk_destroy_buffer(ctx, &bo2);
  sc_done_v: tvdb_vk_destroy_buffer(ctx, &bv2);
  sc_done_c: tvdb_vk_destroy_buffer(ctx, &bkc);
  sc_done_map: tvdb_vk_destroy_buffer(ctx, &bmap);
  sc_freemap2:
    free(map4);
    return st;
  }

  tvdb_vk_buffer bc, bv, bk, bo, bp;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, in->count * 4u * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bc, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, in->count * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bv, err)) != TVDB_OK) goto done_c;
  if ((st = tvdb_vk_create_buffer(ctx, (size_t)kx * (size_t)ky * (size_t)kz * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bk, err)) != TVDB_OK) goto done_v;
  if ((st = tvdb_vk_create_buffer(ctx, in->count * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto done_k;
  if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bp, err)) != TVDB_OK) goto done_o;
  int32_t* c4 = (int32_t*)bc.mapped;
  for (size_t i = 0; i < in->count; ++i) {
    c4[4*i+0] = in->coords[i].x; c4[4*i+1] = in->coords[i].y; c4[4*i+2] = in->coords[i].z; c4[4*i+3] = 0;
    out->coords[i] = in->coords[i];
  }
  memcpy(bv.mapped, in->values, in->count * sizeof(float));
  memcpy(bk.mapped, kernel, (size_t)kx * (size_t)ky * (size_t)kz * sizeof(float));
  struct { uint32_t count; uint32_t pad0[3]; int32_t kdim[4]; float pad_value; uint32_t pad1[3]; } par;
  memset(&par, 0, sizeof(par));
  par.count = (uint32_t)in->count; par.kdim[0] = kx; par.kdim[1] = ky; par.kdim[2] = kz; par.pad_value = pad_value;
  memcpy(bp.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuSparseConvSpv; d.spv_len = kTvdbGpuSparseConvSpv_len; d.descriptor_count = 5;
  d.buffers[0] = &bc; d.buffers[1] = &bv; d.buffers[2] = &bk; d.buffers[3] = &bo; d.buffers[4] = &bp;
  for (int i = 0; i < 4; ++i) d.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((in->count + 127u) / 128u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) {
    memcpy(out->values, bo.mapped, in->count * sizeof(float));
    out->count = in->count;
  }
  tvdb_vk_destroy_buffer(ctx, &bp);
done_o: tvdb_vk_destroy_buffer(ctx, &bo);
done_k: tvdb_vk_destroy_buffer(ctx, &bk);
done_v: tvdb_vk_destroy_buffer(ctx, &bv);
done_c: tvdb_vk_destroy_buffer(ctx, &bc);
  return st;
}

// ---- spatial queries --------------------------------------------------------
// Brute-force linear scan of the active coord set (one thread per query /
// active voxel), mirroring tinyvdb_grid_index.c. Indices are int32 on device;
// public wrappers widen/narrow on readback.

// Pack int32 xyz triples into ivec4 (x,y,z,0) for std430 ivec4 buffers.
static void tvdb_pack_int4(int32_t* dst, const int32_t* src, size_t n) {
  for (size_t i = 0; i < n; ++i) {
    dst[4*i+0] = src[3*i+0]; dst[4*i+1] = src[3*i+1]; dst[4*i+2] = src[3*i+2]; dst[4*i+3] = 0;
  }
}

// index kernel: out[i] = first-seen index of query[i] in active, or -1.
/* Above the same crossover as Vulkan, probe the host-built map instead of
 * scanning the active set. O(nq) instead of O(nq*na). */
static tvdb_status_t tvdb_cuda_index_query_map(tvdb_gpu_context_t* ctx,
    const int32_t* active, size_t na, const int32_t* query, size_t nq,
    int32_t* out, tvdb_error_t* err) {
  int32_t* keys = NULL; int32_t* vals = NULL; uint32_t cap = 0;
  int32_t* q3 = NULL;
  CUmodule module = NULL; CUfunction fn = NULL;
  CUdeviceptr dk = 0, dv = 0, dq = 0, dout = 0;
  tvdb_status_t st = tvdb_index_map_build(active, na, &keys, &vals, &cap, err);
  if (st != TVDB_OK) return st;
  q3 = (int32_t*)malloc(nq * 3u * sizeof(int32_t));
  if (!q3) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); st = TVDB_ERROR_OUT_OF_MEMORY; goto done; }
  for (size_t i = 0; i < nq; ++i) { q3[3*i+0]=query[3*i+0]; q3[3*i+1]=query[3*i+1]; q3[3*i+2]=query[3*i+2]; }
  if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto done;
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction",
        ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_index_probe"))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dk, keys, (size_t)cap * 3u * sizeof(int32_t), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dv, vals, (size_t)cap * sizeof(int32_t), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dq, q3, nq * 3u * sizeof(int32_t), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, nq * sizeof(int32_t), err)) != TVDB_OK) goto done;
  unsigned int unq = (unsigned int)nq, ucap = cap, umask = cap - 1u;
  void* args[] = {&dk, &dv, &dout, &dq, &unq, &ucap, &umask};
  unsigned int block = 128, grid = (unq + block - 1u) / block;
  if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out, dout, nq * sizeof(int32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  st = TVDB_OK;
done:
  free(q3); free(keys); free(vals);
  if (dout) ctx->cuda.cuMemFree(dout);
  if (dq) ctx->cuda.cuMemFree(dq);
  if (dv) ctx->cuda.cuMemFree(dv);
  if (dk) ctx->cuda.cuMemFree(dk);
  return st;
}

static tvdb_status_t tvdb_cuda_index_query_linear(tvdb_gpu_context_t* ctx,
    const int32_t* active, size_t na, const int32_t* query, size_t nq,
    int32_t* out, tvdb_error_t* err) {
  CUmodule module = NULL; CUfunction fn = NULL;
  CUdeviceptr da = 0, dq = 0, dout = 0;
  int32_t* a4 = NULL; int32_t* q4 = NULL;
  tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
  if (st != TVDB_OK) return st;
  a4 = (int32_t*)calloc(na ? na : 1, 4u * sizeof(int32_t));
  q4 = (int32_t*)calloc(nq ? nq : 1, 4u * sizeof(int32_t));
  if (!a4 || !q4) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); st = TVDB_ERROR_OUT_OF_MEMORY; goto done; }
  tvdb_pack_int4(a4, active, na);
  tvdb_pack_int4(q4, query, nq);
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_ijk_to_index"))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &da, a4, (na ? na : 1) * 4u * sizeof(int32_t), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dq, q4, (nq ? nq : 1) * 4u * sizeof(int32_t), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, nq * sizeof(int32_t), err)) != TVDB_OK) goto done;
  unsigned int una = (unsigned int)na, unq = (unsigned int)nq;
  void* args[] = {&da, &dq, &dout, &una, &unq};
  unsigned int block = 128, grid = (unq + block - 1u) / block;
  if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out, dout, nq * sizeof(int32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  st = TVDB_OK;
done:
  free(a4); free(q4);
  if (dout) ctx->cuda.cuMemFree(dout);
  if (dq) ctx->cuda.cuMemFree(dq);
  if (da) ctx->cuda.cuMemFree(da);
  return st;
}

/* Original brute-force path: one thread per query, linear scan of the active
 * set. O(nq*na) but needs no precomputation, so it wins for small active sets. */
static tvdb_status_t tvdb_vk_index_query_linear(tvdb_gpu_context_t* ctx,
    const int32_t* active, size_t na, const int32_t* query, size_t nq,
    int32_t* out, tvdb_error_t* err) {
  tvdb_vk_buffer ba, bq, bo, bp;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, (na ? na : 1) * 4u * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &ba, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, nq * 4u * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bq, err)) != TVDB_OK) goto done_a;
  if ((st = tvdb_vk_create_buffer(ctx, nq * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto done_q;
  if ((st = tvdb_vk_create_buffer(ctx, 16, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bp, err)) != TVDB_OK) goto done_o;
  tvdb_pack_int4((int32_t*)ba.mapped, active, na);
  tvdb_pack_int4((int32_t*)bq.mapped, query, nq);
  struct { uint32_t na, nq, pad[2]; } par = {(uint32_t)na, (uint32_t)nq, {0, 0}};
  memcpy(bp.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuIjkToIndexSpv; d.spv_len = kTvdbGpuIjkToIndexSpv_len; d.descriptor_count = 4;
  d.buffers[0] = &ba; d.buffers[1] = &bq; d.buffers[2] = &bo; d.buffers[3] = &bp;
  d.descriptor_types[0] = d.descriptor_types[1] = d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((nq + 127u) / 128u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(out, bo.mapped, nq * sizeof(int32_t));
  tvdb_vk_destroy_buffer(ctx, &bp);
done_o: tvdb_vk_destroy_buffer(ctx, &bo);
done_q: tvdb_vk_destroy_buffer(ctx, &bq);
done_a: tvdb_vk_destroy_buffer(ctx, &ba);
  return st;
}



static tvdb_status_t tvdb_vk_index_query(tvdb_gpu_context_t* ctx,
    const int32_t* active, size_t na, const int32_t* query, size_t nq,
    int32_t* out, tvdb_error_t* err) {
  if (TVDB_INDEX_MAP_FORCE_LINEAR || na < TVDB_INDEX_MAP_MIN_ACTIVE)
    return tvdb_vk_index_query_linear(ctx, active, na, query, nq, out, err);
  int32_t* keys = NULL; int32_t* vals = NULL; uint32_t cap = 0;
  tvdb_status_t st = tvdb_index_map_build(active, na, &keys, &vals, &cap, err);
  if (st != TVDB_OK) return st;

  tvdb_vk_buffer bk, bv, bq, bo, bp;
  /* Zero every handle: the cleanup labels below run tvdb_vk_destroy_buffer on
   * buffers whose create may have failed, and that reads the handles. */
  memset(&bk, 0, sizeof(bk)); memset(&bv, 0, sizeof(bv)); memset(&bq, 0, sizeof(bq));
  memset(&bo, 0, sizeof(bo)); memset(&bp, 0, sizeof(bp));
  if ((st = tvdb_vk_create_buffer(ctx, (size_t)cap * 3u * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bk, err)) != TVDB_OK) goto freemap;
  if ((st = tvdb_vk_create_buffer(ctx, (size_t)cap * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bv, err)) != TVDB_OK) goto done_k;
  if ((st = tvdb_vk_create_buffer(ctx, nq * 3u * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bq, err)) != TVDB_OK) goto done_v;
  if ((st = tvdb_vk_create_buffer(ctx, nq * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto done_q;
  if ((st = tvdb_vk_create_buffer(ctx, 16, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bp, err)) != TVDB_OK) goto done_o;
  memcpy(bk.mapped, keys, (size_t)cap * 3u * sizeof(int32_t));
  memcpy(bv.mapped, vals, (size_t)cap * sizeof(int32_t));
  memcpy(bq.mapped, query, nq * 3u * sizeof(int32_t));
  struct { uint32_t nq, cap, mask, pad; } par = {(uint32_t)nq, cap, cap - 1u, 0u};
  memcpy(bp.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuIndexProbeSpv; d.spv_len = kTvdbGpuIndexProbeSpv_len; d.descriptor_count = 5;
  d.buffers[0] = &bk; d.buffers[1] = &bv; d.buffers[2] = &bo; d.buffers[3] = &bq; d.buffers[4] = &bp;
  d.descriptor_types[0] = d.descriptor_types[1] = d.descriptor_types[2] = d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((nq + 127u) / 128u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(out, bo.mapped, nq * sizeof(int32_t));
  tvdb_vk_destroy_buffer(ctx, &bp);
done_o: tvdb_vk_destroy_buffer(ctx, &bo);
done_q: tvdb_vk_destroy_buffer(ctx, &bq);
done_v: tvdb_vk_destroy_buffer(ctx, &bv);
done_k: tvdb_vk_destroy_buffer(ctx, &bk);
freemap:
  free(keys); free(vals);
  return st;
}

static tvdb_status_t tvdb_gpu_index_query(tvdb_gpu_context_t* ctx,
    const int32_t* active, size_t na, const int32_t* query, size_t nq,
    int32_t* out, tvdb_error_t* err) {
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA)
    return (TVDB_INDEX_MAP_FORCE_LINEAR || na < TVDB_INDEX_MAP_MIN_ACTIVE)
      ? tvdb_cuda_index_query_linear(ctx, active, na, query, nq, out, err)
      : tvdb_cuda_index_query_map(ctx, active, na, query, nq, out, err);
  return tvdb_vk_index_query(ctx, active, na, query, nq, out, err);
}

tvdb_status_t tvdb_gpu_coords_in_grid(tvdb_gpu_context_t* ctx,
    const int32_t* active, size_t na, const int32_t* query, size_t nq,
    uint8_t* out, tvdb_error_t* err) {
  if (!ctx || (!active && na) || (!query && nq) || (!out && nq)) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid coords_in_grid arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (nq == 0) return TVDB_OK;
  int32_t* idx = (int32_t*)malloc(nq * sizeof(int32_t));
  if (!idx) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  tvdb_status_t st = tvdb_gpu_index_query(ctx, active, na, query, nq, idx, err);
  if (st == TVDB_OK)
    for (size_t i = 0; i < nq; ++i) out[i] = idx[i] >= 0 ? 1 : 0;
  free(idx);
  return st;
}

tvdb_status_t tvdb_gpu_ijk_to_index(tvdb_gpu_context_t* ctx,
    const int32_t* active, size_t na, const int32_t* query, size_t nq,
    int64_t* out, tvdb_error_t* err) {
  if (!ctx || (!active && na) || (!query && nq) || (!out && nq)) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid ijk_to_index arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (nq == 0) return TVDB_OK;
  int32_t* idx = (int32_t*)malloc(nq * sizeof(int32_t));
  if (!idx) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  tvdb_status_t st = tvdb_gpu_index_query(ctx, active, na, query, nq, idx, err);
  if (st == TVDB_OK)
    for (size_t i = 0; i < nq; ++i) out[i] = (int64_t)idx[i];
  free(idx);
  return st;
}

// points kernel: out[i] = index of floor((p-origin)/voxel_size) in active, or -1.
/* Above the crossover, probe the host-built map instead of scanning the active
 * set per point. */
static tvdb_status_t tvdb_cuda_points_query_map(tvdb_gpu_context_t* ctx,
    const float* points, size_t np, const float voxel_size[3], const float origin[3],
    const int32_t* active, size_t na, int32_t* out, tvdb_error_t* err) {
  int32_t* keys = NULL; int32_t* vals = NULL; uint32_t cap = 0;
  float* p4 = NULL;
  CUmodule module = NULL; CUfunction fn = NULL;
  CUdeviceptr dk = 0, dv = 0, dp = 0, dout = 0;
  tvdb_status_t st = tvdb_index_map_build(active, na, &keys, &vals, &cap, err);
  if (st != TVDB_OK) return st;
  p4 = (float*)calloc(np ? np : 1, 4u * sizeof(float));
  if (!p4) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); st = TVDB_ERROR_OUT_OF_MEMORY; goto done; }
  for (size_t i = 0; i < np; ++i) { p4[4*i+0]=points[3*i+0]; p4[4*i+1]=points[3*i+1]; p4[4*i+2]=points[3*i+2]; p4[4*i+3]=0.0f; }
  if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto done;
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction",
        ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_points_in_grid_probe"))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dk, keys, (size_t)cap * 3u * sizeof(int32_t), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dv, vals, (size_t)cap * sizeof(int32_t), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dp, p4, (np ? np : 1) * 4u * sizeof(float), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, np * sizeof(int32_t), err)) != TVDB_OK) goto done;
  unsigned int unp = (unsigned int)np, ucap = cap, umask = cap - 1u;
  float vx = voxel_size[0], vy = voxel_size[1], vz = voxel_size[2];
  float ox = origin[0], oy = origin[1], oz = origin[2];
  void* args[] = {&dk, &dv, &dout, &dp, &unp, &ucap, &umask, &vx, &vy, &vz, &ox, &oy, &oz};
  unsigned int block = 128, grid = (unp + block - 1u) / block;
  if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out, dout, np * sizeof(int32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  st = TVDB_OK;
done:
  free(p4); free(keys); free(vals);
  if (dout) ctx->cuda.cuMemFree(dout);
  if (dp) ctx->cuda.cuMemFree(dp);
  if (dv) ctx->cuda.cuMemFree(dv);
  if (dk) ctx->cuda.cuMemFree(dk);
  return st;
}

static tvdb_status_t tvdb_cuda_points_query_linear(tvdb_gpu_context_t* ctx,
    const float* points, size_t np, const float voxel_size[3], const float origin[3],
    const int32_t* active, size_t na, int32_t* out, tvdb_error_t* err) {
  CUmodule module = NULL; CUfunction fn = NULL;
  CUdeviceptr da = 0, dp = 0, dout = 0;
  int32_t* a4 = NULL; float* p4 = NULL;
  tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
  if (st != TVDB_OK) return st;
  a4 = (int32_t*)calloc(na ? na : 1, 4u * sizeof(int32_t));
  p4 = (float*)calloc(np ? np : 1, 4u * sizeof(float));
  if (!a4 || !p4) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); st = TVDB_ERROR_OUT_OF_MEMORY; goto done; }
  tvdb_pack_int4(a4, active, na);
  for (size_t i = 0; i < np; ++i) { p4[4*i+0] = points[3*i+0]; p4[4*i+1] = points[3*i+1]; p4[4*i+2] = points[3*i+2]; p4[4*i+3] = 0.0f; }
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_points_in_grid"))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &da, a4, (na ? na : 1) * 4u * sizeof(int32_t), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dp, p4, (np ? np : 1) * 4u * sizeof(float), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, np * sizeof(int32_t), err)) != TVDB_OK) goto done;
  unsigned int una = (unsigned int)na, unp = (unsigned int)np;
  float vx = voxel_size[0], vy = voxel_size[1], vz = voxel_size[2];
  float ox = origin[0], oy = origin[1], oz = origin[2];
  void* args[] = {&da, &dp, &dout, &una, &unp, &vx, &vy, &vz, &ox, &oy, &oz};
  unsigned int block = 128, grid = (unp + block - 1u) / block;
  if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out, dout, np * sizeof(int32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  st = TVDB_OK;
done:
  free(a4); free(p4);
  if (dout) ctx->cuda.cuMemFree(dout);
  if (dp) ctx->cuda.cuMemFree(dp);
  if (da) ctx->cuda.cuMemFree(da);
  return st;
}

static tvdb_status_t tvdb_vk_points_query(tvdb_gpu_context_t* ctx,
    const float* points, size_t np, const float voxel_size[3], const float origin[3],
    const int32_t* active, size_t na, int32_t* out, tvdb_error_t* err) {
  /* Above the same crossover as ijk_to_index, probe the host-built map instead
   * of scanning the active set once per point. */
  if (!TVDB_INDEX_MAP_FORCE_LINEAR && na >= TVDB_INDEX_MAP_MIN_ACTIVE) {
    int32_t* keys = NULL; int32_t* vals = NULL; uint32_t cap = 0;
    tvdb_status_t st = tvdb_index_map_build(active, na, &keys, &vals, &cap, err);
    if (st != TVDB_OK) return st;
    tvdb_vk_buffer bk, bv, bpts, bo, bp;
    /* Zero every handle: the cleanup labels run tvdb_vk_destroy_buffer on
     * buffers whose create may have failed, and that reads the handles. */
    memset(&bk, 0, sizeof(bk)); memset(&bv, 0, sizeof(bv)); memset(&bpts, 0, sizeof(bpts));
    memset(&bo, 0, sizeof(bo)); memset(&bp, 0, sizeof(bp));
    if ((st = tvdb_vk_create_buffer(ctx, (size_t)cap * 3u * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bk, err)) != TVDB_OK) goto pg_freemap;
    if ((st = tvdb_vk_create_buffer(ctx, (size_t)cap * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bv, err)) != TVDB_OK) goto pg_done_k;
    if ((st = tvdb_vk_create_buffer(ctx, np * 4u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bpts, err)) != TVDB_OK) goto pg_done_v;
    if ((st = tvdb_vk_create_buffer(ctx, np * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto pg_done_pts;
    if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bp, err)) != TVDB_OK) goto pg_done_o;
    memcpy(bk.mapped, keys, (size_t)cap * 3u * sizeof(int32_t));
    memcpy(bv.mapped, vals, (size_t)cap * sizeof(int32_t));
    { float* pm = (float*)bpts.mapped;
      for (size_t i = 0; i < np; ++i) { pm[4*i+0] = points[3*i+0]; pm[4*i+1] = points[3*i+1]; pm[4*i+2] = points[3*i+2]; pm[4*i+3] = 0.0f; } }
    struct { uint32_t np, cap, mask, pad0; float vs[4]; float origin[4]; } par;
    memset(&par, 0, sizeof(par));
    par.np = (uint32_t)np; par.cap = cap; par.mask = cap - 1u;
    par.vs[0] = voxel_size[0]; par.vs[1] = voxel_size[1]; par.vs[2] = voxel_size[2];
    par.origin[0] = origin[0]; par.origin[1] = origin[1]; par.origin[2] = origin[2];
    memcpy(bp.mapped, &par, sizeof(par));
    tvdb_vk_dispatch_desc d;
    memset(&d, 0, sizeof(d));
    d.spv = kTvdbGpuPointsInGridProbeSpv; d.spv_len = kTvdbGpuPointsInGridProbeSpv_len; d.descriptor_count = 5;
    d.buffers[0] = &bk; d.buffers[1] = &bv; d.buffers[2] = &bpts; d.buffers[3] = &bo; d.buffers[4] = &bp;
    d.descriptor_types[0] = d.descriptor_types[1] = d.descriptor_types[2] = d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    d.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    d.group_x = (uint32_t)((np + 127u) / 128u);
    st = tvdb_vk_dispatch(ctx, &d, err);
    if (st == TVDB_OK) memcpy(out, bo.mapped, np * sizeof(int32_t));
    tvdb_vk_destroy_buffer(ctx, &bp);
  pg_done_o: tvdb_vk_destroy_buffer(ctx, &bo);
  pg_done_pts: tvdb_vk_destroy_buffer(ctx, &bpts);
  pg_done_v: tvdb_vk_destroy_buffer(ctx, &bv);
  pg_done_k: tvdb_vk_destroy_buffer(ctx, &bk);
  pg_freemap:
    free(keys); free(vals);
    return st;
  }
  tvdb_vk_buffer ba, bpts, bo, bp;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, (na ? na : 1) * 4u * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &ba, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, np * 4u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bpts, err)) != TVDB_OK) goto done_a;
  if ((st = tvdb_vk_create_buffer(ctx, np * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto done_pts;
  if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bp, err)) != TVDB_OK) goto done_o;
  tvdb_pack_int4((int32_t*)ba.mapped, active, na);
  { float* pm = (float*)bpts.mapped;
    for (size_t i = 0; i < np; ++i) { pm[4*i+0] = points[3*i+0]; pm[4*i+1] = points[3*i+1]; pm[4*i+2] = points[3*i+2]; pm[4*i+3] = 0.0f; } }
  struct { uint32_t na, np, pad[2]; float vs[4]; float origin[4]; } par;
  memset(&par, 0, sizeof(par));
  par.na = (uint32_t)na; par.np = (uint32_t)np;
  par.vs[0] = voxel_size[0]; par.vs[1] = voxel_size[1]; par.vs[2] = voxel_size[2];
  par.origin[0] = origin[0]; par.origin[1] = origin[1]; par.origin[2] = origin[2];
  memcpy(bp.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuPointsInGridSpv; d.spv_len = kTvdbGpuPointsInGridSpv_len; d.descriptor_count = 4;
  d.buffers[0] = &ba; d.buffers[1] = &bpts; d.buffers[2] = &bo; d.buffers[3] = &bp;
  d.descriptor_types[0] = d.descriptor_types[1] = d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((np + 127u) / 128u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(out, bo.mapped, np * sizeof(int32_t));
  tvdb_vk_destroy_buffer(ctx, &bp);
done_o: tvdb_vk_destroy_buffer(ctx, &bo);
done_pts: tvdb_vk_destroy_buffer(ctx, &bpts);
done_a: tvdb_vk_destroy_buffer(ctx, &ba);
  return st;
}

/* World queries are converted once in double on the host; device hash probes
   receive exact int32 triples even near the representability boundary. */
static tvdb_status_t tvdb_gpu_world_query_coords(const float* points,size_t n,
 const float h[3],const float origin[3],int32_t** coords,tvdb_error_t* err) {
  *coords=NULL;
  size_t bytes;
  if(!h || !origin || (n && !points) || n>INT_MAX || !tvdb_size_mul(n,3*sizeof(int32_t),&bytes)) goto invalid;
  for(int k=0;k<3;++k) if(!isfinite(h[k]) || h[k]<=0 || !isfinite(origin[k])) goto invalid;
  for(size_t i=0;i<n;++i) for(int k=0;k<3;++k) {
    double v=floor(((double)points[3*i+k]-origin[k])/h[k]);
    if(!isfinite(points[3*i+k]) || !isfinite(v) || v<INT32_MIN || v>INT32_MAX) goto invalid;
  }
  if(!n) return TVDB_OK;
  *coords=malloc(bytes);
  if(!*coords) { tvdb_gpu_set_error(err,TVDB_ERROR_OUT_OF_MEMORY,"world query coordinate allocation failed"); return TVDB_ERROR_OUT_OF_MEMORY; }
  for(size_t i=0;i<n;++i) for(int k=0;k<3;++k) (*coords)[3*i+k]=(int32_t)floor(((double)points[3*i+k]-origin[k])/h[k]);
  return TVDB_OK;
invalid:
  tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid/unrepresentable world query"); return TVDB_ERROR_INVALID_ARGUMENT;
}

tvdb_status_t tvdb_gpu_points_in_grid(tvdb_gpu_context_t* ctx,
 const float* points,size_t np,const float voxel_size[3],const float origin[3],
 const int32_t* active,size_t na,uint8_t* out,tvdb_error_t* err) {
  if(!ctx || na>INT_MAX || (na && !active) || (np && !out)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid world query buffers"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  int32_t* coords=NULL;
  tvdb_status_t st=tvdb_gpu_world_query_coords(points,np,voxel_size,origin,&coords,err);
  if(st!=TVDB_OK || !np) return st;
  int64_t* indices=malloc(np*sizeof(*indices));
  if(!indices) { free(coords); tvdb_gpu_set_error(err,TVDB_ERROR_OUT_OF_MEMORY,"world query index allocation failed"); return TVDB_ERROR_OUT_OF_MEMORY; }
  st=tvdb_gpu_ijk_to_index(ctx,active,na,coords,np,indices,err);
  if(st==TVDB_OK) for(size_t i=0;i<np;++i) out[i]=indices[i]>=0;
  free(coords); free(indices); return st;
}

// neighbor kernel: out[i] = # active neighbors of active[i] (6- or 26-conn).
/* Above the crossover, probe the host-built map: O(na * connectivity) instead of
 * up to 26 full scans of the active set per voxel (O(na^2 * connectivity)). */
static tvdb_status_t tvdb_cuda_neighbor_counts_map(tvdb_gpu_context_t* ctx,
    const int32_t* active, size_t na, int connectivity, int32_t* out, tvdb_error_t* err) {
  int32_t* keys = NULL; int32_t* vals = NULL; uint32_t cap = 0;
  int32_t* a4 = NULL;
  CUmodule module = NULL; CUfunction fn = NULL;
  CUdeviceptr dk = 0, dv = 0, da = 0, dout = 0;
  tvdb_status_t st = tvdb_index_map_build(active, na, &keys, &vals, &cap, err);
  if (st != TVDB_OK) return st;
  a4 = (int32_t*)calloc(na, 4u * sizeof(int32_t));
  if (!a4) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); st = TVDB_ERROR_OUT_OF_MEMORY; goto done; }
  tvdb_pack_int4(a4, active, na);
  if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto done;
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction",
        ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_neighbor_counts_probe"))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dk, keys, (size_t)cap * 3u * sizeof(int32_t), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dv, vals, (size_t)cap * sizeof(int32_t), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &da, a4, na * 4u * sizeof(int32_t), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, na * sizeof(int32_t), err)) != TVDB_OK) goto done;
  unsigned int una = (unsigned int)na, ucap = cap, umask = cap - 1u;
  void* args[] = {&dk, &dv, &dout, &da, &una, &connectivity, &ucap, &umask};
  unsigned int block = 128, grid = (una + block - 1u) / block;
  if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out, dout, na * sizeof(int32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  st = TVDB_OK;
done:
  free(a4); free(keys); free(vals);
  if (dout) ctx->cuda.cuMemFree(dout);
  if (da) ctx->cuda.cuMemFree(da);
  if (dv) ctx->cuda.cuMemFree(dv);
  if (dk) ctx->cuda.cuMemFree(dk);
  return st;
}

static tvdb_status_t tvdb_cuda_neighbor_counts_linear(tvdb_gpu_context_t* ctx,
    const int32_t* active, size_t na, int connectivity, int32_t* out, tvdb_error_t* err) {
  CUmodule module = NULL; CUfunction fn = NULL;
  CUdeviceptr da = 0, dout = 0;
  int32_t* a4 = NULL;
  tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
  if (st != TVDB_OK) return st;
  a4 = (int32_t*)calloc(na, 4u * sizeof(int32_t));
  if (!a4) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); st = TVDB_ERROR_OUT_OF_MEMORY; goto done; }
  tvdb_pack_int4(a4, active, na);
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_neighbor_counts"))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &da, a4, na * 4u * sizeof(int32_t), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, na * sizeof(int32_t), err)) != TVDB_OK) goto done;
  unsigned int una = (unsigned int)na;
  void* args[] = {&da, &dout, &una, &connectivity};
  unsigned int block = 128, grid = (una + block - 1u) / block;
  if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out, dout, na * sizeof(int32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  st = TVDB_OK;
done:
  free(a4);
  if (dout) ctx->cuda.cuMemFree(dout);
  if (da) ctx->cuda.cuMemFree(da);
  return st;
}

static tvdb_status_t tvdb_vk_neighbor_counts_impl(tvdb_gpu_context_t* ctx,
    const int32_t* active, size_t na, int connectivity, int32_t* out, tvdb_error_t* err) {
  /* The original kernel did up to 26 full scans of the active set per active
   * voxel (O(na^2 * connectivity)). Above the same crossover measured for
   * ijk_to_index, probe the host-built map instead. */
  if (!TVDB_INDEX_MAP_FORCE_LINEAR && na >= TVDB_INDEX_MAP_MIN_ACTIVE) {
    int32_t* keys = NULL; int32_t* vals = NULL; uint32_t cap = 0;
    tvdb_status_t st = tvdb_index_map_build(active, na, &keys, &vals, &cap, err);
    if (st != TVDB_OK) return st;
    tvdb_vk_buffer bk, bv, ba, bo, bp;
    /* Zero every handle: the cleanup labels run tvdb_vk_destroy_buffer on
     * buffers whose create may have failed, and that reads the handles. */
    memset(&bk, 0, sizeof(bk)); memset(&bv, 0, sizeof(bv)); memset(&ba, 0, sizeof(ba));
    memset(&bo, 0, sizeof(bo)); memset(&bp, 0, sizeof(bp));
    if ((st = tvdb_vk_create_buffer(ctx, (size_t)cap * 3u * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bk, err)) != TVDB_OK) goto nc_freemap;
    if ((st = tvdb_vk_create_buffer(ctx, (size_t)cap * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bv, err)) != TVDB_OK) goto nc_done_k;
    if ((st = tvdb_vk_create_buffer(ctx, na * 4u * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &ba, err)) != TVDB_OK) goto nc_done_v;
    if ((st = tvdb_vk_create_buffer(ctx, na * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto nc_done_a;
    if ((st = tvdb_vk_create_buffer(ctx, 32, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bp, err)) != TVDB_OK) goto nc_done_o;
    memcpy(bk.mapped, keys, (size_t)cap * 3u * sizeof(int32_t));
    memcpy(bv.mapped, vals, (size_t)cap * sizeof(int32_t));
    tvdb_pack_int4((int32_t*)ba.mapped, active, na);
    struct { uint32_t na; int32_t connectivity; uint32_t cap; uint32_t mask; } par =
        {(uint32_t)na, connectivity, cap, cap - 1u};
    memcpy(bp.mapped, &par, sizeof(par));
    tvdb_vk_dispatch_desc d;
    memset(&d, 0, sizeof(d));
    d.spv = kTvdbGpuNeighborCountsProbeSpv; d.spv_len = kTvdbGpuNeighborCountsProbeSpv_len; d.descriptor_count = 5;
    d.buffers[0] = &bk; d.buffers[1] = &bv; d.buffers[2] = &ba; d.buffers[3] = &bo; d.buffers[4] = &bp;
    d.descriptor_types[0] = d.descriptor_types[1] = d.descriptor_types[2] = d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    d.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    d.group_x = (uint32_t)((na + 127u) / 128u);
    st = tvdb_vk_dispatch(ctx, &d, err);
    if (st == TVDB_OK) memcpy(out, bo.mapped, na * sizeof(int32_t));
    tvdb_vk_destroy_buffer(ctx, &bp);
  nc_done_o: tvdb_vk_destroy_buffer(ctx, &bo);
  nc_done_a: tvdb_vk_destroy_buffer(ctx, &ba);
  nc_done_v: tvdb_vk_destroy_buffer(ctx, &bv);
  nc_done_k: tvdb_vk_destroy_buffer(ctx, &bk);
  nc_freemap:
    free(keys); free(vals);
    return st;
  }
  tvdb_vk_buffer ba, bo, bp;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, na * 4u * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &ba, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, na * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto done_a;
  if ((st = tvdb_vk_create_buffer(ctx, 16, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bp, err)) != TVDB_OK) goto done_o;
  tvdb_pack_int4((int32_t*)ba.mapped, active, na);
  struct { uint32_t na; int32_t connectivity; uint32_t pad[2]; } par = {(uint32_t)na, connectivity, {0, 0}};
  memcpy(bp.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuNeighborCountsSpv; d.spv_len = kTvdbGpuNeighborCountsSpv_len; d.descriptor_count = 3;
  d.buffers[0] = &ba; d.buffers[1] = &bo; d.buffers[2] = &bp;
  d.descriptor_types[0] = d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((na + 127u) / 128u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(out, bo.mapped, na * sizeof(int32_t));
  tvdb_vk_destroy_buffer(ctx, &bp);
done_o: tvdb_vk_destroy_buffer(ctx, &bo);
done_a: tvdb_vk_destroy_buffer(ctx, &ba);
  return st;
}

tvdb_status_t tvdb_gpu_neighbor_counts(tvdb_gpu_context_t* ctx,
    const int32_t* active, size_t na, int connectivity,
    int32_t* out_counts, tvdb_error_t* err) {
  if (!ctx || (!active && na) || (!out_counts && na) || (connectivity != 6 && connectivity != 26)) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid neighbor_counts arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (na == 0) return TVDB_OK;
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA)
    return (TVDB_INDEX_MAP_FORCE_LINEAR || na < TVDB_INDEX_MAP_MIN_ACTIVE)
      ? tvdb_cuda_neighbor_counts_linear(ctx, active, na, connectivity, out_counts, err)
      : tvdb_cuda_neighbor_counts_map(ctx, active, na, connectivity, out_counts, err);
  return tvdb_vk_neighbor_counts_impl(ctx, active, na, connectivity, out_counts, err);
}

// ---- dense topology / morphology -------------------------------------------

static tvdb_status_t tvdb_vk_morph(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                                   int iterations, int is_dilate, tvdb_error_t* err) {
  size_t n = (size_t)grid->nx * (size_t)grid->ny * (size_t)grid->nz;
  tvdb_vk_buffer ba, bb, bp;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &ba, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bb, err)) != TVDB_OK) goto done_a;
  if ((st = tvdb_vk_create_buffer(ctx, 32, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bp, err)) != TVDB_OK) goto done_b;
  memcpy(ba.mapped, grid->data, n * sizeof(float));
  struct { int32_t dim[4]; int32_t is_dilate; int32_t pad[3]; } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = grid->nx; par.dim[1] = grid->ny; par.dim[2] = grid->nz; par.is_dilate = is_dilate;
  memcpy(bp.mapped, &par, sizeof(par));
  tvdb_vk_buffer* src = &ba; tvdb_vk_buffer* dst = &bb;
  for (int it = 0; it < iterations; ++it) {
    tvdb_vk_dispatch_desc d;
    memset(&d, 0, sizeof(d));
    d.spv = kTvdbGpuMorphSpv; d.spv_len = kTvdbGpuMorphSpv_len; d.descriptor_count = 3;
    d.buffers[0] = src; d.buffers[1] = dst; d.buffers[2] = &bp;
    d.descriptor_types[0] = d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    d.group_x = (uint32_t)((n + 127u) / 128u);
    /* Queue the whole ping-pong instead of waiting per iteration: the buffers
     * are never touched by the host inside the loop, and tvdb_vk_dispatch emits
     * the shader-write -> shader-read barrier that makes each iteration see the
     * previous one. The single flush below is the only wait. */
    d.defer_wait = TVDB_VK_DEFERRED_SUBMIT;
    st = tvdb_vk_dispatch(ctx, &d, err);
    if (st != TVDB_OK) goto done_p;
    tvdb_vk_buffer* tmp = src; src = dst; dst = tmp;
  }
  if ((st = tvdb_vk_flush(ctx, err)) != TVDB_OK) goto done_p;
  memcpy(grid->data, src->mapped, n * sizeof(float));
done_p: tvdb_vk_destroy_buffer(ctx, &bp);
done_b: tvdb_vk_destroy_buffer(ctx, &bb);
done_a: tvdb_vk_destroy_buffer(ctx, &ba);
  return st;
}

static tvdb_status_t tvdb_cuda_morph_impl(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                                          int iterations, int is_dilate, tvdb_error_t* err) {
  CUmodule module = NULL; CUfunction fn = NULL;
  CUdeviceptr da = 0, db = 0;
  size_t n = (size_t)grid->nx * (size_t)grid->ny * (size_t)grid->nz;
  tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
  if (st != TVDB_OK) return st;
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_morph"))) return err ? err->status : TVDB_ERROR_IO;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &da, grid->data, n * sizeof(float), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &db, NULL, n * sizeof(float), err)) != TVDB_OK) goto done;
  int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  unsigned int block = 128, grid_blocks = ((unsigned int)n + block - 1u) / block;
  CUdeviceptr src = da, dst = db;
  /* No per-iteration synchronize. Every launch goes on the NULL stream, which is
   * implicitly ordered, so iteration N+1 cannot start before N finishes and the
   * sync was a full-device stall that bought nothing. The single
   * cuMemcpyDtoH below is itself synchronous with respect to that stream, so the
   * result is still read after the last iteration completed. This mirrors what
   * the Vulkan path above does with one flush, and what the CUDA mean-curvature
   * flow already does. */
  for (int it = 0; it < iterations; ++it) {
    void* args[] = {&src, &dst, &nx, &ny, &nz, &is_dilate};
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid_blocks, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
    CUdeviceptr tmp = src; src = dst; dst = tmp;
  }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(grid->data, src, n * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  st = TVDB_OK;
done:
  if (db) ctx->cuda.cuMemFree(db);
  if (da) ctx->cuda.cuMemFree(da);
  return st;
}

static tvdb_status_t tvdb_gpu_morph(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                                    int iterations, int is_dilate, tvdb_error_t* err) {
  if (!ctx || !grid || !grid->data || grid->nx <= 0 || grid->ny <= 0 || grid->nz <= 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid morphology arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (iterations <= 0) return TVDB_OK;
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA)
    return tvdb_cuda_morph_impl(ctx, grid, iterations, is_dilate, err);
  return tvdb_vk_morph(ctx, grid, iterations, is_dilate, err);
}

tvdb_status_t tvdb_gpu_dilate(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                              int iterations, tvdb_error_t* err) {
  return resident_morph_host(ctx,grid,iterations,0,err);
}
tvdb_status_t tvdb_gpu_erode(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                             int iterations, tvdb_error_t* err) {
  return resident_morph_host(ctx,grid,iterations,1,err);
}

/* Morphological opening and closing, mirroring tvdb_open / tvdb_close exactly:
 * erode then dilate, and dilate then erode, by `iterations` steps each. These
 * were the only CPU morphology ops with no GPU entry point, and they are
 * compositions of two that already exist, so the order and the intermediate
 * result are the same as running the two calls by hand. */
tvdb_status_t tvdb_gpu_open(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                            int iterations, tvdb_error_t* err) {
  return resident_morph_host(ctx,grid,iterations,2,err);
}

tvdb_status_t tvdb_gpu_close(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                             int iterations, tvdb_error_t* err) {
  return resident_morph_host(ctx,grid,iterations,3,err);
}

static tvdb_status_t tvdb_vk_prune(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                                   float background, float tolerance, tvdb_error_t* err) {
  size_t n = (size_t)grid->nx * (size_t)grid->ny * (size_t)grid->nz;
  tvdb_vk_buffer bd, bp;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bd, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, 16, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bp, err)) != TVDB_OK) goto done_d;
  memcpy(bd.mapped, grid->data, n * sizeof(float));
  struct { uint32_t count; float background; float tolerance; uint32_t pad; } par = {(uint32_t)n, background, tolerance, 0};
  memcpy(bp.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuPruneSpv; d.spv_len = kTvdbGpuPruneSpv_len; d.descriptor_count = 2;
  d.buffers[0] = &bd; d.buffers[1] = &bp;
  d.descriptor_types[0] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((n + 127u) / 128u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(grid->data, bd.mapped, n * sizeof(float));
  tvdb_vk_destroy_buffer(ctx, &bp);
done_d: tvdb_vk_destroy_buffer(ctx, &bd);
  return st;
}

static tvdb_status_t tvdb_cuda_prune_impl(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                                          float background, float tolerance, tvdb_error_t* err) {
  CUmodule module = NULL; CUfunction fn = NULL;
  CUdeviceptr dd = 0;
  size_t n = (size_t)grid->nx * (size_t)grid->ny * (size_t)grid->nz;
  tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
  if (st != TVDB_OK) return st;
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_prune"))) return err ? err->status : TVDB_ERROR_IO;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dd, grid->data, n * sizeof(float), err)) != TVDB_OK) goto done;
  unsigned int count = (unsigned int)n;
  void* args[] = {&dd, &count, &background, &tolerance};
  unsigned int block = 128, grid_blocks = (count + block - 1u) / block;
  if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid_blocks, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(grid->data, dd, n * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  st = TVDB_OK;
done:
  if (dd) ctx->cuda.cuMemFree(dd);
  return st;
}

tvdb_status_t tvdb_gpu_prune(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                             float background, float tolerance, tvdb_error_t* err) {
  if (!ctx || !grid || !grid->data || grid->nx <= 0 || grid->ny <= 0 || grid->nz <= 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid prune arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA)
    return tvdb_cuda_prune_impl(ctx, grid, background, tolerance, err);
  return tvdb_vk_prune(ctx, grid, background, tolerance, err);
}

// ---- coarsen / refine (dimension-changing resamples) -----------------------

static tvdb_status_t tvdb_gpu_init_out_grid(tvdb_dense_grid* out, int nx, int ny, int nz,
                                            float vs, float ox, float oy, float oz, tvdb_error_t* err) {
  size_t bytes;
  if (!tvdb_grid_bytes(nx,ny,nz,sizeof(float),&bytes) || bytes/(sizeof(float)) > INT_MAX ||
      !isfinite(vs) || vs <= 0) { tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid output shape"); return TVDB_ERROR_INVALID_ARGUMENT; }
  out->nx = nx; out->ny = ny; out->nz = nz;
  out->voxel_size = vs; out->ox = ox; out->oy = oy; out->oz = oz;
  out->data = (float*)malloc(bytes);
  if (!out->data) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  memset(out->data, 0, bytes);
  return TVDB_OK;
}

/* ---------------------------------------------------------------------------
 * PDE stencils (laplacian, central differences, gradient, divergence, curl).
 *
 * All of them share the same shape: an 8x8 2D workgroup walking (x, y) with the
 * z index taken from the workgroup, clamped reads at the grid edge, and a
 * host-supplied scale so the shader only multiplies. The CPU reference is the
 * contract -- see the comments on the shaders for the exact expressions.
 */

static tvdb_status_t tvdb_vk_stencil2d(tvdb_gpu_context_t* ctx,
    const uint8_t* spv, size_t spv_len,
    const void* src, size_t src_count, int comps_in,
    void* dst, size_t dst_count, int comps_out,
    int nx, int ny, int nz, int op, float scale,
    float g_ox, float g_oy, float g_oz, float g_vs, tvdb_error_t* err) {
  if (!ctx || !spv || spv_len == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "no SPIR-V for this stencil (build with glslangValidator)");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  tvdb_vk_buffer bin, bout, bup;
  memset(&bin, 0, sizeof(bin)); memset(&bout, 0, sizeof(bout)); memset(&bup, 0, sizeof(bup));
  tvdb_status_t st;
  size_t in_bytes  = src_count * sizeof(float);
  size_t out_bytes = dst_count * sizeof(float);
  if ((st = tvdb_vk_create_buffer(ctx, in_bytes,  VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bin,  err)) != TVDB_OK) goto done;
  if ((st = tvdb_vk_create_buffer(ctx, out_bytes, VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bout, err)) != TVDB_OK) goto done_in;
  if ((st = tvdb_vk_create_buffer(ctx, 48,       VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT,  &bup,  err)) != TVDB_OK) goto done_out;
  memcpy(bin.mapped, src, in_bytes);
  /* std140, 48 bytes: ivec4 dim @0, float scale @16, vec4 grid_o @32.
   *
   * std140 aligns a vec4 to 16 bytes, so the C struct needs explicit padding
   * before grid_o. Without it the struct puts grid_o at 20 and the shader reads
   * whatever follows. _Static_assert below pins the layout so this cannot
   * regress silently -- it is the third time this shader has gotten it wrong. */
  typedef struct { int32_t dim[4]; float scale; uint32_t std140_pad[3]; float grid_o[4]; } tvdb_stencil_uniform;
  _Static_assert(sizeof(tvdb_stencil_uniform) == 48, "stencil uniform must match the 48-byte std140 block");
  _Static_assert(offsetof(tvdb_stencil_uniform, scale) == 16, "std140: float scale follows ivec4 dim at 16");
  _Static_assert(offsetof(tvdb_stencil_uniform, grid_o) == 32, "std140: vec4 grid_o must be 16-byte aligned");
  tvdb_stencil_uniform par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = nx; par.dim[1] = ny; par.dim[2] = nz; par.dim[3] = op;
  par.scale = scale;
  par.grid_o[0] = g_ox; par.grid_o[1] = g_oy; par.grid_o[2] = g_oz; par.grid_o[3] = g_vs;
  memcpy(bup.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = spv; d.spv_len = (uint32_t)spv_len; d.descriptor_count = 3;
  d.buffers[0] = &bin; d.buffers[1] = &bout; d.buffers[2] = &bup;
  d.descriptor_types[0] = d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((nx + 7) / 8);
  d.group_y = (uint32_t)((ny + 7) / 8);
  d.group_z = (uint32_t)nz;
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(dst, bout.mapped, out_bytes);
  tvdb_vk_destroy_buffer(ctx, &bup);
done_out: tvdb_vk_destroy_buffer(ctx, &bout);
done_in: tvdb_vk_destroy_buffer(ctx, &bin);
done:
  (void)comps_in; (void)comps_out;
  return st;
}

static tvdb_status_t tvdb_init_out_vec(tvdb_dense_vec_grid* out, int nx, int ny, int nz,
                                       float vs, float ox, float oy, float oz, tvdb_error_t* err) {
  size_t bytes;
  if (!tvdb_grid_bytes(nx,ny,nz,3u * sizeof(float),&bytes) || bytes/(3u * sizeof(float)) > INT_MAX ||
      !isfinite(vs) || vs <= 0) { tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid output shape"); return TVDB_ERROR_INVALID_ARGUMENT; }
  out->nx = nx; out->ny = ny; out->nz = nz;
  out->voxel_size = vs; out->ox = ox; out->oy = oy; out->oz = oz;
  out->data = (float*)malloc(bytes);
  if (!out->data) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  memset(out->data, 0, bytes);
  return TVDB_OK;
}

/* CPU reference used as the CUDA fallback, so both backends agree exactly. */
static void tvdb_cpu_stencil_scalar_scalar(const tvdb_dense_grid* in, int op, tvdb_dense_grid* out) {
  const int nx = in->nx, ny = in->ny, nz = in->nz;
  for (int iz = 0; iz < nz; ++iz) for (int iy = 0; iy < ny; ++iy) for (int ix = 0; ix < nx; ++ix) {
    float v;
    if (op == 0) {
      tvdb_laplacian(in, out); (void)ix; (void)iy; (void)iz; return;
    } else if (op == 1) v = tvdb_central_diff_x(in, ix, iy, iz);
    else if (op == 2) v = tvdb_central_diff_y(in, ix, iy, iz);
    else v = tvdb_central_diff_z(in, ix, iy, iz);
    out->data[((size_t)iz * ny + iy) * nx + ix] = v;
  }
}

/* CUDA launcher shared by the four stencils. `comps_in`/`comps_out` are the
 * per-voxel component counts (1 or 3). Falls back to nothing on failure: the
 * callers check the status and delegate to the CPU reference. */
static tvdb_status_t tvdb_cuda_stencil2d(tvdb_gpu_context_t* ctx, const char* fn,
    const float* src, size_t src_count, int comps_in,
    float* dst, size_t dst_count, int comps_out,
    int nx, int ny, int nz, int op, float scale,
    float g_ox, float g_oy, float g_oz, float g_vs, tvdb_error_t* err) {
  CUmodule module = NULL; CUfunction f = NULL;
  CUdeviceptr dsrc = 0, ddst = 0;
  tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
  if (st != TVDB_OK) return st;
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction",
        ctx->cuda.cuModuleGetFunction(&f, module, fn))) return err ? err->status : TVDB_ERROR_IO;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dsrc, src, src_count * sizeof(float), err)) != TVDB_OK) return st;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &ddst, NULL, dst_count * sizeof(float), err)) != TVDB_OK) goto done;
  /* The backend is SDK-free, so the grid is passed as raw unsigned counts. */
  unsigned int gx = (unsigned int)((nx + 7) / 8), gy = (unsigned int)((ny + 7) / 8), gz = (unsigned int)nz;
  /* All four CUDA stencil kernels share one signature so the argument list can
   * never mismatch the kernel it is launched against -- that bug bit once, when
   * only the scalar->scalar kernel took `op` and the other three read the int*
   * as the float scale. */
  void* args[] = {&dsrc, &ddst, &nx, &ny, &nz, &op, &scale, &g_ox, &g_oy, &g_oz, &g_vs};
  if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel",
        ctx->cuda.cuLaunchKernel(f, gx, gy, gz, 8u, 8u, 1u, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH",
        ctx->cuda.cuMemcpyDtoH(dst, ddst, dst_count * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  st = TVDB_OK;
done:
  if (ddst) ctx->cuda.cuMemFree(ddst);
  if (dsrc) ctx->cuda.cuMemFree(dsrc);
  (void)comps_in; (void)comps_out;
  return st;
}

static tvdb_status_t tvdb_gpu_stencil_scalar_scalar_impl(tvdb_gpu_context_t* ctx,
                                             const tvdb_dense_grid* in,
                                             int op,
                                             tvdb_dense_grid* out,
                                             tvdb_error_t* err) {
  if (!ctx || !in || !in->data || !out || op < 0 || op > 3) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid stencil_scalar_scalar arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if ((tvdb_gpu_init_out_grid(out, in->nx, in->ny, in->nz, in->voxel_size, in->ox, in->oy, in->oz, err)) != TVDB_OK)
    return TVDB_ERROR_OUT_OF_MEMORY;
  size_t n = (size_t)in->nx * (size_t)in->ny * (size_t)in->nz;
  float h = in->voxel_size;
  float scale = (op == 0) ? 1.0f / (h * h) : 1.0f / (2.0f * h);
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    tvdb_status_t cs = tvdb_cuda_stencil2d(ctx, "tvdb_cuda_stencil_scalar_scalar",
        in->data, n, 1, out->data, n, 1, in->nx, in->ny, in->nz, op, scale, in->ox, in->oy, in->oz, in->voxel_size, err);
    if (cs == TVDB_OK) return TVDB_OK;
    /* No stderr: this is a library. The fallback is documented in tinyvdb_gpu.h. */
    free(out->data); out->data = NULL;          /* let the CPU reference own it */
    if ((tvdb_gpu_init_out_grid(out, in->nx, in->ny, in->nz, in->voxel_size, in->ox, in->oy, in->oz, err)) != TVDB_OK)
      return TVDB_ERROR_OUT_OF_MEMORY;
    tvdb_cpu_stencil_scalar_scalar(in, op, out);
    return TVDB_OK;
  }
  return tvdb_vk_stencil2d(ctx, kTvdbGpuStencilScalarScalarSpv, kTvdbGpuStencilScalarScalarSpv_len,
                           in->data, n, 1, out->data, n, 1,
                           in->nx, in->ny, in->nz, op, scale, in->ox, in->oy, in->oz, in->voxel_size, err);
}

/* fp64 scalar stencil. Gated on the optional shaderFloat64 feature: reporting
 * UNIMPLEMENTED is the honest answer, because computing in fp32 would return
 * different values than the caller asked for with no indication. */
static tvdb_status_t tvdb_vk_stencil_d(tvdb_gpu_context_t* ctx,
    const double* src, double* dst, int nx, int ny, int nz, int op, double scale,
    tvdb_error_t* err) {
  if (!ctx->supports_shader_float64) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "device lacks shaderFloat64");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  tvdb_vk_buffer bin, bout, bup;
  memset(&bin, 0, sizeof(bin)); memset(&bout, 0, sizeof(bout)); memset(&bup, 0, sizeof(bup));
  tvdb_status_t st;
  size_t n = (size_t)nx * (size_t)ny * (size_t)nz;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(double), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bin, err)) != TVDB_OK) goto done;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(double), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bout, err)) != TVDB_OK) goto done_in;
  if ((st = tvdb_vk_create_buffer(ctx, 32, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bup, err)) != TVDB_OK) goto done_out;
  memcpy(bin.mapped, src, n * sizeof(double));
  /* std140: ivec4 dim occupies 0..15 and a double is 8-aligned, so scale lands
   * at 16. The shader block is 32 bytes (dim 0..15, scale 16..23, tail 24..31)
   * but the C struct is only 24; the buffer is allocated at the block size, so
   * the tail is simply never written. Asserted rather than assumed -- the fp32
   * equivalent of this assertion caught a real bug.
   *
   * Keeping sizeof == 32 would require explicit tail padding that is never read;
   * asserting the buffer covers the block is the property that actually matters. */
  typedef struct { int32_t dim[4]; double scale; } tvdb_stencil_d_uniform;
  _Static_assert(offsetof(tvdb_stencil_d_uniform, scale) == 16, "std140: double scale follows ivec4 dim at 16");
  _Static_assert(sizeof(tvdb_stencil_d_uniform) <= 32, "fp64 uniform must not overflow the 32-byte std140 buffer");
  tvdb_stencil_d_uniform par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = nx; par.dim[1] = ny; par.dim[2] = nz; par.dim[3] = op;
  par.scale = scale;
  memcpy(bup.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuStencilScalarDSpv; d.spv_len = kTvdbGpuStencilScalarDSpv_len; d.descriptor_count = 3;
  d.buffers[0] = &bin; d.buffers[1] = &bout; d.buffers[2] = &bup;
  d.descriptor_types[0] = d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((nx + 7) / 8);
  d.group_y = (uint32_t)((ny + 7) / 8);
  d.group_z = (uint32_t)nz;
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(dst, bout.mapped, n * sizeof(double));
  tvdb_vk_destroy_buffer(ctx, &bup);
done_out: tvdb_vk_destroy_buffer(ctx, &bout);
done_in: tvdb_vk_destroy_buffer(ctx, &bin);
done:
  return st;
}

/* CPU reference for the fp64 stencils, used as the CUDA fallback. */
static void tvdb_cpu_stencil_scalar_d(const tvdb_dense_grid_d* in, int op, tvdb_dense_grid_d* out) {
  const int nx = in->nx, ny = in->ny, nz = in->nz;
  if (op == 0) { tvdb_laplacian_d(in, out); return; }
  /* tvdb_at_d is a static inline in an internal header, so the clamped read is
   * spelled out here to match it exactly. */
  #define TVDB_D_AT(X, Y, Z) in->data[((size_t)((Z) < 0 ? 0 : ((Z) > nz-1 ? nz-1 : (Z))) * ny + ((Y) < 0 ? 0 : ((Y) > ny-1 ? ny-1 : (Y)))) * nx + ((X) < 0 ? 0 : ((X) > nx-1 ? nx-1 : (X)))]
  for (int iz = 0; iz < nz; ++iz) for (int iy = 0; iy < ny; ++iy) for (int ix = 0; ix < nx; ++ix) {
    double v;
    if (op == 1)      v = (TVDB_D_AT(ix+1, iy, iz) - TVDB_D_AT(ix-1, iy, iz)) / (2.0 * in->voxel_size);
    else if (op == 2) v = (TVDB_D_AT(ix, iy+1, iz) - TVDB_D_AT(ix, iy-1, iz)) / (2.0 * in->voxel_size);
    else              v = (TVDB_D_AT(ix, iy, iz+1) - TVDB_D_AT(ix, iy, iz-1)) / (2.0 * in->voxel_size);
    out->data[((size_t)iz * ny + iy) * nx + ix] = v;
  }
  #undef TVDB_D_AT
}

bool tvdb_gpu_supports_fp64(tvdb_gpu_context_t* ctx)
{
  /* CUDA exposes fp64 on every architecture that can load this module, and
   * NVRTC compiles a double kernel for any arch >= 1.3, which the loader
   * already requires. */
  if (!ctx) return false;
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) return true;
  return ctx->supports_shader_float64 ? true : false;
}

static tvdb_status_t tvdb_cuda_stencil_d(tvdb_gpu_context_t* ctx,
    const double* src, double* dst, int nx, int ny, int nz, int op, double scale,
    tvdb_error_t* err) {
  CUmodule module = NULL; CUfunction f = NULL;
  CUdeviceptr dsrc = 0, ddst = 0;
  tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
  if (st != TVDB_OK) return st;
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction",
        ctx->cuda.cuModuleGetFunction(&f, module, "tvdb_cuda_stencil_scalar_d")))
    return err ? err->status : TVDB_ERROR_IO;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dsrc, src, (size_t)nx*ny*nz * sizeof(double), err)) != TVDB_OK) return st;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &ddst, NULL, (size_t)nx*ny*nz * sizeof(double), err)) != TVDB_OK) goto done;
  unsigned int gx = (unsigned int)((nx + 7) / 8), gy = (unsigned int)((ny + 7) / 8), gz = (unsigned int)nz;
  /* All four CUDA stencil kernels share one signature so the argument list can
   * never mismatch the kernel it is launched against -- that bug bit once, when
   * only the scalar->scalar kernel took `op` and the other three read the int*
   * as the float scale. */
  /* The fp64 kernel keeps its own (dsrc, ddst, nx, ny, nz, op, double scale)
   * signature; it is a different element type, not a different stencil family. */
  void* dargs[] = {&dsrc, &ddst, &nx, &ny, &nz, &op, &scale};
  if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel",
        ctx->cuda.cuLaunchKernel(f, gx, gy, gz, 8u, 8u, 1u, 0, NULL, dargs, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH",
        ctx->cuda.cuMemcpyDtoH(dst, ddst, (size_t)nx*ny*nz * sizeof(double)))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  st = TVDB_OK;
done:
  if (ddst) ctx->cuda.cuMemFree(ddst);
  if (dsrc) ctx->cuda.cuMemFree(dsrc);
  return st;
}

static tvdb_status_t tvdb_vk_csg_d(tvdb_gpu_context_t* ctx,
    const double* a, const double* b, double* dst, int nx, int ny, int nz, int op,
    tvdb_error_t* err) {
  if (!ctx->supports_shader_float64) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "device lacks shaderFloat64");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  tvdb_vk_buffer ba, bb, bout, bup;
  memset(&ba, 0, sizeof(ba)); memset(&bb, 0, sizeof(bb));
  memset(&bout, 0, sizeof(bout)); memset(&bup, 0, sizeof(bup));
  tvdb_status_t st;
  size_t n = (size_t)nx * (size_t)ny * (size_t)nz;
  size_t bytes = n * sizeof(double);
  if ((st = tvdb_vk_create_buffer(ctx, bytes, VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &ba, err)) != TVDB_OK) goto done;
  if ((st = tvdb_vk_create_buffer(ctx, bytes, VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bb, err)) != TVDB_OK) goto done_a;
  if ((st = tvdb_vk_create_buffer(ctx, bytes, VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bout, err)) != TVDB_OK) goto done_b;
  /* A single ivec4 is 16 bytes in std140. */
  if ((st = tvdb_vk_create_buffer(ctx, 16, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bup, err)) != TVDB_OK) goto done_out;
  memcpy(ba.mapped, a, bytes);
  memcpy(bb.mapped, b, bytes);
  typedef struct { int32_t dim[4]; } tvdb_csg_d_uniform;
  _Static_assert(sizeof(tvdb_csg_d_uniform) == 16, "std140: csg_d uniform is one ivec4");
  tvdb_csg_d_uniform par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = nx; par.dim[1] = ny; par.dim[2] = nz; par.dim[3] = op;
  memcpy(bup.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuCsgDSpv; d.spv_len = kTvdbGpuCsgDSpv_len; d.descriptor_count = 4;
  d.buffers[0] = &ba; d.buffers[1] = &bb; d.buffers[2] = &bout; d.buffers[3] = &bup;
  d.descriptor_types[0] = d.descriptor_types[1] = d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((nx + 7) / 8);
  d.group_y = (uint32_t)((ny + 7) / 8);
  d.group_z = (uint32_t)nz;
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(dst, bout.mapped, bytes);
  tvdb_vk_destroy_buffer(ctx, &bup);
done_out: tvdb_vk_destroy_buffer(ctx, &bout);
done_b: tvdb_vk_destroy_buffer(ctx, &bb);
done_a: tvdb_vk_destroy_buffer(ctx, &ba);
done:
  return st;
}

static tvdb_status_t tvdb_cuda_csg_d(tvdb_gpu_context_t* ctx,
    const double* a, const double* b, double* dst, int nx, int ny, int nz, int op,
    tvdb_error_t* err) {
  CUmodule module = NULL; CUfunction f = NULL;
  CUdeviceptr da = 0, db = 0, dd = 0;
  tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
  if (st != TVDB_OK) return st;
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction",
        ctx->cuda.cuModuleGetFunction(&f, module, "tvdb_cuda_csg_d")))
    return err ? err->status : TVDB_ERROR_IO;
  size_t bytes = (size_t)nx * ny * nz * sizeof(double);
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &da, a, bytes, err)) != TVDB_OK) return st;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &db, b, bytes, err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dd, NULL, bytes, err)) != TVDB_OK) goto done;
  unsigned int gx = (unsigned int)((nx + 7) / 8), gy = (unsigned int)((ny + 7) / 8), gz = (unsigned int)nz;
  void* dargs[] = {&da, &db, &dd, &nx, &ny, &nz, &op};
  if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel",
        ctx->cuda.cuLaunchKernel(f, gx, gy, gz, 8u, 8u, 1u, 0, NULL, dargs, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(dst, dd, bytes))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  st = TVDB_OK;
done:
  if (dd) ctx->cuda.cuMemFree(dd);
  if (db) ctx->cuda.cuMemFree(db);
  if (da) ctx->cuda.cuMemFree(da);
  return st;
}

static tvdb_status_t tvdb_vk_sample_d(tvdb_gpu_context_t* ctx,
    const double* grid, const double* pts, double* out, size_t npts,
    int nx, int ny, int nz, double ox, double oy, double oz, double vs,
    tvdb_error_t* err) {
  if (!ctx->supports_shader_float64) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "device lacks shaderFloat64");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  tvdb_vk_buffer bg, bp, bo, bup;
  memset(&bg, 0, sizeof(bg)); memset(&bp, 0, sizeof(bp));
  memset(&bo, 0, sizeof(bo)); memset(&bup, 0, sizeof(bup));
  tvdb_status_t st;
  size_t nv = (size_t)nx * (size_t)ny * (size_t)nz;
  if ((st = tvdb_vk_create_buffer(ctx, nv * sizeof(double), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bg, err)) != TVDB_OK) goto done;
  if ((st = tvdb_vk_create_buffer(ctx, npts * 3 * sizeof(double), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bp, err)) != TVDB_OK) goto done_g;
  if ((st = tvdb_vk_create_buffer(ctx, npts * sizeof(double), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto done_p;
  if ((st = tvdb_vk_create_buffer(ctx, 64, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bup, err)) != TVDB_OK) goto done_o;
  memcpy(bg.mapped, grid, nv * sizeof(double));
  memcpy(bp.mapped, pts, npts * 3 * sizeof(double));
  /* std140: ivec4 dim at 0..15, uint count at 16..19, and a double is
   * 8-aligned so the geometry starts at 24. Block size is 56; the buffer is
   * allocated at 64 to stay aligned for the next slice if this ever becomes a
   * strided binding. Asserted rather than assumed. */
  typedef struct { int32_t dim[4]; uint32_t count; double ox, oy, oz, vs; } tvdb_sample_d_uniform;
  _Static_assert(offsetof(tvdb_sample_d_uniform, count) == 16, "std140: count follows ivec4 dim");
  _Static_assert(offsetof(tvdb_sample_d_uniform, ox) == 24, "std140: double ox is 8-aligned after count");
  _Static_assert(sizeof(tvdb_sample_d_uniform) == 56, "sample_d uniform must be 56 bytes");
  tvdb_sample_d_uniform par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = nx; par.dim[1] = ny; par.dim[2] = nz; par.dim[3] = 0;
  par.count = (uint32_t)npts;
  par.ox = ox; par.oy = oy; par.oz = oz; par.vs = vs;
  memcpy(bup.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuSampleDSpv; d.spv_len = kTvdbGpuSampleDSpv_len; d.descriptor_count = 4;
  d.buffers[0] = &bg; d.buffers[1] = &bp; d.buffers[2] = &bo; d.buffers[3] = &bup;
  d.descriptor_types[0] = d.descriptor_types[1] = d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((npts + 127) / 128);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(out, bo.mapped, npts * sizeof(double));
  tvdb_vk_destroy_buffer(ctx, &bup);
done_o: tvdb_vk_destroy_buffer(ctx, &bo);
done_p: tvdb_vk_destroy_buffer(ctx, &bp);
done_g: tvdb_vk_destroy_buffer(ctx, &bg);
done:
  return st;
}

static tvdb_status_t tvdb_cuda_sample_d(tvdb_gpu_context_t* ctx,
    const double* grid, const double* pts, double* out, size_t npts,
    int nx, int ny, int nz, double ox, double oy, double oz, double vs,
    tvdb_error_t* err) {
  CUmodule module = NULL; CUfunction f = NULL;
  CUdeviceptr dg = 0, dp = 0, dd = 0;
  tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
  if (st != TVDB_OK) return st;
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction",
        ctx->cuda.cuModuleGetFunction(&f, module, "tvdb_cuda_sample_d")))
    return err ? err->status : TVDB_ERROR_IO;
  size_t gbytes = (size_t)nx * ny * nz * sizeof(double);
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dg, grid, gbytes, err)) != TVDB_OK) return st;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dp, pts, npts * 3 * sizeof(double), err)) != TVDB_OK) goto done;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &dd, NULL, npts * sizeof(double), err)) != TVDB_OK) goto done;
  unsigned int gx = (unsigned int)((npts + 127) / 128);
  void* dargs[] = {&dg, &dp, &dd, &nx, &ny, &nz, &ox, &oy, &oz, &vs, &npts};
  if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel",
        ctx->cuda.cuLaunchKernel(f, gx, 1u, 1u, 128u, 1u, 1u, 0, NULL, dargs, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out, dd, npts * sizeof(double)))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  st = TVDB_OK;
done:
  if (dd) ctx->cuda.cuMemFree(dd);
  if (dp) ctx->cuda.cuMemFree(dp);
  if (dg) ctx->cuda.cuMemFree(dg);
  return st;
}

tvdb_status_t tvdb_gpu_sample_trilinear_dense_d_batch(tvdb_gpu_context_t* ctx,
                                                     const tvdb_dense_grid_d* grid,
                                                     const double* points,
                                                     size_t npoints,
                                                     double* out_values,
                                                     tvdb_error_t* err) {
  if (!ctx || !grid || !tvdb_gpu_shape_valid(grid->nx,grid->ny,grid->nz,grid->voxel_size,grid->data,sizeof(double)) ||
      !isfinite(grid->ox) || !isfinite(grid->oy) || !isfinite(grid->oz) || npoints > INT_MAX || !points || !out_values) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid sample_trilinear_dense_d_batch arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  for(size_t i=0;i<npoints;++i) {
    if(!isfinite(points[3*i]) || !isfinite(points[3*i+1]) || !isfinite(points[3*i+2])) {
      tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"nonfinite sample point");
      return TVDB_ERROR_INVALID_ARGUMENT;
    }
  }
  if (npoints == 0) return TVDB_OK;
  if (!tvdb_gpu_supports_fp64(ctx)) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "device does not support fp64");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  tvdb_status_t st = (ctx->backend == TVDB_GPU_BACKEND_CUDA)
      ? tvdb_cuda_sample_d(ctx, grid->data, points, out_values, npoints,
                           nx, ny, nz, grid->ox, grid->oy, grid->oz, grid->voxel_size, err)
      : tvdb_vk_sample_d(ctx, grid->data, points, out_values, npoints,
                         nx, ny, nz, grid->ox, grid->oy, grid->oz, grid->voxel_size, err);
  if (st == TVDB_OK) return TVDB_OK;
  /* Fall back to the CPU reference point by point so a device without fp64
   * still produces the documented result. */
  for (size_t i = 0; i < npoints; ++i)
    out_values[i] = tvdb_sample_trilinear_dense_d(grid, points[3*i], points[3*i+1], points[3*i+2]);
  return TVDB_OK;
}

static tvdb_status_t tvdb_gpu_csg_dense_d_impl(tvdb_gpu_context_t* ctx,
                                   const tvdb_dense_grid_d* a,
                                   const tvdb_dense_grid_d* b,
                                   int op,
                                   tvdb_dense_grid_d* result,
                                   tvdb_error_t* err) {
  if (!ctx || !a || !a->data || !b || !b->data || !result || op < 0 || op > 2) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid csg_dense_d arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (a->nx != b->nx || a->ny != b->ny || a->nz != b->nz) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "csg_dense_d shape mismatch");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (!tvdb_gpu_supports_fp64(ctx)) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "device does not support fp64");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  int nx = a->nx, ny = a->ny, nz = a->nz;
  size_t n = (size_t)nx * (size_t)ny * (size_t)nz;
  size_t bytes = n * sizeof(double);
  result->nx = nx; result->ny = ny; result->nz = nz;
  result->ox = a->ox; result->oy = a->oy; result->oz = a->oz;
  result->voxel_size = a->voxel_size;
  result->data = (double*)malloc(bytes);
  if (!result->data) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }

  tvdb_status_t st = (ctx->backend == TVDB_GPU_BACKEND_CUDA)
      ? tvdb_cuda_csg_d(ctx, a->data, b->data, result->data, nx, ny, nz, op, err)
      : tvdb_vk_csg_d(ctx, a->data, b->data, result->data, nx, ny, nz, op, err);
  if (st == TVDB_OK) return TVDB_OK;
  /* Fall back to the CPU reference so a device without fp64, or a driver that
   * cannot bind the buffers, still produces the documented result rather than an
   * error the caller has to special-case. */
  free(result->data); result->data = (double*)malloc(bytes);
  if (!result->data) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  if (op == 0)      tvdb_csg_union_d(a, b, result);
  else if (op == 1) tvdb_csg_intersection_d(a, b, result);
  else              tvdb_csg_difference_d(a, b, result);
  return TVDB_OK;
}

static tvdb_status_t tvdb_gpu_stencil_scalar_d_impl(tvdb_gpu_context_t* ctx,
                                        const tvdb_dense_grid_d* in,
                                        int op,
                                        tvdb_dense_grid_d* out,
                                        tvdb_error_t* err) {
  if (!ctx || !in || !in->data || !out || op < 0 || op > 3) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid stencil_scalar_d arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (!tvdb_gpu_supports_fp64(ctx)) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "device does not support fp64");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  int nx = in->nx, ny = in->ny, nz = in->nz;
  size_t n = (size_t)nx * (size_t)ny * (size_t)nz;
  double h = in->voxel_size;
  double scale = (op == 0) ? 1.0 / (h * h) : 1.0 / (2.0 * h);
  size_t bytes = n * sizeof(double);
  out->nx = nx; out->ny = ny; out->nz = nz;
  out->ox = in->ox; out->oy = in->oy; out->oz = in->oz; out->voxel_size = in->voxel_size;
  out->data = (double*)malloc(bytes);
  if (!out->data) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    tvdb_status_t cs = tvdb_cuda_stencil_d(ctx, in->data, out->data, nx, ny, nz, op, scale, err);
    if (cs == TVDB_OK) return TVDB_OK;
    free(out->data); out->data = (double*)malloc(bytes);
    if (!out->data) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
    tvdb_cpu_stencil_scalar_d(in, op, out);
    return TVDB_OK;
  }
  tvdb_status_t vs = tvdb_vk_stencil_d(ctx, in->data, out->data, nx, ny, nz, op, scale, err);
  if (vs != TVDB_OK) { free(out->data); out->data = NULL; }
  return vs;
}

static tvdb_status_t tvdb_gpu_gradient_impl(tvdb_gpu_context_t* ctx,
                                const tvdb_dense_grid* in,
                                tvdb_dense_vec_grid* out,
                                tvdb_error_t* err) {
  if (!ctx || !in || !in->data || !out) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid gradient arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if ((tvdb_init_out_vec(out, in->nx, in->ny, in->nz, in->voxel_size, in->ox, in->oy, in->oz, err)) != TVDB_OK)
    return TVDB_ERROR_OUT_OF_MEMORY;
  size_t n = (size_t)in->nx * (size_t)in->ny * (size_t)in->nz;
  float h = in->voxel_size;
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    tvdb_status_t cs = tvdb_cuda_stencil2d(ctx, "tvdb_cuda_stencil_scalar_vec",
        in->data, n, 1, out->data, n * 3u, 3, in->nx, in->ny, in->nz, 0, 1.0f / (2.0f * h), in->ox, in->oy, in->oz, in->voxel_size, err);
    if (cs == TVDB_OK) return TVDB_OK;
    /* No stderr: this is a library. The fallback is documented in tinyvdb_gpu.h. */
    free(out->data); out->data = NULL;
    if ((tvdb_init_out_vec(out, in->nx, in->ny, in->nz, in->voxel_size, in->ox, in->oy, in->oz, err)) != TVDB_OK)
      return TVDB_ERROR_OUT_OF_MEMORY;
    tvdb_gradient(in, out);
    return TVDB_OK;
  }
  return tvdb_vk_stencil2d(ctx, kTvdbGpuStencilScalarVecSpv, kTvdbGpuStencilScalarVecSpv_len,
                           in->data, n, 1, out->data, n * 3u, 3,
                           in->nx, in->ny, in->nz, 0, 1.0f / (2.0f * h), in->ox, in->oy, in->oz, in->voxel_size, err);
}

static tvdb_status_t tvdb_gpu_magnitude_impl(tvdb_gpu_context_t* ctx,
                                 const tvdb_dense_vec_grid* in,
                                 tvdb_dense_grid* out,
                                 tvdb_error_t* err) {
  if (!ctx || !in || !in->data || !out) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid magnitude arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if ((tvdb_gpu_init_out_grid(out, in->nx, in->ny, in->nz, in->voxel_size, in->ox, in->oy, in->oz, err)) != TVDB_OK)
    return TVDB_ERROR_OUT_OF_MEMORY;
  size_t n = (size_t)in->nx * (size_t)in->ny * (size_t)in->nz;
  float h = in->voxel_size;
  tvdb_status_t st;
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA)
    st = tvdb_cuda_stencil2d(ctx, "tvdb_cuda_stencil_vec_scalar",
        in->data, n * 3u, 3, out->data, n, 1, in->nx, in->ny, in->nz, 1, 1.0f,
        in->ox, in->oy, in->oz, in->voxel_size, err);
  else
    st = tvdb_vk_stencil2d(ctx, kTvdbGpuStencilVecScalarSpv, kTvdbGpuStencilVecScalarSpv_len,
        in->data, n * 3u, 3, out->data, n, 1, in->nx, in->ny, in->nz, 1, 1.0f,
        in->ox, in->oy, in->oz, in->voxel_size, err);
  if (st != TVDB_OK) { free(out->data); out->data = NULL; return st; }
  return TVDB_OK;
}

static tvdb_status_t tvdb_gpu_normalize_vec_impl(tvdb_gpu_context_t* ctx,
                                     const tvdb_dense_vec_grid* in,
                                     tvdb_dense_vec_grid* out,
                                     tvdb_error_t* err) {
  if (!ctx || !in || !in->data || !out) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid normalize_vec arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if ((tvdb_init_out_vec(out, in->nx, in->ny, in->nz, in->voxel_size, in->ox, in->oy, in->oz, err)) != TVDB_OK)
    return TVDB_ERROR_OUT_OF_MEMORY;
  size_t n = (size_t)in->nx * (size_t)in->ny * (size_t)in->nz;
  tvdb_status_t st;
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA)
    st = tvdb_cuda_stencil2d(ctx, "tvdb_cuda_stencil_vec_vec",
        in->data, n * 3u, 3, out->data, n * 3u, 3, in->nx, in->ny, in->nz, 1, 1.0f,
        in->ox, in->oy, in->oz, in->voxel_size, err);
  else
    st = tvdb_vk_stencil2d(ctx, kTvdbGpuStencilVecVecSpv, kTvdbGpuStencilVecVecSpv_len,
        in->data, n * 3u, 3, out->data, n * 3u, 3, in->nx, in->ny, in->nz, 1, 1.0f,
        in->ox, in->oy, in->oz, in->voxel_size, err);
  if (st != TVDB_OK) { free(out->data); out->data = NULL; return st; }
  return TVDB_OK;
}

static tvdb_status_t tvdb_gpu_cpt_impl(tvdb_gpu_context_t* ctx,
                           const tvdb_dense_grid* in,
                           tvdb_dense_vec_grid* out,
                           tvdb_error_t* err) {
  if (!ctx || !in || !in->data || !out) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid cpt arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if ((tvdb_init_out_vec(out, in->nx, in->ny, in->nz, in->voxel_size, in->ox, in->oy, in->oz, err)) != TVDB_OK)
    return TVDB_ERROR_OUT_OF_MEMORY;
  size_t n = (size_t)in->nx * (size_t)in->ny * (size_t)in->nz;
  float h = in->voxel_size;
  tvdb_status_t st;
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA)
    st = tvdb_cuda_stencil2d(ctx, "tvdb_cuda_stencil_scalar_vec",
        in->data, n, 1, out->data, n * 3u, 3, in->nx, in->ny, in->nz, 1, 1.0f / (2.0f * h),
        in->ox, in->oy, in->oz, in->voxel_size, err);
  else
    st = tvdb_vk_stencil2d(ctx, kTvdbGpuStencilScalarVecSpv, kTvdbGpuStencilScalarVecSpv_len,
        in->data, n, 1, out->data, n * 3u, 3, in->nx, in->ny, in->nz, 1, 1.0f / (2.0f * h),
        in->ox, in->oy, in->oz, in->voxel_size, err);
  if (st != TVDB_OK) { free(out->data); out->data = NULL; return st; }
  return TVDB_OK;
}

/* Mean curvature flow, `iterations` Jacobi steps. The CPU reference is Jacobi
 * (each step reads a snapshot), so this is `iterations` dispatches ping-ponging
 * two device buffers rather than any in-place dependency. */
static tvdb_status_t tvdb_mcf_vk(tvdb_gpu_context_t* ctx, const float* src, float* dst,
                                 int nx, int ny, int nz, float h, float dt,
                                 size_t n, int iterations, tvdb_error_t* err) {
  tvdb_vk_buffer ha, hb, hp, da, db;
  memset(&ha, 0, sizeof(ha)); memset(&hb, 0, sizeof(hb)); memset(&hp, 0, sizeof(hp));
  memset(&da, 0, sizeof(da)); memset(&db, 0, sizeof(db));
  VkDescriptorSet sets[2] = { VK_NULL_HANDLE, VK_NULL_HANDLE };
  int on_device = 0;
  tvdb_status_t st;
  size_t bytes = n * sizeof(float);
  const VkFlags staging_usage = VK_BUFFER_USAGE_STORAGE_BUFFER_BIT | VK_BUFFER_USAGE_TRANSFER_SRC_BIT | VK_BUFFER_USAGE_TRANSFER_DST_BIT;
  if ((st = tvdb_vk_create_buffer(ctx, bytes, staging_usage, &ha, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, bytes, staging_usage, &hb, err)) != TVDB_OK) goto done_a;
  if ((st = tvdb_vk_create_buffer(ctx, 32, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT | VK_BUFFER_USAGE_TRANSFER_SRC_BIT, &hp, err)) != TVDB_OK) goto done_b;
  memcpy(ha.mapped, src, bytes);

  /* std140, 32 bytes: ivec4 dim @0, float h @16, float dt @20. Constant across
   * every iteration, which is what makes a single upload and a single wait safe. */
  {
    typedef struct { int32_t dim[4]; float h; float dt; uint32_t pad[2]; } tvdb_mcf_uniform;
    _Static_assert(offsetof(tvdb_mcf_uniform, h) == 16, "std140: float h follows ivec4 dim");
    _Static_assert(offsetof(tvdb_mcf_uniform, dt) == 20, "std140: float dt follows h");
    tvdb_mcf_uniform par;
    memset(&par, 0, sizeof(par));
    par.dim[0] = nx; par.dim[1] = ny; par.dim[2] = nz;
    par.h = h; par.dt = dt;
    memcpy(hp.mapped, &par, sizeof(par));
  }

  /* The whole point of the device-local path: stage the grid in once, iterate
   * entirely in device memory, stage out once. Each iteration otherwise re-reads
   * the whole grid across PCIe, which at 262144 voxels is ~21 MB and measured at
   * about 13 GB/s -- the dominant cost once the fence wait was removed. */
  /* Gated on grid size. The stage-in/stage-out are two extra full-buffer copies
   * regardless of size, so they only pay once the per-iteration re-read traffic
   * dominates. Interleaved A/B, 256 iterations, mean curvature flow on Vulkan:
   *   16^3 (4096 vox)   226-234 ms -> 231-241 ms   (2-4% worse: pure overhead)
   *   32^3 (32768 vox)  234-239 ms -> 237-257 ms   (neutral)
   *   64^3 (262144 vox) 504-557 ms -> 252-256 ms   (2.0x better)
   * The threshold sits between 32^3 and 64^3. */
  /* Allocation success is tracked separately from the choice to use the device
     path. Chaining two allocations into one condition and then clearing
     `on_device` on failure leaked the first buffer: the cleanup is guarded by
     `on_device`, so a partial success destroyed nothing. Under memory pressure
     that is exactly the case that happens, so the leak fires when it can least
     be afforded. */
  int have_da = 0, have_db = 0;
  if (n >= TVDB_VK_DEVICE_STAGING_MIN_VOXELS) {
    if ((st = tvdb_vk_create_device_buffer(ctx, bytes, &da, err)) == TVDB_OK) have_da = 1;
    if (have_da && (st = tvdb_vk_create_device_buffer(ctx, bytes, &db, err)) == TVDB_OK) have_db = 1;
    on_device = (have_da && have_db);
  }
  if (!on_device && err) memset(err, 0, sizeof(*err));
  if (on_device) {
    tvdb_vk_copy pre[1] = {{0}};
    pre[0].src = ha.buffer; pre[0].dst = da.buffer; pre[0].size = bytes;
    pre[0].src_stage = VK_PIPELINE_STAGE_HOST_BIT; pre[0].src_access = VK_ACCESS_HOST_WRITE_BIT;
    pre[0].dst_stage = VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT; pre[0].dst_access = VK_ACCESS_SHADER_READ_BIT;
    if ((st = tvdb_vk_run_copies(ctx, pre, 1, err)) != TVDB_OK) goto done_p;
  }

  /* Two descriptor sets, one per ping-pong phase, written once: the step reads
   * the "in" buffer and writes the "out" buffer, and the phases swap which
   * buffer is which. */
  const uint32_t types[3] = { VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,
                              VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER };
  {
    VkDescriptorSetLayout layout = VK_NULL_HANDLE;
    int borrowed = 0;
    if ((st = tvdb_vk_make_layout(ctx, kTvdbGpuMeanCurvatureFlowSpv, kTvdbGpuMeanCurvatureFlowSpv_len, 3, types, &layout, &borrowed, err)) != TVDB_OK) goto done_p;
    const tvdb_vk_buffer* b0[3] = { on_device ? &da : &ha, on_device ? &db : &hb, &hp };
    const tvdb_vk_buffer* b1[3] = { on_device ? &db : &hb, on_device ? &da : &ha, &hp };
    st = tvdb_vk_make_set(ctx, layout, b0, types, 3, &sets[0], err);
    if (st == TVDB_OK) st = tvdb_vk_make_set(ctx, layout, b1, types, 3, &sets[1], err);
    if (layout && !borrowed && ctx->vk.DestroyDescriptorSetLayout)
      ctx->vk.DestroyDescriptorSetLayout(ctx->device, layout, NULL);
    if (st != TVDB_OK) goto done_p;
  }

  for (int it = 0; it < iterations; ++it) {
    tvdb_vk_dispatch_desc d;
    memset(&d, 0, sizeof(d));
    d.spv = kTvdbGpuMeanCurvatureFlowSpv; d.spv_len = kTvdbGpuMeanCurvatureFlowSpv_len; d.descriptor_count = 3;
    d.buffers[0] = on_device ? &da : &ha;
    d.buffers[1] = on_device ? &db : &hb;
    d.buffers[2] = &hp;
    d.descriptor_types[0] = d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    d.group_x = (uint32_t)((nx + 7) / 8);
    d.group_y = (uint32_t)((ny + 7) / 8);
    d.group_z = (uint32_t)nz;
    d.defer_wait = TVDB_VK_DEFERRED_SUBMIT;
    d.preset_set = sets[it & 1];
    if ((st = tvdb_vk_dispatch(ctx, &d, err)) != TVDB_OK) goto done_p;
  }
  if ((st = tvdb_vk_flush(ctx, err)) != TVDB_OK) goto done_p;

  if (on_device) {
    /* Stage the result back to the host-visible side, then read it. */
    const tvdb_vk_buffer* result = (iterations & 1) ? &db : &da;
    tvdb_vk_copy post[1] = {{0}};
    post[0].src = result->buffer; post[0].dst = ((iterations & 1) ? hb : ha).buffer; post[0].size = bytes;
    post[0].src_stage = VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT; post[0].src_access = VK_ACCESS_SHADER_WRITE_BIT;
    post[0].dst_stage = VK_PIPELINE_STAGE_HOST_BIT; post[0].dst_access = VK_ACCESS_HOST_READ_BIT;
    if ((st = tvdb_vk_run_copies(ctx, post, 1, err)) != TVDB_OK) goto done_p;
  }
  memcpy(dst, (iterations & 1 ? hb : ha).mapped, bytes);
  st = TVDB_OK;
done_p:
  for (int i = 0; i < 2; ++i)
    if (sets[i] && ctx->vk.FreeDescriptorSets) ctx->vk.FreeDescriptorSets(ctx->device, ctx->desc_pool, 1, &sets[i]);
  /* Guarded by what was actually allocated, not by which path was taken.
     tvdb_vk_destroy_buffer is a no-op on a zeroed tvdb_vk_buffer. */
  if (have_db) tvdb_vk_destroy_buffer(ctx, &db);
  if (have_da) tvdb_vk_destroy_buffer(ctx, &da);
  tvdb_vk_destroy_buffer(ctx, &hp);
done_b: tvdb_vk_destroy_buffer(ctx, &hb);
done_a: tvdb_vk_destroy_buffer(ctx, &ha);
  return st;
}

static tvdb_status_t tvdb_mcf_cuda(tvdb_gpu_context_t* ctx, const float* src, float* dst,
                                   int nx, int ny, int nz, float h, float dt,
                                   size_t n, int iterations, tvdb_error_t* err) {
  CUmodule module = NULL; CUfunction f = NULL;
  CUdeviceptr d0 = 0, d1 = 0;
  tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
  if (st != TVDB_OK) return st;
  if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction",
        ctx->cuda.cuModuleGetFunction(&f, module, "tvdb_cuda_mean_curvature_flow")))
    return err ? err->status : TVDB_ERROR_IO;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &d0, src, n * sizeof(float), err)) != TVDB_OK) return st;
  if ((st = tvdb_cuda_alloc_copy_in(ctx, &d1, NULL, n * sizeof(float), err)) != TVDB_OK) goto done;
  unsigned int gx = (unsigned int)((nx + 7) / 8), gy = (unsigned int)((ny + 7) / 8), gz = (unsigned int)nz;
  /* All iterations are launched before a single synchronise, mirroring the
   * Vulkan deferred-submit path. Launches go to the NULL stream, which executes
   * in order, so the iteration sequence is respected without a per-step wait --
   * and a per-step wait was measured at the same ~2.3 ms it costs on Vulkan. */
  CUdeviceptr in = d0, out = d1;
  for (int it = 0; it < iterations; ++it) {
    void* args[] = {&in, &out, &nx, &ny, &nz, &h, &dt};
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel",
          ctx->cuda.cuLaunchKernel(f, gx, gy, gz, 8u, 8u, 1u, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
    CUdeviceptr t = in; in = out; out = t;
  }
  if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(dst, in, n * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
  st = TVDB_OK;
done:
  if (d1) ctx->cuda.cuMemFree(d1);
  if (d0) ctx->cuda.cuMemFree(d0);
  return st;
}

tvdb_status_t tvdb_gpu_mean_curvature_flow(tvdb_gpu_context_t* ctx,
                                           const tvdb_dense_grid* in,
                                           float dt, int iterations,
                                           tvdb_dense_grid* out,
                                           tvdb_error_t* err) {
  if (!ctx || !in || !in->data || !out || iterations < 1) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid mean_curvature_flow arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  /* The CPU is a no-op below 3 in any axis, so the GPU is too. */
  if (in->nx < 3 || in->ny < 3 || in->nz < 3) {
    if ((tvdb_gpu_init_out_grid(out, in->nx, in->ny, in->nz, in->voxel_size, in->ox, in->oy, in->oz, err)) != TVDB_OK)
      return TVDB_ERROR_OUT_OF_MEMORY;
    memcpy(out->data, in->data, (size_t)in->nx * in->ny * in->nz * sizeof(float));
    return TVDB_OK;
  }
  size_t n = (size_t)in->nx * (size_t)in->ny * (size_t)in->nz;
  if ((tvdb_gpu_init_out_grid(out, in->nx, in->ny, in->nz, in->voxel_size, in->ox, in->oy, in->oz, err)) != TVDB_OK)
    return TVDB_ERROR_OUT_OF_MEMORY;
  float h = in->voxel_size;
  tvdb_status_t st = (ctx->backend == TVDB_GPU_BACKEND_CUDA)
    ? tvdb_mcf_cuda(ctx, in->data, out->data, in->nx, in->ny, in->nz, h, dt, n, iterations, err)
    : tvdb_mcf_vk(ctx, in->data, out->data, in->nx, in->ny, in->nz, h, dt, n, iterations, err);
  if (st != TVDB_OK) { free(out->data); out->data = NULL; }
  return st;
}

/* Fast sweeping (Eikonal fast sweeping), matching tvdb_fast_sweeping.
 *
 * The CPU is Gauss-Seidel, so a sweep is decomposed into wavefront planes: a
 * voxel at level L = dir.x*ix + dir.y*iy + dir.z*iz reads only levels below L, so
 * every voxel on one plane is independent. One dispatch per plane, in sweep
 * order, on a single in-order queue reproduces the sequential result exactly.
 * This is the workload that makes the deferred-submit path worth having: a 16^3
 * grid is 368 planes per iteration, and waiting per plane would be 368 blocking
 * waits at ~2.4 ms each.
 *
 * Because the planes are deferred, the host must not rewrite anything the GPU
 * still reads. Each plane's parameters differ (direction and level), so all of
 * them are uploaded once, up front, at 256-byte strides in a single uniform
 * buffer, and each plane gets its own pre-built descriptor set selecting its
 * slice. After that the host only issues dispatches. The only per-iteration host
 * write is resetting the change accumulator, which is safe because the previous
 * iteration is flushed first.
 *
 * max_change accumulates on the device with a single atomicMax, so an iteration
 * costs one readback rather than one per plane.
 */
/* is_d selects the fp64 twin. The two are the same wavefront decomposition over a
 * different element width, so they share this driver rather than duplicating
 * 200 lines of plane enumeration, descriptor pre-building and deferred submit;
 * every width-dependent quantity below is computed from `esz`/`is_d`.
 *
 * The one genuine asymmetry is the convergence accumulator. The fp32 shader
 * atomicMaxes the full 32-bit pattern and the host reads a float; the fp64 shader
 * can only atomicMax 32 bits (GLSL has no uint64_t and `union` is reserved), so
 * it tracks the high half of the pattern and the host reconstructs a value good
 * to 2^-20 relative. That is an underestimate, so convergence is detected up to
 * 1e-6 relative late and never early -- see tinyvdb_gpu_fast_sweeping_plane_d.comp.
 */
/* Rebuild a value from the high 32 bits of a non-negative double's IEEE-754
 * pattern, as tracked by tinyvdb_gpu_fast_sweeping_plane_d.comp: the high word is
 * sign(0) | exponent(11) | top 20 mantissa bits. Good to 2^-20 relative and always
 * an underestimate, which is the safe direction for `max_change <= tol`. */
static double tvdb_dbl_from_hi32(uint32_t hi) {
  if (hi == 0u) return 0.0;
  const double m = 1.0 + (double)(hi & 0xFFFFFu) / 1048576.0;   /* 2^20 */
  return ldexp(m, (int)(hi >> 20) - 1023);
}

static tvdb_status_t tvdb_fast_sweeping_vk(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                                           float frozen_band, int max_iters, float tol,
                                           int* out_iters, tvdb_error_t* err, int is_d) {
  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  const float h = grid->voxel_size > 0.0f ? grid->voxel_size : 1.0f;
  const size_t n = (size_t)nx * (size_t)ny * (size_t)nz;
  const float HUGE_VAL_F = 1e30f;
  const size_t esz = is_d ? sizeof(double) : sizeof(float);
  /* std140, 56 bytes: ivec4 dim @0, ivec4 dir @16, int level @32, float h @36,
   * float huge @40, uint nvox @44, two pad @48.
   * The fp64 block is 64 bytes: the two doubles are 8-aligned and land at 40 and
   * 48, with nvox at 56. Asserted rather than assumed -- the fp32 stencil's
   * assert has already caught this class of layout error twice. */
  typedef struct { int32_t dim[4]; int32_t dir[4]; int32_t level; float h; float huge;
                   uint32_t nvox; uint32_t pad0; uint32_t pad1; } tvdb_fs_uniform;
  typedef struct { int32_t dim[4]; int32_t dir[4]; int32_t level; int32_t pad0;
                   double h; double huge; uint32_t nvox; uint32_t pad1; } tvdb_fsd_uniform;
  _Static_assert(sizeof(tvdb_fs_uniform) == 56, "fast-sweeping uniform must be 56 bytes");
  _Static_assert(offsetof(tvdb_fs_uniform, dir) == 16, "std140: ivec4 dir follows ivec4 dim");
  _Static_assert(offsetof(tvdb_fs_uniform, level) == 32, "std140: level follows the two ivec4s");
  _Static_assert(offsetof(tvdb_fs_uniform, h) == 36, "std140: h follows level");
  _Static_assert(offsetof(tvdb_fs_uniform, huge) == 40, "std140: huge follows h");
  _Static_assert(offsetof(tvdb_fs_uniform, nvox) == 44, "std140: nvox follows huge");
  _Static_assert(offsetof(tvdb_fsd_uniform, h) == 40, "std140: fp64 h follows level + pad0");
  _Static_assert(offsetof(tvdb_fsd_uniform, huge) == 48, "std140: fp64 huge follows h");
  _Static_assert(offsetof(tvdb_fsd_uniform, nvox) == 56, "std140: fp64 nvox follows huge");
  _Static_assert(sizeof(tvdb_fsd_uniform) == 64, "fp64 fast-sweeping uniform must be 64 bytes");
  enum { TVDB_FS_STRIDE = 256 };
  /* The sentinel the parameter block tells the shader to seed |phi| with, mirrored
   * here so the write-back can recognise a voxel no sweep reached. Keep in step
   * with pd.huge / par.huge below. */
  const double HUGE_D_TVDB = 1e30;
  const float  HUGE_VAL_F_TVDB = 1e30f;
  const uint8_t* fs_spv = is_d ? kTvdbGpuFastSweepingPlaneDSpv : kTvdbGpuFastSweepingPlaneSpv;
  const size_t fs_spv_len = is_d ? kTvdbGpuFastSweepingPlaneDSpv_len : kTvdbGpuFastSweepingPlaneSpv_len;

  if (frozen_band < 0.0f) frozen_band = 0.0f;
  if (max_iters <= 0) max_iters = 1;

  /* The per-plane descriptor sets are allocated directly below, before any
   * dispatch has run, so the shared pool must exist first. */
  { tvdb_status_t ps = tvdb_vk_ensure_pools(ctx, err); if (ps != TVDB_OK) return ps; }

  static const int kDirs[8][3] = {
    { 1, 1, 1}, {-1, 1, 1}, { 1,-1, 1}, {-1,-1, 1},
    { 1, 1,-1}, {-1, 1,-1}, { 1,-1,-1}, {-1,-1,-1}
  };

  /* Enumerate the planes up front: this fixes every offset and count below. */
  int* plane_of = NULL;          /* not needed; kept for clarity of intent */
  int total_planes = 0;
  for (int d = 0; d < 8; ++d) {
    int dx = kDirs[d][0], dy = kDirs[d][1], dz = kDirs[d][2];
    int lo = (dx > 0 ? 0 : -(nx - 1)) + (dy > 0 ? 0 : -(ny - 1)) + (dz > 0 ? 0 : -(nz - 1));
    int hi = (dx > 0 ? nx - 1 : 0) + (dy > 0 ? ny - 1 : 0) + (dz > 0 ? nz - 1 : 0);
    total_planes += hi - lo + 1;
  }
  (void)plane_of;

  uint8_t* sign_pos = (uint8_t*)malloc(n);
  uint8_t* frozen = (uint8_t*)malloc(n);
  uint32_t* frozen32 = (uint32_t*)malloc(n * sizeof(uint32_t));
  void* absphi = malloc(n * esz);
  if (!sign_pos || !frozen || !frozen32 || !absphi) {
    free(sign_pos); free(frozen); free(frozen32); free(absphi);
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  for (size_t i = 0; i < n; ++i) {
    float v = grid->data[i];
    sign_pos[i] = (v >= 0.0f) ? 1u : 0u;
    float av = fabsf(v);
    int is_frozen = (av <= frozen_band);
    frozen[i] = (uint8_t)is_frozen;
    frozen32[i] = (uint32_t)is_frozen;
    /* The fp64 twin's inputs are still fp32 grids, so |phi| is staged by
       widening rather than by writing n doubles out of an fp32 array. */
    if (is_d) { double a = is_frozen ? (double)av : 1e30; ((double*)absphi)[i] = a; }
    else      { ((float*)absphi)[i] = is_frozen ? av : HUGE_VAL_F; }
  }

  tvdb_vk_buffer bphi, bfrz, bchg, bpar;
  memset(&bphi, 0, sizeof(bphi)); memset(&bfrz, 0, sizeof(bfrz));
  memset(&bchg, 0, sizeof(bchg)); memset(&bpar, 0, sizeof(bpar));
  VkDescriptorSet sets = VK_NULL_HANDLE;
  int nsets = 0;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, n * esz, VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bphi, err)) != TVDB_OK) goto done;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(uint32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bfrz, err)) != TVDB_OK) goto done_phi;
  if ((st = tvdb_vk_create_buffer(ctx, 4, VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bchg, err)) != TVDB_OK) goto done_frz;

  if ((st = tvdb_vk_create_buffer(ctx, (size_t)total_planes * TVDB_FS_STRIDE, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bpar, err)) != TVDB_OK) goto done_chg;
  memcpy(bphi.mapped, absphi, n * esz);
  /* The shader declares FrozenBuf as `uint frozen[]`, so std430 makes each
   * element four bytes. A byte-per-voxel upload would read four voxels' worth
   * of bytes at 4*gid, both mis-gathering the flag and running past the end of
   * the declared descriptor range. */
  memcpy(bfrz.mapped, frozen32, n * sizeof(uint32_t));
  ((float*)bchg.mapped)[0] = 0.0f;

  /* One descriptor set for the whole solve, bound to the parameter buffer as a
   * dynamic uniform; each plane selects its own 256-byte slice with the bind
   * dynamic offset. A set per plane (the previous shape) needed total_planes =
   * 8*(3N-2) sets -- 176 for an 8^3 grid, 944 at 40^3 -- drawn from the shared
   * pool whose maxSets is 1024, so every grid above 43 per axis failed with
   * VK_ERROR_OUT_OF_POOL_MEMORY. The test suite's largest case sat at 92% of the
   * limit, which is why it passed. One set removes the ceiling entirely and drops
   * 2 driver calls per plane per solve. */
  {
    const uint32_t types[4] = { VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,
                               VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER_DYNAMIC };
    /* Take the layout from the pipeline cache rather than making one here: the set
     * is bound with that pipeline's pipeline layout, and a set allocated from a
     * different (even identically defined) layout object crashes on some drivers. */
    tvdb_vk_pipeline_entry *pe = NULL;
    if ((st = tvdb_vk_get_pipeline(ctx, fs_spv, fs_spv_len, 4, types, &pe, NULL, err)) != TVDB_OK) goto done_sets;
    VkDescriptorSetLayout layout = pe->set_layout;
    /* Fill every plane's slice up front, then bind them all with one set. */
    {
      int p = 0;
      for (int d = 0; d < 8; ++d) {
        int dx = kDirs[d][0], dy = kDirs[d][1], dz = kDirs[d][2];
        int lo = (dx > 0 ? 0 : -(nx - 1)) + (dy > 0 ? 0 : -(ny - 1)) + (dz > 0 ? 0 : -(nz - 1));
        int hi = (dx > 0 ? nx - 1 : 0) + (dy > 0 ? ny - 1 : 0) + (dz > 0 ? nz - 1 : 0);
        for (int lvl = lo; lvl <= hi; ++lvl, ++p) {
          /* Both uniform shapes are filled field by field; only the width of h and
             huge differs, and the surrounding ints are at the same offsets. */
          if (is_d) {
            tvdb_fsd_uniform pd;
            memset(&pd, 0, sizeof(pd));
            pd.dim[0] = nx; pd.dim[1] = ny; pd.dim[2] = nz;
            pd.dir[0] = dx; pd.dir[1] = dy; pd.dir[2] = dz;
            pd.level = lvl; pd.h = (double)h; pd.huge = 1e30; pd.nvox = (uint32_t)n;
            memcpy((char*)bpar.mapped + (size_t)p * TVDB_FS_STRIDE, &pd, sizeof(pd));
          } else {
            tvdb_fs_uniform par;
            memset(&par, 0, sizeof(par));
            par.dim[0] = nx; par.dim[1] = ny; par.dim[2] = nz;
            par.dir[0] = dx; par.dir[1] = dy; par.dir[2] = dz;
            par.level = lvl; par.h = h; par.huge = HUGE_VAL_F; par.nvox = (uint32_t)n;
            memcpy((char*)bpar.mapped + (size_t)p * TVDB_FS_STRIDE, &par, sizeof(par));
          }
        }
      }
      /* The pipeline layout the cache hands back must be built from the same
       * descriptor types, so the layout has to be created with DYNAMIC above. */
      VkDescriptorSetAllocateInfo dsai;
      memset(&dsai, 0, sizeof(dsai));
      dsai.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
      dsai.descriptorPool = ctx->desc_pool;
      dsai.descriptorSetCount = 1;
      dsai.pSetLayouts = &layout;
      if (!tvdb_vk_ok(ctx->vk.AllocateDescriptorSets(ctx->device, &dsai, &sets), err, "vkAllocateDescriptorSets")) {
        st = err ? err->status : TVDB_ERROR_IO; goto done_sets_layout;
      }
      nsets = 1;
      VkDescriptorBufferInfo infos[4];
      VkWriteDescriptorSet wr[4];
      memset(infos, 0, sizeof(infos)); memset(wr, 0, sizeof(wr));
      for (int i = 0; i < 3; ++i) {
        infos[i].buffer = (i == 0 ? bphi.buffer : (i == 1 ? bchg.buffer : bfrz.buffer));
        infos[i].offset = 0;
        infos[i].offset = 0;
        infos[i].range = (i == 0 ? n * esz : (i == 1 ? 4u : n * sizeof(uint32_t)));
      }
      /* Dynamic binding: the descriptor covers exactly one slice at offset 0 and
       * the dispatch's dynamic offset selects the slice. The range must be the
       * slice, not the whole buffer -- a dynamic offset is added to the
       * descriptor's offset, so a whole-buffer range plus an offset runs past the
       * end of the allocation for every plane but the first. */
      infos[3].buffer = bpar.buffer;
      infos[3].offset = 0;
      infos[3].range = TVDB_FS_STRIDE;
      for (int i = 0; i < 4; ++i) {
        wr[i].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        wr[i].dstSet = sets;
        wr[i].dstBinding = (uint32_t)i;
        wr[i].descriptorCount = 1;
        wr[i].descriptorType = types[i];
        wr[i].pBufferInfo = &infos[i];
      }
      ctx->vk.UpdateDescriptorSets(ctx->device, 4, wr, 0, NULL);
    }
    /* The layout belongs to the pipeline cache and is released with the context. */
  }

  {
    int iter = 0;
    for (; iter < max_iters; ++iter) {
      ((uint32_t*)bchg.mapped)[0] = 0u;         /* safe: the previous iteration was flushed */
      for (int p = 0; p < total_planes; ++p) {
        tvdb_vk_dispatch_desc dd;
        memset(&dd, 0, sizeof(dd));
        dd.spv = fs_spv; dd.spv_len = fs_spv_len; dd.descriptor_count = 4;
        dd.buffers[0] = &bphi; dd.buffers[1] = &bchg; dd.buffers[2] = &bfrz; dd.buffers[3] = &bpar;
        dd.descriptor_types[0] = dd.descriptor_types[1] = dd.descriptor_types[2] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
        dd.descriptor_types[3] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER_DYNAMIC;
        dd.group_x = (uint32_t)((n + 63u) / 64u);
        dd.defer_wait = TVDB_VK_DEFERRED_SUBMIT;
        dd.preset_set = sets;
        dd.dynamic_offset = (uint32_t)p * TVDB_FS_STRIDE;
        if ((st = tvdb_vk_dispatch(ctx, &dd, err)) != TVDB_OK) goto done_sets;
      }
      if ((st = tvdb_vk_flush(ctx, err)) != TVDB_OK) goto done_sets;
      uint32_t bits;
      double max_change;
      memcpy(&bits, bchg.mapped, 4);
      if (is_d) max_change = tvdb_dbl_from_hi32(bits);
      else      { float f; memcpy(&f, &bits, 4); max_change = (double)f; }
      if (max_change <= (double)tol) { ++iter; break; }
    }
    /* Write back signed values. Frozen voxels are skipped entirely rather than
     * overwritten: the device buffer only ever holds |phi|, so copying it over
     * a frozen voxel would replace its original signed value with the positive
     * magnitude.
     *
     * A voxel no sweep ever reached is skipped for the same reason the CPU sweep
     * skips it: its |phi| is still the 1e30 sentinel the buffer was seeded with,
     * and writing that back would replace the caller's value with ~1e30 while
     * reporting success. That is exactly the band=0 case -- nothing is frozen, so
     * nothing can propagate -- which is what test_gpu_fast_sweeping's
     * band-zero-unsolved case pins down. */
    for (size_t i = 0; i < n; ++i) {
      if (frozen[i]) continue;
      if (is_d) { double a = ((const double*)bphi.mapped)[i];
                  if (a >= HUGE_D_TVDB * 0.5) continue;
                  grid->data[i] = (float)(sign_pos[i] ? a : -a); }
      else      { float  a = ((const float*)bphi.mapped)[i];
                  if (a >= HUGE_VAL_F_TVDB * 0.5f) continue;
                  grid->data[i] = sign_pos[i] ? a : -a; }
    }
    *out_iters = iter;
    st = TVDB_OK;
  }
done_sets_layout:
  if (nsets && sets && ctx->vk.FreeDescriptorSets)
    ctx->vk.FreeDescriptorSets(ctx->device, ctx->desc_pool, 1, &sets);
done_sets:
  tvdb_vk_destroy_buffer(ctx, &bpar);
done_chg:
  tvdb_vk_destroy_buffer(ctx, &bchg);
done_frz: tvdb_vk_destroy_buffer(ctx, &bfrz);
done_phi: tvdb_vk_destroy_buffer(ctx, &bphi);
done:
  free(sign_pos); free(frozen); free(frozen32); free(absphi);
  return st;
}

/* ---- persistent device-resident index map ---------------------------------- */

struct tvdb_gpu_index_map {
  tvdb_gpu_context_t* ctx;
  tvdb_gpu_backend_t backend;
  uint32_t cap;
  uint32_t mask;
  size_t   na;
  /* The active set itself, still needed by neighbor_counts (it iterates the
   * active voxels) and kept so the map is self-contained. */
  tvdb_vk_buffer bkeys, bvals, bact;
  CUdeviceptr dkeys, dvals, dact;
  /* Two descriptor sets, both built once against the device buffers, because the
   * three probe kernels do not agree on what bindings 2 and 3 mean:
   * index_probe and points_in_grid_probe read (2 = out, 3 = query), while
   * neighbor_counts_probe reads (2 = active, 3 = counts). One set would mean
   * rebinding binding 2 around every neighbor_counts call and hoping the other
   * two paths leave it in the shape they expect; two sets make each query
   * stateless. One layout, since the types are identical. */
  VkDescriptorSet set_io;    /* bindings 2=out, 3=in  */
  VkDescriptorSet set_agg;   /* bindings 2=in,  3=out */
  VkDescriptorSetLayout layout;
  int layout_borrowed;
  /* One pipeline per probe shader, created once, so a query does not go through
   * the dispatch helper's cache lookup and a create-then-destroy of a throwaway
   * pipeline per call. Three, not two: ijk_to_index and points_in_grid share a
   * descriptor *shape* but not a shader, and points_in_grid reads 4 floats per
   * point where ijk_to_index reads 3 ints, with a different uniform block. Sharing
   * slot 0 between them ran the index probe for points queries. */
  VkPipeline pipe[3];        /* 0 = index, 1 = neighbor counts, 2 = points */
  VkPipelineLayout pipelinelayout[3];
  /* Per-query scratch, allocated at build time and grown on demand.
   * bq/dq is the query payload and is written as 3 x int32 for ijk_to_index but
   * 4 x float for points_in_grid, so it is sized for the larger of the two.
   * bo/dout is the per-query int32 result. bout is separate and exactly na long,
   * because only neighbor_counts writes per-active-voxel output. */
  /* io scratch. The device side is DEVICE_LOCAL and the host side is a staging
   * pair, because a shader reading and writing 3 MB of HOST_VISIBLE_COHERENT
   * memory goes over the bus for every access: with host-visible scratch the
   * reusable query was a flat ~34 ms on Vulkan at *every* active-set size, which
   * is the signature of the transfer path rather than of the map. The map itself
   * was already device-local; the scratch was the part left behind. */
  tvdb_vk_buffer bq, bo;          /* host-visible staging */
  tvdb_vk_buffer bqd, bod;        /* device-local, what the shader touches */
  tvdb_vk_buffer bp, bout;        /* uniform; counts output */
  CUdeviceptr dq, dout, dpb;
  size_t io_cap;          /* elements the io scratch currently holds */
};

size_t tvdb_gpu_index_map_active_count(const tvdb_gpu_index_map_t* map) {
  return map ? map->na : 0;
}

static tvdb_status_t tvdb_index_map_upload_vulkan(tvdb_gpu_context_t* ctx,
    tvdb_gpu_index_map_t* m, const int32_t* keys, const int32_t* vals,
    const int32_t* act4, tvdb_error_t* err) {
  size_t kbytes = (size_t)m->cap * 3u * sizeof(int32_t);
  size_t vbytes = (size_t)m->cap * sizeof(int32_t);
  size_t abytes = (m->na ? m->na : 1) * 4u * sizeof(int32_t);
  /* DEVICE_LOCAL, not host-visible staging: the map is written once and then
   * only read, so there is nothing to gain from mapping it and a per-call
   * host-visible copy is exactly the cost this type exists to avoid. */
  tvdb_status_t st;
  if ((st = tvdb_vk_create_device_buffer(ctx, kbytes, &m->bkeys, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_device_buffer(ctx, vbytes, &m->bvals, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_device_buffer(ctx, abytes, &m->bact, err)) != TVDB_OK) return st;

  /* Stage the three uploads through a single host-visible scratch buffer, one
   * copy each, and do the transfers on a throwaway command buffer. */
  tvdb_vk_buffer stage;
  memset(&stage, 0, sizeof(stage));
  size_t maxb = kbytes > vbytes ? kbytes : vbytes;
  if (abytes > maxb) maxb = abytes;
  if ((st = tvdb_vk_create_buffer(ctx, maxb, VK_BUFFER_USAGE_TRANSFER_SRC_BIT, &stage, err)) != TVDB_OK) return st;

  tvdb_vk_copy copies[3];
  memset(copies, 0, sizeof(copies));
  VkDeviceSize off = 0;
  /* key copy */
  memcpy(stage.mapped, keys, kbytes);
  copies[0].src = stage.buffer; copies[0].dst = m->bkeys.buffer; copies[0].size = kbytes;
  copies[0].src_stage = VK_PIPELINE_STAGE_HOST_BIT; copies[0].src_access = VK_ACCESS_HOST_WRITE_BIT;
  copies[0].dst_stage = VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT; copies[0].dst_access = VK_ACCESS_SHADER_READ_BIT;
  off = 0;
  /* value copy reuses the same staging buffer */
  tvdb_vk_buffer stage2;
  memset(&stage2, 0, sizeof(stage2));
  if ((st = tvdb_vk_create_buffer(ctx, maxb, VK_BUFFER_USAGE_TRANSFER_SRC_BIT, &stage2, err)) != TVDB_OK) {
    tvdb_vk_destroy_buffer(ctx, &stage); return st;
  }
  memcpy(stage2.mapped, vals, vbytes);
  copies[1].src = stage2.buffer; copies[1].dst = m->bvals.buffer; copies[1].size = vbytes;
  copies[1].src_stage = VK_PIPELINE_STAGE_HOST_BIT; copies[1].src_access = VK_ACCESS_HOST_WRITE_BIT;
  copies[1].dst_stage = VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT; copies[1].dst_access = VK_ACCESS_SHADER_READ_BIT;
  tvdb_vk_buffer stage3;
  memset(&stage3, 0, sizeof(stage3));
  if ((st = tvdb_vk_create_buffer(ctx, maxb, VK_BUFFER_USAGE_TRANSFER_SRC_BIT, &stage3, err)) != TVDB_OK) {
    tvdb_vk_destroy_buffer(ctx, &stage); tvdb_vk_destroy_buffer(ctx, &stage2); return st;
  }
  memcpy(stage3.mapped, act4, abytes);
  copies[2].src = stage3.buffer; copies[2].dst = m->bact.buffer; copies[2].size = abytes;
  copies[2].src_stage = VK_PIPELINE_STAGE_HOST_BIT; copies[2].src_access = VK_ACCESS_HOST_WRITE_BIT;
  copies[2].dst_stage = VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT; copies[2].dst_access = VK_ACCESS_SHADER_READ_BIT;
  st = tvdb_vk_run_copies(ctx, copies, 3, err);
  tvdb_vk_destroy_buffer(ctx, &stage3);
  tvdb_vk_destroy_buffer(ctx, &stage2);
  tvdb_vk_destroy_buffer(ctx, &stage);
  (void)off;
  return st;
}

tvdb_status_t tvdb_gpu_index_map_create(tvdb_gpu_context_t* ctx,
                                        const int32_t* active, size_t na,
                                        tvdb_gpu_index_map_t** out, tvdb_error_t* err) {
  if (out) *out = NULL;
  if (!ctx || !out || !active || na == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid index_map_create arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  int32_t* keys = NULL; int32_t* vals = NULL; uint32_t cap = 0;
  tvdb_status_t st = tvdb_index_map_build(active, na, &keys, &vals, &cap, err);
  if (st != TVDB_OK) return st;
  int32_t* act4 = (int32_t*)malloc(na * 4u * sizeof(int32_t));
  tvdb_gpu_index_map_t* m = (tvdb_gpu_index_map_t*)calloc(1, sizeof(*m));
  if (!act4 || !m) {
    free(keys); free(vals); free(act4); free(m);
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  for (size_t i = 0; i < na; ++i) {
    act4[4*i+0] = active[3*i+0]; act4[4*i+1] = active[3*i+1];
    act4[4*i+2] = active[3*i+2]; act4[4*i+3] = 0;
  }
  m->ctx = ctx; m->backend = ctx->backend; m->cap = cap; m->mask = cap - 1u; m->na = na;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    /* tvdb_cuda_ok returns 1/0, not a tvdb_status_t (TVDB_OK is 0, so storing it
     * in one and comparing against TVDB_OK fails on success). */
    if (!tvdb_cuda_ok(ctx, err, "alloc", ctx->cuda.cuMemAlloc(&m->dkeys, (size_t)cap * 3u * sizeof(int32_t)))) goto cuda_fail;
    if (!tvdb_cuda_ok(ctx, err, "alloc", ctx->cuda.cuMemAlloc(&m->dvals, (size_t)cap * sizeof(int32_t)))) goto cuda_fail;
    if (!tvdb_cuda_ok(ctx, err, "alloc", ctx->cuda.cuMemAlloc(&m->dact, na * 4u * sizeof(int32_t)))) goto cuda_fail;
    if (!tvdb_cuda_ok(ctx, err, "h2d", ctx->cuda.cuMemcpyHtoD(m->dkeys, keys, (size_t)cap * 3u * sizeof(int32_t))) ||
        !tvdb_cuda_ok(ctx, err, "h2d", ctx->cuda.cuMemcpyHtoD(m->dvals, vals, (size_t)cap * sizeof(int32_t))) ||
        !tvdb_cuda_ok(ctx, err, "h2d", ctx->cuda.cuMemcpyHtoD(m->dact, act4, na * 4u * sizeof(int32_t))))
      goto cuda_fail;
    /* The io scratch has to exist before the first query, not be created on
     * demand: a query that finds the scratch "big enough" must find it
     * allocated, or it hands cuMemcpyHtoD a null pointer. */
    m->io_cap = na > (size_t)(1u << 20) ? na : (size_t)(1u << 20);
    if (!tvdb_cuda_ok(ctx, err, "alloc", ctx->cuda.cuMemAlloc(&m->dq, m->io_cap * 4u * sizeof(float)))) goto cuda_fail;
    if (!tvdb_cuda_ok(ctx, err, "alloc", ctx->cuda.cuMemAlloc(&m->dout, m->io_cap * sizeof(int32_t)))) goto cuda_fail;
    free(keys); free(vals); free(act4);
    *out = m;
    return TVDB_OK;
  cuda_fail:
    if (m->dkeys) ctx->cuda.cuMemFree(m->dkeys);
    if (m->dvals) ctx->cuda.cuMemFree(m->dvals);
    if (m->dact) ctx->cuda.cuMemFree(m->dact);
    free(keys); free(vals); free(act4); free(m);
    /* Never report success here: the status has to be a real error even if the
     * driver call did not fill `err`. */
    return (err && err->status != TVDB_OK) ? err->status : TVDB_ERROR_IO;
  }

  if ((st = tvdb_index_map_upload_vulkan(ctx, m, keys, vals, act4, err)) != TVDB_OK) {
    free(keys); free(vals); free(act4); free(m);
    return st;
  }
  free(keys); free(vals); free(act4);

  /* Query scratch, sized for a full-size batch; smaller batches reuse the front.
   *
   * tvdb_vk_ensure_pools first, for the same reason as in mesh_to_sdf: the two
   * descriptor sets are allocated below, before any dispatch in this call, so the
   * shared pool may not exist yet. Everything else in this function creates
   * buffers, which the device path does not need a pool for, so a build where
   * this is the first GPU call handed vkAllocateDescriptorSets a NULL pool and
   * segfaulted the driver. */
  { tvdb_status_t ps = tvdb_vk_ensure_pools(ctx, err); if (ps != TVDB_OK) goto vk_fail; }
  {
    /* 4 floats per point is the larger of the two query payload shapes. */
    m->io_cap = na > (size_t)(1u << 20) ? na : (size_t)(1u << 20);
    if ((st = tvdb_vk_create_buffer(ctx, m->io_cap * 4u * sizeof(float),
          VK_BUFFER_USAGE_STORAGE_BUFFER_BIT | VK_BUFFER_USAGE_TRANSFER_DST_BIT, &m->bq, err)) != TVDB_OK) goto vk_fail;
    if ((st = tvdb_vk_create_buffer(ctx, m->io_cap * sizeof(int32_t),
          VK_BUFFER_USAGE_STORAGE_BUFFER_BIT | VK_BUFFER_USAGE_TRANSFER_SRC_BIT, &m->bo, err)) != TVDB_OK) goto vk_fail;
    if ((st = tvdb_vk_create_device_buffer(ctx, m->io_cap * 4u * sizeof(float), &m->bqd, err)) != TVDB_OK) goto vk_fail;
    if ((st = tvdb_vk_create_device_buffer(ctx, m->io_cap * sizeof(int32_t), &m->bod, err)) != TVDB_OK) goto vk_fail;
    if ((st = tvdb_vk_create_buffer(ctx, na * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &m->bout, err)) != TVDB_OK) goto vk_fail;
    if ((st = tvdb_vk_create_buffer(ctx, 64, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &m->bp, err)) != TVDB_OK) goto vk_fail;
  }
  {
    const uint32_t types[5] = { VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,
                                VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,
                                VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER };
    if ((st = tvdb_vk_make_layout(ctx, kTvdbGpuIndexProbeSpv, kTvdbGpuIndexProbeSpv_len,
                                  5, types, &m->layout, &m->layout_borrowed, err)) != TVDB_OK) goto vk_fail;
    VkDescriptorSetAllocateInfo dsai;
    memset(&dsai, 0, sizeof(dsai));
    dsai.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
    dsai.descriptorPool = ctx->desc_pool;
    dsai.descriptorSetCount = 1;
    dsai.pSetLayouts = &m->layout;
    /* One layout per set, even though both sets use the same one.
     * VUID-VkDescriptorSetAllocateInfo-descriptorSetCount-00301 requires
     * descriptorSetCount to be <= the number of layouts in pSetLayouts, so a
     * 2-set allocation with a single-layout array is a validation violation --
     * and on this driver it is not a tidy error, it is a segfault inside
     * libnvidia-glcore. Passing the same layout twice costs nothing. */
    VkDescriptorSetLayout layout_pair[2] = { m->layout, m->layout };
    dsai.descriptorSetCount = 2;
    dsai.pSetLayouts = layout_pair;
    VkDescriptorSet pair[2] = { VK_NULL_HANDLE, VK_NULL_HANDLE };
    if (!tvdb_vk_ok(ctx->vk.AllocateDescriptorSets(ctx->device, &dsai, pair), err, "vkAllocateDescriptorSets")) {
      st = err ? err->status : TVDB_ERROR_IO; goto vk_fail;
    }
    m->set_io = pair[0]; m->set_agg = pair[1];
    VkDescriptorBufferInfo infos[5];
    VkWriteDescriptorSet wr[10];
    memset(infos, 0, sizeof(infos)); memset(wr, 0, sizeof(wr));
    /* bindings 0, 1 and 4 are identical for both sets */
    infos[0].buffer = m->bkeys.buffer; infos[0].range = (size_t)m->cap * 3u * sizeof(int32_t);
    infos[1].buffer = m->bvals.buffer; infos[1].range = (size_t)m->cap * sizeof(int32_t);
    infos[4].buffer = m->bp.buffer;  infos[4].range = 64u;
    /* Hoisted out of the per-set loop on purpose: the VkWriteDescriptorSet array
     * stores *pointers* to these, and a local array declared inside the loop body
     * would be dead by the time UpdateDescriptorSets reads it. That is a
     * use-after-scope, and the driver faulted on the garbage it read. */
    VkDescriptorBufferInfo local[2][5];
    int w = 0;
    for (int si = 0; si < 2; ++si) {
      /* set_io: 2 = output ints, 3 = query input. set_agg: 2 = active ivec4,
       * 3 = counts out. Ranges are refreshed by tvdb_index_map_ensure_io when
       * the scratch grows; the defaults here are the build-time sizes. */
      memcpy(local[si], infos, sizeof(infos));
      if (si == 0) { local[si][2].buffer = m->bod.buffer; local[si][2].range = m->io_cap * sizeof(int32_t);
                     local[si][3].buffer = m->bqd.buffer; local[si][3].range = m->io_cap * 4u * sizeof(float); }
      else         { local[si][2].buffer = m->bact.buffer; local[si][2].range = (m->na ? m->na : 1) * 4u * sizeof(int32_t);
                     local[si][3].buffer = m->bout.buffer; local[si][3].range = (m->na ? m->na : 1) * sizeof(int32_t); }
      for (int i = 0; i < 5; ++i) {
        wr[w].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        wr[w].dstSet = (si == 0) ? m->set_io : m->set_agg;
        wr[w].dstBinding = (uint32_t)i; wr[w].descriptorCount = 1;
        wr[w].descriptorType = types[i]; wr[w].pBufferInfo = &local[si][i];
        ++w;
      }
    }
    ctx->vk.UpdateDescriptorSets(ctx->device, (uint32_t)w, wr, 0, NULL);

    /* Two pipelines up front. ijk_to_index and points_in_grid share the index
     * probe; neighbor_counts has its own. Created here so a query is bind +
     * dispatch, and does not pay the dispatch helper's cache walk or a
     * create-then-destroy of a throwaway pipeline per call. */
    {
      struct { const uint8_t* spv; uint32_t len; int slot; } shapes[3] = {
        { kTvdbGpuIndexProbeSpv,           kTvdbGpuIndexProbeSpv_len,           0 },
        { kTvdbGpuNeighborCountsProbeSpv,  kTvdbGpuNeighborCountsProbeSpv_len,  1 },
        { kTvdbGpuPointsInGridProbeSpv,    kTvdbGpuPointsInGridProbeSpv_len,    2 },
      };
      for (int si = 0; si < 3; ++si) {
        VkShaderModuleCreateInfo smci;
        memset(&smci, 0, sizeof(smci));
        smci.sType = VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO;
        smci.codeSize = shapes[si].len; smci.pCode = (const uint32_t*)shapes[si].spv;
        VkShaderModule sh = VK_NULL_HANDLE;
        if (!tvdb_vk_ok(ctx->vk.CreateShaderModule(ctx->device, &smci, NULL, &sh), err, "vkCreateShaderModule")) {
          st = err ? err->status : TVDB_ERROR_IO; goto vk_fail; }
        VkPipelineLayoutCreateInfo plci;
        memset(&plci, 0, sizeof(plci));
        plci.sType = VK_STRUCTURE_TYPE_PIPELINE_LAYOUT_CREATE_INFO;
        plci.setLayoutCount = 1; plci.pSetLayouts = &m->layout;
        if (!tvdb_vk_ok(ctx->vk.CreatePipelineLayout(ctx->device, &plci, NULL, &m->pipelinelayout[si]), err, "vkCreatePipelineLayout")) {
          ctx->vk.DestroyShaderModule(ctx->device, sh, NULL);
          st = err ? err->status : TVDB_ERROR_IO; goto vk_fail; }
        VkComputePipelineCreateInfo cpci;
        memset(&cpci, 0, sizeof(cpci));
        cpci.sType = VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO;
        cpci.stage.sType = VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO;
        cpci.stage.stage = VK_SHADER_STAGE_COMPUTE_BIT;
        cpci.stage.module = sh; cpci.stage.pName = "main";
        cpci.layout = m->pipelinelayout[si];
        if (!tvdb_vk_ok(ctx->vk.CreateComputePipelines(ctx->device, VK_NULL_HANDLE, 1, &cpci, NULL, &m->pipe[si]), err, "vkCreateComputePipelines")) {
          ctx->vk.DestroyPipelineLayout(ctx->device, m->pipelinelayout[si], NULL);
          ctx->vk.DestroyShaderModule(ctx->device, sh, NULL);
          st = err ? err->status : TVDB_ERROR_IO; goto vk_fail; }
        ctx->vk.DestroyShaderModule(ctx->device, sh, NULL);   /* pipeline keeps it alive */
      }
    }
  }
  *out = m;
  return TVDB_OK;
vk_fail:
  for (int i = 0; i < 3; ++i) {
    if (m->pipe[i] && ctx->vk.DestroyPipeline) ctx->vk.DestroyPipeline(ctx->device, m->pipe[i], NULL);
    if (m->pipelinelayout[i] && ctx->vk.DestroyPipelineLayout) ctx->vk.DestroyPipelineLayout(ctx->device, m->pipelinelayout[i], NULL);
  }
  if (m->set_io != VK_NULL_HANDLE && ctx->vk.FreeDescriptorSets) {
    VkDescriptorSet one = m->set_io; ctx->vk.FreeDescriptorSets(ctx->device, ctx->desc_pool, 1, &one);
  }
  if (m->layout != VK_NULL_HANDLE && !m->layout_borrowed && ctx->vk.DestroyDescriptorSetLayout)
    ctx->vk.DestroyDescriptorSetLayout(ctx->device, m->layout, NULL);
  tvdb_vk_destroy_buffer(ctx, &m->bp);
  tvdb_vk_destroy_buffer(ctx, &m->bout);
  tvdb_vk_destroy_buffer(ctx, &m->bo);
  tvdb_vk_destroy_buffer(ctx, &m->bq);
  tvdb_vk_destroy_buffer(ctx, &m->bact);
  tvdb_vk_destroy_buffer(ctx, &m->bvals);
  tvdb_vk_destroy_buffer(ctx, &m->bkeys);
  free(m);
  return st;
}

void tvdb_gpu_index_map_destroy(tvdb_gpu_context_t* ctx, tvdb_gpu_index_map_t* m) {
  if (!m) return;
  if (!ctx) ctx = m->ctx;
  if (!ctx) { free(m); return; }
  { VkDescriptorSet pair[2] = { m->set_io, m->set_agg };
    uint32_t n = (pair[0] != VK_NULL_HANDLE ? 1u : 0u) + (pair[1] != VK_NULL_HANDLE ? 1u : 0u);
    if (n && ctx->vk.FreeDescriptorSets) ctx->vk.FreeDescriptorSets(ctx->device, ctx->desc_pool, n, pair); }
  for (int i = 0; i < 3; ++i) {
    if (m->pipe[i] && ctx->vk.DestroyPipeline) ctx->vk.DestroyPipeline(ctx->device, m->pipe[i], NULL);
    if (m->pipelinelayout[i] && ctx->vk.DestroyPipelineLayout) ctx->vk.DestroyPipelineLayout(ctx->device, m->pipelinelayout[i], NULL);
  }
  if (m->layout != VK_NULL_HANDLE && !m->layout_borrowed && ctx->vk.DestroyDescriptorSetLayout)
    ctx->vk.DestroyDescriptorSetLayout(ctx->device, m->layout, NULL);
  if (m->backend == TVDB_GPU_BACKEND_CUDA) {
    if (m->dkeys) ctx->cuda.cuMemFree(m->dkeys);
    if (m->dvals) ctx->cuda.cuMemFree(m->dvals);
    if (m->dact) ctx->cuda.cuMemFree(m->dact);
    if (m->dq) ctx->cuda.cuMemFree(m->dq);
    if (m->dout) ctx->cuda.cuMemFree(m->dout);
    if (m->dpb) ctx->cuda.cuMemFree(m->dpb);
  } else {
    tvdb_vk_destroy_buffer(ctx, &m->bp);
    tvdb_vk_destroy_buffer(ctx, &m->bout);
    tvdb_vk_destroy_buffer(ctx, &m->bod);
    tvdb_vk_destroy_buffer(ctx, &m->bqd);
    tvdb_vk_destroy_buffer(ctx, &m->bo);
    tvdb_vk_destroy_buffer(ctx, &m->bq);
    tvdb_vk_destroy_buffer(ctx, &m->bact);
    tvdb_vk_destroy_buffer(ctx, &m->bvals);
    tvdb_vk_destroy_buffer(ctx, &m->bkeys);
  }
  free(m);
}

/* Reusable-map queries. Same kernels and same contract as the per-call paths; the
 * only difference is that the map's device buffers and descriptor set already
 * exist, so a query is a small buffer upload, one dispatch and a readback. */

/* Make the io scratch hold at least `need` elements. `need` is the larger of the
 * query count and the active count, because the aggregate query (neighbor_counts)
 * writes per-active-voxel output through the same result buffer. */
static tvdb_status_t tvdb_index_map_ensure_io(tvdb_gpu_index_map_t* m, size_t need, tvdb_error_t* err) {
  tvdb_gpu_context_t* ctx = m->ctx;
  if (need <= m->io_cap) return TVDB_OK;
  /* Round up so a run of increasing sizes does not reallocate on every call. */
  size_t cap = m->io_cap ? m->io_cap : (size_t)(1u << 20);
  while (cap < need) cap <<= 1;
  if (m->backend == TVDB_GPU_BACKEND_CUDA) {
    if (m->dq) { ctx->cuda.cuMemFree(m->dq); m->dq = 0; }
    if (m->dout) { ctx->cuda.cuMemFree(m->dout); m->dout = 0; }
    if (!tvdb_cuda_ok(ctx, err, "alloc", ctx->cuda.cuMemAlloc(&m->dq, cap * 4u * sizeof(float)))) return TVDB_ERROR_OUT_OF_MEMORY;
    if (!tvdb_cuda_ok(ctx, err, "alloc", ctx->cuda.cuMemAlloc(&m->dout, cap * sizeof(int32_t)))) return TVDB_ERROR_OUT_OF_MEMORY;
    m->io_cap = cap;
    return TVDB_OK;
  }
  tvdb_vk_destroy_buffer(ctx, &m->bq);
  tvdb_vk_destroy_buffer(ctx, &m->bo);
  tvdb_vk_destroy_buffer(ctx, &m->bqd);
  tvdb_vk_destroy_buffer(ctx, &m->bod);
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, cap * 4u * sizeof(float),
        VK_BUFFER_USAGE_STORAGE_BUFFER_BIT | VK_BUFFER_USAGE_TRANSFER_DST_BIT, &m->bq, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, cap * sizeof(int32_t),
        VK_BUFFER_USAGE_STORAGE_BUFFER_BIT | VK_BUFFER_USAGE_TRANSFER_SRC_BIT, &m->bo, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_device_buffer(ctx, cap * 4u * sizeof(float), &m->bqd, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_device_buffer(ctx, cap * sizeof(int32_t), &m->bod, err)) != TVDB_OK) return st;
  m->io_cap = cap;
  /* The shader sees the device-side buffers; the host-visible pair is staging
   * only. Re-point binding 2 on set_io and bindings 2/3 on set_agg. */
  VkDescriptorBufferInfo io[1], agg[2];
  VkWriteDescriptorSet wr[3];
  memset(io, 0, sizeof(io)); memset(agg, 0, sizeof(agg)); memset(wr, 0, sizeof(wr));
  io[0].buffer = m->bod.buffer; io[0].range = cap * sizeof(int32_t);
  wr[0].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
  wr[0].dstSet = m->set_io; wr[0].dstBinding = 2; wr[0].descriptorCount = 1;
  wr[0].descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; wr[0].pBufferInfo = &io[0];
  agg[0].buffer = m->bact.buffer; agg[0].range = (m->na ? m->na : 1) * 4u * sizeof(int32_t);
  agg[1].buffer = m->bout.buffer; agg[1].range = (m->na ? m->na : 1) * sizeof(int32_t);
  for (int i = 0; i < 2; ++i) {
    wr[1+i].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
    wr[1+i].dstSet = m->set_agg; wr[1+i].dstBinding = (uint32_t)(i + 2); wr[1+i].descriptorCount = 1;
    wr[1+i].descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; wr[1+i].pBufferInfo = &agg[i];
  }
  ctx->vk.UpdateDescriptorSets(ctx->device, 3, wr, 0, NULL);
  return TVDB_OK;
}

/* Stage a query's payload into device memory and its result back out. The two
 * transfers are issued as one command buffer so a query costs one submit, not
 * two, which is the whole reason the reusable form is worth having. */
static tvdb_status_t tvdb_index_map_query_vulkan(tvdb_gpu_context_t* ctx,
    tvdb_gpu_index_map_t* m, const void* payload, size_t payload_bytes,
    const void* par, size_t par_bytes, int slot,
    uint32_t group_x, void* out, size_t out_bytes, tvdb_error_t* err) {
  /* payload may legitimately be empty: neighbor_counts takes no per-query
   * input, because the active set is already resident in device memory. A
   * zero-size copy and zero-size barriers are invalid, so the staging is
   * skipped entirely rather than issued with length 0. */
  if (payload_bytes) memcpy(m->bq.mapped, payload, payload_bytes);
  memcpy(m->bp.mapped, par, par_bytes);
  /* The aggregate probe writes its per-active-voxel counts to binding 3, which
   * set_agg binds to `bout`; the two io probes write to binding 2, which set_io
   * binds to the device-side result buffer. Picking the wrong one silently
   * produced an all-zero count buffer. */
  const tvdb_vk_buffer* res_dev = (slot == 1) ? &m->bout : &m->bod;
  const tvdb_vk_buffer* res_host = &m->bo;   /* both paths stage results here */
  VkCommandBufferAllocateInfo cbai;
  memset(&cbai, 0, sizeof(cbai));
  cbai.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
  cbai.commandPool = ctx->cmd_pool;
  cbai.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
  cbai.commandBufferCount = 1;
  VkCommandBuffer cmd = VK_NULL_HANDLE;
  if (!tvdb_vk_ok(ctx->vk.AllocateCommandBuffers(ctx->device, &cbai, &cmd), err, "vkAllocateCommandBuffers"))
    return err ? err->status : TVDB_ERROR_IO;
  VkCommandBufferBeginInfo begin;
  memset(&begin, 0, sizeof(begin));
  begin.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;
  begin.flags = VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT;
  if (!tvdb_vk_ok(ctx->vk.BeginCommandBuffer(cmd, &begin), err, "vkBeginCommandBuffer")) goto fail;
  if (payload_bytes) {
    VkBufferCopy bc;
    bc.srcOffset = 0; bc.dstOffset = 0; bc.size = payload_bytes;
    ctx->vk.CmdCopyBuffer(cmd, m->bq.buffer, m->bqd.buffer, 1, &bc);
    { VkBufferMemoryBarrier b;
      memset(&b, 0, sizeof(b));
      b.sType = VK_STRUCTURE_TYPE_BUFFER_MEMORY_BARRIER;
      b.srcAccessMask = VK_ACCESS_HOST_WRITE_BIT; b.dstAccessMask = VK_ACCESS_TRANSFER_READ_BIT;
      b.srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED; b.dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
      b.buffer = m->bq.buffer; b.offset = 0; b.size = payload_bytes;
      ctx->vk.CmdPipelineBarrier(cmd, VK_PIPELINE_STAGE_HOST_BIT, VK_PIPELINE_STAGE_TRANSFER_BIT, 0, 0, NULL, 1, &b, 0, NULL); }
    { VkBufferMemoryBarrier b;
      memset(&b, 0, sizeof(b));
      b.sType = VK_STRUCTURE_TYPE_BUFFER_MEMORY_BARRIER;
      b.srcAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT; b.dstAccessMask = VK_ACCESS_SHADER_READ_BIT;
      b.srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED; b.dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
      b.buffer = m->bqd.buffer; b.offset = 0; b.size = payload_bytes;
      ctx->vk.CmdPipelineBarrier(cmd, VK_PIPELINE_STAGE_TRANSFER_BIT, VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT, 0, 0, NULL, 1, &b, 0, NULL); }
  }
  { /* slot 1 is the aggregate probe and needs the other set; 0 and 2 are the io
     * probes and share set_io, which has 2=out and 3=in. */
    VkDescriptorSet set = (slot == 1) ? m->set_agg : m->set_io;
    ctx->vk.CmdBindPipeline(cmd, VK_PIPELINE_BIND_POINT_COMPUTE, m->pipe[slot]);
    ctx->vk.CmdBindDescriptorSets(cmd, VK_PIPELINE_BIND_POINT_COMPUTE, m->pipelinelayout[slot],
                                  0, 1, &set, 0, NULL); }
  ctx->vk.CmdDispatch(cmd, group_x, 1, 1);
  { VkBufferMemoryBarrier b;
    memset(&b, 0, sizeof(b));
    b.sType = VK_STRUCTURE_TYPE_BUFFER_MEMORY_BARRIER;
    b.srcAccessMask = VK_ACCESS_SHADER_WRITE_BIT; b.dstAccessMask = VK_ACCESS_TRANSFER_READ_BIT;
    b.srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED; b.dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
    b.buffer = res_dev->buffer; b.offset = 0; b.size = out_bytes;
    ctx->vk.CmdPipelineBarrier(cmd, VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT, VK_PIPELINE_STAGE_TRANSFER_BIT, 0, 0, NULL, 1, &b, 0, NULL); }
  { VkBufferCopy bc;
    bc.srcOffset = 0; bc.dstOffset = 0; bc.size = out_bytes;
    ctx->vk.CmdCopyBuffer(cmd, res_dev->buffer, res_host->buffer, 1, &bc); }
  { VkBufferMemoryBarrier b;
    memset(&b, 0, sizeof(b));
    b.sType = VK_STRUCTURE_TYPE_BUFFER_MEMORY_BARRIER;
    b.srcAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT; b.dstAccessMask = VK_ACCESS_HOST_READ_BIT;
    b.srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED; b.dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
    b.buffer = res_host->buffer; b.offset = 0; b.size = out_bytes;
    ctx->vk.CmdPipelineBarrier(cmd, VK_PIPELINE_STAGE_TRANSFER_BIT, VK_PIPELINE_STAGE_HOST_BIT, 0, 0, NULL, 1, &b, 0, NULL); }
  if (!tvdb_vk_ok(ctx->vk.EndCommandBuffer(cmd), err, "vkEndCommandBuffer")) goto fail;
  VkFenceCreateInfo fci;
  memset(&fci, 0, sizeof(fci));
  fci.sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO;
  VkFence fence = VK_NULL_HANDLE;
  if (!tvdb_vk_ok(ctx->vk.CreateFence(ctx->device, &fci, NULL, &fence), err, "vkCreateFence")) goto fail;
  { VkSubmitInfo si;
    memset(&si, 0, sizeof(si));
    si.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
    si.commandBufferCount = 1; si.pCommandBuffers = &cmd;
    if (!tvdb_vk_ok(ctx->vk.QueueSubmit(ctx->queue, 1, &si, fence), err, "vkQueueSubmit")) {
      ctx->vk.DestroyFence(ctx->device, fence, NULL); goto fail; } }
  if (!tvdb_vk_ok(ctx->vk.WaitForFences(ctx->device, 1, &fence, VK_TRUE, UINT64_MAX), err, "vkWaitForFences")) {
    ctx->vk.DestroyFence(ctx->device, fence, NULL); goto fail; }
  ctx->vk.DestroyFence(ctx->device, fence, NULL);
  if (ctx->vk.FreeCommandBuffers) ctx->vk.FreeCommandBuffers(ctx->device, ctx->cmd_pool, 1, &cmd);
  memcpy(out, res_host->mapped, out_bytes);
  return TVDB_OK;
fail:
  if (cmd && ctx->vk.FreeCommandBuffers) ctx->vk.FreeCommandBuffers(ctx->device, ctx->cmd_pool, 1, &cmd);
  return err ? err->status : TVDB_ERROR_IO;
}

tvdb_status_t tvdb_gpu_ijk_to_index_mapped(tvdb_gpu_context_t* ctx,
                                           const tvdb_gpu_index_map_t* cm,
                                           const int32_t* query, size_t nq,
                                           int32_t* out, tvdb_error_t* err) {
  if (!ctx || !cm || !query || !out || nq == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid ijk_to_index_mapped arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (cm->ctx != ctx) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "index map belongs to a different context");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_gpu_index_map_t* m = (tvdb_gpu_index_map_t*)cm;
  tvdb_status_t st;
  if (cm->backend == TVDB_GPU_BACKEND_CUDA) {
    if ((st = tvdb_index_map_ensure_io(m, nq > m->na ? nq : m->na, err)) != TVDB_OK) return st;
    if (!m->dpb) {
      unsigned int dummy = 0;
      if (!tvdb_cuda_ok(ctx, err, "alloc", ctx->cuda.cuMemAlloc(&m->dpb, 16))) return TVDB_ERROR_OUT_OF_MEMORY;
      (void)dummy;
    }
    CUmodule module = NULL; CUfunction f = NULL;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) return st;
    if (!tvdb_cuda_ok(ctx, err, "f", ctx->cuda.cuModuleGetFunction(&f, module, "tvdb_cuda_index_probe"))) return TVDB_ERROR_IO;
      if (!tvdb_cuda_ok(ctx, err, "h2d", ctx->cuda.cuMemcpyHtoD(m->dq, query, nq * 3u * sizeof(int32_t)))) return TVDB_ERROR_IO;
    unsigned int unq = (unsigned int)nq, ucap = m->cap, umask = m->mask, block = 128;
    void* args[] = {&m->dkeys, &m->dvals, &m->dout, &m->dq, &unq, &ucap, &umask};
    unsigned int grid = (unq + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "k", ctx->cuda.cuLaunchKernel(f, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) return TVDB_ERROR_IO;
    if (!tvdb_cuda_ok(ctx, err, "s", ctx->cuda.cuCtxSynchronize())) return TVDB_ERROR_IO;
    if (!tvdb_cuda_ok(ctx, err, "d2h", ctx->cuda.cuMemcpyDtoH(out, m->dout, nq * sizeof(int32_t)))) return TVDB_ERROR_IO;
    return TVDB_OK;
  }
  if ((st = tvdb_index_map_ensure_io(m, nq > m->na ? nq : m->na, err)) != TVDB_OK) return st;
  uint32_t par[4] = { (uint32_t)nq, m->cap, m->mask, 0u };
  return tvdb_index_map_query_vulkan(ctx, m, query, nq * 3u * sizeof(int32_t),
                                    par, sizeof(par), 0,
                                    (uint32_t)((nq + 127u) / 128u),
                                    out, nq * sizeof(int32_t), err);
}

tvdb_status_t tvdb_gpu_neighbor_counts_mapped(tvdb_gpu_context_t* ctx,
                                              const tvdb_gpu_index_map_t* cm,
                                              int connectivity,
                                              int32_t* out_counts,
                                              tvdb_error_t* err) {
  if (!ctx || !cm || !out_counts) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid neighbor_counts_mapped arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (cm->ctx != ctx) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "index map belongs to a different context");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  size_t na = cm->na;
  tvdb_gpu_index_map_t* m = (tvdb_gpu_index_map_t*)cm;
  tvdb_status_t st;
  if (cm->backend == TVDB_GPU_BACKEND_CUDA) {
    if ((st = tvdb_index_map_ensure_io(m, na, err)) != TVDB_OK) return st;
    CUmodule module = NULL; CUfunction f = NULL;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) return st;
    if (!tvdb_cuda_ok(ctx, err, "f", ctx->cuda.cuModuleGetFunction(&f, module, "tvdb_cuda_neighbor_counts_probe"))) return TVDB_ERROR_IO;
    unsigned int una = (unsigned int)na, ucap = m->cap, umask = m->mask, block = 128;
    void* args[] = {&m->dkeys, &m->dvals, &m->dout, &m->dact, &una, &connectivity, &ucap, &umask};
    unsigned int grid = (una + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "k", ctx->cuda.cuLaunchKernel(f, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) return TVDB_ERROR_IO;
    if (!tvdb_cuda_ok(ctx, err, "s", ctx->cuda.cuCtxSynchronize())) return TVDB_ERROR_IO;
    if (!tvdb_cuda_ok(ctx, err, "d2h", ctx->cuda.cuMemcpyDtoH(out_counts, m->dout, na * sizeof(int32_t)))) return TVDB_ERROR_IO;
    return TVDB_OK;
  }
  if ((st = tvdb_index_map_ensure_io(m, na, err)) != TVDB_OK) return st;
  { /* std140: na @0, connectivity @4, cap @8, mask @12 */
    uint32_t par[4] = { (uint32_t)na, (uint32_t)connectivity, m->cap, m->mask };
    return tvdb_index_map_query_vulkan(ctx, m, NULL, 0,
                                      par, sizeof(par), 1,
                                      (uint32_t)((na + 127u) / 128u),
                                      out_counts, na * sizeof(int32_t), err); }
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_points_in_grid_mapped(tvdb_gpu_context_t* ctx,
 const tvdb_gpu_index_map_t* cm,const float* points,size_t np,
 const float voxel_size[3],const float origin[3],int32_t* out,tvdb_error_t* err) {
  if(!ctx || !cm || cm->ctx!=ctx || (np && !out)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid mapped world query"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  int32_t* coords=NULL;
  tvdb_status_t st=tvdb_gpu_world_query_coords(points,np,voxel_size,origin,&coords,err);
  if(st!=TVDB_OK || !np) return st;
  st=tvdb_gpu_ijk_to_index_mapped(ctx,cm,coords,np,out,err);
  free(coords); return st;
}

/* fp64 twin of tvdb_gpu_fast_sweeping. The wavefront decomposition and the
 * deferred per-plane submit are shared with the fp32 path; the grids are fp32 in
 * and out, matching tvdb_fast_sweeping_d's own interface being fp64 -- see the
 * header for the one behavioural difference, the 2^-20 change accumulator. */
int tvdb_gpu_fast_sweeping_d(tvdb_gpu_context_t* ctx, tvdb_dense_grid_d* grid,
                             double frozen_band, int max_iters, double tol,
                             int* out_iters, tvdb_error_t* err) {
  if (out_iters) *out_iters = 0;
  if (!ctx || !grid || !grid->data) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid fast_sweeping_d arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    if (out_iters) *out_iters = tvdb_fast_sweeping_d(grid, frozen_band, max_iters, tol);
    return TVDB_OK;
  }
  if (kTvdbGpuFastSweepingPlaneDSpv_len == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED,
                       "fast_sweeping_d SPIR-V unavailable; rebuild with glslangValidator");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  if (!ctx->supports_shader_float64) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "device lacks shaderFloat64");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  /* The shared driver works on a tvdb_dense_grid, so the fp64 grid is copied into
   * an fp32 view rather than duplicating the driver. |phi| and the solve are done
   * in fp64 on the device; only the input and the written-back result are fp32. */
  tvdb_dense_grid view;
  view.nx = grid->nx; view.ny = grid->ny; view.nz = grid->nz;
  view.ox = grid->ox; view.oy = grid->oy; view.oz = grid->oz;
  view.voxel_size = grid->voxel_size;
  view.data = (float*)malloc((size_t)grid->nx * grid->ny * grid->nz * sizeof(float));
  if (!view.data) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  size_t n = (size_t)grid->nx * grid->ny * grid->nz;
  for (size_t i = 0; i < n; ++i) view.data[i] = (float)grid->data[i];
  int iters = 0;
  tvdb_status_t st = tvdb_fast_sweeping_vk(ctx, &view, (float)frozen_band, max_iters,
                                           (float)tol, &iters, err, 1);
  if (st == TVDB_OK)
    for (size_t i = 0; i < n; ++i) grid->data[i] = (double)view.data[i];
  free(view.data);
  if (st == TVDB_OK && out_iters) *out_iters = iters;
  return st;
}

tvdb_status_t tvdb_gpu_fast_sweeping(tvdb_gpu_context_t* ctx,
                                     tvdb_dense_grid* grid,
                                     float frozen_band,
                                     int max_iters, float tol,
                                     int* out_iters,
                                     tvdb_error_t* err) {
  if (!ctx || !grid || !grid->data) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid fast_sweeping arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (out_iters) *out_iters = 0;
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    if (out_iters) *out_iters = tvdb_fast_sweeping(grid, frozen_band, max_iters, tol);
    return TVDB_OK;
  }
  if (kTvdbGpuFastSweepingPlaneSpv_len == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "fast_sweeping SPIR-V unavailable; rebuild with glslangValidator");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  int iters = 0;
  tvdb_status_t st = tvdb_fast_sweeping_vk(ctx, grid, frozen_band, max_iters, tol, &iters, err, 0);
  if (st == TVDB_OK && out_iters) *out_iters = iters;
  return st;
}

static tvdb_status_t tvdb_gpu_divergence_impl(tvdb_gpu_context_t* ctx,
                                  const tvdb_dense_vec_grid* in,
                                  tvdb_dense_grid* out,
                                  tvdb_error_t* err) {
  if (!ctx || !in || !in->data || !out) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid divergence arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if ((tvdb_gpu_init_out_grid(out, in->nx, in->ny, in->nz, in->voxel_size, in->ox, in->oy, in->oz, err)) != TVDB_OK)
    return TVDB_ERROR_OUT_OF_MEMORY;
  size_t n = (size_t)in->nx * (size_t)in->ny * (size_t)in->nz;
  float h = in->voxel_size;
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    tvdb_status_t cs = tvdb_cuda_stencil2d(ctx, "tvdb_cuda_stencil_vec_scalar",
        in->data, n * 3u, 3, out->data, n, 1, in->nx, in->ny, in->nz, 0, 1.0f / (2.0f * h), in->ox, in->oy, in->oz, in->voxel_size, err);
    if (cs == TVDB_OK) return TVDB_OK;
    /* No stderr: this is a library. The fallback is documented in tinyvdb_gpu.h. */
    free(out->data); out->data = NULL;
    if ((tvdb_gpu_init_out_grid(out, in->nx, in->ny, in->nz, in->voxel_size, in->ox, in->oy, in->oz, err)) != TVDB_OK)
      return TVDB_ERROR_OUT_OF_MEMORY;
    tvdb_divergence(in, out);
    return TVDB_OK;
  }
  return tvdb_vk_stencil2d(ctx, kTvdbGpuStencilVecScalarSpv, kTvdbGpuStencilVecScalarSpv_len,
                           in->data, n * 3u, 3, out->data, n, 1,
                           in->nx, in->ny, in->nz, 0, 1.0f / (2.0f * h), in->ox, in->oy, in->oz, in->voxel_size, err);
}

static tvdb_status_t tvdb_gpu_curl_impl(tvdb_gpu_context_t* ctx,
                            const tvdb_dense_vec_grid* in,
                            tvdb_dense_vec_grid* out,
                            tvdb_error_t* err) {
  if (!ctx || !in || !in->data || !out) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid curl arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if ((tvdb_init_out_vec(out, in->nx, in->ny, in->nz, in->voxel_size, in->ox, in->oy, in->oz, err)) != TVDB_OK)
    return TVDB_ERROR_OUT_OF_MEMORY;
  size_t n = (size_t)in->nx * (size_t)in->ny * (size_t)in->nz;
  float h = in->voxel_size;
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    tvdb_status_t cs = tvdb_cuda_stencil2d(ctx, "tvdb_cuda_stencil_vec_vec",
        in->data, n * 3u, 3, out->data, n * 3u, 3, in->nx, in->ny, in->nz, 0, 1.0f / (2.0f * h), in->ox, in->oy, in->oz, in->voxel_size, err);
    if (cs == TVDB_OK) return TVDB_OK;
    /* No stderr: this is a library. The fallback is documented in tinyvdb_gpu.h. */
    free(out->data); out->data = NULL;
    if ((tvdb_init_out_vec(out, in->nx, in->ny, in->nz, in->voxel_size, in->ox, in->oy, in->oz, err)) != TVDB_OK)
      return TVDB_ERROR_OUT_OF_MEMORY;
    tvdb_curl(in, out);
    return TVDB_OK;
  }
  return tvdb_vk_stencil2d(ctx, kTvdbGpuStencilVecVecSpv, kTvdbGpuStencilVecVecSpv_len,
                           in->data, n * 3u, 3, out->data, n * 3u, 3,
                           in->nx, in->ny, in->nz, 0, 1.0f / (2.0f * h), in->ox, in->oy, in->oz, in->voxel_size, err);
}

tvdb_status_t tvdb_gpu_coarsen(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* in,
                               int factor, tvdb_dense_grid* out, tvdb_error_t* err) {
  return resident_resample_host(ctx,in,factor,0,out,err);
}

tvdb_status_t tvdb_gpu_refine(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* in,
                              int factor, tvdb_dense_grid* out, tvdb_error_t* err) {
  return resident_resample_host(ctx,in,factor,1,out,err);
}

// ---- volume render ----------------------------------------------------------

static void tvdb_v3_sub(const float a[3], const float b[3], float o[3]) {
  o[0] = a[0]-b[0]; o[1] = a[1]-b[1]; o[2] = a[2]-b[2];
}
static void tvdb_v3_cross(const float a[3], const float b[3], float o[3]) {
  o[0] = a[1]*b[2]-a[2]*b[1]; o[1] = a[2]*b[0]-a[0]*b[2]; o[2] = a[0]*b[1]-a[1]*b[0];
}
static void tvdb_v3_norm(float a[3]) {
  float l = sqrtf(a[0]*a[0]+a[1]*a[1]+a[2]*a[2]);
  if (l > 0.0f) { a[0]/=l; a[1]/=l; a[2]/=l; }
}

tvdb_status_t tvdb_gpu_volume_render(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* density,
                                     const float eye[3], const float center[3],
                                     const float up[3], float fov_y, int width, int height,
                                     float sigma, float step, float background,
                                     float* out_image, tvdb_error_t* err) {
  if (!ctx || !density || !density->data || !eye || !center || !up || !out_image ||
      width < 1 || height < 1 || step <= 0.0f || fov_y <= 0.0f) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid volume_render arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  // Camera basis (matches render.c, including the up-parallel fallback).
  float fwd[3]; tvdb_v3_sub(center, eye, fwd); tvdb_v3_norm(fwd);
  float right[3]; tvdb_v3_cross(fwd, up, right);
  if (right[0]*right[0] + right[1]*right[1] + right[2]*right[2] < 1e-12f) {
    float alt[3] = {1.0f, 0.0f, 0.0f};
    if (fabsf(fwd[0]) > 0.9f) { alt[0] = 0.0f; alt[1] = 1.0f; }
    tvdb_v3_cross(fwd, alt, right);
  }
  tvdb_v3_norm(right);
  float cup[3]; tvdb_v3_cross(right, fwd, cup);
  float tan_half = tanf(0.5f * fov_y);
  float aspect = (float)width / (float)height;
  float lo[3] = {density->ox, density->oy, density->oz};
  float hi[3] = {density->ox + density->nx * density->voxel_size,
                 density->oy + density->ny * density->voxel_size,
                 density->oz + density->nz * density->voxel_size};
  size_t nin = (size_t)density->nx * (size_t)density->ny * (size_t)density->nz;
  size_t npix = (size_t)width * (size_t)height;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dd = 0, dimg = 0;
    tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
    if (st != TVDB_OK) return st;
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_volume_render"))) return err ? err->status : TVDB_ERROR_IO;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dd, density->data, nin * sizeof(float), err)) != TVDB_OK) goto vdone;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dimg, NULL, npix * sizeof(float), err)) != TVDB_OK) goto vdone;
    int nx = density->nx, ny = density->ny, nz = density->nz;
    float ox = density->ox, oy = density->oy, oz = density->oz, vs = density->voxel_size;
    float ex = eye[0], ey = eye[1], ez = eye[2];
    float fwx = fwd[0], fwy = fwd[1], fwz = fwd[2];
    float rx = right[0], ry = right[1], rz = right[2];
    float ux = cup[0], uy = cup[1], uz = cup[2];
    float lox = lo[0], loy = lo[1], loz = lo[2], hix = hi[0], hiy = hi[1], hiz = hi[2];
    void* args[] = {&dd, &dimg, &nx, &ny, &nz, &ox, &oy, &oz, &vs,
                    &lox, &loy, &loz, &hix, &hiy, &hiz,
                    &ex, &ey, &ez, &fwx, &fwy, &fwz, &rx, &ry, &rz, &ux, &uy, &uz,
                    &tan_half, &aspect, &sigma, &step, &background, &width, &height};
    unsigned int block = 64, grid = ((unsigned int)npix + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto vdone; }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto vdone; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out_image, dimg, npix * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto vdone; }
    st = TVDB_OK;
vdone:
    if (dimg) ctx->cuda.cuMemFree(dimg);
    if (dd) ctx->cuda.cuMemFree(dd);
    return st;
  }

  tvdb_vk_buffer bd, bo, bp;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, nin * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bd, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, npix * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto vdone_d;
  if ((st = tvdb_vk_create_buffer(ctx, 176, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bp, err)) != TVDB_OK) goto vdone_o;
  memcpy(bd.mapped, density->data, nin * sizeof(float));
  struct {
    int32_t dim[4]; int32_t wh[4]; float grid_origin[4]; float lo[4]; float hi[4];
    float eye[4]; float fwd[4]; float right[4]; float cup[4]; float cam[4]; float cam2[4];
  } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = density->nx; par.dim[1] = density->ny; par.dim[2] = density->nz; par.dim[3] = width;
  par.wh[0] = height;
  par.grid_origin[0] = density->ox; par.grid_origin[1] = density->oy; par.grid_origin[2] = density->oz; par.grid_origin[3] = density->voxel_size;
  par.lo[0] = lo[0]; par.lo[1] = lo[1]; par.lo[2] = lo[2];
  par.hi[0] = hi[0]; par.hi[1] = hi[1]; par.hi[2] = hi[2];
  par.eye[0] = eye[0]; par.eye[1] = eye[1]; par.eye[2] = eye[2];
  par.fwd[0] = fwd[0]; par.fwd[1] = fwd[1]; par.fwd[2] = fwd[2];
  par.right[0] = right[0]; par.right[1] = right[1]; par.right[2] = right[2];
  par.cup[0] = cup[0]; par.cup[1] = cup[1]; par.cup[2] = cup[2];
  par.cam[0] = tan_half; par.cam[1] = aspect; par.cam[2] = sigma; par.cam[3] = step;
  par.cam2[0] = background;
  memcpy(bp.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuVolumeRenderSpv; d.spv_len = kTvdbGpuVolumeRenderSpv_len; d.descriptor_count = 3;
  d.buffers[0] = &bd; d.buffers[1] = &bo; d.buffers[2] = &bp;
  d.descriptor_types[0] = d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((npix + 63u) / 64u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(out_image, bo.mapped, npix * sizeof(float));
  tvdb_vk_destroy_buffer(ctx, &bp);
vdone_o: tvdb_vk_destroy_buffer(ctx, &bo);
vdone_d: tvdb_vk_destroy_buffer(ctx, &bd);
  return st;
}

// ---- batched ray queries ----------------------------------------------------

tvdb_status_t tvdb_gpu_uniform_ray_samples(tvdb_gpu_context_t* ctx,
                                           const float* rays, size_t n_rays, size_t n_samples,
                                           float* out_points, float* out_t, tvdb_error_t* err) {
  if (!ctx || !rays || !out_points || !out_t || n_samples == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid uniform_ray_samples arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (n_rays == 0) return TVDB_OK;
  size_t ntot = n_rays * n_samples;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dr = 0, dp = 0, dt = 0;
    tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
    if (st != TVDB_OK) return st;
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_ray_samples"))) return err ? err->status : TVDB_ERROR_IO;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dr, rays, n_rays * 8u * sizeof(float), err)) != TVDB_OK) goto sdone;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dp, NULL, ntot * 3u * sizeof(float), err)) != TVDB_OK) goto sdone;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dt, NULL, ntot * sizeof(float), err)) != TVDB_OK) goto sdone;
    unsigned int unr = (unsigned int)n_rays, uns = (unsigned int)n_samples;
    void* args[] = {&dr, &dp, &dt, &unr, &uns};
    unsigned int block = 128, grid = ((unsigned int)ntot + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto sdone; }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto sdone; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out_points, dp, ntot * 3u * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto sdone; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out_t, dt, ntot * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto sdone; }
    st = TVDB_OK;
sdone:
    if (dt) ctx->cuda.cuMemFree(dt);
    if (dp) ctx->cuda.cuMemFree(dp);
    if (dr) ctx->cuda.cuMemFree(dr);
    return st;
  }

  tvdb_vk_buffer br, bp, bt, bu;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, n_rays * 8u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &br, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, ntot * 3u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bp, err)) != TVDB_OK) goto sd_r;
  if ((st = tvdb_vk_create_buffer(ctx, ntot * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bt, err)) != TVDB_OK) goto sd_p;
  if ((st = tvdb_vk_create_buffer(ctx, 16, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto sd_t;
  memcpy(br.mapped, rays, n_rays * 8u * sizeof(float));
  struct { uint32_t n_rays, n_samples, pad[2]; } par = {(uint32_t)n_rays, (uint32_t)n_samples, {0, 0}};
  memcpy(bu.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuRaySamplesSpv; d.spv_len = kTvdbGpuRaySamplesSpv_len; d.descriptor_count = 4;
  d.buffers[0] = &br; d.buffers[1] = &bp; d.buffers[2] = &bt; d.buffers[3] = &bu;
  d.descriptor_types[0] = d.descriptor_types[1] = d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((ntot + 127u) / 128u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) {
    memcpy(out_points, bp.mapped, ntot * 3u * sizeof(float));
    memcpy(out_t, bt.mapped, ntot * sizeof(float));
  }
  tvdb_vk_destroy_buffer(ctx, &bu);
sd_t: tvdb_vk_destroy_buffer(ctx, &bt);
sd_p: tvdb_vk_destroy_buffer(ctx, &bp);
sd_r: tvdb_vk_destroy_buffer(ctx, &br);
  return st;
}

tvdb_status_t tvdb_gpu_voxels_along_ray(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                                        const float* rays, size_t n_rays, size_t cap,
                                        int32_t* out_voxels, int32_t* out_counts, tvdb_error_t* err) {
  if (!ctx || !grid || !grid->data || !rays || !out_voxels || !out_counts || cap == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid voxels_along_ray arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (n_rays == 0) return TVDB_OK;
  size_t nvox = n_rays * cap * 3u;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dr = 0, dv = 0, dc = 0;
    tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
    if (st != TVDB_OK) return st;
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_voxels_along_ray"))) return err ? err->status : TVDB_ERROR_IO;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dr, rays, n_rays * 8u * sizeof(float), err)) != TVDB_OK) goto xdone;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dv, NULL, nvox * sizeof(int32_t), err)) != TVDB_OK) goto xdone;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dc, NULL, n_rays * sizeof(int32_t), err)) != TVDB_OK) goto xdone;
    int nx = grid->nx, ny = grid->ny, nz = grid->nz;
    float ox = grid->ox, oy = grid->oy, oz = grid->oz, vs = grid->voxel_size;
    unsigned int unr = (unsigned int)n_rays, ucap = (unsigned int)cap;
    void* args[] = {&dr, &dv, &dc, &nx, &ny, &nz, &ox, &oy, &oz, &vs, &unr, &ucap};
    unsigned int block = 64, grid_blocks = (unr + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid_blocks, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto xdone; }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto xdone; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out_voxels, dv, nvox * sizeof(int32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto xdone; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out_counts, dc, n_rays * sizeof(int32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto xdone; }
    st = TVDB_OK;
xdone:
    if (dc) ctx->cuda.cuMemFree(dc);
    if (dv) ctx->cuda.cuMemFree(dv);
    if (dr) ctx->cuda.cuMemFree(dr);
    return st;
  }

  tvdb_vk_buffer br, bv, bc, bu;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, n_rays * 8u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &br, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, nvox * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bv, err)) != TVDB_OK) goto xd_r;
  if ((st = tvdb_vk_create_buffer(ctx, n_rays * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bc, err)) != TVDB_OK) goto xd_v;
  if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto xd_c;
  memcpy(br.mapped, rays, n_rays * 8u * sizeof(float));
  struct { int32_t dim[4]; float grid[4]; uint32_t n_rays; uint32_t cap; uint32_t pad[2]; } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = grid->nx; par.dim[1] = grid->ny; par.dim[2] = grid->nz;
  par.grid[0] = grid->ox; par.grid[1] = grid->oy; par.grid[2] = grid->oz; par.grid[3] = grid->voxel_size;
  par.n_rays = (uint32_t)n_rays; par.cap = (uint32_t)cap;
  memcpy(bu.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuVoxelsAlongRaySpv; d.spv_len = kTvdbGpuVoxelsAlongRaySpv_len; d.descriptor_count = 4;
  d.buffers[0] = &br; d.buffers[1] = &bv; d.buffers[2] = &bc; d.buffers[3] = &bu;
  d.descriptor_types[0] = d.descriptor_types[1] = d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((n_rays + 63u) / 64u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) {
    memcpy(out_voxels, bv.mapped, nvox * sizeof(int32_t));
    memcpy(out_counts, bc.mapped, n_rays * sizeof(int32_t));
  }
  tvdb_vk_destroy_buffer(ctx, &bu);
xd_c: tvdb_vk_destroy_buffer(ctx, &bc);
xd_v: tvdb_vk_destroy_buffer(ctx, &bv);
xd_r: tvdb_vk_destroy_buffer(ctx, &br);
  return st;
}

tvdb_status_t tvdb_gpu_segments_along_ray(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                                          const float* rays, size_t n_rays, float isovalue,
                                          size_t step_count, size_t cap,
                                          float* out_t_pairs, int32_t* out_counts, tvdb_error_t* err) {
  if (!ctx || !grid || !grid->data || !rays || !out_t_pairs || !out_counts || cap == 0 || step_count < 2) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid segments_along_ray arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (n_rays == 0) return TVDB_OK;
  size_t nin = (size_t)grid->nx * (size_t)grid->ny * (size_t)grid->nz;
  size_t npair = n_rays * cap * 2u;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dg = 0, dr = 0, dp = 0, dc = 0;
    tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
    if (st != TVDB_OK) return st;
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_segments_along_ray"))) return err ? err->status : TVDB_ERROR_IO;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dg, grid->data, nin * sizeof(float), err)) != TVDB_OK) goto gdone;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dr, rays, n_rays * 8u * sizeof(float), err)) != TVDB_OK) goto gdone;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dp, NULL, npair * sizeof(float), err)) != TVDB_OK) goto gdone;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dc, NULL, n_rays * sizeof(int32_t), err)) != TVDB_OK) goto gdone;
    int nx = grid->nx, ny = grid->ny, nz = grid->nz;
    float ox = grid->ox, oy = grid->oy, oz = grid->oz, vs = grid->voxel_size;
    unsigned int unr = (unsigned int)n_rays, usc = (unsigned int)step_count, ucap = (unsigned int)cap;
    void* args[] = {&dg, &dr, &dp, &dc, &nx, &ny, &nz, &ox, &oy, &oz, &vs, &unr, &isovalue, &usc, &ucap};
    unsigned int block = 64, grid_blocks = (unr + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid_blocks, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto gdone; }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto gdone; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out_t_pairs, dp, npair * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto gdone; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out_counts, dc, n_rays * sizeof(int32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto gdone; }
    st = TVDB_OK;
gdone:
    if (dc) ctx->cuda.cuMemFree(dc);
    if (dp) ctx->cuda.cuMemFree(dp);
    if (dr) ctx->cuda.cuMemFree(dr);
    if (dg) ctx->cuda.cuMemFree(dg);
    return st;
  }

  tvdb_vk_buffer bg, br, bp, bc, bu;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, nin * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bg, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, n_rays * 8u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &br, err)) != TVDB_OK) goto gd_g;
  if ((st = tvdb_vk_create_buffer(ctx, npair * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bp, err)) != TVDB_OK) goto gd_r;
  if ((st = tvdb_vk_create_buffer(ctx, n_rays * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bc, err)) != TVDB_OK) goto gd_p;
  if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto gd_c;
  memcpy(bg.mapped, grid->data, nin * sizeof(float));
  memcpy(br.mapped, rays, n_rays * 8u * sizeof(float));
  struct { int32_t dim[4]; float grid[4]; uint32_t n_rays; uint32_t cap; uint32_t step_count; float isovalue; } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = grid->nx; par.dim[1] = grid->ny; par.dim[2] = grid->nz;
  par.grid[0] = grid->ox; par.grid[1] = grid->oy; par.grid[2] = grid->oz; par.grid[3] = grid->voxel_size;
  par.n_rays = (uint32_t)n_rays; par.cap = (uint32_t)cap; par.step_count = (uint32_t)step_count; par.isovalue = isovalue;
  memcpy(bu.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuSegmentsAlongRaySpv; d.spv_len = kTvdbGpuSegmentsAlongRaySpv_len; d.descriptor_count = 5;
  d.buffers[0] = &bg; d.buffers[1] = &br; d.buffers[2] = &bp; d.buffers[3] = &bc; d.buffers[4] = &bu;
  for (int i = 0; i < 4; ++i) d.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((n_rays + 63u) / 64u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) {
    memcpy(out_t_pairs, bp.mapped, npair * sizeof(float));
    memcpy(out_counts, bc.mapped, n_rays * sizeof(int32_t));
  }
  tvdb_vk_destroy_buffer(ctx, &bu);
gd_c: tvdb_vk_destroy_buffer(ctx, &bc);
gd_p: tvdb_vk_destroy_buffer(ctx, &bp);
gd_r: tvdb_vk_destroy_buffer(ctx, &br);
gd_g: tvdb_vk_destroy_buffer(ctx, &bg);
  return st;
}

// ---- TSDF integration -------------------------------------------------------

tvdb_status_t tvdb_gpu_integrate_tsdf(tvdb_gpu_context_t* ctx, tvdb_dense_grid* tsdf,
                                      tvdb_dense_grid* weights, const tvdb_depth_frame* frame,
                                      tvdb_error_t* err) {
  if (!ctx || !tsdf || !weights || !frame || !tsdf->data || !weights->data || !frame->depth ||
      tsdf->nx != weights->nx || tsdf->ny != weights->ny || tsdf->nz != weights->nz ||
      frame->width < 1 || frame->height < 1) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid integrate_tsdf arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  float pose_cw[12];
  tvdb_invert_rigid_pose(frame->pose, pose_cw);
  size_t nv = (size_t)tsdf->nx * (size_t)tsdf->ny * (size_t)tsdf->nz;
  size_t ndepth = (size_t)frame->width * (size_t)frame->height;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dt = 0, dw = 0, dd = 0;
    tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
    if (st != TVDB_OK) return st;
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_integrate_tsdf"))) return err ? err->status : TVDB_ERROR_IO;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dt, tsdf->data, nv * sizeof(float), err)) != TVDB_OK) goto tdone;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dw, weights->data, nv * sizeof(float), err)) != TVDB_OK) goto tdone;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dd, frame->depth, ndepth * sizeof(float), err)) != TVDB_OK) goto tdone;
    int nx = tsdf->nx, ny = tsdf->ny, nz = tsdf->nz;
    float ox = tsdf->ox, oy = tsdf->oy, oz = tsdf->oz, vs = tsdf->voxel_size;
    float p[12]; for (int i = 0; i < 12; ++i) p[i] = pose_cw[i];
    float fx = frame->fx, fy = frame->fy, ccx = frame->cx, ccy = frame->cy;
    int width = frame->width, height = frame->height;
    float dmin = frame->depth_min, dmax = frame->depth_max, trunc = frame->trunc_distance;
    void* args[] = {&dt, &dw, &dd, &nx, &ny, &nz, &ox, &oy, &oz, &vs,
                    &p[0],&p[1],&p[2],&p[3],&p[4],&p[5],&p[6],&p[7],&p[8],&p[9],&p[10],&p[11],
                    &fx, &fy, &ccx, &ccy, &width, &height, &dmin, &dmax, &trunc};
    unsigned int block = 128, grid = ((unsigned int)nv + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto tdone; }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto tdone; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(tsdf->data, dt, nv * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto tdone; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(weights->data, dw, nv * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto tdone; }
    st = TVDB_OK;
tdone:
    if (dd) ctx->cuda.cuMemFree(dd);
    if (dw) ctx->cuda.cuMemFree(dw);
    if (dt) ctx->cuda.cuMemFree(dt);
    return st;
  }

  tvdb_vk_buffer bt, bw, bd, bu;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, nv * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bt, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, nv * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bw, err)) != TVDB_OK) goto td_t;
  if ((st = tvdb_vk_create_buffer(ctx, ndepth * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bd, err)) != TVDB_OK) goto td_w;
  if ((st = tvdb_vk_create_buffer(ctx, 128, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto td_d;
  memcpy(bt.mapped, tsdf->data, nv * sizeof(float));
  memcpy(bw.mapped, weights->data, nv * sizeof(float));
  memcpy(bd.mapped, frame->depth, ndepth * sizeof(float));
  struct {
    int32_t dim[4]; float grid[4]; float pose0[4]; float pose1[4]; float pose2[4];
    float intr[4]; int32_t fdim[4]; float rng[4];
  } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = tsdf->nx; par.dim[1] = tsdf->ny; par.dim[2] = tsdf->nz;
  par.grid[0] = tsdf->ox; par.grid[1] = tsdf->oy; par.grid[2] = tsdf->oz; par.grid[3] = tsdf->voxel_size;
  for (int i = 0; i < 4; ++i) { par.pose0[i] = pose_cw[i]; par.pose1[i] = pose_cw[4+i]; par.pose2[i] = pose_cw[8+i]; }
  par.intr[0] = frame->fx; par.intr[1] = frame->fy; par.intr[2] = frame->cx; par.intr[3] = frame->cy;
  par.fdim[0] = frame->width; par.fdim[1] = frame->height;
  par.rng[0] = frame->depth_min; par.rng[1] = frame->depth_max; par.rng[2] = frame->trunc_distance;
  memcpy(bu.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuTsdfSpv; d.spv_len = kTvdbGpuTsdfSpv_len; d.descriptor_count = 4;
  d.buffers[0] = &bt; d.buffers[1] = &bw; d.buffers[2] = &bd; d.buffers[3] = &bu;
  d.descriptor_types[0] = d.descriptor_types[1] = d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((nv + 127u) / 128u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) {
    memcpy(tsdf->data, bt.mapped, nv * sizeof(float));
    memcpy(weights->data, bw.mapped, nv * sizeof(float));
  }
  tvdb_vk_destroy_buffer(ctx, &bu);
td_d: tvdb_vk_destroy_buffer(ctx, &bd);
td_w: tvdb_vk_destroy_buffer(ctx, &bw);
td_t: tvdb_vk_destroy_buffer(ctx, &bt);
  return st;
}

// ---- grid statistics --------------------------------------------------------

// Combine the per-thread (min,max,sum,sumsq) partials in double, matching
// tvdb_grid_statistics' min/max/mean/stddev/sum/count semantics.
/* Number of workgroups for a two-stage reduction over `count` elements.
 *
 * These reductions used to run as a single wavefront of min(count,256) threads,
 * i.e. one workgroup, which left the whole rest of the device idle on anything
 * larger than a few thousand voxels. `ngroups` is capped so the host-side fold of
 * the partials stays cheap, and is also <= ceil(count/256) so every workgroup is
 * guaranteed at least one element -- which is what lets the shaders use
 * opposite-infinity sentinels for the min/max accumulators instead of having to
 * mask empty slices afterwards. */
#define TVDB_GPU_REDUCE_GROUPS 1024u
static uint32_t tvdb_gpu_reduce_groups(size_t count) {
  size_t want = (count + 255u) / 256u;
  if (want > TVDB_GPU_REDUCE_GROUPS) want = TVDB_GPU_REDUCE_GROUPS;
  if (want < 1u) want = 1u;
  return (uint32_t)want;
}

static void tvdb_finalize_stats(const float* partials, uint32_t nthreads, size_t n,
                                tvdb_grid_stats_t* out) {
  double mn = partials[0], mx = partials[1], sum = 0.0, sumsq = 0.0;
  for (uint32_t t = 0; t < nthreads; ++t) {
    if (partials[4*t+0] < mn) mn = partials[4*t+0];
    if (partials[4*t+1] > mx) mx = partials[4*t+1];
    sum += partials[4*t+2];
    sumsq += partials[4*t+3];
  }
  double mean = sum / (double)n;
  double var = sumsq / (double)n - mean * mean;
  if (var < 0.0) var = 0.0;
  out->min = mn; out->max = mx; out->mean = mean;
  out->stddev = sqrt(var); out->sum = sum; out->count = n;
}

tvdb_status_t tvdb_gpu_grid_statistics(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                                       tvdb_grid_stats_t* out, tvdb_error_t* err) {
  return resident_reduce_host(ctx,grid,0,0,0,out,err);
}

// ---- diagnostics validators -------------------------------------------------

tvdb_status_t tvdb_gpu_check_fog_volume(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                                        double eps, int* out_valid, double* out_min,
                                        double* out_max, tvdb_error_t* err) {
  tvdb_grid_stats_t s;
  tvdb_status_t st = tvdb_gpu_grid_statistics(ctx, grid, &s, err);
  if (st != TVDB_OK) return st;
  if (out_min) *out_min = s.min;
  if (out_max) *out_max = s.max;
  if (out_valid) *out_valid = (s.min >= -eps && s.max <= 1.0 + eps) ? 1 : 0;
  return TVDB_OK;
}

static void tvdb_finalize_ls_check(const float* partials, uint32_t nthreads, size_t band_total,
                                   tvdb_level_set_check_t* out) {
  (void)band_total;
  double sum_mag = 0.0, max_err = 0.0, bad = 0.0, band = 0.0;
  for (uint32_t t = 0; t < nthreads; ++t) {
    sum_mag += partials[4*t+0];
    if (partials[4*t+1] > max_err) max_err = partials[4*t+1];
    bad += partials[4*t+2];
    band += partials[4*t+3];
  }
  out->band_count = (size_t)band;
  if (band > 0.0) {
    out->mean_grad_mag = sum_mag / band;
    out->bad_fraction = bad / band;
    out->max_grad_error = max_err;
  }
}

tvdb_status_t tvdb_gpu_check_level_set(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                                       double band_world, double tol,
                                       tvdb_level_set_check_t* out, tvdb_error_t* err) {
  return resident_reduce_host(ctx,grid,1,band_world,tol,out,err);
}

// ---- signed flood fill ------------------------------------------------------

// Seed boundary far voxels and assign final signs (shared host helpers).
static void tvdb_flood_seed(const float* data, uint32_t* vis, int nx, int ny, int nz, float thresh) {
  for (int k = 0; k < nz; ++k)
    for (int j = 0; j < ny; ++j)
      for (int i = 0; i < nx; ++i) {
        if (i != 0 && i != nx-1 && j != 0 && j != ny-1 && k != 0 && k != nz-1) continue;
        size_t idx = ((size_t)k * ny + j) * nx + i;
        vis[idx] = (fabsf(data[idx]) >= thresh) ? 1u : 0u;
      }
}
static void tvdb_flood_assign(float* data, const uint32_t* vis, size_t n, float thresh, float band) {
  for (size_t i = 0; i < n; ++i)
    if (fabsf(data[i]) >= thresh) data[i] = vis[i] ? band : -band;
}

tvdb_status_t tvdb_gpu_signed_flood_fill(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                                         float band_world, tvdb_error_t* err) {
  if (!ctx || !grid || !tvdb_gpu_shape_valid(grid->nx,grid->ny,grid->nz,grid->voxel_size,grid->data,sizeof(float)) || !isfinite(band_world) || band_world <= 0.0f) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid signed_flood_fill arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  size_t n = (size_t)nx * (size_t)ny * (size_t)nz;
  if (n == 0) return TVDB_OK;
  float thresh = band_world;
  uint32_t* vis = (uint32_t*)calloc(n, sizeof(uint32_t));
  if (!vis) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  tvdb_flood_seed(grid->data, vis, nx, ny, nz, thresh);
  size_t max_iter = n + 1;  // worst-case label-propagation depth
  tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dg = 0, dv = 0, dn = 0, dc = 0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto fcu_ret;
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_flood"))) { st = err ? err->status : TVDB_ERROR_IO; goto fcu_ret; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dg, grid->data, n * sizeof(float), err)) != TVDB_OK) goto fcu_free;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dv, vis, n * sizeof(uint32_t), err)) != TVDB_OK) goto fcu_free;
    if ((st=tvdb_cuda_alloc_copy_in(ctx,&dn,NULL,n*sizeof(uint32_t),err))!=TVDB_OK) goto fcu_free;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dc, NULL, sizeof(uint32_t), err)) != TVDB_OK) goto fcu_free;
    unsigned int block = 128, gridb = ((unsigned int)n + block - 1u) / block;
    for (size_t it = 0; it < max_iter; ++it) {
      uint32_t zero = 0;
      if (!tvdb_cuda_ok(ctx, err, "cuMemcpyHtoD", ctx->cuda.cuMemcpyHtoD(dc, &zero, sizeof(uint32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto fcu_free; }
      void* args[] = {&dg, &dv, &dn, &dc, &nx, &ny, &nz, &thresh};
      if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, gridb, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto fcu_free; }
      if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto fcu_free; }
      uint32_t changed = 0;
      if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(&changed, dc, sizeof(uint32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto fcu_free; }
      { CUdeviceptr swap=dv; dv=dn; dn=swap; }
      if (!changed) break;
    }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(vis, dv, n * sizeof(uint32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto fcu_free; }
    st = TVDB_OK;
fcu_free:
    if (dc) ctx->cuda.cuMemFree(dc);
    if (dn) ctx->cuda.cuMemFree(dn);
    if (dv) ctx->cuda.cuMemFree(dv);
    if (dg) ctx->cuda.cuMemFree(dg);
fcu_ret:
    if (st == TVDB_OK) tvdb_flood_assign(grid->data, vis, n, thresh, band_world);
    free(vis);
    return st;
  }

  tvdb_vk_buffer bg, bv, bn, bc, bu;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bg, err)) != TVDB_OK) { free(vis); return st; }
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(uint32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bv, err)) != TVDB_OK) goto fvk_g;
  if ((st=tvdb_vk_create_buffer(ctx,n*sizeof(uint32_t),VK_BUFFER_USAGE_STORAGE_BUFFER_BIT,&bn,err))!=TVDB_OK) goto fvk_v;
  if ((st = tvdb_vk_create_buffer(ctx, sizeof(uint32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bc, err)) != TVDB_OK) goto fvk_n;
  if ((st = tvdb_vk_create_buffer(ctx, 32, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto fvk_c;
  memcpy(bg.mapped, grid->data, n * sizeof(float));
  memcpy(bv.mapped, vis, n * sizeof(uint32_t));
  struct { int32_t dim[4]; float thresh; float pad[3]; } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = nx; par.dim[1] = ny; par.dim[2] = nz; par.thresh = thresh;
  memcpy(bu.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuFloodSpv; d.spv_len = kTvdbGpuFloodSpv_len; d.descriptor_count = 5;
  d.buffers[0] = &bg; d.buffers[1] = &bv; d.buffers[2] = &bc; d.buffers[3] = &bu; d.buffers[4]=&bn;
  d.descriptor_types[0] = d.descriptor_types[1] = d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER; d.descriptor_types[4]=VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.group_x = (uint32_t)((n + 127u) / 128u);
  for (size_t it = 0; it < max_iter; ++it) {
    *(uint32_t*)bc.mapped = 0u;
    st = tvdb_vk_dispatch(ctx, &d, err);
    if (st != TVDB_OK) goto fvk_done;
    { tvdb_vk_buffer swap=bv; bv=bn; bn=swap; }
    if (*(uint32_t*)bc.mapped == 0u) break;
  }
  memcpy(vis, bv.mapped, n * sizeof(uint32_t));
  tvdb_flood_assign(grid->data, vis, n, thresh, band_world);
  st = TVDB_OK;
fvk_done:
  tvdb_vk_destroy_buffer(ctx, &bu);
fvk_c: tvdb_vk_destroy_buffer(ctx, &bc);
fvk_n: tvdb_vk_destroy_buffer(ctx, &bn);
fvk_v: tvdb_vk_destroy_buffer(ctx, &bv);
fvk_g: tvdb_vk_destroy_buffer(ctx, &bg);
  free(vis);
  return st;
}

// ---- trilinear splat --------------------------------------------------------

static tvdb_status_t tvdb_gpu_splat_dense_impl(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                                             const float* points, const float* vals, size_t n,
                                             float* weights, const char* cuda_kernel,
                                             const uint8_t* spv, uint32_t spv_len, tvdb_error_t* err) {
  if (!ctx || !grid || !tvdb_gpu_shape_valid(grid->nx,grid->ny,grid->nz,grid->voxel_size,grid->data,sizeof(float)) ||
      !isfinite(grid->ox) || !isfinite(grid->oy) || !isfinite(grid->oz) || n>INT_MAX || (!points && n) || (!vals && n)) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid splat arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  for(size_t i=0;i<n;++i) for(int k=0;k<3;++k) if(!isfinite(points[3*i+k])) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"nonfinite splat point"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (n == 0) return TVDB_OK;
  size_t nvox = (size_t)grid->nx * (size_t)grid->ny * (size_t)grid->nz;
  int has_weights = weights ? 1 : 0;
  tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dd = 0, dp = 0, dv = 0, dw = 0;
    float* p4 = (float*)malloc(n * 4u * sizeof(float));
    if (!p4) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
    for (size_t i = 0; i < n; ++i) { p4[4*i+0]=points[3*i+0]; p4[4*i+1]=points[3*i+1]; p4[4*i+2]=points[3*i+2]; p4[4*i+3]=0.0f; }
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) { free(p4); return st; }
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, cuda_kernel))) { free(p4); return err ? err->status : TVDB_ERROR_IO; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dd, grid->data, nvox * sizeof(float), err)) != TVDB_OK) goto scu_free;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dp, p4, n * 4u * sizeof(float), err)) != TVDB_OK) goto scu_free;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dv, vals, n * sizeof(float), err)) != TVDB_OK) goto scu_free;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dw, has_weights ? weights : NULL, has_weights ? nvox * sizeof(float) : sizeof(float), err)) != TVDB_OK) goto scu_free;
    int nx = grid->nx, ny = grid->ny, nz = grid->nz;
    float ox = grid->ox, oy = grid->oy, oz = grid->oz, vs = grid->voxel_size;
    unsigned int uc = (unsigned int)n;
    void* args[] = {&dd, &dp, &dv, &dw, &nx, &ny, &nz, &ox, &oy, &oz, &vs, &uc, &has_weights};
    unsigned int block = 128, gridb = ((unsigned int)n + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, gridb, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto scu_free; }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto scu_free; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(grid->data, dd, nvox * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto scu_free; }
    if (has_weights && !tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(weights, dw, nvox * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto scu_free; }
    st = TVDB_OK;
scu_free:
    if (dw) ctx->cuda.cuMemFree(dw);
    if (dv) ctx->cuda.cuMemFree(dv);
    if (dp) ctx->cuda.cuMemFree(dp);
    if (dd) ctx->cuda.cuMemFree(dd);
    free(p4);
    return st;
  }

  tvdb_vk_buffer bd, bp, bv, bw, bu;
  size_t wbytes = has_weights ? nvox * sizeof(float) : sizeof(float);
  if ((st = tvdb_vk_create_buffer(ctx, nvox * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bd, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, n * 4u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bp, err)) != TVDB_OK) goto sd_d;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bv, err)) != TVDB_OK) goto sd_p;
  if ((st = tvdb_vk_create_buffer(ctx, wbytes, VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bw, err)) != TVDB_OK) goto sd_v;
  if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto sd_w;
  memcpy(bd.mapped, grid->data, nvox * sizeof(float));
  { float* pm = (float*)bp.mapped;
    for (size_t i = 0; i < n; ++i) { pm[4*i+0]=points[3*i+0]; pm[4*i+1]=points[3*i+1]; pm[4*i+2]=points[3*i+2]; pm[4*i+3]=0.0f; } }
  memcpy(bv.mapped, vals, n * sizeof(float));
  if (has_weights) memcpy(bw.mapped, weights, nvox * sizeof(float));
  struct { int32_t dim[4]; float grid[4]; uint32_t count; uint32_t has_weights; uint32_t pad[2]; } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = grid->nx; par.dim[1] = grid->ny; par.dim[2] = grid->nz;
  par.grid[0] = grid->ox; par.grid[1] = grid->oy; par.grid[2] = grid->oz; par.grid[3] = grid->voxel_size;
  par.count = (uint32_t)n; par.has_weights = (uint32_t)has_weights;
  memcpy(bu.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = spv; d.spv_len = spv_len; d.descriptor_count = 5;
  d.buffers[0] = &bd; d.buffers[1] = &bp; d.buffers[2] = &bv; d.buffers[3] = &bw; d.buffers[4] = &bu;
  for (int i = 0; i < 4; ++i) d.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((n + 127u) / 128u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) {
    memcpy(grid->data, bd.mapped, nvox * sizeof(float));
    if (has_weights) memcpy(weights, bw.mapped, nvox * sizeof(float));
  }
  tvdb_vk_destroy_buffer(ctx, &bu);
sd_w: tvdb_vk_destroy_buffer(ctx, &bw);
sd_v: tvdb_vk_destroy_buffer(ctx, &bv);
sd_p: tvdb_vk_destroy_buffer(ctx, &bp);
sd_d: tvdb_vk_destroy_buffer(ctx, &bd);
  return st;
}

tvdb_status_t tvdb_gpu_splat_trilinear_dense(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                                             const float* points, const float* vals, size_t n,
                                             float* weights, tvdb_error_t* err) {
  return tvdb_gpu_splat_dense_impl(ctx, grid, points, vals, n, weights, "tvdb_cuda_splat",
                                   kTvdbGpuSplatSpv, kTvdbGpuSplatSpv_len, err);
}

tvdb_status_t tvdb_gpu_splat_quadratic_dense(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                                             const float* points, const float* vals, size_t n,
                                             float* weights, tvdb_error_t* err) {
  return tvdb_gpu_splat_dense_impl(ctx, grid, points, vals, n, weights, "tvdb_cuda_splat_quadratic",
                                   kTvdbGpuSplatQuadraticSpv, kTvdbGpuSplatQuadraticSpv_len, err);
}

// ---- Gaussian spherical-harmonics color evaluation --------------------------

tvdb_status_t tvdb_gpu_gaussian_sh_eval(tvdb_gpu_context_t* ctx, uint32_t num_gaussians,
                                        uint32_t degree, const float* sh_coeffs, const float* dirs,
                                        float* out_colors, tvdb_error_t* err) {
  if (!ctx || degree > 3 || (num_gaussians && (!sh_coeffs || !dirs || !out_colors))) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid gaussian_sh_eval arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (num_gaussians == 0) return TVDB_OK;
  uint32_t K = (degree + 1u) * (degree + 1u);
  size_t n = num_gaussians;
  size_t sh_floats = n * K * 3u;
  size_t out_floats = n * 3u;
  tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dsh = 0, dd = 0, dout = 0;
    float* d4 = (float*)malloc(n * 4u * sizeof(float));
    if (!d4) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
    for (size_t i = 0; i < n; ++i) { d4[4*i+0]=dirs[3*i+0]; d4[4*i+1]=dirs[3*i+1]; d4[4*i+2]=dirs[3*i+2]; d4[4*i+3]=0.0f; }
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) { free(d4); return st; }
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_gaussian_sh"))) { free(d4); return err ? err->status : TVDB_ERROR_IO; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dsh, sh_coeffs, sh_floats * sizeof(float), err)) != TVDB_OK) goto shcu_free;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dd, d4, n * 4u * sizeof(float), err)) != TVDB_OK) goto shcu_free;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, out_floats * sizeof(float), err)) != TVDB_OK) goto shcu_free;
    unsigned int uc = (unsigned int)n, ud = degree, uk = K;
    void* args[] = {&dsh, &dd, &dout, &uc, &ud, &uk};
    unsigned int block = 128, gridb = (uc + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, gridb, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto shcu_free; }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto shcu_free; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out_colors, dout, out_floats * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto shcu_free; }
    st = TVDB_OK;
shcu_free:
    if (dout) ctx->cuda.cuMemFree(dout);
    if (dd) ctx->cuda.cuMemFree(dd);
    if (dsh) ctx->cuda.cuMemFree(dsh);
    free(d4);
    return st;
  }

  tvdb_vk_buffer bsh, bd, bout, bu;
  if ((st = tvdb_vk_create_buffer(ctx, sh_floats * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bsh, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, n * 4u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bd, err)) != TVDB_OK) goto shd_sh;
  if ((st = tvdb_vk_create_buffer(ctx, out_floats * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bout, err)) != TVDB_OK) goto shd_d;
  if ((st = tvdb_vk_create_buffer(ctx, 16, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto shd_out;
  memcpy(bsh.mapped, sh_coeffs, sh_floats * sizeof(float));
  { float* dm = (float*)bd.mapped;
    for (size_t i = 0; i < n; ++i) { dm[4*i+0]=dirs[3*i+0]; dm[4*i+1]=dirs[3*i+1]; dm[4*i+2]=dirs[3*i+2]; dm[4*i+3]=0.0f; } }
  uint32_t par[4] = {(uint32_t)n, degree, K, 0};
  memcpy(bu.mapped, par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuGaussianShSpv; d.spv_len = kTvdbGpuGaussianShSpv_len; d.descriptor_count = 4;
  d.buffers[0] = &bsh; d.buffers[1] = &bd; d.buffers[2] = &bout; d.buffers[3] = &bu;
  d.descriptor_types[0] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((n + 127u) / 128u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(out_colors, bout.mapped, out_floats * sizeof(float));
  tvdb_vk_destroy_buffer(ctx, &bu);
shd_out: tvdb_vk_destroy_buffer(ctx, &bout);
shd_d: tvdb_vk_destroy_buffer(ctx, &bd);
shd_sh: tvdb_vk_destroy_buffer(ctx, &bsh);
  return st;
}

// ---- Gaussian projection (3D -> 2D screen-space conic) -----------------------

// Build the interleaved per-Gaussian input buffer (stride 14 floats).
static float* tvdb_gaussian_pack_inputs(uint32_t n, const float* means, const float* quats,
                                        const float* log_scales, const float* opacities,
                                        const float* sh_dc) {
  float* in = (float*)malloc((size_t)n * 14u * sizeof(float));
  if (!in) return NULL;
  for (uint32_t i = 0; i < n; ++i) {
    float* d = in + (size_t)i * 14u;
    d[0]=means[3*i+0]; d[1]=means[3*i+1]; d[2]=means[3*i+2];
    d[3]=quats[4*i+0]; d[4]=quats[4*i+1]; d[5]=quats[4*i+2]; d[6]=quats[4*i+3];
    d[7]=log_scales[3*i+0]; d[8]=log_scales[3*i+1]; d[9]=log_scales[3*i+2];
    d[10]= opacities ? opacities[i] : 0.0f;
    if (sh_dc) { d[11]=sh_dc[3*i+0]; d[12]=sh_dc[3*i+1]; d[13]=sh_dc[3*i+2]; }
    else { d[11]=1.0f; d[12]=0.0f; d[13]=0.0f; }
  }
  return in;
}

tvdb_status_t tvdb_gpu_gaussian_project(tvdb_gpu_context_t* ctx, uint32_t num_gaussians,
                                        const float* means, const float* quats, const float* log_scales,
                                        const float* opacities, const float* sh_dc,
                                        const float extrinsics[16], const float intrinsics[9],
                                        float z_near, float z_far,
                                        tvdb_projected_gaussian_t* out, tvdb_error_t* err) {
  if (!ctx || !extrinsics || !intrinsics || (num_gaussians && (!means || !quats || !log_scales || !out))) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid gaussian_project arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (num_gaussians == 0) return TVDB_OK;
  size_t n = num_gaussians;
  const float eps2d = 0.3f;
  float fx = intrinsics[0], fy = intrinsics[4], cx = intrinsics[2], cy = intrinsics[5];
  tvdb_status_t st;
  float* in = tvdb_gaussian_pack_inputs(num_gaussians, means, quats, log_scales, opacities, sh_dc);
  if (!in) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr din = 0, dout = 0, dextr = 0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) { free(in); return st; }
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_gaussian_project"))) { free(in); return err ? err->status : TVDB_ERROR_IO; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &din, in, n * 14u * sizeof(float), err)) != TVDB_OK) goto pcu_free;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dextr, extrinsics, 16u * sizeof(float), err)) != TVDB_OK) goto pcu_free;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, n * 11u * sizeof(float), err)) != TVDB_OK) goto pcu_free;
    unsigned int uc = (unsigned int)n;
    void* args[] = {&din, &dout, &dextr, &fx, &fy, &cx, &cy, &z_near, &z_far, (void*)&eps2d, &uc};
    unsigned int block = 128, gridb = (uc + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, gridb, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto pcu_free; }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto pcu_free; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out, dout, n * 11u * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto pcu_free; }
    st = TVDB_OK;
pcu_free:
    if (dout) ctx->cuda.cuMemFree(dout);
    if (dextr) ctx->cuda.cuMemFree(dextr);
    if (din) ctx->cuda.cuMemFree(din);
    free(in);
    return st;
  }

  tvdb_vk_buffer bin, bout, bu;
  if ((st = tvdb_vk_create_buffer(ctx, n * 14u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bin, err)) != TVDB_OK) { free(in); return st; }
  if ((st = tvdb_vk_create_buffer(ctx, n * 11u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bout, err)) != TVDB_OK) goto pd_in;
  if ((st = tvdb_vk_create_buffer(ctx, 112, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto pd_out;
  memcpy(bin.mapped, in, n * 14u * sizeof(float));
  struct { float extr[16]; float fxfycxcy[4]; float nfe[4]; uint32_t count; uint32_t pad[3]; } par;
  memset(&par, 0, sizeof(par));
  memcpy(par.extr, extrinsics, 16u * sizeof(float));
  par.fxfycxcy[0]=fx; par.fxfycxcy[1]=fy; par.fxfycxcy[2]=cx; par.fxfycxcy[3]=cy;
  par.nfe[0]=z_near; par.nfe[1]=z_far; par.nfe[2]=eps2d;
  par.count = (uint32_t)n;
  memcpy(bu.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuGaussianProjectSpv; d.spv_len = kTvdbGpuGaussianProjectSpv_len; d.descriptor_count = 3;
  d.buffers[0] = &bin; d.buffers[1] = &bout; d.buffers[2] = &bu;
  d.descriptor_types[0] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((n + 127u) / 128u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(out, bout.mapped, n * 11u * sizeof(float));
  tvdb_vk_destroy_buffer(ctx, &bu);
pd_out: tvdb_vk_destroy_buffer(ctx, &bout);
pd_in: tvdb_vk_destroy_buffer(ctx, &bin);
  free(in);
  return st;
}

// ---- Gaussian MCMC densification helpers ------------------------------------

tvdb_status_t tvdb_gpu_gaussian_mcmc_relocation(tvdb_gpu_context_t* ctx, uint32_t num_gaussians,
                                                const float* opacities, const float* scales,
                                                const int32_t* ratios, float* new_opacities,
                                                float* new_scales, tvdb_error_t* err) {
  if (!ctx || (num_gaussians && (!opacities || !scales || !ratios || !new_opacities || !new_scales))) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid mcmc_relocation arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (num_gaussians == 0) return TVDB_OK;
  const uint32_t nmax = 51u;
  size_t n = num_gaussians;
  // Interleave inputs (stride 5: opacity, sx, sy, sz, ratio) + build binom table.
  float* gin = (float*)malloc(n * 5u * sizeof(float));
  float* binoms = (float*)malloc((size_t)nmax * nmax * sizeof(float));
  if (!gin || !binoms) { free(gin); free(binoms); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  for (size_t i = 0; i < n; ++i) {
    gin[5*i+0]=opacities[i]; gin[5*i+1]=scales[3*i+0]; gin[5*i+2]=scales[3*i+1]; gin[5*i+3]=scales[3*i+2];
    gin[5*i+4]=(float)ratios[i];
  }
  for (uint32_t i = 0; i < nmax; ++i) {
    for (uint32_t k = 0; k < nmax; ++k) binoms[i*nmax+k] = 0.0f;
    binoms[i*nmax+0] = 1.0f;
    for (uint32_t k = 1; k <= i; ++k) binoms[i*nmax+k] = binoms[(i-1)*nmax+(k-1)] + binoms[(i-1)*nmax+k];
  }
  tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dgin = 0, dB = 0, dop = 0, dsc = 0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto rel_free_host;
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_mcmc_relocation"))) { st = err ? err->status : TVDB_ERROR_IO; goto rel_free_host; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dgin, gin, n * 5u * sizeof(float), err)) != TVDB_OK) goto rel_cu;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dB, binoms, (size_t)nmax * nmax * sizeof(float), err)) != TVDB_OK) goto rel_cu;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dop, NULL, n * sizeof(float), err)) != TVDB_OK) goto rel_cu;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dsc, NULL, n * 3u * sizeof(float), err)) != TVDB_OK) goto rel_cu;
    {
      unsigned int uc = (unsigned int)n, un = nmax, block = 128, gb = (uc + block - 1u) / block;
      void* args[] = {&dgin, &dB, &dop, &dsc, &uc, &un};
      if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, gb, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto rel_cu; }
    }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto rel_cu; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(new_opacities, dop, n * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto rel_cu; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(new_scales, dsc, n * 3u * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto rel_cu; }
    st = TVDB_OK;
rel_cu:
    if (dsc) ctx->cuda.cuMemFree(dsc);
    if (dop) ctx->cuda.cuMemFree(dop);
    if (dB) ctx->cuda.cuMemFree(dB);
    if (dgin) ctx->cuda.cuMemFree(dgin);
    goto rel_free_host;
  }

  {
    tvdb_vk_buffer bg, bb, bo, bs, bu;
    if ((st = tvdb_vk_create_buffer(ctx, n * 5u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bg, err)) != TVDB_OK) goto rel_free_host;
    if ((st = tvdb_vk_create_buffer(ctx, (size_t)nmax * nmax * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bb, err)) != TVDB_OK) goto rel_g;
    if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto rel_b;
    if ((st = tvdb_vk_create_buffer(ctx, n * 3u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bs, err)) != TVDB_OK) goto rel_o;
    if ((st = tvdb_vk_create_buffer(ctx, 16, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto rel_s;
    memcpy(bg.mapped, gin, n * 5u * sizeof(float));
    memcpy(bb.mapped, binoms, (size_t)nmax * nmax * sizeof(float));
    uint32_t par[4] = {(uint32_t)n, nmax, 0, 0};
    memcpy(bu.mapped, par, sizeof(par));
    tvdb_vk_dispatch_desc d;
    memset(&d, 0, sizeof(d));
    d.spv = kTvdbGpuMcmcRelocationSpv; d.spv_len = kTvdbGpuMcmcRelocationSpv_len; d.descriptor_count = 5;
    d.buffers[0]=&bg; d.buffers[1]=&bb; d.buffers[2]=&bo; d.buffers[3]=&bs; d.buffers[4]=&bu;
    for (int i = 0; i < 4; ++i) d.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    d.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    d.group_x = (uint32_t)((n + 127u) / 128u);
    st = tvdb_vk_dispatch(ctx, &d, err);
    if (st == TVDB_OK) { memcpy(new_opacities, bo.mapped, n * sizeof(float)); memcpy(new_scales, bs.mapped, n * 3u * sizeof(float)); }
    tvdb_vk_destroy_buffer(ctx, &bu);
rel_s: tvdb_vk_destroy_buffer(ctx, &bs);
rel_o: tvdb_vk_destroy_buffer(ctx, &bo);
rel_b: tvdb_vk_destroy_buffer(ctx, &bb);
rel_g: tvdb_vk_destroy_buffer(ctx, &bg);
  }
rel_free_host:
  free(gin); free(binoms);
  return st;
}

tvdb_status_t tvdb_gpu_gaussian_mcmc_add_noise(tvdb_gpu_context_t* ctx, uint32_t num_gaussians,
                                               const float* means, const float* quats, const float* log_scales,
                                               const float* opacities_logit, const float* rand, float lr,
                                               float* out_means, tvdb_error_t* err) {
  if (!ctx || (num_gaussians && (!means || !quats || !log_scales || !opacities_logit || !rand || !out_means))) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid mcmc_add_noise arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (num_gaussians == 0) return TVDB_OK;
  size_t n = num_gaussians;
  float* gin = (float*)malloc(n * 14u * sizeof(float));
  if (!gin) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  for (size_t i = 0; i < n; ++i) {
    float* d = gin + i * 14u;
    d[0]=means[3*i+0]; d[1]=means[3*i+1]; d[2]=means[3*i+2];
    d[3]=quats[4*i+0]; d[4]=quats[4*i+1]; d[5]=quats[4*i+2]; d[6]=quats[4*i+3];
    d[7]=log_scales[3*i+0]; d[8]=log_scales[3*i+1]; d[9]=log_scales[3*i+2];
    d[10]=opacities_logit[i]; d[11]=rand[3*i+0]; d[12]=rand[3*i+1]; d[13]=rand[3*i+2];
  }
  tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dgin = 0, dout = 0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) { free(gin); return st; }
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_mcmc_noise"))) { free(gin); return err ? err->status : TVDB_ERROR_IO; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dgin, gin, n * 14u * sizeof(float), err)) != TVDB_OK) goto noi_cu;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, n * 3u * sizeof(float), err)) != TVDB_OK) goto noi_cu;
    {
      unsigned int uc = (unsigned int)n, block = 128, gb = (uc + block - 1u) / block;
      void* args[] = {&dgin, &dout, &uc, &lr};
      if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, gb, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto noi_cu; }
    }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto noi_cu; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out_means, dout, n * 3u * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto noi_cu; }
    st = TVDB_OK;
noi_cu:
    if (dout) ctx->cuda.cuMemFree(dout);
    if (dgin) ctx->cuda.cuMemFree(dgin);
    free(gin);
    return st;
  }

  {
    tvdb_vk_buffer bg, bo, bu;
    if ((st = tvdb_vk_create_buffer(ctx, n * 14u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bg, err)) != TVDB_OK) { free(gin); return st; }
    if ((st = tvdb_vk_create_buffer(ctx, n * 3u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto noi_g;
    if ((st = tvdb_vk_create_buffer(ctx, 16, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto noi_o;
    memcpy(bg.mapped, gin, n * 14u * sizeof(float));
    struct { uint32_t count; float lr; uint32_t pad[2]; } par;
    memset(&par, 0, sizeof(par)); par.count = (uint32_t)n; par.lr = lr;
    memcpy(bu.mapped, &par, sizeof(par));
    tvdb_vk_dispatch_desc d;
    memset(&d, 0, sizeof(d));
    d.spv = kTvdbGpuMcmcNoiseSpv; d.spv_len = kTvdbGpuMcmcNoiseSpv_len; d.descriptor_count = 3;
    d.buffers[0]=&bg; d.buffers[1]=&bo; d.buffers[2]=&bu;
    d.descriptor_types[0]=d.descriptor_types[1]=VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    d.descriptor_types[2]=VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    d.group_x = (uint32_t)((n + 127u) / 128u);
    st = tvdb_vk_dispatch(ctx, &d, err);
    if (st == TVDB_OK) memcpy(out_means, bo.mapped, n * 3u * sizeof(float));
    tvdb_vk_destroy_buffer(ctx, &bu);
noi_o: tvdb_vk_destroy_buffer(ctx, &bo);
noi_g: tvdb_vk_destroy_buffer(ctx, &bg);
  }
  free(gin);
  return st;
}

// ---- points -> dense occupancy mask -----------------------------------------

tvdb_status_t tvdb_gpu_points_to_mask(tvdb_gpu_context_t* ctx, tvdb_dense_grid* mask,
                                      const float* points, size_t n, tvdb_error_t* err) {
  if (!ctx || !mask || !mask->data || (!points && n) || mask->voxel_size <= 0.0f) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid points_to_mask arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (n == 0) return TVDB_OK;
  size_t nvox = (size_t)mask->nx * (size_t)mask->ny * (size_t)mask->nz;
  tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dm = 0, dp = 0;
    float* p4 = (float*)malloc(n * 4u * sizeof(float));
    if (!p4) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
    for (size_t i = 0; i < n; ++i) { p4[4*i+0]=points[3*i+0]; p4[4*i+1]=points[3*i+1]; p4[4*i+2]=points[3*i+2]; p4[4*i+3]=0.0f; }
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) { free(p4); return st; }
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_points_to_mask"))) { free(p4); return err ? err->status : TVDB_ERROR_IO; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dm, mask->data, nvox * sizeof(float), err)) != TVDB_OK) goto mcu_free;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dp, p4, n * 4u * sizeof(float), err)) != TVDB_OK) goto mcu_free;
    int nx = mask->nx, ny = mask->ny, nz = mask->nz;
    float ox = mask->ox, oy = mask->oy, oz = mask->oz, vs = mask->voxel_size;
    unsigned int uc = (unsigned int)n;
    void* args[] = {&dm, &dp, &nx, &ny, &nz, &ox, &oy, &oz, &vs, &uc};
    unsigned int block = 128, gridb = ((unsigned int)n + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, gridb, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto mcu_free; }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto mcu_free; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(mask->data, dm, nvox * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto mcu_free; }
    st = TVDB_OK;
mcu_free:
    if (dp) ctx->cuda.cuMemFree(dp);
    if (dm) ctx->cuda.cuMemFree(dm);
    free(p4);
    return st;
  }

  tvdb_vk_buffer bm, bp, bu;
  if ((st = tvdb_vk_create_buffer(ctx, nvox * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bm, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, n * 4u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bp, err)) != TVDB_OK) goto md_m;
  if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto md_p;
  memcpy(bm.mapped, mask->data, nvox * sizeof(float));
  { float* pm = (float*)bp.mapped;
    for (size_t i = 0; i < n; ++i) { pm[4*i+0]=points[3*i+0]; pm[4*i+1]=points[3*i+1]; pm[4*i+2]=points[3*i+2]; pm[4*i+3]=0.0f; } }
  struct { int32_t dim[4]; float grid[4]; uint32_t count; uint32_t pad[3]; } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = mask->nx; par.dim[1] = mask->ny; par.dim[2] = mask->nz;
  par.grid[0] = mask->ox; par.grid[1] = mask->oy; par.grid[2] = mask->oz; par.grid[3] = mask->voxel_size;
  par.count = (uint32_t)n;
  memcpy(bu.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuPointsToMaskSpv; d.spv_len = kTvdbGpuPointsToMaskSpv_len; d.descriptor_count = 3;
  d.buffers[0] = &bm; d.buffers[1] = &bp; d.buffers[2] = &bu;
  d.descriptor_types[0] = d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((n + 127u) / 128u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(mask->data, bm.mapped, nvox * sizeof(float));
  tvdb_vk_destroy_buffer(ctx, &bu);
md_p: tvdb_vk_destroy_buffer(ctx, &bp);
md_m: tvdb_vk_destroy_buffer(ctx, &bm);
  return st;
}

// ---- sparse voxelize (dense occupancy + atomic-counter compaction) ----------

static size_t tvdb_next_pow2_size(size_t v) {
  // Guard against overflow: above the top bit, `p <<= 1` would wrap to 0 and
  // spin forever. Return 0 so the caller's size cap rejects it.
  if (v > (~(size_t)0 >> 1) + 1) return 0;
  size_t p = 1; while (p < v) p <<= 1; return p;
}

static int tvdb_cmp_int3(const void* a, const void* b) {
  const int32_t* x = (const int32_t*)a; const int32_t* y = (const int32_t*)b;
  if (x[0] != y[0]) return x[0] < y[0] ? -1 : 1;
  if (x[1] != y[1]) return x[1] < y[1] ? -1 : 1;
  if (x[2] != y[2]) return x[2] < y[2] ? -1 : 1;
  return 0;
}

// Sort + remove duplicate ijk triples in place; returns the unique count.
static size_t tvdb_dedup_int3(int32_t* c, size_t n) {
  if (n == 0) return 0;
  qsort(c, n, 3u * sizeof(int32_t), tvdb_cmp_int3);
  size_t w = 1;
  for (size_t i = 1; i < n; ++i) {
    if (tvdb_cmp_int3(c + 3*i, c + 3*(w-1)) != 0) {
      if (w != i) { c[3*w+0]=c[3*i+0]; c[3*w+1]=c[3*i+1]; c[3*w+2]=c[3*i+2]; }
      ++w;
    }
  }
  return w;
}

// Unbounded (hash-based) voxelization: an open-addressing GPU hash set sized
// O(point count) builds the unique occupied-voxel set with memory independent
// of the ijk bounding-box volume. A host-side dedup finalizes the result so it
// is exact regardless of any insertion race.
static tvdb_status_t tvdb_gpu_voxelize_hashed(tvdb_gpu_context_t* ctx, const float* points, size_t n,
                                              const float voxel_size[3], const float origin[3],
                                              int32_t** out_coords, size_t* out_count, tvdb_error_t* err) {
  size_t cap = tvdb_next_pow2_size(n * 2u);  // load factor <= 0.5 (0 on overflow)
  if (cap == 0 || cap > (size_t)700000000) {  // overflow, or ~8.4 GB of keys: refuse rather than thrash VRAM
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "voxelize hash table too large");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (cap < 16u) cap = 16u;
  uint32_t mask = (uint32_t)(cap - 1u);
  int32_t* coords = (int32_t*)malloc(n * 3u * sizeof(int32_t));  // candidates (<= n unique voxels)
  if (!coords) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  uint32_t cand = 0;
  tvdb_status_t st;
  float vx = voxel_size[0], vy = voxel_size[1], vz = voxel_size[2];
  float ox = origin[0], oy = origin[1], oz = origin[2];

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fi = NULL, fc = NULL;
    CUdeviceptr dstate = 0, dkeys = 0, dp = 0, dcnt = 0, dout = 0;
    float* p4 = (float*)malloc(n * 4u * sizeof(float));
    uint32_t* zstate = (uint32_t*)calloc(cap, sizeof(uint32_t));
    if (!p4 || !zstate) { free(p4); free(zstate); free(coords); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
    for (size_t i = 0; i < n; ++i) { p4[4*i+0]=points[3*i+0]; p4[4*i+1]=points[3*i+1]; p4[4*i+2]=points[3*i+2]; p4[4*i+3]=0.0f; }
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto hcu_host;
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fi, module, "tvdb_cuda_hash_insert"))) { st = err ? err->status : TVDB_ERROR_IO; goto hcu_host; }
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fc, module, "tvdb_cuda_hash_compact"))) { st = err ? err->status : TVDB_ERROR_IO; goto hcu_host; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dstate, zstate, cap * sizeof(uint32_t), err)) != TVDB_OK) goto hcu_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dkeys, NULL, cap * 3u * sizeof(int32_t), err)) != TVDB_OK) goto hcu_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dp, p4, n * 4u * sizeof(float), err)) != TVDB_OK) goto hcu_dev;
    uint32_t zero = 0;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dcnt, &zero, sizeof(uint32_t), err)) != TVDB_OK) goto hcu_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, cap * 3u * sizeof(int32_t), err)) != TVDB_OK) goto hcu_dev;
    unsigned int uc = (unsigned int)n, ucap = (unsigned int)cap, umask = mask;
    void* iargs[] = {&dstate, &dkeys, &dp, &vx, &vy, &vz, &ox, &oy, &oz, &uc, &ucap, &umask};
    unsigned int block = 128, gi = (uc + block - 1u) / block, gc = (ucap + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fi, gi, 1, 1, block, 1, 1, 0, NULL, iargs, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto hcu_dev; }
    void* cargs[] = {&dstate, &dkeys, &dcnt, &dout, &ucap};
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fc, gc, 1, 1, block, 1, 1, 0, NULL, cargs, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto hcu_dev; }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto hcu_dev; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(&cand, dcnt, sizeof(uint32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto hcu_dev; }
    if (cand > n) cand = (uint32_t)n;
    if (cand && !tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(coords, dout, (size_t)cand * 3u * sizeof(int32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto hcu_dev; }
    st = TVDB_OK;
hcu_dev:
    if (dout) ctx->cuda.cuMemFree(dout);
    if (dcnt) ctx->cuda.cuMemFree(dcnt);
    if (dp) ctx->cuda.cuMemFree(dp);
    if (dkeys) ctx->cuda.cuMemFree(dkeys);
    if (dstate) ctx->cuda.cuMemFree(dstate);
hcu_host:
    free(p4); free(zstate);
    if (st != TVDB_OK) { free(coords); return st; }
  } else {
    tvdb_vk_buffer bstate, bkeys, bp, bcnt, bout, bui, buc;
    if ((st = tvdb_vk_create_buffer(ctx, cap * sizeof(uint32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bstate, err)) != TVDB_OK) { free(coords); return st; }
    if ((st = tvdb_vk_create_buffer(ctx, cap * 3u * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bkeys, err)) != TVDB_OK) goto hd_state;
    if ((st = tvdb_vk_create_buffer(ctx, n * 4u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bp, err)) != TVDB_OK) goto hd_keys;
    if ((st = tvdb_vk_create_buffer(ctx, sizeof(uint32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bcnt, err)) != TVDB_OK) goto hd_p;
    if ((st = tvdb_vk_create_buffer(ctx, cap * 3u * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bout, err)) != TVDB_OK) goto hd_cnt;
    if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bui, err)) != TVDB_OK) goto hd_out;
    if ((st = tvdb_vk_create_buffer(ctx, 16, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &buc, err)) != TVDB_OK) goto hd_ui;
    memset(bstate.mapped, 0, cap * sizeof(uint32_t));
    *(uint32_t*)bcnt.mapped = 0u;
    { float* pm = (float*)bp.mapped;
      for (size_t i = 0; i < n; ++i) { pm[4*i+0]=points[3*i+0]; pm[4*i+1]=points[3*i+1]; pm[4*i+2]=points[3*i+2]; pm[4*i+3]=0.0f; } }
    struct { float vs[4]; float origin[4]; uint32_t count; uint32_t cap; uint32_t mask; uint32_t pad; } ipar;
    memset(&ipar, 0, sizeof(ipar));
    ipar.vs[0]=vx; ipar.vs[1]=vy; ipar.vs[2]=vz; ipar.origin[0]=ox; ipar.origin[1]=oy; ipar.origin[2]=oz;
    ipar.count=(uint32_t)n; ipar.cap=(uint32_t)cap; ipar.mask=mask;
    memcpy(bui.mapped, &ipar, sizeof(ipar));
    struct { uint32_t cap; uint32_t pad[3]; } cpar;
    memset(&cpar, 0, sizeof(cpar)); cpar.cap=(uint32_t)cap;
    memcpy(buc.mapped, &cpar, sizeof(cpar));
    {
      tvdb_vk_dispatch_desc di;
      memset(&di, 0, sizeof(di));
      di.spv = kTvdbGpuHashInsertSpv; di.spv_len = kTvdbGpuHashInsertSpv_len; di.descriptor_count = 4;
      di.buffers[0]=&bstate; di.buffers[1]=&bkeys; di.buffers[2]=&bp; di.buffers[3]=&bui;
      di.descriptor_types[0]=di.descriptor_types[1]=di.descriptor_types[2]=VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
      di.descriptor_types[3]=VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
      di.group_x = (uint32_t)((n + 127u) / 128u);
      st = tvdb_vk_dispatch(ctx, &di, err);
    }
    if (st == TVDB_OK) {
      tvdb_vk_dispatch_desc dc;
      memset(&dc, 0, sizeof(dc));
      dc.spv = kTvdbGpuHashCompactSpv; dc.spv_len = kTvdbGpuHashCompactSpv_len; dc.descriptor_count = 5;
      dc.buffers[0]=&bstate; dc.buffers[1]=&bkeys; dc.buffers[2]=&bcnt; dc.buffers[3]=&bout; dc.buffers[4]=&buc;
      dc.descriptor_types[0]=dc.descriptor_types[1]=dc.descriptor_types[2]=dc.descriptor_types[3]=VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
      dc.descriptor_types[4]=VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
      dc.group_x = (uint32_t)((cap + 127u) / 128u);
      st = tvdb_vk_dispatch(ctx, &dc, err);
    }
    if (st == TVDB_OK) {
      cand = *(uint32_t*)bcnt.mapped;
      if (cand > n) cand = (uint32_t)n;
      memcpy(coords, bout.mapped, (size_t)cand * 3u * sizeof(int32_t));
    }
    tvdb_vk_destroy_buffer(ctx, &buc);
hd_ui: tvdb_vk_destroy_buffer(ctx, &bui);
hd_out: tvdb_vk_destroy_buffer(ctx, &bout);
hd_cnt: tvdb_vk_destroy_buffer(ctx, &bcnt);
hd_p: tvdb_vk_destroy_buffer(ctx, &bp);
hd_keys: tvdb_vk_destroy_buffer(ctx, &bkeys);
hd_state: tvdb_vk_destroy_buffer(ctx, &bstate);
    if (st != TVDB_OK) { free(coords); return st; }
  }

  size_t uniq = tvdb_dedup_int3(coords, cand);
  *out_coords = coords;
  *out_count = uniq;
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_voxelize_points_unbounded(tvdb_gpu_context_t* ctx, const float* points, size_t n,
                                                 const float voxel_size[3], const float origin[3],
                                                 int32_t** out_coords, size_t* out_count, tvdb_error_t* err) {
  if (out_coords) *out_coords = NULL;
  if (out_count) *out_count = 0;
  if (!ctx || !out_coords || !out_count || !voxel_size || !origin || (!points && n) ||
      voxel_size[0] <= 0.0f || voxel_size[1] <= 0.0f || voxel_size[2] <= 0.0f) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid voxelize_points_unbounded arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (n == 0) return TVDB_OK;
  return tvdb_gpu_voxelize_hashed(ctx, points, n, voxel_size, origin, out_coords, out_count, err);
}

tvdb_status_t tvdb_gpu_voxelize_points(tvdb_gpu_context_t* ctx, const float* points, size_t n,
                                       const float voxel_size[3], const float origin[3],
                                       int32_t** out_coords, size_t* out_count, tvdb_error_t* err) {
  if (out_coords) *out_coords = NULL;
  if (out_count) *out_count = 0;
  if (!ctx || !out_coords || !out_count || !voxel_size || !origin || (!points && n) ||
      voxel_size[0] <= 0.0f || voxel_size[1] <= 0.0f || voxel_size[2] <= 0.0f) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid voxelize_points arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (n == 0) return TVDB_OK;

  // ijk bounding box over all points (host).
  int32_t bbmin[3], bbmax[3];
  for (int a = 0; a < 3; ++a) {
    int v = (int)floorf((points[a] - origin[a]) / voxel_size[a]);
    bbmin[a] = bbmax[a] = v;
  }
  for (size_t i = 1; i < n; ++i)
    for (int a = 0; a < 3; ++a) {
      int v = (int)floorf((points[3*i+a] - origin[a]) / voxel_size[a]);
      if (v < bbmin[a]) bbmin[a] = v;
      if (v > bbmax[a]) bbmax[a] = v;
    }
  long long dx = (long long)bbmax[0] - bbmin[0] + 1;
  long long dy = (long long)bbmax[1] - bbmin[1] + 1;
  long long dz = (long long)bbmax[2] - bbmin[2] + 1;
  long long vol = dx * dy * dz;
  if (vol <= 0 || vol > (long long)400000000) {  // ~1.6 GB of uint occupancy
    // Dense bbox occupancy would exceed VRAM; use the O(n) hash-set path, whose
    // memory is independent of the bounding-box volume.
    return tvdb_gpu_voxelize_hashed(ctx, points, n, voxel_size, origin, out_coords, out_count, err);
  }
  size_t volume = (size_t)vol;
  int32_t* coords = (int32_t*)malloc(n * 3u * sizeof(int32_t));
  if (!coords) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  uint32_t unique = 0;
  tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fm = NULL, fc = NULL;
    CUdeviceptr docc = 0, dp = 0, dcnt = 0, dout = 0;
    float* p4 = (float*)malloc(n * 4u * sizeof(float));
    uint32_t* zocc = (uint32_t*)calloc(volume, sizeof(uint32_t));
    if (!p4 || !zocc) { free(p4); free(zocc); free(coords); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
    for (size_t i = 0; i < n; ++i) { p4[4*i+0]=points[3*i+0]; p4[4*i+1]=points[3*i+1]; p4[4*i+2]=points[3*i+2]; p4[4*i+3]=0.0f; }
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto vcu_host;
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fm, module, "tvdb_cuda_voxelize_mark"))) { st = err ? err->status : TVDB_ERROR_IO; goto vcu_host; }
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fc, module, "tvdb_cuda_voxelize_compact"))) { st = err ? err->status : TVDB_ERROR_IO; goto vcu_host; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &docc, zocc, volume * sizeof(uint32_t), err)) != TVDB_OK) goto vcu_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dp, p4, n * 4u * sizeof(float), err)) != TVDB_OK) goto vcu_dev;
    uint32_t zero = 0;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dcnt, &zero, sizeof(uint32_t), err)) != TVDB_OK) goto vcu_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, n * 3u * sizeof(int32_t), err)) != TVDB_OK) goto vcu_dev;
    int idx[3] = {(int)dx, (int)dy, (int)dz}, bb[3] = {bbmin[0], bbmin[1], bbmin[2]};
    float vx = voxel_size[0], vy = voxel_size[1], vz = voxel_size[2], ox = origin[0], oy = origin[1], oz = origin[2];
    unsigned int uc = (unsigned int)n, ucap = (unsigned int)n, uvol = (unsigned int)volume;
    void* margs[] = {&docc, &dp, &idx[0], &idx[1], &idx[2], &bb[0], &bb[1], &bb[2], &vx, &vy, &vz, &ox, &oy, &oz, &uc};
    unsigned int block = 128, gmark = (uc + block - 1u) / block, gcomp = (uvol + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fm, gmark, 1, 1, block, 1, 1, 0, NULL, margs, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto vcu_dev; }
    void* cargs[] = {&docc, &dcnt, &dout, &idx[0], &idx[1], &idx[2], &bb[0], &bb[1], &bb[2], &ucap};
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fc, gcomp, 1, 1, block, 1, 1, 0, NULL, cargs, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto vcu_dev; }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto vcu_dev; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(&unique, dcnt, sizeof(uint32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto vcu_dev; }
    if (unique > n) unique = (uint32_t)n;
    if (unique && !tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(coords, dout, (size_t)unique * 3u * sizeof(int32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto vcu_dev; }
    st = TVDB_OK;
vcu_dev:
    if (dout) ctx->cuda.cuMemFree(dout);
    if (dcnt) ctx->cuda.cuMemFree(dcnt);
    if (dp) ctx->cuda.cuMemFree(dp);
    if (docc) ctx->cuda.cuMemFree(docc);
vcu_host:
    free(p4); free(zocc);
    if (st == TVDB_OK) { *out_coords = coords; *out_count = unique; } else free(coords);
    return st;
  }

  tvdb_vk_buffer bocc, bp, bcnt, bout, bum, buc;
  if ((st = tvdb_vk_create_buffer(ctx, volume * sizeof(uint32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bocc, err)) != TVDB_OK) { free(coords); return st; }
  if ((st = tvdb_vk_create_buffer(ctx, n * 4u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bp, err)) != TVDB_OK) goto vd_occ;
  if ((st = tvdb_vk_create_buffer(ctx, sizeof(uint32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bcnt, err)) != TVDB_OK) goto vd_p;
  if ((st = tvdb_vk_create_buffer(ctx, n * 3u * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bout, err)) != TVDB_OK) goto vd_cnt;
  if ((st = tvdb_vk_create_buffer(ctx, 80, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bum, err)) != TVDB_OK) goto vd_out;
  if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &buc, err)) != TVDB_OK) goto vd_um;
  memset(bocc.mapped, 0, volume * sizeof(uint32_t));
  *(uint32_t*)bcnt.mapped = 0u;
  { float* pm = (float*)bp.mapped;
    for (size_t i = 0; i < n; ++i) { pm[4*i+0]=points[3*i+0]; pm[4*i+1]=points[3*i+1]; pm[4*i+2]=points[3*i+2]; pm[4*i+3]=0.0f; } }
  struct { int32_t dims[4]; int32_t bbmin[4]; float vs[4]; float origin[4]; uint32_t count; uint32_t pad[3]; } mpar;
  memset(&mpar, 0, sizeof(mpar));
  mpar.dims[0]=(int)dx; mpar.dims[1]=(int)dy; mpar.dims[2]=(int)dz;
  mpar.bbmin[0]=bbmin[0]; mpar.bbmin[1]=bbmin[1]; mpar.bbmin[2]=bbmin[2];
  mpar.vs[0]=voxel_size[0]; mpar.vs[1]=voxel_size[1]; mpar.vs[2]=voxel_size[2];
  mpar.origin[0]=origin[0]; mpar.origin[1]=origin[1]; mpar.origin[2]=origin[2];
  mpar.count=(uint32_t)n;
  memcpy(bum.mapped, &mpar, sizeof(mpar));
  struct { int32_t dims[4]; int32_t bbmin[4]; uint32_t cap; uint32_t pad[3]; } cpar;
  memset(&cpar, 0, sizeof(cpar));
  cpar.dims[0]=(int)dx; cpar.dims[1]=(int)dy; cpar.dims[2]=(int)dz;
  cpar.bbmin[0]=bbmin[0]; cpar.bbmin[1]=bbmin[1]; cpar.bbmin[2]=bbmin[2];
  cpar.cap=(uint32_t)n;
  memcpy(buc.mapped, &cpar, sizeof(cpar));
  {
    tvdb_vk_dispatch_desc dm;
    memset(&dm, 0, sizeof(dm));
    dm.spv = kTvdbGpuVoxelizeMarkSpv; dm.spv_len = kTvdbGpuVoxelizeMarkSpv_len; dm.descriptor_count = 3;
    dm.buffers[0] = &bocc; dm.buffers[1] = &bp; dm.buffers[2] = &bum;
    dm.descriptor_types[0] = dm.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    dm.descriptor_types[2] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    dm.group_x = (uint32_t)((n + 127u) / 128u);
    st = tvdb_vk_dispatch(ctx, &dm, err);
  }
  if (st == TVDB_OK) {
    tvdb_vk_dispatch_desc dc;
    memset(&dc, 0, sizeof(dc));
    dc.spv = kTvdbGpuVoxelizeCompactSpv; dc.spv_len = kTvdbGpuVoxelizeCompactSpv_len; dc.descriptor_count = 4;
    dc.buffers[0] = &bocc; dc.buffers[1] = &bcnt; dc.buffers[2] = &bout; dc.buffers[3] = &buc;
    dc.descriptor_types[0] = dc.descriptor_types[1] = dc.descriptor_types[2] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    dc.descriptor_types[3] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    dc.group_x = (uint32_t)((volume + 127u) / 128u);
    st = tvdb_vk_dispatch(ctx, &dc, err);
  }
  if (st == TVDB_OK) {
    unique = *(uint32_t*)bcnt.mapped;
    if (unique > n) unique = (uint32_t)n;
    memcpy(coords, bout.mapped, (size_t)unique * 3u * sizeof(int32_t));
  }
  tvdb_vk_destroy_buffer(ctx, &buc);
vd_um: tvdb_vk_destroy_buffer(ctx, &bum);
vd_out: tvdb_vk_destroy_buffer(ctx, &bout);
vd_cnt: tvdb_vk_destroy_buffer(ctx, &bcnt);
vd_p: tvdb_vk_destroy_buffer(ctx, &bp);
vd_occ: tvdb_vk_destroy_buffer(ctx, &bocc);
  if (st == TVDB_OK) { *out_coords = coords; *out_count = unique; } else free(coords);
  return st;
}

// ---- sparse erode (dense occupancy + compaction) ----------------------------

// One erode step on raw coord/value arrays -> malloc'd output arrays.
static tvdb_status_t tvdb_gpu_sparse_erode_step(tvdb_gpu_context_t* ctx,
    const int32_t* coords, const float* vals, size_t cnt,
    int32_t** out_c, float** out_v, size_t* out_n, tvdb_error_t* err) {
  *out_c = NULL; *out_v = NULL; *out_n = 0;
  if (cnt == 0) return TVDB_OK;
  int32_t bbmin[3], bbmax[3];
  for (int a = 0; a < 3; ++a) { bbmin[a] = bbmax[a] = coords[a]; }
  for (size_t i = 1; i < cnt; ++i)
    for (int a = 0; a < 3; ++a) { int v = coords[3*i+a]; if (v < bbmin[a]) bbmin[a] = v; if (v > bbmax[a]) bbmax[a] = v; }
  long long dx = (long long)bbmax[0]-bbmin[0]+1, dy = (long long)bbmax[1]-bbmin[1]+1, dz = (long long)bbmax[2]-bbmin[2]+1;
  if (dx<=0 || dy<=0 || dz<=0 || dx>400000000 || dy>400000000/dx || dz>400000000/(dx*dy)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"sparse bbox too large"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  long long vol = dx*dy*dz;
  if (vol <= 0 || vol > (long long)400000000) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "sparse erode bbox too large");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  size_t volume = (size_t)vol;
  int32_t* outd = (int32_t*)malloc(cnt * 4u * sizeof(int32_t));
  if (!outd) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  uint32_t m = 0;
  tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fm = NULL, fe = NULL;
    CUdeviceptr docc = 0, dval = 0, dc = 0, div = 0, dcnt = 0, dout = 0;
    int32_t* c4 = (int32_t*)malloc(cnt * 4u * sizeof(int32_t));
    uint32_t* zocc = (uint32_t*)calloc(volume, sizeof(uint32_t));
    if (!c4 || !zocc) { free(c4); free(zocc); free(outd); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
    for (size_t i = 0; i < cnt; ++i) { c4[4*i+0]=coords[3*i+0]; c4[4*i+1]=coords[3*i+1]; c4[4*i+2]=coords[3*i+2]; c4[4*i+3]=0; }
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto ecu_host;
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fm, module, "tvdb_cuda_sparse_mark"))) { st = err?err->status:TVDB_ERROR_IO; goto ecu_host; }
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fe, module, "tvdb_cuda_sparse_erode"))) { st = err?err->status:TVDB_ERROR_IO; goto ecu_host; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &docc, zocc, volume*sizeof(uint32_t), err)) != TVDB_OK) goto ecu_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dval, NULL, volume*sizeof(float), err)) != TVDB_OK) goto ecu_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dc, c4, cnt*4u*sizeof(int32_t), err)) != TVDB_OK) goto ecu_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &div, vals, cnt*sizeof(float), err)) != TVDB_OK) goto ecu_dev;
    uint32_t zero = 0;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dcnt, &zero, sizeof(uint32_t), err)) != TVDB_OK) goto ecu_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, cnt*4u*sizeof(int32_t), err)) != TVDB_OK) goto ecu_dev;
    int idx[3] = {(int)dx,(int)dy,(int)dz}, bb[3] = {bbmin[0],bbmin[1],bbmin[2]};
    unsigned int uc = (unsigned int)cnt, ucap = (unsigned int)cnt, uvol = (unsigned int)volume;
    void* margs[] = {&docc,&dval,&dc,&div,&idx[0],&idx[1],&idx[2],&bb[0],&bb[1],&bb[2],&uc};
    unsigned int block=128, gm=(uc+block-1u)/block, ge=(uvol+block-1u)/block;
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fm, gm,1,1, block,1,1, 0, NULL, margs, NULL))) { st=err?err->status:TVDB_ERROR_IO; goto ecu_dev; }
    void* eargs[] = {&docc,&dval,&dcnt,&dout,&idx[0],&idx[1],&idx[2],&bb[0],&bb[1],&bb[2],&ucap};
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fe, ge,1,1, block,1,1, 0, NULL, eargs, NULL))) { st=err?err->status:TVDB_ERROR_IO; goto ecu_dev; }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st=err?err->status:TVDB_ERROR_IO; goto ecu_dev; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(&m, dcnt, sizeof(uint32_t)))) { st=err?err->status:TVDB_ERROR_IO; goto ecu_dev; }
    if (m > cnt) m = (uint32_t)cnt;
    if (m && !tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(outd, dout, (size_t)m*4u*sizeof(int32_t)))) { st=err?err->status:TVDB_ERROR_IO; goto ecu_dev; }
    st = TVDB_OK;
ecu_dev:
    if (dout) ctx->cuda.cuMemFree(dout);
    if (dcnt) ctx->cuda.cuMemFree(dcnt);
    if (div) ctx->cuda.cuMemFree(div);
    if (dc) ctx->cuda.cuMemFree(dc);
    if (dval) ctx->cuda.cuMemFree(dval);
    if (docc) ctx->cuda.cuMemFree(docc);
ecu_host:
    free(c4); free(zocc);
    goto finish;
  }
  {
    tvdb_vk_buffer bocc, bval, bc, biv, bcnt, bout, bum, bue;
    if ((st = tvdb_vk_create_buffer(ctx, volume*sizeof(uint32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bocc, err)) != TVDB_OK) { free(outd); return st; }
    if ((st = tvdb_vk_create_buffer(ctx, volume*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bval, err)) != TVDB_OK) goto ed_occ;
    if ((st = tvdb_vk_create_buffer(ctx, cnt*4u*sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bc, err)) != TVDB_OK) goto ed_val;
    if ((st = tvdb_vk_create_buffer(ctx, cnt*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &biv, err)) != TVDB_OK) goto ed_c;
    if ((st = tvdb_vk_create_buffer(ctx, sizeof(uint32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bcnt, err)) != TVDB_OK) goto ed_iv;
    if ((st = tvdb_vk_create_buffer(ctx, cnt*4u*sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bout, err)) != TVDB_OK) goto ed_cnt;
    if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bum, err)) != TVDB_OK) goto ed_out;
    if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bue, err)) != TVDB_OK) goto ed_um;
    memset(bocc.mapped, 0, volume*sizeof(uint32_t));
    *(uint32_t*)bcnt.mapped = 0u;
    { int32_t* cm = (int32_t*)bc.mapped;
      for (size_t i = 0; i < cnt; ++i) { cm[4*i+0]=coords[3*i+0]; cm[4*i+1]=coords[3*i+1]; cm[4*i+2]=coords[3*i+2]; cm[4*i+3]=0; } }
    memcpy(biv.mapped, vals, cnt*sizeof(float));
    struct { int32_t dims[4]; int32_t bbmin[4]; uint32_t count; uint32_t pad[3]; } mp;
    memset(&mp, 0, sizeof(mp));
    mp.dims[0]=(int)dx; mp.dims[1]=(int)dy; mp.dims[2]=(int)dz; mp.bbmin[0]=bbmin[0]; mp.bbmin[1]=bbmin[1]; mp.bbmin[2]=bbmin[2]; mp.count=(uint32_t)cnt;
    memcpy(bum.mapped, &mp, sizeof(mp));
    struct { int32_t dims[4]; int32_t bbmin[4]; uint32_t count; uint32_t cap; uint32_t pad[2]; } ep;
    memset(&ep, 0, sizeof(ep));
    ep.dims[0]=(int)dx; ep.dims[1]=(int)dy; ep.dims[2]=(int)dz; ep.bbmin[0]=bbmin[0]; ep.bbmin[1]=bbmin[1]; ep.bbmin[2]=bbmin[2]; ep.cap=(uint32_t)cnt;
    memcpy(bue.mapped, &ep, sizeof(ep));
    tvdb_vk_dispatch_desc dm;
    memset(&dm, 0, sizeof(dm));
    dm.spv = kTvdbGpuSparseMarkSpv; dm.spv_len = kTvdbGpuSparseMarkSpv_len; dm.descriptor_count = 5;
    dm.buffers[0]=&bocc; dm.buffers[1]=&bval; dm.buffers[2]=&bc; dm.buffers[3]=&biv; dm.buffers[4]=&bum;
    for (int i = 0; i < 4; ++i) dm.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    dm.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    dm.group_x = (uint32_t)((cnt + 127u) / 128u);
    /* Mark and erode are two dependent dispatches with no host traffic between
     * them, so both are queued and awaited once. */
    dm.defer_wait = TVDB_VK_DEFERRED_SUBMIT;
    st = tvdb_vk_dispatch(ctx, &dm, err);
    if (st == TVDB_OK) {
      tvdb_vk_dispatch_desc de;
      memset(&de, 0, sizeof(de));
      de.spv = kTvdbGpuSparseErodeSpv; de.spv_len = kTvdbGpuSparseErodeSpv_len; de.descriptor_count = 5;
      de.buffers[0]=&bocc; de.buffers[1]=&bval; de.buffers[2]=&bcnt; de.buffers[3]=&bout; de.buffers[4]=&bue;
      for (int i = 0; i < 4; ++i) de.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
      de.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
      de.group_x = (uint32_t)((volume + 127u) / 128u);
      de.defer_wait = TVDB_VK_DEFERRED_SUBMIT;
      st = tvdb_vk_dispatch(ctx, &de, err);
    }
    if (st == TVDB_OK) st = tvdb_vk_flush(ctx, err);
    if (st == TVDB_OK) {
      m = *(uint32_t*)bcnt.mapped; if (m > cnt) m = (uint32_t)cnt;
      memcpy(outd, bout.mapped, (size_t)m*4u*sizeof(int32_t));
    }
    tvdb_vk_destroy_buffer(ctx, &bue);
ed_um: tvdb_vk_destroy_buffer(ctx, &bum);
ed_out: tvdb_vk_destroy_buffer(ctx, &bout);
ed_cnt: tvdb_vk_destroy_buffer(ctx, &bcnt);
ed_iv: tvdb_vk_destroy_buffer(ctx, &biv);
ed_c: tvdb_vk_destroy_buffer(ctx, &bc);
ed_val: tvdb_vk_destroy_buffer(ctx, &bval);
ed_occ: tvdb_vk_destroy_buffer(ctx, &bocc);
  }
finish:
  if (st == TVDB_OK) {
    int32_t* oc = (int32_t*)malloc((m ? (size_t)m : 1) * 3u * sizeof(int32_t));
    float* ov = (float*)malloc((m ? (size_t)m : 1) * sizeof(float));
    if (!oc || !ov) { free(oc); free(ov); free(outd); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
    for (uint32_t i = 0; i < m; ++i) {
      oc[3*i+0]=outd[4*i+0]; oc[3*i+1]=outd[4*i+1]; oc[3*i+2]=outd[4*i+2];
      int32_t bits = outd[4*i+3]; memcpy(&ov[i], &bits, sizeof(float));
    }
    *out_c = oc; *out_v = ov; *out_n = m;
  }
  free(outd);
  return st;
}

// One dilate step on raw coord/value arrays -> malloc'd output arrays.
static tvdb_status_t tvdb_gpu_sparse_dilate_step(tvdb_gpu_context_t* ctx,
    const int32_t* coords, const float* vals, size_t cnt, float background,
    int32_t** out_c, float** out_v, size_t* out_n, tvdb_error_t* err) {
  *out_c = NULL; *out_v = NULL; *out_n = 0;
  if (cnt == 0) return TVDB_OK;
  int32_t bbmin[3], bbmax[3];
  for (int a = 0; a < 3; ++a) bbmin[a] = bbmax[a] = coords[a];
  for (size_t i = 1; i < cnt; ++i)
    for (int a = 0; a < 3; ++a) { int v = coords[3*i+a]; if (v < bbmin[a]) bbmin[a] = v; if (v > bbmax[a]) bbmax[a] = v; }
  for (int a = 0; a < 3; ++a) { if(bbmin[a]>INT32_MIN) --bbmin[a]; if(bbmax[a]<INT32_MAX) ++bbmax[a]; }  // room for grown neighbors
  long long dx = (long long)bbmax[0]-bbmin[0]+1, dy = (long long)bbmax[1]-bbmin[1]+1, dz = (long long)bbmax[2]-bbmin[2]+1;
  if (dx<=0 || dy<=0 || dz<=0 || dx>400000000 || dy>400000000/dx || dz>400000000/(dx*dy)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"sparse bbox too large"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  long long vol = dx*dy*dz;
  if (vol <= 0 || vol > (long long)400000000) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "sparse dilate bbox too large");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  size_t volume = (size_t)vol;
  size_t cap = cnt * 7u;
  int32_t* outd = (int32_t*)malloc(cap * 4u * sizeof(int32_t));
  if (!outd) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  uint32_t m = 0;
  tvdb_status_t st;
  int idx[3] = {(int)dx,(int)dy,(int)dz}, bb[3] = {bbmin[0],bbmin[1],bbmin[2]};

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fm = NULL, fs = NULL, ff = NULL;
    CUdeviceptr docc = 0, dval = 0, doutocc = 0, dc = 0, div = 0, dcnt = 0, dout = 0;
    int32_t* c4 = (int32_t*)malloc(cnt*4u*sizeof(int32_t));
    uint32_t* zocc = (uint32_t*)calloc(volume, sizeof(uint32_t));
    float* bgfill = (float*)malloc(volume*sizeof(float));
    if (!c4 || !zocc || !bgfill) { free(c4); free(zocc); free(bgfill); free(outd); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
    for (size_t i = 0; i < cnt; ++i) { c4[4*i+0]=coords[3*i+0]; c4[4*i+1]=coords[3*i+1]; c4[4*i+2]=coords[3*i+2]; c4[4*i+3]=0; }
    for (size_t i = 0; i < volume; ++i) bgfill[i] = background;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto dcu_host;
    if (!tvdb_cuda_ok(ctx, err, "f", ctx->cuda.cuModuleGetFunction(&fm, module, "tvdb_cuda_sparse_mark")) ||
        !tvdb_cuda_ok(ctx, err, "f", ctx->cuda.cuModuleGetFunction(&fs, module, "tvdb_cuda_sparse_dilate_scatter")) ||
        !tvdb_cuda_ok(ctx, err, "f", ctx->cuda.cuModuleGetFunction(&ff, module, "tvdb_cuda_sparse_finalize"))) { st = err?err->status:TVDB_ERROR_IO; goto dcu_host; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &docc, zocc, volume*sizeof(uint32_t), err)) != TVDB_OK) goto dcu_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dval, bgfill, volume*sizeof(float), err)) != TVDB_OK) goto dcu_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &doutocc, zocc, volume*sizeof(uint32_t), err)) != TVDB_OK) goto dcu_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dc, c4, cnt*4u*sizeof(int32_t), err)) != TVDB_OK) goto dcu_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &div, vals, cnt*sizeof(float), err)) != TVDB_OK) goto dcu_dev;
    uint32_t zero = 0;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dcnt, &zero, sizeof(uint32_t), err)) != TVDB_OK) goto dcu_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, cap*4u*sizeof(int32_t), err)) != TVDB_OK) goto dcu_dev;
    unsigned int uc=(unsigned int)cnt, ucap=(unsigned int)cap, uvol=(unsigned int)volume, block=128;
    void* margs[] = {&docc,&dval,&dc,&div,&idx[0],&idx[1],&idx[2],&bb[0],&bb[1],&bb[2],&uc};
    if (!tvdb_cuda_ok(ctx, err, "k", ctx->cuda.cuLaunchKernel(fm,(uc+block-1u)/block,1,1,block,1,1,0,NULL,margs,NULL))) { st=err?err->status:TVDB_ERROR_IO; goto dcu_dev; }
    void* sargs[] = {&dval,&doutocc,&dc,&div,&idx[0],&idx[1],&idx[2],&bb[0],&bb[1],&bb[2],&uc};
    if (!tvdb_cuda_ok(ctx, err, "k", ctx->cuda.cuLaunchKernel(fs,(uc+block-1u)/block,1,1,block,1,1,0,NULL,sargs,NULL))) { st=err?err->status:TVDB_ERROR_IO; goto dcu_dev; }
    void* fargs[] = {&dval,&doutocc,&dcnt,&dout,&idx[0],&idx[1],&idx[2],&bb[0],&bb[1],&bb[2],&ucap};
    if (!tvdb_cuda_ok(ctx, err, "k", ctx->cuda.cuLaunchKernel(ff,(uvol+block-1u)/block,1,1,block,1,1,0,NULL,fargs,NULL))) { st=err?err->status:TVDB_ERROR_IO; goto dcu_dev; }
    if (!tvdb_cuda_ok(ctx, err, "s", ctx->cuda.cuCtxSynchronize())) { st=err?err->status:TVDB_ERROR_IO; goto dcu_dev; }
    if (!tvdb_cuda_ok(ctx, err, "c", ctx->cuda.cuMemcpyDtoH(&m, dcnt, sizeof(uint32_t)))) { st=err?err->status:TVDB_ERROR_IO; goto dcu_dev; }
    if (m > cap) m = (uint32_t)cap;
    if (m && !tvdb_cuda_ok(ctx, err, "c", ctx->cuda.cuMemcpyDtoH(outd, dout, (size_t)m*4u*sizeof(int32_t)))) { st=err?err->status:TVDB_ERROR_IO; goto dcu_dev; }
    st = TVDB_OK;
dcu_dev:
    if (dout) ctx->cuda.cuMemFree(dout);
    if (dcnt) ctx->cuda.cuMemFree(dcnt);
    if (div) ctx->cuda.cuMemFree(div);
    if (dc) ctx->cuda.cuMemFree(dc);
    if (doutocc) ctx->cuda.cuMemFree(doutocc);
    if (dval) ctx->cuda.cuMemFree(dval);
    if (docc) ctx->cuda.cuMemFree(docc);
dcu_host:
    free(c4); free(zocc); free(bgfill);
    goto dfinish;
  }
  {
    tvdb_vk_buffer bocc, bval, boutocc, bc, biv, bcnt, bout, buc, buf;
    if ((st = tvdb_vk_create_buffer(ctx, volume*sizeof(uint32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bocc, err)) != TVDB_OK) { free(outd); return st; }
    if ((st = tvdb_vk_create_buffer(ctx, volume*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bval, err)) != TVDB_OK) goto dd_occ;
    if ((st = tvdb_vk_create_buffer(ctx, volume*sizeof(uint32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &boutocc, err)) != TVDB_OK) goto dd_val;
    if ((st = tvdb_vk_create_buffer(ctx, cnt*4u*sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bc, err)) != TVDB_OK) goto dd_oo;
    if ((st = tvdb_vk_create_buffer(ctx, cnt*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &biv, err)) != TVDB_OK) goto dd_c;
    if ((st = tvdb_vk_create_buffer(ctx, sizeof(uint32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bcnt, err)) != TVDB_OK) goto dd_iv;
    if ((st = tvdb_vk_create_buffer(ctx, cap*4u*sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bout, err)) != TVDB_OK) goto dd_cnt;
    if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &buc, err)) != TVDB_OK) goto dd_out;
    if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &buf, err)) != TVDB_OK) goto dd_uc;
    memset(bocc.mapped, 0, volume*sizeof(uint32_t));
    memset(boutocc.mapped, 0, volume*sizeof(uint32_t));
    { float* vm = (float*)bval.mapped; for (size_t i = 0; i < volume; ++i) vm[i] = background; }
    *(uint32_t*)bcnt.mapped = 0u;
    { int32_t* cm = (int32_t*)bc.mapped;
      for (size_t i = 0; i < cnt; ++i) { cm[4*i+0]=coords[3*i+0]; cm[4*i+1]=coords[3*i+1]; cm[4*i+2]=coords[3*i+2]; cm[4*i+3]=0; } }
    memcpy(biv.mapped, vals, cnt*sizeof(float));
    struct { int32_t dims[4]; int32_t bbmin[4]; uint32_t count; uint32_t pad[3]; } cu;
    memset(&cu, 0, sizeof(cu));
    cu.dims[0]=(int)dx; cu.dims[1]=(int)dy; cu.dims[2]=(int)dz; cu.bbmin[0]=bbmin[0]; cu.bbmin[1]=bbmin[1]; cu.bbmin[2]=bbmin[2]; cu.count=(uint32_t)cnt;
    memcpy(buc.mapped, &cu, sizeof(cu));
    struct { int32_t dims[4]; int32_t bbmin[4]; uint32_t cap; uint32_t pad[3]; } fu;
    memset(&fu, 0, sizeof(fu));
    fu.dims[0]=(int)dx; fu.dims[1]=(int)dy; fu.dims[2]=(int)dz; fu.bbmin[0]=bbmin[0]; fu.bbmin[1]=bbmin[1]; fu.bbmin[2]=bbmin[2]; fu.cap=(uint32_t)cap;
    memcpy(buf.mapped, &fu, sizeof(fu));
    tvdb_vk_dispatch_desc dm;
    memset(&dm, 0, sizeof(dm));
    dm.spv = kTvdbGpuSparseMarkSpv; dm.spv_len = kTvdbGpuSparseMarkSpv_len; dm.descriptor_count = 5;
    dm.buffers[0]=&bocc; dm.buffers[1]=&bval; dm.buffers[2]=&bc; dm.buffers[3]=&biv; dm.buffers[4]=&buc;
    for (int i = 0; i < 4; ++i) dm.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    dm.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    dm.group_x = (uint32_t)((cnt + 127u) / 128u);
    /* mark -> scatter -> finalize is a three-kernel chain with no host traffic
     * in between; queue all three and wait once. */
    dm.defer_wait = TVDB_VK_DEFERRED_SUBMIT;
    st = tvdb_vk_dispatch(ctx, &dm, err);
    if (st == TVDB_OK) {
      tvdb_vk_dispatch_desc ds;
      memset(&ds, 0, sizeof(ds));
      ds.spv = kTvdbGpuSparseDilateScatterSpv; ds.spv_len = kTvdbGpuSparseDilateScatterSpv_len; ds.descriptor_count = 5;
      ds.buffers[0]=&bval; ds.buffers[1]=&boutocc; ds.buffers[2]=&bc; ds.buffers[3]=&biv; ds.buffers[4]=&buc;
      for (int i = 0; i < 4; ++i) ds.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
      ds.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
      ds.group_x = (uint32_t)((cnt + 127u) / 128u);
      ds.defer_wait = TVDB_VK_DEFERRED_SUBMIT;
      st = tvdb_vk_dispatch(ctx, &ds, err);
    }
    if (st == TVDB_OK) {
      tvdb_vk_dispatch_desc df;
      memset(&df, 0, sizeof(df));
      df.spv = kTvdbGpuSparseFinalizeSpv; df.spv_len = kTvdbGpuSparseFinalizeSpv_len; df.descriptor_count = 5;
      df.buffers[0]=&bval; df.buffers[1]=&boutocc; df.buffers[2]=&bcnt; df.buffers[3]=&bout; df.buffers[4]=&buf;
      for (int i = 0; i < 4; ++i) df.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
      df.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
      df.group_x = (uint32_t)((volume + 127u) / 128u);
      df.defer_wait = TVDB_VK_DEFERRED_SUBMIT;
      st = tvdb_vk_dispatch(ctx, &df, err);
    }
    if (st == TVDB_OK) st = tvdb_vk_flush(ctx, err);
    if (st == TVDB_OK) {
      m = *(uint32_t*)bcnt.mapped; if (m > cap) m = (uint32_t)cap;
      memcpy(outd, bout.mapped, (size_t)m*4u*sizeof(int32_t));
    }
    tvdb_vk_destroy_buffer(ctx, &buf);
dd_uc: tvdb_vk_destroy_buffer(ctx, &buc);
dd_out: tvdb_vk_destroy_buffer(ctx, &bout);
dd_cnt: tvdb_vk_destroy_buffer(ctx, &bcnt);
dd_iv: tvdb_vk_destroy_buffer(ctx, &biv);
dd_c: tvdb_vk_destroy_buffer(ctx, &bc);
dd_oo: tvdb_vk_destroy_buffer(ctx, &boutocc);
dd_val: tvdb_vk_destroy_buffer(ctx, &bval);
dd_occ: tvdb_vk_destroy_buffer(ctx, &bocc);
  }
dfinish:
  if (st == TVDB_OK) {
    int32_t* oc = (int32_t*)malloc((m ? (size_t)m : 1) * 3u * sizeof(int32_t));
    float* ov = (float*)malloc((m ? (size_t)m : 1) * sizeof(float));
    if (!oc || !ov) { free(oc); free(ov); free(outd); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
    for (uint32_t i = 0; i < m; ++i) {
      oc[3*i+0]=outd[4*i+0]; oc[3*i+1]=outd[4*i+1]; oc[3*i+2]=outd[4*i+2];
      int32_t bits = outd[4*i+3]; memcpy(&ov[i], &bits, sizeof(float));
    }
    *out_c = oc; *out_v = ov; *out_n = m;
  }
  free(outd);
  return st;
}

/* Canonicalize duplicate coordinates before non-atomic dense marking. */
typedef struct { tvdb_vec3i c; size_t index; } tvdb_morph_coord;
static int tvdb_morph_coord_compare(const void* a,const void* b) {
  const tvdb_morph_coord *x=a,*y=b;
  if(x->c.x!=y->c.x) return x->c.x<y->c.x ? -1:1;
  if(x->c.y!=y->c.y) return x->c.y<y->c.y ? -1:1;
  if(x->c.z!=y->c.z) return x->c.z<y->c.z ? -1:1;
  return x->index<y->index ? -1 : x->index>y->index;
}
static bool tvdb_gpu_morph_canonical(const tvdb_sparse_grid* in,int32_t* cc,float* cv,size_t* count) {
  size_t bytes;
  if(!tvdb_size_mul(in->count,sizeof(tvdb_morph_coord),&bytes)) return false;
  tvdb_morph_coord* sorted=malloc(bytes ? bytes : 1);
  if(!sorted) return false;
  for(size_t i=0;i<in->count;++i) { sorted[i].c=in->coords[i]; sorted[i].index=i; }
  qsort(sorted,in->count,sizeof(*sorted),tvdb_morph_coord_compare);
  size_t n=0;
  for(size_t i=0;i<in->count;++i) {
    if(i && sorted[i].c.x==sorted[i-1].c.x && sorted[i].c.y==sorted[i-1].c.y && sorted[i].c.z==sorted[i-1].c.z) continue;
    cc[3*n]=sorted[i].c.x; cc[3*n+1]=sorted[i].c.y; cc[3*n+2]=sorted[i].c.z;
    cv[n++]=in->values[sorted[i].index];
  }
  free(sorted); *count=n; return true;
}

static tvdb_status_t tvdb_gpu_dilate_sparse_impl(tvdb_gpu_context_t* ctx, const tvdb_sparse_grid* in,
                                     float background, int iterations,
                                     tvdb_sparse_grid* out, tvdb_error_t* err) {
  if (!ctx || !in || !out || iterations <= 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid dilate_sparse arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  out->count = 0; out->voxel_size = in->voxel_size; out->ox = in->ox; out->oy = in->oy; out->oz = in->oz;
  size_t cnt = in->count;
  int32_t* cc = (int32_t*)malloc((cnt ? cnt : 1) * 3u * sizeof(int32_t));
  float* cv = (float*)malloc((cnt ? cnt : 1) * sizeof(float));
  if (!cc || !cv) { free(cc); free(cv); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  if(!tvdb_gpu_morph_canonical(in,cc,cv,&cnt)) { free(cc); free(cv); tvdb_gpu_set_error(err,TVDB_ERROR_OUT_OF_MEMORY,"canonical coordinates allocation failed"); return TVDB_ERROR_OUT_OF_MEMORY; }

  tvdb_status_t st = TVDB_OK;
  for (int it = 0; it < iterations && cnt > 0; ++it) {
    int32_t* nc = NULL; float* nv = NULL; size_t nn = 0;
    st = tvdb_gpu_sparse_dilate_step(ctx, cc, cv, cnt, background, &nc, &nv, &nn, err);
    free(cc); free(cv);
    if (st != TVDB_OK) { cc = NULL; cv = NULL; cnt = 0; break; }
    cc = nc; cv = nv; cnt = nn;
  }
  if (st == TVDB_OK) {
    if (!tvdb_sparse_grid_reserve(out, cnt ? cnt : 1)) { st = TVDB_ERROR_OUT_OF_MEMORY; tvdb_gpu_set_error(err, st, "OOM"); }
    else {
      for (size_t i = 0; i < cnt; ++i) {
        out->coords[i].x = cc[3*i+0]; out->coords[i].y = cc[3*i+1]; out->coords[i].z = cc[3*i+2];
        out->values[i] = cv[i];
      }
      out->count = cnt;
    }
  }
  free(cc); free(cv);
  return st;
}

tvdb_status_t tvdb_gpu_active_grid_coords(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* dense,
                                          float background, float tolerance,
                                          tvdb_sparse_grid* out, tvdb_error_t* err) {
  return resident_active_host(ctx,dense,background,tolerance,out,err);
}

tvdb_status_t tvdb_gpu_grid_checksum(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                                     uint32_t* out_checksum, tvdb_error_t* err) {
  return resident_reduce_host(ctx,grid,2,0,0,out_checksum,err);
}

// Min-pool one source grid into a device output buffer (CAS atomic-min).
static tvdb_status_t tvdb_gpu_merge_one(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* src,
    int onx, int ony, int onz, int offx, int offy, int offz,
    tvdb_vk_buffer* bout, CUdeviceptr dout, tvdb_error_t* err) {
  size_t ns = (size_t)src->nx * (size_t)src->ny * (size_t)src->nz;
  if (ns == 0) return TVDB_OK;
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr ds = 0;
    tvdb_status_t st = tvdb_cuda_get_module(ctx, &module, err);
    if (st != TVDB_OK) return st;
    if (!tvdb_cuda_ok(ctx, err, "f", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_merge_scatter"))) return err?err->status:TVDB_ERROR_IO;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &ds, src->data, ns*sizeof(float), err)) != TVDB_OK) return st;
    int snx=src->nx, sny=src->ny, snz=src->nz; unsigned int uc=(unsigned int)ns, block=128;
    void* args[] = {&dout,&ds,&snx,&sny,&snz,&onx,&ony,&onz,&offx,&offy,&offz,&uc};
    if (!tvdb_cuda_ok(ctx, err, "k", ctx->cuda.cuLaunchKernel(fn,(uc+block-1u)/block,1,1,block,1,1,0,NULL,args,NULL))) { ctx->cuda.cuMemFree(ds); return err?err->status:TVDB_ERROR_IO; }
    if (!tvdb_cuda_ok(ctx, err, "s", ctx->cuda.cuCtxSynchronize())) { ctx->cuda.cuMemFree(ds); return err?err->status:TVDB_ERROR_IO; }
    ctx->cuda.cuMemFree(ds);
    return TVDB_OK;
  }
  tvdb_vk_buffer bs, bu;
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, ns*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bs, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, 64, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) { tvdb_vk_destroy_buffer(ctx, &bs); return st; }
  memcpy(bs.mapped, src->data, ns*sizeof(float));
  struct { int32_t sdim[4]; int32_t odim[4]; int32_t off[4]; uint32_t count; uint32_t pad[3]; } par;
  memset(&par, 0, sizeof(par));
  par.sdim[0]=src->nx; par.sdim[1]=src->ny; par.sdim[2]=src->nz;
  par.odim[0]=onx; par.odim[1]=ony; par.odim[2]=onz;
  par.off[0]=offx; par.off[1]=offy; par.off[2]=offz; par.count=(uint32_t)ns;
  memcpy(bu.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuMergeScatterSpv; d.spv_len = kTvdbGpuMergeScatterSpv_len; d.descriptor_count = 3;
  d.buffers[0]=bout; d.buffers[1]=&bs; d.buffers[2]=&bu;
  d.descriptor_types[0]=d.descriptor_types[1]=VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2]=VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((ns + 127u) / 128u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  tvdb_vk_destroy_buffer(ctx, &bu);
  tvdb_vk_destroy_buffer(ctx, &bs);
  return st;
}

tvdb_status_t tvdb_gpu_merge_grids(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* a,
                                   const tvdb_dense_grid* b, float background,
                                   tvdb_dense_grid* out, tvdb_error_t* err) {
  if (!ctx || !a || !b || !out || out==a || out==b ||
      !tvdb_gpu_shape_valid(a->nx,a->ny,a->nz,a->voxel_size,a->data,sizeof(float)) ||
      !tvdb_gpu_shape_valid(b->nx,b->ny,b->nz,b->voxel_size,b->data,sizeof(float)) ||
      !isfinite(a->ox) || !isfinite(a->oy) || !isfinite(a->oz) ||
      !isfinite(b->ox) || !isfinite(b->oy) || !isfinite(b->oz) || fabsf(a->voxel_size - b->voxel_size) > 1e-6f) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid merge_grids arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  float vs = a->voxel_size;
  float ax1 = a->ox + a->nx*vs, ay1 = a->oy + a->ny*vs, az1 = a->oz + a->nz*vs;
  float bx1 = b->ox + b->nx*vs, by1 = b->oy + b->ny*vs, bz1 = b->oz + b->nz*vs;
  float ox = a->ox < b->ox ? a->ox : b->ox, oy = a->oy < b->oy ? a->oy : b->oy, oz = a->oz < b->oz ? a->oz : b->oz;
  float mx = ax1 > bx1 ? ax1 : bx1, my = ay1 > by1 ? ay1 : by1, mz = az1 > bz1 ? az1 : bz1;
  double dx=ceil(((double)mx-ox)/vs),dy=ceil(((double)my-oy)/vs),dz=ceil(((double)mz-oz)/vs);
  if(!isfinite(dx) || !isfinite(dy) || !isfinite(dz) || dx<1 || dy<1 || dz<1 || dx>INT_MAX || dy>INT_MAX || dz>INT_MAX) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"merged dimensions overflow"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  int nx=(int)dx,ny=(int)dy,nz=(int)dz;
  tvdb_status_t st = tvdb_gpu_init_out_grid(out, nx, ny, nz, vs, ox, oy, oz, err);
  if (st != TVDB_OK) return st;
  size_t nvox = (size_t)nx*(size_t)ny*(size_t)nz;
  for (size_t i = 0; i < nvox; ++i) out->data[i] = background;
  int sax = (int)roundf((a->ox-ox)/vs), say = (int)roundf((a->oy-oy)/vs), saz = (int)roundf((a->oz-oz)/vs);
  int sbx = (int)roundf((b->ox-ox)/vs), sby = (int)roundf((b->oy-oy)/vs), sbz = (int)roundf((b->oz-oz)/vs);

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUdeviceptr dout = 0;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, out->data, nvox*sizeof(float), err)) != TVDB_OK) return st;
    if ((st = tvdb_gpu_merge_one(ctx, a, nx,ny,nz, sax,say,saz, NULL, dout, err)) != TVDB_OK) { ctx->cuda.cuMemFree(dout); return st; }
    if ((st = tvdb_gpu_merge_one(ctx, b, nx,ny,nz, sbx,sby,sbz, NULL, dout, err)) != TVDB_OK) { ctx->cuda.cuMemFree(dout); return st; }
    if (!tvdb_cuda_ok(ctx, err, "c", ctx->cuda.cuMemcpyDtoH(out->data, dout, nvox*sizeof(float)))) st = err?err->status:TVDB_ERROR_IO;
    ctx->cuda.cuMemFree(dout);
    return st;
  }

  tvdb_vk_buffer bout;
  if ((st = tvdb_vk_create_buffer(ctx, nvox*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bout, err)) != TVDB_OK) return st;
  memcpy(bout.mapped, out->data, nvox*sizeof(float));
  if ((st = tvdb_gpu_merge_one(ctx, a, nx,ny,nz, sax,say,saz, &bout, 0, err)) == TVDB_OK)
    st = tvdb_gpu_merge_one(ctx, b, nx,ny,nz, sbx,sby,sbz, &bout, 0, err);
  if (st == TVDB_OK) memcpy(out->data, bout.mapped, nvox*sizeof(float));
  tvdb_vk_destroy_buffer(ctx, &bout);
  return st;
}

static tvdb_status_t tvdb_gpu_erode_sparse_impl(tvdb_gpu_context_t* ctx, const tvdb_sparse_grid* in,
                                    int iterations, tvdb_sparse_grid* out, tvdb_error_t* err) {
  if (!ctx || !in || !out || iterations <= 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid erode_sparse arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  out->count = 0; out->voxel_size = in->voxel_size; out->ox = in->ox; out->oy = in->oy; out->oz = in->oz;
  size_t cnt = in->count;
  int32_t* cc = (int32_t*)malloc((cnt ? cnt : 1) * 3u * sizeof(int32_t));
  float* cv = (float*)malloc((cnt ? cnt : 1) * sizeof(float));
  if (!cc || !cv) { free(cc); free(cv); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  if(!tvdb_gpu_morph_canonical(in,cc,cv,&cnt)) { free(cc); free(cv); tvdb_gpu_set_error(err,TVDB_ERROR_OUT_OF_MEMORY,"canonical coordinates allocation failed"); return TVDB_ERROR_OUT_OF_MEMORY; }

  tvdb_status_t st = TVDB_OK;
  for (int it = 0; it < iterations && cnt > 0; ++it) {
    int32_t* nc = NULL; float* nv = NULL; size_t nn = 0;
    st = tvdb_gpu_sparse_erode_step(ctx, cc, cv, cnt, &nc, &nv, &nn, err);
    free(cc); free(cv);
    if (st != TVDB_OK) { cc = NULL; cv = NULL; cnt = 0; break; }
    cc = nc; cv = nv; cnt = nn;
  }
  if (st == TVDB_OK) {
    if (!tvdb_sparse_grid_reserve(out, cnt ? cnt : 1)) { st = TVDB_ERROR_OUT_OF_MEMORY; tvdb_gpu_set_error(err, st, "OOM"); }
    else {
      for (size_t i = 0; i < cnt; ++i) {
        out->coords[i].x = cc[3*i+0]; out->coords[i].y = cc[3*i+1]; out->coords[i].z = cc[3*i+2];
        out->values[i] = cv[i];
      }
      out->count = cnt;
    }
  }
  free(cc); free(cv);
  return st;
}

// ---- mesh -> SDF (brute force) ----------------------------------------------

/* ---- mesh_to_sdf over the shared BVH --------------------------------------
 *
 * The brute-force kernel is O(voxels * faces). This walks the same
 * tvdb_mesh_bvh_t the CPU query uses -- see the header for why sharing the tree
 * rather than re-deriving one is the point. A uniform bin grid was tried first
 * and measured 1.2-5.1x *slower* than the exhaustive scan, because a uniform grid
 * degenerates to O(faces) per query for a point deep inside the mesh; that is
 * exactly what a hierarchy fixes, so this does not have the problem.
 */

/* Node indices only: the shader recomputes each bound on pop, which halves the
 * stack and is bit-identical. MUST match TVDB_BVH_GPU_STACK in
 * tinyvdb_gpu_mesh_to_sdf_bvh.comp. */
#define TVDB_MESH_SDF_BVH_GPU_STACK 48

/* Two-sided gate, both bounds measured (interleaved, 2.7M-voxel grids, so the
 * only variable is the mesh):
 *
 *   faces     brute      bvh      verdict
 *      4,096   427-435ms  288-357ms  bvh 1.2-1.5x
 *      9,216   607-628ms  492-527ms  bvh 1.2x
 *     16,384   879-913ms 1038-1101ms brute 1.2x
 *     25,600  1232-1272ms 1962-1990ms brute 1.6x
 *
 * The hierarchy stops paying above ~10k faces, and the reason is the tree this
 * build produces: a median centroid split on a level-set shell, where every
 * centroid sits on the same thin surface, gives depth 22-31 for 2k-16k faces --
 * roughly 2.5x log2(n) rather than log2(n). The walk is a serial dependent-load
 * chain, so its cost grows with that depth, and past ~10k faces it exceeds what
 * the scan saves. Note the gate is genuinely two-dimensional: at 16,384 faces on
 * a 12.8M-voxel grid the hierarchy wins again (3.27-3.34s vs 4.03-4.11s),
 * because a bigger grid amortises the node buffer. A single threshold in
 * faces*voxels does not fit these points, so the face bound is applied and that
 * corner falls back to the scan.
 *
 * A better build (SAH, or a BVH over triangle *edges* rather than centroids)
 * would move the upper bound out; the traversal itself is not the limitation
 * where the tree is shallow. */
#ifndef TVDB_MESH_SDF_BVH_MIN_FACES
#define TVDB_MESH_SDF_BVH_MIN_FACES 64
#endif
#ifndef TVDB_MESH_SDF_BVH_MAX_FACES
#define TVDB_MESH_SDF_BVH_MAX_FACES 10240
#endif

static tvdb_status_t tvdb_vk_mesh_to_sdf_bvh(tvdb_gpu_context_t* ctx,
    const tvdb_triangle_mesh* mesh, const float* verts, const float* normals,
    float voxel_size, float band_width, tvdb_dense_grid* out, tvdb_error_t* err) {
  int nx = out->nx, ny = out->ny, nz = out->nz;
  size_t nvox = (size_t)nx * (size_t)ny * (size_t)nz;
  size_t nf = mesh->face_count;

  tvdb_mesh_bvh_t* bvh = NULL;
  if (!tvdb_mesh_bvh_build(mesh, &bvh)) {
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "BVH build failed");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  int32_t node_count = tvdb_mesh_bvh_node_count(bvh);
  int32_t prim_count = tvdb_mesh_bvh_prim_count(bvh);
  int32_t depth = tvdb_mesh_bvh_max_depth(bvh);
  const tvdb_mesh_bvh_node_t* nodes = tvdb_mesh_bvh_nodes(bvh);
  const int32_t* prims = tvdb_mesh_bvh_prims(bvh);
  /* A depth-first walk needs at most depth+1 entries. Rather than assume, check:
   * a deeper tree falls back to the exhaustive scan, so a mismatch with the
   * shader's stack bound costs speed and never correctness. */
  if (node_count <= 0 || prim_count <= 0 || (int32_t)depth + 1 > TVDB_MESH_SDF_BVH_GPU_STACK) {
    tvdb_mesh_bvh_destroy(bvh);
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  /* The nodes go to the device as raw 40-byte records, so the shader's struct
   * and this one have to agree exactly. */
  _Static_assert(sizeof(tvdb_mesh_bvh_node_t) == 40, "BVH node layout is the upload format");

  long long slice = (long long)nx * ny;
  int zslab = (int)(TVDB_MESH_SDF_MAX_VOXELS_PER_DISPATCH / (slice > 0 ? slice : 1));
  if (zslab < 1) zslab = 1;
  int nslabs = (nz + zslab - 1) / zslab;

  { tvdb_status_t ps = tvdb_vk_ensure_pools(ctx, err); if (ps != TVDB_OK) { tvdb_mesh_bvh_destroy(bvh); return ps; } }

  enum { MBVH_STRIDE = 256 };
  tvdb_vk_buffer bv, bn, bo, bu, bnd, bpr;
  VkDescriptorSet* msets = NULL;
  int nmsets = 0;
  memset(&bv, 0, sizeof(bv)); memset(&bn, 0, sizeof(bn)); memset(&bo, 0, sizeof(bo));
  memset(&bu, 0, sizeof(bu)); memset(&bnd, 0, sizeof(bnd)); memset(&bpr, 0, sizeof(bpr));
  tvdb_status_t st;
  if ((st = tvdb_vk_create_buffer(ctx, nf*9u*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bv, err)) != TVDB_OK) goto done;
  if ((st = tvdb_vk_create_buffer(ctx, nf*3u*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bn, err)) != TVDB_OK) goto done;
  if ((st = tvdb_vk_create_buffer(ctx, nvox*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto done;
  if ((st = tvdb_vk_create_buffer(ctx, (size_t)nslabs * MBVH_STRIDE, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto done;
  if ((st = tvdb_vk_create_buffer(ctx, (size_t)node_count * sizeof(tvdb_mesh_bvh_node_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bnd, err)) != TVDB_OK) goto done;
  if ((st = tvdb_vk_create_buffer(ctx, (size_t)prim_count * sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bpr, err)) != TVDB_OK) goto done;
  memcpy(bv.mapped, verts, nf*9u*sizeof(float));
  memcpy(bn.mapped, normals, nf*3u*sizeof(float));
  memcpy(bnd.mapped, nodes, (size_t)node_count * sizeof(tvdb_mesh_bvh_node_t));
  memcpy(bpr.mapped, prims, (size_t)prim_count * sizeof(int32_t));
  {
    /* std140, asserted. The shader declares `ivec2 zrange; ivec2 pad0; uint
     * node_count; uint prim_count;` and pad0 occupies 48..55, so the two uints
     * land at 56 and 60 and the block is 64 bytes. Asserting offset 48 (the
     * natural packing) is what caught this. */
    typedef struct { int32_t vdim[4]; float grid_o[4]; float band; uint32_t face_count;
                     int32_t zrange[2]; int32_t pad0[2]; uint32_t node_count, prim_count; } mbvh_uniform;
    _Static_assert(offsetof(mbvh_uniform, band) == 32, "std140: band after ivec4+vec4");
    _Static_assert(offsetof(mbvh_uniform, face_count) == 36, "std140: face_count after band");
    _Static_assert(offsetof(mbvh_uniform, zrange) == 40, "std140: zrange after face_count");
    _Static_assert(offsetof(mbvh_uniform, node_count) == 56, "std140: node_count after the ivec2 pad");
    _Static_assert(offsetof(mbvh_uniform, prim_count) == 60, "std140: prim_count after node_count");
    _Static_assert(sizeof(mbvh_uniform) == 64, "bvh uniform must be 64 bytes");
    for (int s = 0; s < nslabs; ++s) {
      int z0 = s * zslab;
      int zc = (z0 + zslab <= nz) ? zslab : (nz - z0);
      mbvh_uniform par;
      memset(&par, 0, sizeof(par));
      par.vdim[0]=nx; par.vdim[1]=ny; par.vdim[2]=nz; par.vdim[3]=0;
      par.grid_o[0]=out->ox; par.grid_o[1]=out->oy; par.grid_o[2]=out->oz; par.grid_o[3]=voxel_size;
      par.band=band_width; par.face_count=(uint32_t)nf;
      par.zrange[0]=z0; par.zrange[1]=zc;
      par.node_count=(uint32_t)node_count; par.prim_count=(uint32_t)prim_count;
      memcpy((char*)bu.mapped + (size_t)s * MBVH_STRIDE, &par, sizeof(par));
    }
  }
  {
    const uint32_t types[6] = { VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,
                                VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER,
                                VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, VK_DESCRIPTOR_TYPE_STORAGE_BUFFER };
    VkDescriptorSetLayout layout = VK_NULL_HANDLE;
    int borrowed = 0;
    if ((st = tvdb_vk_make_layout(ctx, kTvdbGpuMeshToSdfBvhSpv, kTvdbGpuMeshToSdfBvhSpv_len,
                                  6, types, &layout, &borrowed, err)) != TVDB_OK) goto done;
    msets = (VkDescriptorSet*)calloc((size_t)nslabs, sizeof(VkDescriptorSet));
    if (!msets) { st = TVDB_ERROR_OUT_OF_MEMORY; if (err) tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
                  if (layout && !borrowed && ctx->vk.DestroyDescriptorSetLayout) ctx->vk.DestroyDescriptorSetLayout(ctx->device, layout, NULL);
                  goto done; }
    /* One layout per set: descriptorSetCount must not exceed the layout count
     * (VUID-VkDescriptorSetAllocateInfo-descriptorSetCount-00301), and a
     * single-layout array with count > 1 segfaults this driver. */
    VkDescriptorSetLayout* layouts = (VkDescriptorSetLayout*)malloc((size_t)nslabs * sizeof(VkDescriptorSetLayout));
    if (!layouts) { st = TVDB_ERROR_OUT_OF_MEMORY; free(msets); msets = NULL;
                    if (layout && !borrowed && ctx->vk.DestroyDescriptorSetLayout) ctx->vk.DestroyDescriptorSetLayout(ctx->device, layout, NULL);
                    goto done; }
    for (int s = 0; s < nslabs; ++s) layouts[s] = layout;
    VkDescriptorSetAllocateInfo dsai;
    memset(&dsai, 0, sizeof(dsai));
    dsai.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
    dsai.descriptorPool = ctx->desc_pool;
    dsai.descriptorSetCount = (uint32_t)nslabs;
    dsai.pSetLayouts = layouts;
    VkResult ar = ctx->vk.AllocateDescriptorSets(ctx->device, &dsai, msets);
    free(layouts);
    if (!tvdb_vk_ok(ar, err, "vkAllocateDescriptorSets")) { st = err ? err->status : TVDB_ERROR_IO;
      if (layout && !borrowed && ctx->vk.DestroyDescriptorSetLayout) ctx->vk.DestroyDescriptorSetLayout(ctx->device, layout, NULL);
      goto done; }
    nmsets = nslabs;
    VkDescriptorBufferInfo infos[6];
    VkWriteDescriptorSet wr[6];
    memset(infos, 0, sizeof(infos)); memset(wr, 0, sizeof(wr));
    for (int s = 0; s < nslabs; ++s) {
      infos[0].buffer = bv.buffer; infos[0].range = nf*9u*sizeof(float);
      infos[1].buffer = bn.buffer; infos[1].range = nf*3u*sizeof(float);
      infos[2].buffer = bo.buffer; infos[2].range = nvox*sizeof(float);
      infos[3].buffer = bu.buffer; infos[3].offset = (VkDeviceSize)s * MBVH_STRIDE; infos[3].range = 64u;
      infos[4].buffer = bnd.buffer; infos[4].range = (size_t)node_count * sizeof(tvdb_mesh_bvh_node_t);
      infos[5].buffer = bpr.buffer; infos[5].range = (size_t)prim_count * sizeof(int32_t);
      for (int i = 0; i < 6; ++i) {
        wr[i].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        wr[i].dstSet = msets[s]; wr[i].dstBinding = (uint32_t)i; wr[i].descriptorCount = 1;
        wr[i].descriptorType = types[i]; wr[i].pBufferInfo = &infos[i];
      }
      ctx->vk.UpdateDescriptorSets(ctx->device, 6, wr, 0, NULL);
    }
    if (layout && !borrowed && ctx->vk.DestroyDescriptorSetLayout)
      ctx->vk.DestroyDescriptorSetLayout(ctx->device, layout, NULL);
  }
  for (int s = 0; s < nslabs; ++s) {
    int z0 = s * zslab;
    int zc = (z0 + zslab <= nz) ? zslab : (nz - z0);
    size_t slab_vox = (size_t)slice * (size_t)zc;
    tvdb_vk_dispatch_desc d;
    memset(&d, 0, sizeof(d));
    d.spv = kTvdbGpuMeshToSdfBvhSpv; d.spv_len = kTvdbGpuMeshToSdfBvhSpv_len; d.descriptor_count = 6;
    d.buffers[0]=&bv; d.buffers[1]=&bn; d.buffers[2]=&bo; d.buffers[3]=&bu; d.buffers[4]=&bnd; d.buffers[5]=&bpr;
    for (int i = 0; i < 3; ++i) d.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    for (int i = 4; i < 6; ++i) d.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    d.group_x = (uint32_t)((slab_vox + 63u) / 64u);
    d.defer_wait = TVDB_VK_DEFERRED_SUBMIT;
    d.preset_set = msets[s];
    if ((st = tvdb_vk_dispatch(ctx, &d, err)) != TVDB_OK) break;
  }
  if (st == TVDB_OK) st = tvdb_vk_flush(ctx, err);
  if (st == TVDB_OK) memcpy(out->data, bo.mapped, nvox*sizeof(float));
done:
  if (nmsets && msets && ctx->vk.FreeDescriptorSets)
    for (int s = 0; s < nmsets; ++s) if (msets[s]) ctx->vk.FreeDescriptorSets(ctx->device, ctx->desc_pool, 1, &msets[s]);
  free(msets);
  tvdb_vk_destroy_buffer(ctx, &bpr);
  tvdb_vk_destroy_buffer(ctx, &bnd);
  tvdb_vk_destroy_buffer(ctx, &bu);
  tvdb_vk_destroy_buffer(ctx, &bo);
  tvdb_vk_destroy_buffer(ctx, &bn);
  tvdb_vk_destroy_buffer(ctx, &bv);
  tvdb_mesh_bvh_destroy(bvh);
  return st;
}

/* ---- surface_area / volume -------------------------------------------------
 *
 * Two dispatches over one partials buffer, then a single fp64 downloaded. The
 * final scaling is done on the host in fp64 so the f32 results are bit-identical
 * to the CPU's `((double)count) * h * h` -- the count is an exact integer, so
 * this is an exact reproduction, not a tolerance.
 */

#define TVDB_MEASURE_MAX_GROUPS 1024u
#define TVDB_MEASURE_PARTIAL_BYTES (TVDB_MEASURE_MAX_GROUPS * sizeof(double))

/* op: 0 = surface area, 1 = volume. is_d selects the fp64 path. */
static tvdb_status_t tvdb_gpu_measure_count(tvdb_gpu_context_t* ctx,
    const void* src, int is_d, int nx, int ny, int nz, int op,
    double* out_count, tvdb_error_t* err) {
  return resident_measure_host(ctx,src,is_d,nx,ny,nz,op,out_count,err);
}

tvdb_status_t tvdb_gpu_surface_area(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                                    float* out_area, tvdb_error_t* err) {
  double crossings = 0.0;
  if (!ctx || !grid || !out_area) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "surface_area: null argument");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (!grid->data) { *out_area = 0.0f; return TVDB_OK; }  /* matches the CPU */
  tvdb_status_t st = tvdb_gpu_measure_count(ctx, grid->data, 0,
      grid->nx, grid->ny, grid->nz, 0, &crossings, err);
  if (st != TVDB_OK) return st;
  /* Same association order as the CPU's (float)crossings * h * h. */
  *out_area = (float)crossings * grid->voxel_size * grid->voxel_size;
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_volume(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                              float* out_volume, tvdb_error_t* err) {
  double inside = 0.0;
  if (!ctx || !grid || !out_volume) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "volume: null argument");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (!grid->data) { *out_volume = 0.0f; return TVDB_OK; }
  tvdb_status_t st = tvdb_gpu_measure_count(ctx, grid->data, 0,
      grid->nx, grid->ny, grid->nz, 1, &inside, err);
  if (st != TVDB_OK) return st;
  const float h = grid->voxel_size;
  *out_volume = (float)inside * h * h * h;
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_surface_area_d(tvdb_gpu_context_t* ctx, const tvdb_dense_grid_d* grid,
                                      double* out_area, tvdb_error_t* err) {
  double crossings = 0.0;
  if (!ctx || !grid || !out_area) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "surface_area_d: null argument");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (!grid->data) { *out_area = 0.0; return TVDB_OK; }
  tvdb_status_t st = tvdb_gpu_measure_count(ctx, grid->data, 1,
      grid->nx, grid->ny, grid->nz, 0, &crossings, err);
  if (st != TVDB_OK) return st;
  *out_area = crossings * grid->voxel_size * grid->voxel_size;
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_volume_d(tvdb_gpu_context_t* ctx, const tvdb_dense_grid_d* grid,
                                double* out_volume, tvdb_error_t* err) {
  double inside = 0.0;
  if (!ctx || !grid || !out_volume) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "volume_d: null argument");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (!grid->data) { *out_volume = 0.0; return TVDB_OK; }
  tvdb_status_t st = tvdb_gpu_measure_count(ctx, grid->data, 1,
      grid->nx, grid->ny, grid->nz, 1, &inside, err);
  if (st != TVDB_OK) return st;
  *out_volume = inside * grid->voxel_size * grid->voxel_size * grid->voxel_size;
  return TVDB_OK;
}

/* Shared projected PCG; Laplacian applications stay on the selected device.
   One pair of device buffers is reused for the entire solve. Projection and
   double reductions are host-side so CPU/GPU share the numerical contract. */
typedef struct {
  tvdb_gpu_context_t* ctx;
  tvdb_vk_buffer in,out,uniform;
  CUdeviceptr din,dout;
  CUfunction kernel;
  bool initialized;
} tvdb_gpu_poisson_workspace;
static void tvdb_gpu_poisson_release(tvdb_gpu_poisson_workspace* w) {
  if(w->ctx->backend==TVDB_GPU_BACKEND_CUDA) {
    if(w->din) w->ctx->cuda.cuMemFree(w->din);
    if(w->dout) w->ctx->cuda.cuMemFree(w->dout);
  } else {
    tvdb_vk_destroy_buffer(w->ctx,&w->uniform);
    tvdb_vk_destroy_buffer(w->ctx,&w->out);
    tvdb_vk_destroy_buffer(w->ctx,&w->in);
  }
}
static tvdb_status_t tvdb_gpu_poisson_apply(void* context,const void* src,void* dst,
 int nx,int ny,int nz,double h,bool fp64,tvdb_error_t* err) {
  tvdb_gpu_poisson_workspace* w=(tvdb_gpu_poisson_workspace*)context;
  tvdb_gpu_context_t* ctx=w->ctx;
  size_t bytes;
  if(!tvdb_grid_bytes(nx,ny,nz,fp64?sizeof(double):sizeof(float),&bytes)) return TVDB_ERROR_INVALID_ARGUMENT;
  tvdb_status_t st;
  double ds=-1/(h*h); float fs=(float)ds;
  if(ctx->backend==TVDB_GPU_BACKEND_CUDA) {
    if(!w->initialized) {
      CUmodule module;
      if((st=tvdb_cuda_get_module(ctx,&module,err))!=TVDB_OK) return st;
      /* The fp64 kernel is named tvdb_cuda_stencil_scalar_d in the PTX source. This
       * asked for "tvdb_cuda_stencil_d", which is the name of a host wrapper in
       * this file, not a kernel, so every fp64 Poisson solve on CUDA failed at
       * module load with CUDA_ERROR_NOT_FOUND. The fp32 spelling below was
       * already correct, which is why only the _d and _dd paths were broken. */
      if(!tvdb_cuda_ok(ctx,err,"Poisson kernel",ctx->cuda.cuModuleGetFunction(&w->kernel,module,
          fp64?"tvdb_cuda_stencil_scalar_d":"tvdb_cuda_stencil_scalar_scalar"))) return TVDB_ERROR_IO;
      if((st=tvdb_cuda_alloc_copy_in(ctx,&w->din,NULL,bytes,err))!=TVDB_OK) return st;
      if((st=tvdb_cuda_alloc_copy_in(ctx,&w->dout,NULL,bytes,err))!=TVDB_OK) return st;
      w->initialized=true;
    }
    if(!tvdb_cuda_ok(ctx,err,"Poisson upload",ctx->cuda.cuMemcpyHtoD(w->din,src,bytes))) return TVDB_ERROR_IO;
    int op=0; float zero=0,one=1;
    void* args_f[]={&w->din,&w->dout,&nx,&ny,&nz,&op,&fs,&zero,&zero,&zero,&one};
    void* args_d[]={&w->din,&w->dout,&nx,&ny,&nz,&op,&ds};
    if(!tvdb_cuda_ok(ctx,err,"Poisson apply",ctx->cuda.cuLaunchKernel(w->kernel,
        (unsigned int)((nx-1)/8+1),(unsigned int)((ny-1)/8+1),(unsigned int)nz,8,8,1,0,NULL,
        fp64?args_d:args_f,NULL))) return TVDB_ERROR_IO;
    if(!tvdb_cuda_ok(ctx,err,"Poisson synchronize",ctx->cuda.cuCtxSynchronize())) return TVDB_ERROR_IO;
    if(!tvdb_cuda_ok(ctx,err,"Poisson download",ctx->cuda.cuMemcpyDtoH(dst,w->dout,bytes))) return TVDB_ERROR_IO;
    return TVDB_OK;
  }
  if(!w->initialized) {
    if((st=tvdb_vk_create_buffer(ctx,bytes,VK_BUFFER_USAGE_STORAGE_BUFFER_BIT,&w->in,err))!=TVDB_OK) return st;
    if((st=tvdb_vk_create_buffer(ctx,bytes,VK_BUFFER_USAGE_STORAGE_BUFFER_BIT,&w->out,err))!=TVDB_OK) return st;
    if((st=tvdb_vk_create_buffer(ctx,48,VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT,&w->uniform,err))!=TVDB_OK) return st;
    w->initialized=true;
  }
  memcpy(w->in.mapped,src,bytes); memset(w->uniform.mapped,0,48);
  int32_t dims[4]={nx,ny,nz,0}; memcpy(w->uniform.mapped,dims,sizeof(dims));
  if(fp64) memcpy((char*)w->uniform.mapped+16,&ds,sizeof(ds));
  else memcpy((char*)w->uniform.mapped+16,&fs,sizeof(fs));
  tvdb_vk_dispatch_desc d; memset(&d,0,sizeof(d));
  d.spv=fp64?kTvdbGpuStencilScalarDSpv:kTvdbGpuStencilScalarScalarSpv;
  d.spv_len=fp64?kTvdbGpuStencilScalarDSpv_len:kTvdbGpuStencilScalarScalarSpv_len;
  d.descriptor_count=3; d.buffers[0]=&w->in; d.buffers[1]=&w->out; d.buffers[2]=&w->uniform;
  d.descriptor_types[0]=d.descriptor_types[1]=VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2]=VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x=(uint32_t)((nx-1)/8+1); d.group_y=(uint32_t)((ny-1)/8+1); d.group_z=(uint32_t)nz;
  st=tvdb_vk_dispatch(ctx,&d,err);
  if(st==TVDB_OK) memcpy(dst,w->out.mapped,bytes);
  return st;
}

/* ---- comp_max / comp_min / comp_sum / comp_mult ---------------------------- */

/* op: 0 max, 1 min, 2 sum, 3 mult. Mirrors the four CPU ops, which differ only
 * in the combining expression. */
static tvdb_status_t tvdb_gpu_comp(tvdb_gpu_context_t* ctx, int op,
    const tvdb_dense_grid* a, const tvdb_dense_grid* b,
    tvdb_dense_grid* result, tvdb_error_t* err) {
  if (!ctx || !a || !b || !result || op < 0 || op > 3) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "comp: invalid arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  /* The CPU ops return immediately, leaving `result` untouched, unless all three
     grids share a shape. Reproducing the "untouched" half matters as much as the
     arithmetic: clamping b's extent instead would produce a field where the CPU
     produces none at all. */
  if (a->nx != b->nx || a->ny != b->ny || a->nz != b->nz ||
      a->nx != result->nx || a->ny != result->ny || a->nz != result->nz) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"comp: shape mismatch"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  size_t bytes;
  if(!a->data || !b->data || !result->data || !tvdb_grid_bytes(a->nx,a->ny,a->nz,sizeof(float),&bytes) || bytes/sizeof(float)>INT_MAX) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"comp: invalid grid size/data"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  const int nx = a->nx, ny = a->ny, nz = a->nz;
  const size_t n = (size_t)nx * (size_t)ny * (size_t)nz;
  if (n == 0) return TVDB_OK;
  if (ctx->backend == TVDB_GPU_BACKEND_VULKAN && kTvdbGpuCompSpv_len == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "comp SPIR-V unavailable; rebuild with glslangValidator");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  return resident_binary_host(ctx,a,b,op,0,result,err);
}

tvdb_status_t tvdb_gpu_comp_max(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* a,
                                const tvdb_dense_grid* b, tvdb_dense_grid* result,
                                tvdb_error_t* err) {
  return tvdb_gpu_comp(ctx, 0, a, b, result, err);
}
tvdb_status_t tvdb_gpu_comp_min(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* a,
                                const tvdb_dense_grid* b, tvdb_dense_grid* result,
                                tvdb_error_t* err) {
  return tvdb_gpu_comp(ctx, 1, a, b, result, err);
}
tvdb_status_t tvdb_gpu_comp_sum(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* a,
                                const tvdb_dense_grid* b, tvdb_dense_grid* result,
                                tvdb_error_t* err) {
  return tvdb_gpu_comp(ctx, 2, a, b, result, err);
}
tvdb_status_t tvdb_gpu_comp_mult(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* a,
                                 const tvdb_dense_grid* b, tvdb_dense_grid* result,
                                 tvdb_error_t* err) {
  return tvdb_gpu_comp(ctx, 3, a, b, result, err);
}

/* ---- advect --------------------------------------------------------------- */

/* One dispatch of tinyvdb_gpu_advect.comp. The kernel has 6 bindings, all of
 * which the spec's uniform + storage kinds can express, so this goes through
 * tvdb_gpu_dispatch and both backends share the sequence below. */
static tvdb_status_t tvdb_gpu_advect_step(tvdb_gpu_context_t* ctx,
    int op, int order, int clamp_flag,
    const tvdb_dense_grid* field, const tvdb_dense_vec_grid* vel,
    const float* phat, const float* pstar, float* out,
    float dt, float inv_h, size_t n, int defer, tvdb_error_t* err) {
  typedef struct { int32_t dim[4]; int32_t cfg[4]; float inv_h; float dt; uint32_t nvox; }
          advect_uniform;
  _Static_assert(offsetof(advect_uniform, inv_h) == 32, "std140: inv_h follows the two ivec4s");
  _Static_assert(offsetof(advect_uniform, dt) == 36, "std140: dt follows inv_h");
  _Static_assert(offsetof(advect_uniform, nvox) == 40, "std140: nvox follows dt");
  _Static_assert(sizeof(advect_uniform) == 44, "advect uniform must end at the last std140 field");
  advect_uniform par;
  memset(&par, 0, sizeof par);
  par.dim[0] = field->nx; par.dim[1] = field->ny; par.dim[2] = field->nz; par.dim[3] = op;
  par.cfg[0] = order; par.cfg[1] = clamp_flag;
  par.inv_h = inv_h; par.dt = dt; par.nvox = (uint32_t)n;
  /* field, vel, phat, pstar, out, uniform. Phat and pstar are read for ops 1 and
     2 only; passing the right pointer for the others keeps the binding count
     fixed, so one layout serves every op. */
  tvdb_gpu_binding_t b[6];
  b[0].kind = TVDB_GPU_BIND_STORAGE_IN;  b[0].host_data = (void*)field->data; b[0].size_bytes = n * sizeof(float);
  b[1].kind = TVDB_GPU_BIND_STORAGE_IN;  b[1].host_data = (void*)vel->data;   b[1].size_bytes = n * 3u * sizeof(float);
  b[2].kind = TVDB_GPU_BIND_STORAGE_IN;  b[2].host_data = (void*)(phat  ? phat  : field->data);
  b[2].size_bytes = n * sizeof(float);
  b[3].kind = TVDB_GPU_BIND_STORAGE_IN;  b[3].host_data = (void*)(pstar ? pstar : field->data);
  b[3].size_bytes = n * sizeof(float);
  b[4].kind = TVDB_GPU_BIND_STORAGE_INOUT; b[4].host_data = out;              b[4].size_bytes = n * sizeof(float);
  b[5].kind = TVDB_GPU_BIND_UNIFORM;     b[5].host_data = (void*)&par;        b[5].size_bytes = 48;
  tvdb_gpu_dispatch_spec_t spec;
  memset(&spec, 0, sizeof spec);
  spec.spv = kTvdbGpuAdvectSpv; spec.spv_len = kTvdbGpuAdvectSpv_len;
  spec.cuda_kernel = "tvdb_cuda_advect";
  spec.bindings = b; spec.num_bindings = 6;
  spec.group_count_x = (uint32_t)((n + 63u) / 64u);
  spec.defer = defer;
  return tvdb_gpu_dispatch(ctx, &spec, err);
}

static tvdb_status_t tvdb_gpu_advect_impl(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* field,
                              const tvdb_dense_vec_grid* velocity, float dt, int scheme,
                              int clamp, tvdb_dense_grid* result, tvdb_error_t* err) {
  if (!ctx || !field || !velocity || !result) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "advect: null argument");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  /* The CPU returns without writing when any of these fail, so `result` is left
     untouched rather than partially updated. Reproduced here. */
  if (!field->data || !velocity->data || !result->data) return TVDB_OK;
  if (field->nx != velocity->nx || field->ny != velocity->ny || field->nz != velocity->nz) return TVDB_OK;
  if (field->nx != result->nx || field->ny != result->ny || field->nz != result->nz) return TVDB_OK;
  if (scheme < TVDB_ADVECT_RK1 || scheme > TVDB_ADVECT_BFECC) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "advect: unknown scheme");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  const int nx = field->nx, ny = field->ny, nz = field->nz;
  const size_t n = (size_t)nx * (size_t)ny * (size_t)nz;
  if (n == 0) return TVDB_OK;
  const float inv_h = 1.0f / field->voxel_size;
  tvdb_error_t local; memset(&local, 0, sizeof local);
  tvdb_status_t st;

  if (scheme <= TVDB_ADVECT_RK4) {
    /* Pure semi-Lagrangian, RK order = scheme + 1. The RK schemes ignore the
       clamp flag, as the CPU documents. */
    return tvdb_gpu_advect_step(ctx, 0, scheme + 1, 0, field, velocity,
                                NULL, NULL, result->data, dt, inv_h, n, 0, err);
  }

  /* MacCormack and BFECC both start with a forward then a backward RK2 pass to
     estimate the round-trip error, so phat and pstar are needed either way. */
  float* phat  = (float*)malloc(n * sizeof(float));
  float* pstar = (float*)malloc(n * sizeof(float));
  if (!phat || !pstar) {
    free(phat); free(pstar);
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
    return TVDB_ERROR_OUT_OF_MEMORY;
  }
  /* A grid view of phat. The backward pass advects *phat*, not field: the pair is
     a round trip A then A^-1, and re-advecting the original field instead makes
     the "error" term nonsense -- which showed up as a ~1e-1 discrepancy on a
     field of scale 1.2 while all four RK schemes matched to 2e-07. */
  tvdb_dense_grid phat_grid = *field;
  phat_grid.data = phat;
  /* Not deferred, deliberately. Each pass writes a host scratch buffer that the
     next pass reads, and a queued dispatch sees whatever the host has written
     by the time it runs -- deferring the pair would feed the second pass the
     first pass's *inputs* instead of its output, and the result would be wrong
     with no diagnostic. Deferral needs the ping/pong buffers device-resident,
     which is the index-map machinery, not a flag. A single-dispatch scheme
     (RK1-4) is the case that can defer, and it has nothing to gain. */
  st = tvdb_gpu_advect_step(ctx, 0, 2, 0, field, velocity, NULL, NULL, phat, dt, inv_h, n, 0, &local);
  if (st != TVDB_OK) { free(phat); free(pstar);
    if (err) *err = local; return st; }
  st = tvdb_gpu_advect_step(ctx, 0, 2, 0, &phat_grid, velocity, NULL, NULL, pstar, -dt, inv_h, n, 0, &local);
  if (st != TVDB_OK) { free(phat); free(pstar);
    if (err) *err = local; return st; }

  if (scheme == TVDB_ADVECT_MACCORMACK) {
    st = tvdb_gpu_advect_step(ctx, 1, 2, clamp, field, velocity, phat, pstar,
                              result->data, dt, inv_h, n, 0, &local);
  } else {
    /* BFECC: correct into phat (reusing the buffer, which the next pass no longer
       needs), advect that forward, then clamp in place if asked. The forward pass
       samples the *corrected* field, so phat needs a grid view of its own -- the
       CPU does the same thing with its `corr` grid. */
    tvdb_dense_grid corr = *field;
    corr.data = phat;
    st = tvdb_gpu_advect_step(ctx, 2, 2, 0, field, velocity, NULL, pstar,
                              phat, dt, inv_h, n, 0, &local);
    if (st == TVDB_OK)
      st = tvdb_gpu_advect_step(ctx, 0, 2, 0, &corr, velocity, NULL, NULL,
                                result->data, dt, inv_h, n, 0, &local);
    if (st == TVDB_OK && clamp)
      st = tvdb_gpu_advect_step(ctx, 3, 2, 0, field, velocity, NULL, NULL,
                                result->data, dt, inv_h, n, 0, &local);
  }
  free(phat); free(pstar);
  if (err && st == TVDB_OK) memset(err, 0, sizeof *err);
  return st;
}

/* ---- filters and the single-node semi-Lagrangian advect -------------------- */

/* One dispatch of tinyvdb_gpu_filter.comp. op: 0 separable pass, 1 Laplacian
 * iteration, 2 semi-Lagrangian advect. The kernel is 5 bindings and all of them
 * map onto the dispatch spec's binding kinds, so both backends share it. */
static tvdb_status_t tvdb_gpu_filter_step(tvdb_gpu_context_t* ctx, int op, int axis,
    int radius, const float* in, const float* vel, const float* kern, float* out,
    int nx, int ny, int nz, float dt, float inv_h, size_t n, tvdb_error_t* err) {
  typedef struct { int32_t dim[4]; int32_t cfg[4]; float inv_h; float dt; uint32_t nvox; }
          filter_uniform;
  _Static_assert(offsetof(filter_uniform, inv_h) == 32, "std140: inv_h follows the two ivec4s");
  _Static_assert(offsetof(filter_uniform, nvox) == 40, "std140: nvox follows dt");
  _Static_assert(sizeof(filter_uniform) == 44, "filter uniform must end at the last std140 field");
  filter_uniform par;
  memset(&par, 0, sizeof par);
  par.dim[0] = nx; par.dim[1] = ny; par.dim[2] = nz; par.dim[3] = op;
  par.cfg[0] = axis; par.cfg[1] = radius;
  par.inv_h = inv_h; par.dt = dt; par.nvox = (uint32_t)n;
  tvdb_gpu_binding_t b[5];
  b[0].kind = TVDB_GPU_BIND_STORAGE_IN;  b[0].host_data = (void*)in;  b[0].size_bytes = n * sizeof(float);
  b[1].kind = TVDB_GPU_BIND_STORAGE_INOUT; b[1].host_data = out;    b[1].size_bytes = n * sizeof(float);
  /* vel / kern are read only by ops 2 and 0; the spec always binds five, so point
     the unused ones at `in` rather than at NULL (which the spec rejects). */
  b[2].kind = TVDB_GPU_BIND_STORAGE_IN;  b[2].host_data = (void*)(vel ? vel : in);
  b[2].size_bytes = (vel ? n * 3u : n) * sizeof(float);
  b[3].kind = TVDB_GPU_BIND_STORAGE_IN;  b[3].host_data = (void*)(kern ? kern : in);
  b[3].size_bytes = (kern ? (size_t)(2 * radius + 1) : 1) * sizeof(float);
  b[4].kind = TVDB_GPU_BIND_UNIFORM;     b[4].host_data = (void*)&par;  b[4].size_bytes = 48;
  tvdb_gpu_dispatch_spec_t spec;
  memset(&spec, 0, sizeof spec);
  spec.spv = kTvdbGpuFilterSpv; spec.spv_len = kTvdbGpuFilterSpv_len;
  spec.cuda_kernel = "tvdb_cuda_filter";
  spec.bindings = b; spec.num_bindings = 5;
  /* The shader's local size is 32 (its median op needs 125 floats of private
     memory per thread). The CUDA path hardcodes 128 threads, so it launches 4x the
     blocks needed there and the kernel's bounds check discards the surplus. */
  spec.group_count_x = (uint32_t)((n + 31u) / 32u);
  return tvdb_gpu_dispatch(ctx, &spec, err);
}

/* Shared by mean_filter and gaussian_filter, which differ only in the kernel.
 * Returns without touching `grid` on the same conditions the CPU does, and
 * leaves it untouched if any pass fails. */
static tvdb_status_t tvdb_gpu_separable(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                                        const float* kern, int radius, int iterations,
                                        tvdb_error_t* err) {
  if (!ctx || !grid) { tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "filter: null grid"); return TVDB_ERROR_INVALID_ARGUMENT; }
  if (!grid->data || iterations <= 0 || radius <= 0) return TVDB_OK;   /* CPU returns */
  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  const size_t n = (size_t)nx * (size_t)ny * (size_t)nz;
  if (n == 0) return TVDB_OK;
  float* a = (float*)malloc(n * sizeof(float));
  float* b2 = (float*)malloc(n * sizeof(float));
  if (!a || !b2) { free(a); free(b2);
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  /* grid is the live input, so work on a copy and commit at the end: a failure
     partway through must not leave the caller's grid half-filtered. */
  float* cur = (float*)malloc(n * sizeof(float));
  if (!cur) { free(a); free(b2);
    tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  memcpy(cur, grid->data, n * sizeof(float));
  tvdb_error_t local; memset(&local, 0, sizeof local);
  tvdb_status_t st = TVDB_OK;
  float* ping = a; float* pong = b2;
  /* Each axis reads the *previous* axis's output: grid -> ping -> pong -> grid.
     Feeding every axis the same input is not a slower version of this, it is a
     different filter -- it keeps only the z pass and silently drops the other
     two -- and it agrees with the CPU for one iteration only by accident of the
     z pass being the last one written. */
  for (int it = 0; it < iterations && st == TVDB_OK; ++it) {
    st = tvdb_gpu_filter_step(ctx, 0, 0, radius, cur,    NULL, kern, ping,
                              nx, ny, nz, 0.0f, 0.0f, n, &local);
    if (st != TVDB_OK) break;
    st = tvdb_gpu_filter_step(ctx, 0, 1, radius, ping,   NULL, kern, pong,
                              nx, ny, nz, 0.0f, 0.0f, n, &local);
    if (st != TVDB_OK) break;
    st = tvdb_gpu_filter_step(ctx, 0, 2, radius, pong,   NULL, kern, cur,
                              nx, ny, nz, 0.0f, 0.0f, n, &local);
  }
  if (st == TVDB_OK) memcpy(grid->data, cur, n * sizeof(float));
  free(a); free(b2); free(cur);
  if (err && st == TVDB_OK) memset(err, 0, sizeof *err);
  else if (err) *err = local;
  return st;
}

tvdb_status_t tvdb_gpu_mean_filter(tvdb_gpu_context_t* ctx,tvdb_dense_grid* grid,int width, int iterations,tvdb_error_t* err) {
  return resident_filter_host(ctx,grid,0,width,iterations,err);
}

tvdb_status_t tvdb_gpu_gaussian_filter(tvdb_gpu_context_t* ctx,tvdb_dense_grid* grid,int width, int iterations,tvdb_error_t* err) {
  return resident_filter_host(ctx,grid,1,width,iterations,err);
}

tvdb_status_t tvdb_gpu_laplacian_filter(tvdb_gpu_context_t* ctx,tvdb_dense_grid* grid,int iterations,tvdb_error_t* err) {
  return resident_filter_host(ctx,grid,2,0,iterations,err);
}

/* Windowed median (parallels tvdb_median_filter). Jacobi: the CPU copies the grid
 * into a scratch buffer and reads only from that, so the host alternates two
 * buffers and copies back at the end. The selected value is order independent, so
 * this is bit-identical to the CPU's quickselect on finite input.
 *
 * radius is bounded at 2, which the shader's 125-float private window implies.
 * Beyond that this reports UNIMPLEMENTED rather than truncating the window --
 * a silently smaller window is a different filter. */
#define TVDB_GPU_MEDIAN_MAX_RADIUS 2

tvdb_status_t tvdb_gpu_median_filter(tvdb_gpu_context_t* ctx,tvdb_dense_grid* grid,int width, int iterations,tvdb_error_t* err) {
  return resident_filter_host(ctx,grid,3,width,iterations,err);
}

static tvdb_status_t tvdb_gpu_advect_semi_lagrangian_impl(tvdb_gpu_context_t* ctx,
    const tvdb_dense_grid* field, const tvdb_dense_vec_grid* velocity, float dt,
    tvdb_dense_grid* result, tvdb_error_t* err) {
  if (!ctx || !field || !velocity || !result) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "advect_sl: null argument");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (!field->data || !velocity->data || !result->data) return TVDB_OK;
  if (field->nx != velocity->nx || field->ny != velocity->ny || field->nz != velocity->nz) return TVDB_OK;
  if (field->nx != result->nx || field->ny != result->ny || field->nz != result->nz) return TVDB_OK;
  const size_t n = (size_t)field->nx * field->ny * field->nz;
  if (n == 0) return TVDB_OK;
  return tvdb_gpu_filter_step(ctx, 2, 0, 0, field->data, velocity->data, NULL,
                              result->data, field->nx, field->ny, field->nz,
                              dt, 1.0f / field->voxel_size, n, err);
}

tvdb_status_t tvdb_gpu_mesh_to_sdf(tvdb_gpu_context_t* ctx, const tvdb_triangle_mesh* mesh,
                                   float voxel_size, float band_width,
                                   tvdb_dense_grid* out, tvdb_error_t* err) {
  if (!ctx || !mesh || !out || mesh->vertex_count == 0 || mesh->face_count == 0 ||
      voxel_size <= 0.0f || band_width <= 0.0f) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid mesh_to_sdf arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_vec3f bmn = mesh->vertices[0], bmx = mesh->vertices[0];
  for (size_t i = 1; i < mesh->vertex_count; ++i) {
    tvdb_vec3f v = mesh->vertices[i];
    if (v.x < bmn.x) bmn.x = v.x; if (v.x > bmx.x) bmx.x = v.x;
    if (v.y < bmn.y) bmn.y = v.y; if (v.y > bmx.y) bmx.y = v.y;
    if (v.z < bmn.z) bmn.z = v.z; if (v.z > bmx.z) bmx.z = v.z;
  }
  bmn.x -= band_width; bmn.y -= band_width; bmn.z -= band_width;
  bmx.x += band_width; bmx.y += band_width; bmx.z += band_width;
  int nx = (int)ceilf((bmx.x - bmn.x) / voxel_size);
  int ny = (int)ceilf((bmx.y - bmn.y) / voxel_size);
  int nz = (int)ceilf((bmx.z - bmn.z) / voxel_size);
  if (nx < 1) nx = 1; if (ny < 1) ny = 1; if (nz < 1) nz = 1;
  tvdb_status_t st = tvdb_gpu_init_out_grid(out, nx, ny, nz, voxel_size, bmn.x, bmn.y, bmn.z, err);
  if (st != TVDB_OK) return st;
  size_t nvox = (size_t)nx*(size_t)ny*(size_t)nz;
  size_t nf = mesh->face_count;

  float* verts = (float*)malloc(nf * 9u * sizeof(float));
  float* normals = (float*)malloc(nf * 3u * sizeof(float));
  if (!verts || !normals) { free(verts); free(normals); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  for (size_t f = 0; f < nf; ++f) {
    tvdb_vec3f a = mesh->vertices[mesh->faces[f].v0];
    tvdb_vec3f b = mesh->vertices[mesh->faces[f].v1];
    tvdb_vec3f c = mesh->vertices[mesh->faces[f].v2];
    verts[9*f+0]=a.x; verts[9*f+1]=a.y; verts[9*f+2]=a.z;
    verts[9*f+3]=b.x; verts[9*f+4]=b.y; verts[9*f+5]=b.z;
    verts[9*f+6]=c.x; verts[9*f+7]=c.y; verts[9*f+8]=c.z;
    float ux=b.x-a.x, uy=b.y-a.y, uz=b.z-a.z, vx=c.x-a.x, vy=c.y-a.y, vz=c.z-a.z;
    float nxn=uy*vz-uz*vy, nyn=uz*vx-ux*vz, nzn=ux*vy-uy*vx;
    float l = sqrtf(nxn*nxn+nyn*nyn+nzn*nzn);
    if (l > 0.0f) { nxn/=l; nyn/=l; nzn/=l; }
    normals[3*f+0]=nxn; normals[3*f+1]=nyn; normals[3*f+2]=nzn;
  }

#ifndef TVDB_MESH_SDF_FORCE_BRUTE
#define TVDB_MESH_SDF_FORCE_BRUTE 0
#endif
  /* BVH first, exhaustive scan as the fallback: the BVH build can decline (very
   * deep tree, allocation failure), in which case this returns UNSUPPORTED and
   * the scan below runs. The scan stays for CUDA, which has no path here yet. */
  if (ctx->backend != TVDB_GPU_BACKEND_CUDA && !TVDB_MESH_SDF_FORCE_BRUTE &&
      mesh->face_count >= TVDB_MESH_SDF_BVH_MIN_FACES &&
      mesh->face_count <= TVDB_MESH_SDF_BVH_MAX_FACES) {
    tvdb_status_t bs = tvdb_vk_mesh_to_sdf_bvh(ctx, mesh, verts, normals, voxel_size,
                                               band_width, out, err);
    if (bs != TVDB_ERROR_UNIMPLEMENTED) {
      free(verts); free(normals);
      return bs;
    }
  }

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dv=0, dn=0, dout=0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto ms_host;
    if (!tvdb_cuda_ok(ctx, err, "f", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_mesh_to_sdf"))) { st=err?err->status:TVDB_ERROR_IO; goto ms_host; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dv, verts, nf*9u*sizeof(float), err)) != TVDB_OK) goto ms_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dn, normals, nf*3u*sizeof(float), err)) != TVDB_OK) goto ms_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, nvox*sizeof(float), err)) != TVDB_OK) goto ms_dev;
    float ox=out->ox, oy=out->oy, oz=out->oz;
    unsigned int unf=(unsigned int)nf, block=64;
    /* One launch per z slab, for the same TDR reason as Vulkan: a single launch
     * over millions of threads that each scan every face is one long unyielding
     * kernel. The slabs are queued back to back and awaited once. */
    long long slice = (long long)nx * ny;
    int zslab = (int)(TVDB_MESH_SDF_MAX_VOXELS_PER_DISPATCH / (slice > 0 ? slice : 1));
    if (zslab < 1) zslab = 1;
    for (int z0 = 0; z0 < nz; z0 += zslab) {
      int zc = (z0 + zslab <= nz) ? zslab : (nz - z0);
      unsigned int uvox = (unsigned int)(slice * zc);
      int zb = z0;
      void* args[] = {&dv,&dn,&dout,&nx,&ny,&nz,&ox,&oy,&oz,&voxel_size,&band_width,&unf,&zb,&zc};
      if (!tvdb_cuda_ok(ctx, err, "k", ctx->cuda.cuLaunchKernel(fn,(uvox+block-1u)/block,1,1,block,1,1,0,NULL,args,NULL))) { st=err?err->status:TVDB_ERROR_IO; goto ms_dev; }
    }
    if (!tvdb_cuda_ok(ctx, err, "s", ctx->cuda.cuCtxSynchronize())) { st=err?err->status:TVDB_ERROR_IO; goto ms_dev; }
    if (!tvdb_cuda_ok(ctx, err, "c", ctx->cuda.cuMemcpyDtoH(out->data, dout, nvox*sizeof(float)))) { st=err?err->status:TVDB_ERROR_IO; goto ms_dev; }
    st = TVDB_OK;
ms_dev:
    if (dout) ctx->cuda.cuMemFree(dout);
    if (dn) ctx->cuda.cuMemFree(dn);
    if (dv) ctx->cuda.cuMemFree(dv);
ms_host:
    free(verts); free(normals);
    return st;
  }

  /* Chunk z into slabs so no single dispatch is large enough to trip the driver's
   * watchdog. The uniform for every slab is written up front, into its own
   * 256-byte slice, and each slab gets a pre-built descriptor set bound to that
   * slice. That matters for more than tidiness: writing the uniform between
   * dispatches would force a wait after every slab, because the host must not
   * touch a buffer a queued dispatch still reads. With the slices pre-written the
   * whole chain is queued and awaited once. */
  long long slice = (long long)nx * ny;
  int zslab = (int)(TVDB_MESH_SDF_MAX_VOXELS_PER_DISPATCH / (slice > 0 ? slice : 1));
  if (zslab < 1) zslab = 1;
  int nslabs = (nz + zslab - 1) / zslab;
  enum { MSDF_STRIDE = 256 };   /* one 56-byte uniform block per slab, padded */

  tvdb_vk_buffer bv, bn, bo, bu;
  VkDescriptorSet* msets = NULL;
  int nmsets = 0;
  memset(&bv, 0, sizeof(bv)); memset(&bn, 0, sizeof(bn));
  memset(&bo, 0, sizeof(bo)); memset(&bu, 0, sizeof(bu));
  if ((st = tvdb_vk_create_buffer(ctx, nf*9u*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bv, err)) != TVDB_OK) { free(verts); free(normals); return st; }
  if ((st = tvdb_vk_create_buffer(ctx, nf*3u*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bn, err)) != TVDB_OK) goto mvd_v;
  if ((st = tvdb_vk_create_buffer(ctx, nvox*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto mvd_n;
  if ((st = tvdb_vk_create_buffer(ctx, (size_t)nslabs * MSDF_STRIDE, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto mvd_o;
  memcpy(bv.mapped, verts, nf*9u*sizeof(float));
  memcpy(bn.mapped, normals, nf*3u*sizeof(float));
  {
    /* std140: dim 0..15, grid_o 16..31, band 32..35, face_count 36..39,
     * zrange 40..47, pad 48..55. Asserted, because the shader reads zrange as an
     * ivec2 and a mis-sized struct here is a silently wrong slab. */
    typedef struct { int32_t dim[4]; float grid_o[4]; float band; uint32_t face_count;
                     int32_t zrange[2]; int32_t pad[2]; } msdf_uniform;
    _Static_assert(offsetof(msdf_uniform, band) == 32, "std140: band follows ivec4 + vec4");
    _Static_assert(offsetof(msdf_uniform, face_count) == 36, "std140: face_count follows band");
    _Static_assert(offsetof(msdf_uniform, zrange) == 40, "std140: ivec2 zrange follows face_count");
    _Static_assert(sizeof(msdf_uniform) == 56, "mesh_to_sdf uniform must be 56 bytes");
    for (int s = 0; s < nslabs; ++s) {
      int z0 = s * zslab;
      int zc = (z0 + zslab <= nz) ? zslab : (nz - z0);
      msdf_uniform par;
      memset(&par, 0, sizeof(par));
      par.dim[0]=nx; par.dim[1]=ny; par.dim[2]=nz;
      par.grid_o[0]=out->ox; par.grid_o[1]=out->oy; par.grid_o[2]=out->oz; par.grid_o[3]=voxel_size;
      par.band=band_width; par.face_count=(uint32_t)nf;
      par.zrange[0]=z0; par.zrange[1]=zc;
      memcpy((char*)bu.mapped + (size_t)s * MSDF_STRIDE, &par, sizeof(par));
    }
  }
  {
    const uint32_t types[4] = { VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,
                               VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER };
    VkDescriptorSetLayout layout = VK_NULL_HANDLE;
    int borrowed = 0;
    /* The slab sets are allocated below, before any dispatch in this call, so the
     * shared pool has to exist first. mesh_to_sdf is otherwise usually preceded by
     * other work that would have created it lazily -- calling it as the first GPU
     * op in a process handed vkAllocateDescriptorSets a NULL pool and crashed the
     * driver. */
    { tvdb_status_t ps = tvdb_vk_ensure_pools(ctx, err); if (ps != TVDB_OK) goto mvd_o; }
    if ((st = tvdb_vk_make_layout(ctx, kTvdbGpuMeshToSdfSpv, kTvdbGpuMeshToSdfSpv_len,
                                  4, types, &layout, &borrowed, err)) != TVDB_OK) goto mvd_o;
    msets = (VkDescriptorSet*)calloc((size_t)nslabs, sizeof(VkDescriptorSet));
    if (!msets) { st = TVDB_ERROR_OUT_OF_MEMORY; if (err) tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM");
                  if (layout && !borrowed && ctx->vk.DestroyDescriptorSetLayout) ctx->vk.DestroyDescriptorSetLayout(ctx->device, layout, NULL);
                  goto mvd_o; }
    for (int sidx = 0; sidx < nslabs; ++sidx) {
      VkDescriptorSetAllocateInfo dsai;
      memset(&dsai, 0, sizeof(dsai));
      dsai.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
      dsai.descriptorPool = ctx->desc_pool;
      dsai.descriptorSetCount = 1;
      dsai.pSetLayouts = &layout;
      if (!tvdb_vk_ok(ctx->vk.AllocateDescriptorSets(ctx->device, &dsai, &msets[sidx]), err, "vkAllocateDescriptorSets")) {
        st = err ? err->status : TVDB_ERROR_IO;
        nmsets = sidx;
        if (layout && !borrowed && ctx->vk.DestroyDescriptorSetLayout) ctx->vk.DestroyDescriptorSetLayout(ctx->device, layout, NULL);
        goto mvd_o;
      }
      VkDescriptorBufferInfo infos[4];
      VkWriteDescriptorSet wr[4];
      memset(infos, 0, sizeof(infos)); memset(wr, 0, sizeof(wr));
      infos[0].buffer = bv.buffer; infos[0].offset = 0; infos[0].range = nf*9u*sizeof(float);
      infos[1].buffer = bn.buffer; infos[1].offset = 0; infos[1].range = nf*3u*sizeof(float);
      infos[2].buffer = bo.buffer; infos[2].offset = 0; infos[2].range = nvox*sizeof(float);
      infos[3].buffer = bu.buffer; infos[3].offset = (VkDeviceSize)sidx * MSDF_STRIDE; infos[3].range = 56u;
      for (int i = 0; i < 4; ++i) {
        wr[i].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        wr[i].dstSet = msets[sidx]; wr[i].dstBinding = (uint32_t)i; wr[i].descriptorCount = 1;
        wr[i].descriptorType = types[i]; wr[i].pBufferInfo = &infos[i];
      }
      ctx->vk.UpdateDescriptorSets(ctx->device, 4, wr, 0, NULL);
      nmsets = sidx + 1;
    }
    if (layout && !borrowed && ctx->vk.DestroyDescriptorSetLayout)
      ctx->vk.DestroyDescriptorSetLayout(ctx->device, layout, NULL);

    for (int sidx = 0; sidx < nslabs; ++sidx) {
      int z0 = sidx * zslab;
      int zc = (z0 + zslab <= nz) ? zslab : (nz - z0);
      size_t slab_vox = (size_t)slice * (size_t)zc;
      tvdb_vk_dispatch_desc d;
      memset(&d, 0, sizeof(d));
      d.spv = kTvdbGpuMeshToSdfSpv; d.spv_len = kTvdbGpuMeshToSdfSpv_len; d.descriptor_count = 4;
      d.buffers[0]=&bv; d.buffers[1]=&bn; d.buffers[2]=&bo; d.buffers[3]=&bu;
      d.descriptor_types[0]=d.descriptor_types[1]=d.descriptor_types[2]=VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
      d.descriptor_types[3]=VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
      d.group_x = (uint32_t)((slab_vox + 63u) / 64u);
      d.defer_wait = TVDB_VK_DEFERRED_SUBMIT;
      d.preset_set = msets[sidx];
      if ((st = tvdb_vk_dispatch(ctx, &d, err)) != TVDB_OK) break;
    }
    if (st == TVDB_OK) st = tvdb_vk_flush(ctx, err);
  }
  if (st == TVDB_OK) memcpy(out->data, bo.mapped, nvox*sizeof(float));
  if (nmsets && msets && ctx->vk.FreeDescriptorSets)
    for (int sidx = 0; sidx < nmsets; ++sidx) if (msets[sidx]) ctx->vk.FreeDescriptorSets(ctx->device, ctx->desc_pool, 1, &msets[sidx]);
  free(msets);
  tvdb_vk_destroy_buffer(ctx, &bu);
mvd_o: tvdb_vk_destroy_buffer(ctx, &bo);
mvd_n: tvdb_vk_destroy_buffer(ctx, &bn);
mvd_v: tvdb_vk_destroy_buffer(ctx, &bv);
  free(verts); free(normals);
  return st;
}

// ---- marching cubes (GPU) ---------------------------------------------------

tvdb_status_t tvdb_gpu_marching_cubes(tvdb_gpu_context_t* ctx,const tvdb_dense_grid* grid,
    float isovalue,float** out_verts,size_t* out_tri_count,tvdb_error_t* err) {
  if(out_verts)*out_verts=NULL;
  if(out_tri_count)*out_tri_count=0;
  if(!ctx || !grid || !grid->data || !out_verts || !out_tri_count ||
     grid->nx<2 || grid->ny<2 || grid->nz<2) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid marching_cubes arguments");return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_gpu_grid_desc_t d={grid->nx,grid->ny,grid->nz,1,TVDB_GPU_F32,
    grid->ox,grid->oy,grid->oz,grid->voxel_size};
  tvdb_gpu_dense_grid_t* resident=NULL;tvdb_gpu_buffer_t* mesh=NULL;size_t count=0;
  tvdb_status_t st=tvdb_gpu_dense_grid_create(ctx,&d,&resident,err);
  if(st!=TVDB_OK)return st;
  st=tvdb_gpu_dense_grid_upload(resident,grid->data,resident->bytes,err);
  if(st==TVDB_OK)st=tvdb_gpu_marching_cubes_resident(ctx,resident,isovalue,&mesh,&count,err);
  if(st==TVDB_OK) {
    float* vertices=malloc((count?count:1)*9*sizeof(float));
    if(!vertices){st=TVDB_ERROR_OUT_OF_MEMORY;tvdb_gpu_set_error(err,st,"mesh allocation failed");}
    else {
      if(count)st=tvdb_gpu_buffer_download(mesh,vertices,count*9*sizeof(float),err);
      if(st==TVDB_OK){*out_verts=vertices;*out_tri_count=count;}else free(vertices);
    }
  }
  tvdb_gpu_buffer_destroy(mesh);tvdb_gpu_dense_grid_destroy(resident);return st;
}

// ---- strided sparse convolution (output-grid building) ----------------------

static int tvdb_floordiv(int a, int b) { int q = a / b, r = a % b; return (r != 0 && ((r < 0) != (b < 0))) ? q - 1 : q; }

typedef struct { int32_t c[3]; } tvdb_oc_entry;
static int tvdb_oc_cmp(const void* a,const void* b) {
  const tvdb_oc_entry *x=(const tvdb_oc_entry*)a,*y=(const tvdb_oc_entry*)b;
  for(int k=0;k<3;++k) if(x->c[k]!=y->c[k]) return x->c[k]<y->c[k] ? -1 : 1;
  return 0;
}

static tvdb_status_t tvdb_gpu_sparse_conv3d_strided_impl(tvdb_gpu_context_t* ctx, const tvdb_sparse_grid* in,
                                             const float* kernel, int kx, int ky, int kz,
                                             int stride, float pad_value,
                                             tvdb_sparse_grid* out, tvdb_error_t* err) {
  if (!ctx || !in || !kernel || !out || kx <= 0 || ky <= 0 || kz <= 0 || stride <= 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid strided sparse conv arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  out->count = 0; out->voxel_size = in->voxel_size * (float)stride; out->ox = in->ox; out->oy = in->oy; out->oz = in->oz;
  size_t n_in = in->count;
  if (n_in == 0) return TVDB_OK;

  // Output coords = unique floor(coord/stride) of the input set.
  tvdb_oc_entry* ent = (tvdb_oc_entry*)malloc(n_in * sizeof(tvdb_oc_entry));
  if (!ent) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  for (size_t i = 0; i < n_in; ++i) {
    int ox = tvdb_floordiv(in->coords[i].x, stride);
    int oy = tvdb_floordiv(in->coords[i].y, stride);
    int oz = tvdb_floordiv(in->coords[i].z, stride);
    ent[i].c[0] = ox; ent[i].c[1] = oy; ent[i].c[2] = oz;
  }
  qsort(ent, n_in, sizeof(tvdb_oc_entry), tvdb_oc_cmp);
  size_t n_out = 0;
  for (size_t i = 0; i < n_in; ++i) if (i == 0 || tvdb_oc_cmp(&ent[i],&ent[i-1]) != 0) {
    ent[n_out].c[0] = ent[i].c[0]; ent[n_out].c[1] = ent[i].c[1]; ent[n_out].c[2] = ent[i].c[2]; ++n_out;
  }

  size_t kn = (size_t)kx * (size_t)ky * (size_t)kz;
  int32_t* in4 = (int32_t*)malloc(n_in * 4u * sizeof(int32_t));
  int32_t* outc4 = (int32_t*)malloc(n_out * 4u * sizeof(int32_t));
  float* outval = (float*)malloc(n_out * sizeof(float));
  if (!in4 || !outc4 || !outval) { free(ent); free(in4); free(outc4); free(outval); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  for (size_t i = 0; i < n_in; ++i) { in4[4*i+0]=in->coords[i].x; in4[4*i+1]=in->coords[i].y; in4[4*i+2]=in->coords[i].z; memcpy(&in4[4*i+3], &in->values[i], sizeof(float)); }
  for (size_t i = 0; i < n_out; ++i) { outc4[4*i+0]=ent[i].c[0]; outc4[4*i+1]=ent[i].c[1]; outc4[4*i+2]=ent[i].c[2]; outc4[4*i+3]=0; }
  tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr di=0, doc=0, dk=0, dov=0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto cs_host;
    if (!tvdb_cuda_ok(ctx, err, "f", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_sparse_conv_strided"))) { st=err?err->status:TVDB_ERROR_IO; goto cs_host; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &di, in4, n_in*4u*sizeof(int32_t), err)) != TVDB_OK) goto cs_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &doc, outc4, n_out*4u*sizeof(int32_t), err)) != TVDB_OK) goto cs_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dk, kernel, kn*sizeof(float), err)) != TVDB_OK) goto cs_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dov, NULL, n_out*sizeof(float), err)) != TVDB_OK) goto cs_dev;
    unsigned int uni=(unsigned int)n_in, uno=(unsigned int)n_out, block=128;
    void* args[] = {&di,&doc,&dk,&dov,&uni,&uno,&kx,&ky,&kz,&stride,&pad_value};
    if (!tvdb_cuda_ok(ctx, err, "k", ctx->cuda.cuLaunchKernel(fn,(uno+block-1u)/block,1,1,block,1,1,0,NULL,args,NULL))) { st=err?err->status:TVDB_ERROR_IO; goto cs_dev; }
    if (!tvdb_cuda_ok(ctx, err, "s", ctx->cuda.cuCtxSynchronize())) { st=err?err->status:TVDB_ERROR_IO; goto cs_dev; }
    if (!tvdb_cuda_ok(ctx, err, "c", ctx->cuda.cuMemcpyDtoH(outval, dov, n_out*sizeof(float)))) { st=err?err->status:TVDB_ERROR_IO; goto cs_dev; }
    st = TVDB_OK;
cs_dev:
    if (dov) ctx->cuda.cuMemFree(dov);
    if (dk) ctx->cuda.cuMemFree(dk);
    if (doc) ctx->cuda.cuMemFree(doc);
    if (di) ctx->cuda.cuMemFree(di);
    goto cs_build;
  }
  {
    tvdb_vk_buffer bi, boc, bk, bov, bu;
    if ((st = tvdb_vk_create_buffer(ctx, n_in*4u*sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bi, err)) != TVDB_OK) goto cs_host;
    if ((st = tvdb_vk_create_buffer(ctx, n_out*4u*sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &boc, err)) != TVDB_OK) goto cs_bi;
    if ((st = tvdb_vk_create_buffer(ctx, kn*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bk, err)) != TVDB_OK) goto cs_boc;
    if ((st = tvdb_vk_create_buffer(ctx, n_out*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bov, err)) != TVDB_OK) goto cs_bk;
    if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto cs_bov;
    memcpy(bi.mapped, in4, n_in*4u*sizeof(int32_t));
    memcpy(boc.mapped, outc4, n_out*4u*sizeof(int32_t));
    memcpy(bk.mapped, kernel, kn*sizeof(float));
    struct { uint32_t n_in, n_out, pad0[2]; int32_t kdim[4]; int32_t stride; float pad_value; uint32_t pad1[2]; } par;
    memset(&par, 0, sizeof(par));
    par.n_in=(uint32_t)n_in; par.n_out=(uint32_t)n_out; par.kdim[0]=kx; par.kdim[1]=ky; par.kdim[2]=kz; par.stride=stride; par.pad_value=pad_value;
    memcpy(bu.mapped, &par, sizeof(par));
    tvdb_vk_dispatch_desc d;
    memset(&d, 0, sizeof(d));
    d.spv = kTvdbGpuSparseConvStridedSpv; d.spv_len = kTvdbGpuSparseConvStridedSpv_len; d.descriptor_count = 5;
    d.buffers[0]=&bi; d.buffers[1]=&boc; d.buffers[2]=&bk; d.buffers[3]=&bov; d.buffers[4]=&bu;
    for (int i = 0; i < 4; ++i) d.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    d.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    d.group_x = (uint32_t)((n_out + 127u) / 128u);
    st = tvdb_vk_dispatch(ctx, &d, err);
    if (st == TVDB_OK) memcpy(outval, bov.mapped, n_out*sizeof(float));
    tvdb_vk_destroy_buffer(ctx, &bu);
cs_bov: tvdb_vk_destroy_buffer(ctx, &bov);
cs_bk: tvdb_vk_destroy_buffer(ctx, &bk);
cs_boc: tvdb_vk_destroy_buffer(ctx, &boc);
cs_bi: tvdb_vk_destroy_buffer(ctx, &bi);
  }
cs_build:
  if (st == TVDB_OK) {
    if (!tvdb_sparse_grid_reserve(out, n_out ? n_out : 1)) { st = TVDB_ERROR_OUT_OF_MEMORY; tvdb_gpu_set_error(err, st, "OOM"); }
    else {
      for (size_t i = 0; i < n_out; ++i) { out->coords[i].x=outc4[4*i+0]; out->coords[i].y=outc4[4*i+1]; out->coords[i].z=outc4[4*i+2]; out->values[i]=outval[i]; }
      out->count = n_out;
    }
  }
cs_host:
  free(ent); free(in4); free(outc4); free(outval);
  return st;
}

// ---- transposed sparse convolution ------------------------------------------

static tvdb_status_t tvdb_gpu_sparse_conv3d_transpose_impl(tvdb_gpu_context_t* ctx, const tvdb_sparse_grid* in,
                                               const float* kernel, int kx, int ky, int kz,
                                               int stride, tvdb_sparse_grid* out, tvdb_error_t* err) {
  if (!ctx || !in || !kernel || !out || kx <= 0 || ky <= 0 || kz <= 0 || stride <= 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid transpose conv arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  out->count = 0; out->voxel_size = in->voxel_size / (float)stride; out->ox = in->ox; out->oy = in->oy; out->oz = in->oz;
  size_t n_in = in->count;
  if (n_in == 0) return TVDB_OK;
  int ax = kx/2, ay = ky/2, az = kz/2;
  // Output bbox over ic*stride + tap, tap in [-a, k-1-a].
  int32_t bbmin[3]={INT32_MAX,INT32_MAX,INT32_MAX},bbmax[3]={INT32_MIN,INT32_MIN,INT32_MIN};
  bool any=false;
  for(size_t i=0;i<n_in;++i) {
    int64_t base[3]={(int64_t)in->coords[i].x*stride,(int64_t)in->coords[i].y*stride,(int64_t)in->coords[i].z*stride};
    int anchor[3]={ax,ay,az},dims[3]={kx,ky,kz};
    int64_t lo[3],hi[3]; bool valid=true;
    for(int a=0;a<3;++a) {
      lo[a]=base[a]-anchor[a]; hi[a]=base[a]+dims[a]-1-anchor[a];
      if(lo[a]>INT32_MAX || hi[a]<INT32_MIN) valid=false;
      if(lo[a]<INT32_MIN) lo[a]=INT32_MIN;
      if(hi[a]>INT32_MAX) hi[a]=INT32_MAX;
    }
    if(!valid) continue;
    any=true;
    for(int a=0;a<3;++a) { if(lo[a]<bbmin[a]) bbmin[a]=(int32_t)lo[a]; if(hi[a]>bbmax[a]) bbmax[a]=(int32_t)hi[a]; }
  }
  if(!any) return TVDB_OK;
  long long dx=(long long)bbmax[0]-bbmin[0]+1, dy=(long long)bbmax[1]-bbmin[1]+1, dz=(long long)bbmax[2]-bbmin[2]+1;
  if (dx<=0 || dy<=0 || dz<=0 || dx>400000000 || dy>400000000/dx || dz>400000000/(dx*dy)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"sparse bbox too large"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  long long vol = dx*dy*dz;
  if (vol <= 0 || vol > (long long)400000000) { tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "transpose conv bbox too large"); return TVDB_ERROR_INVALID_ARGUMENT; }
  size_t volume = (size_t)vol, kn = (size_t)kx*ky*kz;
  size_t capll; if (!tvdb_size_mul(n_in,kn,&capll)) capll=volume; if (capll > volume) capll = volume; size_t cap = capll;
  int idx[3] = {(int)dx,(int)dy,(int)dz}, bb[3] = {bbmin[0],bbmin[1],bbmin[2]};

  int32_t* in4 = (int32_t*)malloc(n_in*4u*sizeof(int32_t));
  int32_t* outd = (int32_t*)malloc(cap*4u*sizeof(int32_t));
  if (!in4 || !outd) { free(in4); free(outd); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  for (size_t i = 0; i < n_in; ++i) { in4[4*i+0]=in->coords[i].x; in4[4*i+1]=in->coords[i].y; in4[4*i+2]=in->coords[i].z; memcpy(&in4[4*i+3], &in->values[i], sizeof(float)); }
  uint32_t m = 0; tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fs=NULL, ff=NULL; CUdeviceptr dv=0, doc=0, di=0, dk=0, dcnt=0, dout=0;
    float* zf = (float*)calloc(volume, sizeof(float)); uint32_t* zu = (uint32_t*)calloc(volume, sizeof(uint32_t));
    if (!zf || !zu) { free(zf); free(zu); free(in4); free(outd); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto tc_host;
    if (!tvdb_cuda_ok(ctx, err, "f", ctx->cuda.cuModuleGetFunction(&fs, module, "tvdb_cuda_conv_transpose_scatter")) ||
        !tvdb_cuda_ok(ctx, err, "f", ctx->cuda.cuModuleGetFunction(&ff, module, "tvdb_cuda_sparse_finalize"))) { st=err?err->status:TVDB_ERROR_IO; goto tc_host; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dv, zf, volume*sizeof(float), err)) != TVDB_OK) goto tc_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &doc, zu, volume*sizeof(uint32_t), err)) != TVDB_OK) goto tc_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &di, in4, n_in*4u*sizeof(int32_t), err)) != TVDB_OK) goto tc_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dk, kernel, kn*sizeof(float), err)) != TVDB_OK) goto tc_dev;
    { uint32_t z=0; if ((st = tvdb_cuda_alloc_copy_in(ctx, &dcnt, &z, sizeof(uint32_t), err)) != TVDB_OK) goto tc_dev; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, cap*4u*sizeof(int32_t), err)) != TVDB_OK) goto tc_dev;
    unsigned int uni=(unsigned int)n_in, uvol=(unsigned int)volume, ucap=(unsigned int)cap, block=128;
    void* sargs[] = {&dv,&doc,&di,&dk,&idx[0],&idx[1],&idx[2],&bb[0],&bb[1],&bb[2],&kx,&ky,&kz,&stride,&uni};
    if (!tvdb_cuda_ok(ctx, err, "k", ctx->cuda.cuLaunchKernel(fs,(uni+block-1u)/block,1,1,block,1,1,0,NULL,sargs,NULL))) { st=err?err->status:TVDB_ERROR_IO; goto tc_dev; }
    void* fargs[] = {&dv,&doc,&dcnt,&dout,&idx[0],&idx[1],&idx[2],&bb[0],&bb[1],&bb[2],&ucap};
    if (!tvdb_cuda_ok(ctx, err, "k", ctx->cuda.cuLaunchKernel(ff,(uvol+block-1u)/block,1,1,block,1,1,0,NULL,fargs,NULL))) { st=err?err->status:TVDB_ERROR_IO; goto tc_dev; }
    if (!tvdb_cuda_ok(ctx, err, "s", ctx->cuda.cuCtxSynchronize())) { st=err?err->status:TVDB_ERROR_IO; goto tc_dev; }
    if (!tvdb_cuda_ok(ctx, err, "c", ctx->cuda.cuMemcpyDtoH(&m, dcnt, sizeof(uint32_t)))) { st=err?err->status:TVDB_ERROR_IO; goto tc_dev; }
    if (m > cap) m = (uint32_t)cap;
    if (m && !tvdb_cuda_ok(ctx, err, "c", ctx->cuda.cuMemcpyDtoH(outd, dout, (size_t)m*4u*sizeof(int32_t)))) { st=err?err->status:TVDB_ERROR_IO; goto tc_dev; }
    st = TVDB_OK;
tc_dev:
    if (dout) ctx->cuda.cuMemFree(dout); if (dcnt) ctx->cuda.cuMemFree(dcnt); if (dk) ctx->cuda.cuMemFree(dk);
    if (di) ctx->cuda.cuMemFree(di); if (doc) ctx->cuda.cuMemFree(doc); if (dv) ctx->cuda.cuMemFree(dv);
    free(zf); free(zu);
    goto tc_build;
tc_host:
    free(zf); free(zu); free(in4); free(outd); return st;
  }
  {
    tvdb_vk_buffer bv, boc, bi, bk, bcnt, bout, bus, buf;
    if ((st = tvdb_vk_create_buffer(ctx, volume*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bv, err)) != TVDB_OK) { free(in4); free(outd); return st; }
    if ((st = tvdb_vk_create_buffer(ctx, volume*sizeof(uint32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &boc, err)) != TVDB_OK) goto td_v;
    if ((st = tvdb_vk_create_buffer(ctx, n_in*4u*sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bi, err)) != TVDB_OK) goto td_oc;
    if ((st = tvdb_vk_create_buffer(ctx, kn*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bk, err)) != TVDB_OK) goto td_i;
    if ((st = tvdb_vk_create_buffer(ctx, sizeof(uint32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bcnt, err)) != TVDB_OK) goto td_k;
    if ((st = tvdb_vk_create_buffer(ctx, cap*4u*sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bout, err)) != TVDB_OK) goto td_cnt;
    if ((st = tvdb_vk_create_buffer(ctx, 64, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bus, err)) != TVDB_OK) goto td_out;
    if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &buf, err)) != TVDB_OK) goto td_us;
    memset(bv.mapped, 0, volume*sizeof(float)); memset(boc.mapped, 0, volume*sizeof(uint32_t)); *(uint32_t*)bcnt.mapped = 0u;
    memcpy(bi.mapped, in4, n_in*4u*sizeof(int32_t)); memcpy(bk.mapped, kernel, kn*sizeof(float));
    struct { int32_t dims[4]; int32_t bbmin[4]; int32_t kdim[4]; int32_t stride; uint32_t n_in; uint32_t pad[2]; } sp;
    memset(&sp, 0, sizeof(sp)); sp.dims[0]=(int)dx; sp.dims[1]=(int)dy; sp.dims[2]=(int)dz; sp.bbmin[0]=bbmin[0]; sp.bbmin[1]=bbmin[1]; sp.bbmin[2]=bbmin[2];
    sp.kdim[0]=kx; sp.kdim[1]=ky; sp.kdim[2]=kz; sp.stride=stride; sp.n_in=(uint32_t)n_in;
    memcpy(bus.mapped, &sp, sizeof(sp));
    struct { int32_t dims[4]; int32_t bbmin[4]; uint32_t cap; uint32_t pad[3]; } fp;
    memset(&fp, 0, sizeof(fp)); fp.dims[0]=(int)dx; fp.dims[1]=(int)dy; fp.dims[2]=(int)dz; fp.bbmin[0]=bbmin[0]; fp.bbmin[1]=bbmin[1]; fp.bbmin[2]=bbmin[2]; fp.cap=(uint32_t)cap;
    memcpy(buf.mapped, &fp, sizeof(fp));
    tvdb_vk_dispatch_desc ds;
    memset(&ds, 0, sizeof(ds));
    ds.spv = kTvdbGpuConvTransposeScatterSpv; ds.spv_len = kTvdbGpuConvTransposeScatterSpv_len; ds.descriptor_count = 5;
    ds.buffers[0]=&bv; ds.buffers[1]=&boc; ds.buffers[2]=&bi; ds.buffers[3]=&bk; ds.buffers[4]=&bus;
    for (int i = 0; i < 4; ++i) ds.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    ds.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    ds.group_x = (uint32_t)((n_in + 127u) / 128u);
    /* scatter -> finalize, one wait. */
    ds.defer_wait = TVDB_VK_DEFERRED_SUBMIT;
    st = tvdb_vk_dispatch(ctx, &ds, err);
    if (st == TVDB_OK) {
      tvdb_vk_dispatch_desc df;
      memset(&df, 0, sizeof(df));
      df.spv = kTvdbGpuSparseFinalizeSpv; df.spv_len = kTvdbGpuSparseFinalizeSpv_len; df.descriptor_count = 5;
      df.buffers[0]=&bv; df.buffers[1]=&boc; df.buffers[2]=&bcnt; df.buffers[3]=&bout; df.buffers[4]=&buf;
      for (int i = 0; i < 4; ++i) df.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
      df.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
      df.group_x = (uint32_t)((volume + 127u) / 128u);
      df.defer_wait = TVDB_VK_DEFERRED_SUBMIT;
      st = tvdb_vk_dispatch(ctx, &df, err);
    }
    if (st == TVDB_OK) st = tvdb_vk_flush(ctx, err);
    if (st == TVDB_OK) { m = *(uint32_t*)bcnt.mapped; if (m > cap) m = (uint32_t)cap; memcpy(outd, bout.mapped, (size_t)m*4u*sizeof(int32_t)); }
    tvdb_vk_destroy_buffer(ctx, &buf);
td_us: tvdb_vk_destroy_buffer(ctx, &bus);
td_out: tvdb_vk_destroy_buffer(ctx, &bout);
td_cnt: tvdb_vk_destroy_buffer(ctx, &bcnt);
td_k: tvdb_vk_destroy_buffer(ctx, &bk);
td_i: tvdb_vk_destroy_buffer(ctx, &bi);
td_oc: tvdb_vk_destroy_buffer(ctx, &boc);
td_v: tvdb_vk_destroy_buffer(ctx, &bv);
  }
tc_build:
  if (st == TVDB_OK) {
    if (!tvdb_sparse_grid_reserve(out, m ? m : 1)) { st = TVDB_ERROR_OUT_OF_MEMORY; tvdb_gpu_set_error(err, st, "OOM"); }
    else {
      for (uint32_t i = 0; i < m; ++i) { out->coords[i].x=outd[4*i+0]; out->coords[i].y=outd[4*i+1]; out->coords[i].z=outd[4*i+2]; int32_t bits=outd[4*i+3]; memcpy(&out->values[i], &bits, sizeof(float)); }
      out->count = m;
    }
  }
  free(in4); free(outd);
  return st;
}

// ---- generic compute-dispatch engine ----------------------------------------

/* Deferred dispatches, and the buffers they still need.
 *
 * A queued dispatch references its VkBuffers in a command buffer that has not
 * executed yet, and Vulkan requires them to stay alive until it has. The buffers
 * here are created per call, so ownership moves into this queue and the flush
 * destroys them. A queue entry therefore holds the buffers by value, not a
 * pointer to a local -- holding a pointer to the caller's frame is exactly the
 * dangling-reference bug this is here to avoid.
 *
 * Each context owns its queue and releases it before destroying the device.
 */
tvdb_status_t tvdb_gpu_dispatch_flush(tvdb_gpu_context_t* ctx, tvdb_error_t* err) {
  if (!ctx) { tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "flush: null ctx"); return TVDB_ERROR_INVALID_ARGUMENT; }
  tvdb_status_t st = TVDB_OK;
  if (ctx->backend == TVDB_GPU_BACKEND_VULKAN) st = tvdb_vk_flush(ctx, err);
  for (unsigned int q = 0; q < ctx->deferred_count; ++q) {
    tvdb_gpu_deferred* d = &ctx->deferred[q];
    if (st == TVDB_OK)
      for (unsigned int i = 0; i < d->nout; ++i)
        if (d->bufs[d->output_binding[i]].mapped)
          memcpy(d->host[i], d->bufs[d->output_binding[i]].mapped, d->bytes[i]);
    for (unsigned int i = 0; i < d->nbufs; ++i) tvdb_vk_destroy_buffer(ctx, &d->bufs[i]);
  }
  ctx->deferred_count = 0;
  return st;
}

tvdb_status_t tvdb_gpu_dispatch(tvdb_gpu_context_t* ctx, const tvdb_gpu_dispatch_spec_t* spec,
                                tvdb_error_t* err) {
  if (!ctx || !spec || spec->num_bindings > 6 || (spec->num_bindings && !spec->bindings)) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid dispatch spec");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  for (unsigned int i = 0; i < spec->num_bindings; ++i) {
    const tvdb_gpu_binding_t* b = &spec->bindings[i];
    if (b->kind < TVDB_GPU_BIND_STORAGE_IN || b->kind > TVDB_GPU_BIND_UNIFORM ||
        b->size_bytes == 0 || (b->kind != TVDB_GPU_BIND_STORAGE_OUT && !b->host_data) ||
        ((b->kind == TVDB_GPU_BIND_STORAGE_OUT || b->kind == TVDB_GPU_BIND_STORAGE_INOUT) && !b->host_data)) {
      tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid dispatch binding");
      return TVDB_ERROR_INVALID_ARGUMENT;
    }
  }
  tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    if (!spec->cuda_kernel) { tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "no CUDA kernel name in dispatch spec"); return TVDB_ERROR_UNIMPLEMENTED; }
    CUmodule module = NULL; CUfunction fn = NULL;
    CUdeviceptr dptr[6]; for (int i = 0; i < 6; ++i) dptr[i] = 0;
    void* args[6]; for (int i = 0; i < 6; ++i) args[i] = NULL;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) return st;
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, spec->cuda_kernel))) return err ? err->status : TVDB_ERROR_IO;
    st = TVDB_OK;
    for (unsigned int i = 0; i < spec->num_bindings && st == TVDB_OK; ++i) {
      const tvdb_gpu_binding_t* b = &spec->bindings[i];
      int upload = (b->kind != TVDB_GPU_BIND_STORAGE_OUT);
      st = tvdb_cuda_alloc_copy_in(ctx, &dptr[i], upload ? b->host_data : NULL, b->size_bytes, err);
      args[i] = &dptr[i];
    }
    if (st == TVDB_OK) {
      unsigned int block = 128;
      if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, spec->group_count_x ? spec->group_count_x : 1u, 1, 1, block, 1, 1, 0, NULL, args, NULL))) st = err ? err->status : TVDB_ERROR_IO;
    }
    if (st == TVDB_OK && !tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) st = err ? err->status : TVDB_ERROR_IO;
    for (unsigned int i = 0; i < spec->num_bindings && st == TVDB_OK; ++i) {
      const tvdb_gpu_binding_t* b = &spec->bindings[i];
      if (b->kind == TVDB_GPU_BIND_STORAGE_OUT || b->kind == TVDB_GPU_BIND_STORAGE_INOUT)
        if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(b->host_data, dptr[i], b->size_bytes))) st = err ? err->status : TVDB_ERROR_IO;
    }
    for (unsigned int i = 0; i < spec->num_bindings; ++i) if (dptr[i]) ctx->cuda.cuMemFree(dptr[i]);
    return st;
  }

  // Vulkan path.
  if (!spec->spv || spec->spv_len == 0) { tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "no SPIR-V in dispatch spec"); return TVDB_ERROR_UNIMPLEMENTED; }
  tvdb_vk_buffer bufs[6]; memset(bufs, 0, sizeof(bufs));
  unsigned int created = 0;
  st = TVDB_OK;
  for (unsigned int i = 0; i < spec->num_bindings && st == TVDB_OK; ++i) {
    const tvdb_gpu_binding_t* b = &spec->bindings[i];
    uint32_t usage = (b->kind == TVDB_GPU_BIND_UNIFORM) ? VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT : VK_BUFFER_USAGE_STORAGE_BUFFER_BIT;
    size_t sz = (b->kind == TVDB_GPU_BIND_UNIFORM && b->size_bytes < 16) ? 16 : b->size_bytes;
    st = tvdb_vk_create_buffer(ctx, sz, usage, &bufs[i], err);
    if (st != TVDB_OK) break;
    created = i + 1;
    if (b->kind != TVDB_GPU_BIND_STORAGE_OUT) memcpy(bufs[i].mapped, b->host_data, b->size_bytes);
  }
  if (st == TVDB_OK) {
    tvdb_vk_dispatch_desc d;
    memset(&d, 0, sizeof(d));
    d.spv = spec->spv; d.spv_len = spec->spv_len; d.descriptor_count = spec->num_bindings;
    for (unsigned int i = 0; i < spec->num_bindings; ++i) {
      d.buffers[i] = &bufs[i];
      d.descriptor_types[i] = (spec->bindings[i].kind == TVDB_GPU_BIND_UNIFORM)
          ? VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER : VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    }
    d.group_x = spec->group_count_x ? spec->group_count_x : 1u;
    /* The dispatch itself is unconditional. An earlier version put
       `st = tvdb_vk_dispatch(...)` inside the defer branch, so every
       non-deferred call skipped the dispatch entirely while `st` stayed TVDB_OK
       from the buffer-creation loop -- a silently "successful" no-op that showed
       up as five ops reading back their uninitialised input buffers. */
    const int can_defer = spec->defer && (ctx->deferred_count < TVDB_GPU_DEFER_MAX);
    if (can_defer) d.defer_wait = TVDB_VK_DEFERRED_SUBMIT;
    st = tvdb_vk_dispatch(ctx, &d, err);
    if (st == TVDB_OK && can_defer) {
      /* Ownership of the buffers moves to the queue: a queued command buffer
         still references them, and Vulkan requires them to outlive it. */
      tvdb_gpu_deferred* q = &ctx->deferred[ctx->deferred_count++];
      q->nbufs = created;
      for (unsigned int i = 0; i < created; ++i) q->bufs[i] = bufs[i];
      q->nout = 0;
      for (unsigned int i = 0; i < spec->num_bindings; ++i) {
        const tvdb_gpu_binding_t* b = &spec->bindings[i];
        if (b->kind == TVDB_GPU_BIND_STORAGE_OUT || b->kind == TVDB_GPU_BIND_STORAGE_INOUT) {
          q->output_binding[q->nout] = i;
          q->host[q->nout] = b->host_data;
          q->bytes[q->nout] = b->size_bytes;
          q->nout++;
        }
      }
      created = 0;
    }
    if (st == TVDB_OK && !can_defer) {
      for (unsigned int i = 0; i < spec->num_bindings; ++i) {
        const tvdb_gpu_binding_t* b = &spec->bindings[i];
        if (b->kind == TVDB_GPU_BIND_STORAGE_OUT || b->kind == TVDB_GPU_BIND_STORAGE_INOUT)
          memcpy(b->host_data, bufs[i].mapped, b->size_bytes);
      }
    }
  }
  for (unsigned int i = 0; i < created; ++i) tvdb_vk_destroy_buffer(ctx, &bufs[i]);
  return st;
}

tvdb_status_t tvdb_gpu_axpy(tvdb_gpu_context_t* ctx, const float* x, const float* y,
                            float alpha, size_t n, float* out, tvdb_error_t* err) {
  if (!ctx || (n && (!x || !y || !out))) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid axpy arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (n == 0) return TVDB_OK;
  struct { uint32_t n; float alpha; uint32_t pad[2]; } params;
  memset(&params, 0, sizeof(params));
  params.n = (uint32_t)n; params.alpha = alpha;
  tvdb_gpu_binding_t bindings[4];
  bindings[0].kind = TVDB_GPU_BIND_STORAGE_IN;  bindings[0].host_data = (void*)x;   bindings[0].size_bytes = n * sizeof(float);
  bindings[1].kind = TVDB_GPU_BIND_STORAGE_IN;  bindings[1].host_data = (void*)y;   bindings[1].size_bytes = n * sizeof(float);
  bindings[2].kind = TVDB_GPU_BIND_STORAGE_OUT; bindings[2].host_data = out;         bindings[2].size_bytes = n * sizeof(float);
  bindings[3].kind = TVDB_GPU_BIND_UNIFORM;     bindings[3].host_data = &params;     bindings[3].size_bytes = sizeof(params);
  tvdb_gpu_dispatch_spec_t spec;
  memset(&spec, 0, sizeof(spec));
  spec.spv = kTvdbGpuAxpySpv; spec.spv_len = kTvdbGpuAxpySpv_len;
  spec.cuda_kernel = "tvdb_cuda_axpy";
  spec.bindings = bindings; spec.num_bindings = 4;
  spec.group_count_x = (uint32_t)((n + 127u) / 128u);
  return tvdb_gpu_dispatch(ctx, &spec, err);
}

// ---- device-resident buffer interop -----------------------------------------

tvdb_status_t tvdb_gpu_buffer_create(tvdb_gpu_context_t* ctx, size_t size_bytes,
                                     tvdb_gpu_buffer_t** out, tvdb_error_t* err) {
  if (!ctx || !out || size_bytes == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid buffer_create arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  *out = NULL;
  tvdb_gpu_buffer_t* b = (tvdb_gpu_buffer_t*)calloc(1, sizeof(*b));
  if (!b) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  b->ctx = ctx; b->backend = ctx->backend; b->size = size_bytes;
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    if (!tvdb_cuda_ok(ctx, err, "cuMemAlloc", ctx->cuda.cuMemAlloc(&b->cu, size_bytes))) { free(b); return err ? err->status : TVDB_ERROR_IO; }
  } else {
    tvdb_status_t st = tvdb_vk_create_buffer(ctx, size_bytes, VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &b->vk, err);
    if (st != TVDB_OK) { free(b); return st; }
  }
  *out = b;
  return TVDB_OK;
}

void tvdb_gpu_buffer_destroy(tvdb_gpu_buffer_t* buf) {
  if (!buf) return;
  if (buf->resident) buf->ctx->resident_metrics.live_bytes -= buf->size;
  if (buf->backend == TVDB_GPU_BACKEND_CUDA) {
    if (buf->imported) {
      // The mapped device pointer is owned by the external-memory object; do not
      // cuMemFree it. Releasing the external memory frees the mapping.
      if (buf->ext_mem && buf->ctx->cuda.cuDestroyExternalMemory) buf->ctx->cuda.cuDestroyExternalMemory(buf->ext_mem);
    } else if (buf->cu) {
      buf->ctx->cuda.cuMemFree(buf->cu);
    }
  } else {
    tvdb_vk_destroy_buffer(buf->ctx, &buf->vk);
  }
  free(buf);
}

tvdb_status_t tvdb_gpu_buffer_upload(tvdb_gpu_buffer_t* buf, const void* src, size_t size, tvdb_error_t* err) {
  if (!buf || !src || size > buf->size) { tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid buffer_upload arguments"); return TVDB_ERROR_INVALID_ARGUMENT; }
  if (buf->resident) buf->ctx->resident_metrics.upload_bytes += size;
  if (buf->backend == TVDB_GPU_BACKEND_CUDA) {
    if (!tvdb_cuda_ok(buf->ctx, err, "cuMemcpyHtoD", buf->ctx->cuda.cuMemcpyHtoD(buf->cu, src, size))) return err ? err->status : TVDB_ERROR_IO;
  } else if (buf->vk.mapped) {
    memcpy(buf->vk.mapped, src, size);
  } else {
    // Device-local (e.g. exportable) buffer: stage through a host-visible buffer.
    tvdb_vk_buffer staging;
    tvdb_status_t st = tvdb_vk_create_buffer(buf->ctx, size, VK_BUFFER_USAGE_TRANSFER_SRC_BIT, &staging, err);
    if (st != TVDB_OK) return st;
    memcpy(staging.mapped, src, size);
    tvdb_vk_copy copy = {0};
    copy.src=staging.buffer; copy.dst=buf->vk.buffer; copy.size=size;
    copy.src_stage=VK_PIPELINE_STAGE_HOST_BIT; copy.src_access=VK_ACCESS_HOST_WRITE_BIT;
    copy.dst_stage=VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT; copy.dst_access=VK_ACCESS_SHADER_READ_BIT|VK_ACCESS_SHADER_WRITE_BIT;
    st=tvdb_vk_run_copies(buf->ctx,&copy,1,err);
    tvdb_vk_destroy_buffer(buf->ctx, &staging);
    if (st != TVDB_OK) return st;
  }
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_buffer_download(tvdb_gpu_buffer_t* buf, void* dst, size_t size, tvdb_error_t* err) {
  if (!buf || !dst || size > buf->size) { tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid buffer_download arguments"); return TVDB_ERROR_INVALID_ARGUMENT; }
  if (buf->resident) buf->ctx->resident_metrics.download_bytes += size;
  if (buf->backend == TVDB_GPU_BACKEND_CUDA) {
    if (!tvdb_cuda_ok(buf->ctx, err, "cuMemcpyDtoH", buf->ctx->cuda.cuMemcpyDtoH(dst, buf->cu, size))) return err ? err->status : TVDB_ERROR_IO;
  } else if (buf->vk.mapped) {
    memcpy(dst, buf->vk.mapped, size);
  } else {
    // Device-local (e.g. exportable) buffer: stage through a host-visible buffer.
    tvdb_vk_buffer staging;
    tvdb_status_t st = tvdb_vk_create_buffer(buf->ctx, size, VK_BUFFER_USAGE_TRANSFER_DST_BIT, &staging, err);
    if (st != TVDB_OK) return st;
    tvdb_vk_copy copy = {0};
    copy.src=buf->vk.buffer; copy.dst=staging.buffer; copy.size=size;
    copy.src_stage=VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT|VK_PIPELINE_STAGE_TRANSFER_BIT;
    copy.src_access=VK_ACCESS_SHADER_WRITE_BIT|VK_ACCESS_TRANSFER_WRITE_BIT;
    copy.dst_stage=VK_PIPELINE_STAGE_HOST_BIT; copy.dst_access=VK_ACCESS_HOST_READ_BIT;
    st=tvdb_vk_run_copies(buf->ctx,&copy,1,err);
    if (st == TVDB_OK) memcpy(dst, staging.mapped, size);
    tvdb_vk_destroy_buffer(buf->ctx, &staging);
    if (st != TVDB_OK) return st;
  }
  return TVDB_OK;
}

size_t tvdb_gpu_buffer_size(const tvdb_gpu_buffer_t* buf) { return buf ? buf->size : 0; }

uint64_t tvdb_gpu_buffer_native_handle(const tvdb_gpu_buffer_t* buf) {
  if (!buf) return 0;
  if (buf->backend == TVDB_GPU_BACKEND_CUDA) return (uint64_t)buf->cu;
  return (uint64_t)(uintptr_t)buf->vk.buffer;
}

// ---- cross-API external-memory interop (Vulkan export -> CUDA import) --------
//
// On Linux with VK_KHR_external_memory{,_fd} and the CUDA driver's external-memory
// entry points present, a device-local Vulkan buffer can be shared with CUDA
// without a host round-trip: export the backing memory as an opaque POSIX fd, then
// import it into CUDA. Both contexts must reference the same physical GPU.

tvdb_status_t tvdb_gpu_context_device_uuid(const tvdb_gpu_context_t* ctx, uint8_t uuid[16],
                                           tvdb_error_t* err) {
  if (!ctx || !uuid) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid device_uuid arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (!ctx->has_device_uuid) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "device UUID is unavailable for this context");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  memcpy(uuid, ctx->device_uuid, 16);
  return TVDB_OK;
}

int tvdb_gpu_context_supports_external_memory(const tvdb_gpu_context_t* ctx) {
  if (!ctx) return 0;
  if (ctx->backend == TVDB_GPU_BACKEND_VULKAN)
    return ctx->supports_external_memory && ctx->vk.GetMemoryFdKHR ? 1 : 0;
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA)
    return (ctx->cuda.cuImportExternalMemory && ctx->cuda.cuExternalMemoryGetMappedBuffer) ? 1 : 0;
  return 0;
}

tvdb_status_t tvdb_gpu_buffer_create_exportable(tvdb_gpu_context_t* ctx, size_t size_bytes,
                                                tvdb_gpu_buffer_t** out, tvdb_error_t* err) {
  if (!ctx || !out || size_bytes == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid buffer_create_exportable arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  *out = NULL;
  if (ctx->backend != TVDB_GPU_BACKEND_VULKAN || !ctx->supports_external_memory || !ctx->vk.GetMemoryFdKHR) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "external-memory export requires a Vulkan context with VK_KHR_external_memory_fd");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  tvdb_gpu_buffer_t* b = (tvdb_gpu_buffer_t*)calloc(1, sizeof(*b));
  if (!b) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  b->ctx = ctx; b->backend = TVDB_GPU_BACKEND_VULKAN; b->size = size_bytes;

  VkExternalMemoryBufferCreateInfo emb;
  memset(&emb, 0, sizeof(emb));
  emb.sType = VK_STRUCTURE_TYPE_EXTERNAL_MEMORY_BUFFER_CREATE_INFO;
  emb.handleTypes = VK_EXTERNAL_MEMORY_HANDLE_TYPE_OPAQUE_FD_BIT;
  VkBufferCreateInfo bci;
  memset(&bci, 0, sizeof(bci));
  bci.sType = VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO;
  bci.pNext = &emb;
  bci.size = size_bytes;
  bci.usage = VK_BUFFER_USAGE_STORAGE_BUFFER_BIT | VK_BUFFER_USAGE_TRANSFER_SRC_BIT | VK_BUFFER_USAGE_TRANSFER_DST_BIT;
  bci.sharingMode = VK_SHARING_MODE_EXCLUSIVE;
  if (!tvdb_vk_ok(ctx->vk.CreateBuffer(ctx->device, &bci, NULL, &b->vk.buffer), err, "vkCreateBuffer")) { free(b); return err ? err->status : TVDB_ERROR_IO; }

  VkMemoryRequirements req;
  ctx->vk.GetBufferMemoryRequirements(ctx->device, b->vk.buffer, &req);
  uint32_t mt = tvdb_vk_find_memory_type(ctx, req.memoryTypeBits, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT);
  if (mt == UINT32_MAX) mt = tvdb_vk_find_memory_type(ctx, req.memoryTypeBits, 0);
  if (mt == UINT32_MAX) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "no suitable Vulkan memory type for exportable buffer");
    ctx->vk.DestroyBuffer(ctx->device, b->vk.buffer, NULL); free(b);
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  // Dedicated allocation keeps the export's offset at 0, which the CUDA import expects.
  VkMemoryDedicatedAllocateInfo ded;
  memset(&ded, 0, sizeof(ded));
  ded.sType = VK_STRUCTURE_TYPE_MEMORY_DEDICATED_ALLOCATE_INFO;
  ded.buffer = b->vk.buffer;
  VkExportMemoryAllocateInfo exp;
  memset(&exp, 0, sizeof(exp));
  exp.sType = VK_STRUCTURE_TYPE_EXPORT_MEMORY_ALLOCATE_INFO;
  exp.pNext = &ded;
  exp.handleTypes = VK_EXTERNAL_MEMORY_HANDLE_TYPE_OPAQUE_FD_BIT;
  VkMemoryAllocateInfo mai;
  memset(&mai, 0, sizeof(mai));
  mai.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
  mai.pNext = &exp;
  mai.allocationSize = req.size;
  mai.memoryTypeIndex = mt;
  if (!tvdb_vk_ok(ctx->vk.AllocateMemory(ctx->device, &mai, NULL, &b->vk.memory), err, "vkAllocateMemory")) {
    ctx->vk.DestroyBuffer(ctx->device, b->vk.buffer, NULL); free(b);
    return err ? err->status : TVDB_ERROR_IO;
  }
  if (!tvdb_vk_ok(ctx->vk.BindBufferMemory(ctx->device, b->vk.buffer, b->vk.memory, 0), err, "vkBindBufferMemory")) {
    tvdb_vk_destroy_buffer(ctx, &b->vk); free(b);
    return err ? err->status : TVDB_ERROR_IO;
  }
  b->vk.size = req.size;
  b->vk.mapped = NULL;  // device-local: not host-mapped (upload/download stage through a temp buffer)
  *out = b;
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_buffer_export(tvdb_gpu_buffer_t* buf, uint64_t* out_handle, tvdb_error_t* err) {
  if (!buf || !out_handle) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid buffer_export arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  *out_handle = 0;
  if (buf->backend != TVDB_GPU_BACKEND_VULKAN || !buf->ctx->vk.GetMemoryFdKHR || !buf->vk.memory) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "buffer is not exportable on this context");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  VkMemoryGetFdInfoKHR gfi;
  memset(&gfi, 0, sizeof(gfi));
  gfi.sType = VK_STRUCTURE_TYPE_MEMORY_GET_FD_INFO_KHR;
  gfi.memory = buf->vk.memory;
  gfi.handleType = VK_EXTERNAL_MEMORY_HANDLE_TYPE_OPAQUE_FD_BIT;
  int fd = -1;
  if (!tvdb_vk_ok(buf->ctx->vk.GetMemoryFdKHR(buf->ctx->device, &gfi, &fd), err, "vkGetMemoryFdKHR")) return err ? err->status : TVDB_ERROR_IO;
  if (fd < 0) { tvdb_gpu_set_error(err, TVDB_ERROR_IO, "vkGetMemoryFdKHR returned an invalid fd"); return TVDB_ERROR_IO; }
  // The fd is a freshly dup'd handle owned by the caller; CUDA import consumes it.
  *out_handle = (uint64_t)(unsigned int)fd;
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_buffer_import(tvdb_gpu_context_t* ctx, uint64_t handle, size_t size_bytes,
                                     tvdb_gpu_buffer_t** out, tvdb_error_t* err) {
  if (!ctx || !out || size_bytes == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid buffer_import arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  *out = NULL;
  // This call owns the fd: CUDA consumes it on success; on any failure here we
  // close it so the caller never has to track a half-imported handle.
  if (ctx->backend != TVDB_GPU_BACKEND_CUDA || !ctx->cuda.cuImportExternalMemory || !ctx->cuda.cuExternalMemoryGetMappedBuffer) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "external-memory import requires a CUDA context with external-memory support");
    tvdb_close_opaque_fd(handle);
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  tvdb_gpu_buffer_t* b = (tvdb_gpu_buffer_t*)calloc(1, sizeof(*b));
  if (!b) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); tvdb_close_opaque_fd(handle); return TVDB_ERROR_OUT_OF_MEMORY; }
  b->ctx = ctx; b->backend = TVDB_GPU_BACKEND_CUDA; b->size = size_bytes; b->imported = 1;

  CUDA_EXTERNAL_MEMORY_HANDLE_DESC hd;
  memset(&hd, 0, sizeof(hd));
  hd.type = CU_EXTERNAL_MEMORY_HANDLE_TYPE_OPAQUE_FD;
  hd.handle.fd = (int)(unsigned int)handle;
  hd.size = (unsigned long long)size_bytes;
  hd.flags = CUDA_EXTERNAL_MEMORY_DEDICATED;
  if (!tvdb_cuda_ok(ctx, err, "cuImportExternalMemory", ctx->cuda.cuImportExternalMemory(&b->ext_mem, &hd))) { tvdb_close_opaque_fd(handle); free(b); return err ? err->status : TVDB_ERROR_IO; }

  CUDA_EXTERNAL_MEMORY_BUFFER_DESC bd;
  memset(&bd, 0, sizeof(bd));
  bd.offset = 0;
  bd.size = (unsigned long long)size_bytes;
  if (!tvdb_cuda_ok(ctx, err, "cuExternalMemoryGetMappedBuffer", ctx->cuda.cuExternalMemoryGetMappedBuffer(&b->cu, b->ext_mem, &bd))) {
    if (ctx->cuda.cuDestroyExternalMemory) ctx->cuda.cuDestroyExternalMemory(b->ext_mem);
    free(b);
    return err ? err->status : TVDB_ERROR_IO;
  }
  *out = b;
  return TVDB_OK;
}

// ---- Gaussian-splat rasterizer (forward) ------------------------------------

#define TVDB_GPU_GAUSS_TILE 16

typedef struct { uint32_t gid; float depth; int32_t tx, ty; } tvdb_gauss_entry;
static int tvdb_gauss_entry_cmp(const void* a, const void* b) {
  const tvdb_gauss_entry* e = (const tvdb_gauss_entry*)a; const tvdb_gauss_entry* k = (const tvdb_gauss_entry*)b;
  if (e->tx != k->tx) return e->tx < k->tx ? -1 : 1;
  if (e->ty != k->ty) return e->ty < k->ty ? -1 : 1;
  if (e->depth != k->depth) return e->depth < k->depth ? -1 : 1;
  return 0;
}

tvdb_status_t tvdb_gpu_gaussian_rasterize_forward(tvdb_gpu_context_t* ctx,
    const tvdb_projected_gaussian_t* gaussians, uint32_t num_gaussians,
    uint32_t width, uint32_t height, uint32_t num_features,
    float background[3], float alpha_threshold, tvdb_raster_output_t* out, tvdb_error_t* err) {
  if (!ctx || !gaussians || !out || width == 0 || height == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid gaussian forward arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (num_features == 0) num_features = 3;
  if (num_features > 3) num_features = 3;
  if (alpha_threshold <= 0.0f) alpha_threshold = 0.005f;
  const uint32_t TS = TVDB_GPU_GAUSS_TILE;
  uint32_t ntx = (width + TS - 1) / TS, nty = (height + TS - 1) / TS;
  size_t npix = (size_t)width * height;

  memset(out, 0, sizeof(*out));
  out->width = width; out->height = height; out->num_features = num_features; out->owns_data = 1;
  out->image = (float*)calloc(npix * num_features, sizeof(float));
  out->alpha = (float*)calloc(npix, sizeof(float));
  out->last_ids = (int32_t*)malloc(npix * sizeof(int32_t));
  if (!out->image || !out->alpha || !out->last_ids) { tvdb_raster_output_destroy(out); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }

  // Build per-(gaussian,tile) entries and depth-sort (same order as the CPU).
  size_t max_entries = (size_t)num_gaussians * 16u + 1u;
  tvdb_gauss_entry* ent = (tvdb_gauss_entry*)malloc(max_entries * sizeof(tvdb_gauss_entry));
  if (!ent) { tvdb_raster_output_destroy(out); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  size_t ne = 0;
  for (uint32_t i = 0; i < num_gaussians; ++i) {
    if (gaussians[i].radius <= 0.0f || gaussians[i].opacity <= 0.0f) continue;
    int32_t cx = (int32_t)gaussians[i].x, cy = (int32_t)gaussians[i].y, r = (int32_t)(gaussians[i].radius + 0.5f);
    int32_t tx0 = cx/(int32_t)TS, ty0 = cy/(int32_t)TS, tx1 = (cx+r)/(int32_t)TS, ty1 = (cy+r)/(int32_t)TS;
    for (int32_t ty = ty0; ty <= ty1; ++ty) for (int32_t tx = tx0; tx <= tx1; ++tx) {
      if (tx < 0 || ty < 0 || (uint32_t)tx >= ntx || (uint32_t)ty >= nty) continue;
      if (ne >= max_entries) continue;
      ent[ne].gid = i; ent[ne].depth = gaussians[i].depth; ent[ne].tx = tx; ent[ne].ty = ty; ++ne;
    }
  }
  qsort(ent, ne, sizeof(tvdb_gauss_entry), tvdb_gauss_entry_cmp);

  float* gpack = (float*)malloc((size_t)num_gaussians * 12u * sizeof(float));
  int32_t* e4 = (int32_t*)malloc((ne ? ne : 1) * 4u * sizeof(int32_t));
  float* aux = (float*)malloc(npix * 2u * sizeof(float));
  if (!gpack || !e4 || !aux) { free(ent); free(gpack); free(e4); free(aux); tvdb_raster_output_destroy(out); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  for (uint32_t i = 0; i < num_gaussians; ++i) {
    const tvdb_projected_gaussian_t* g = &gaussians[i]; float* d = &gpack[i*12u];
    d[0]=g->x; d[1]=g->y; d[2]=g->conic_a; d[3]=g->conic_b; d[4]=g->conic_c; d[5]=g->opacity;
    d[6]=g->depth; d[7]=g->radius; d[8]=g->feature[0]; d[9]=g->feature[1]; d[10]=g->feature[2]; d[11]=0.0f;
  }
  for (size_t i = 0; i < ne; ++i) { e4[4*i+0]=(int32_t)ent[i].gid; e4[4*i+1]=ent[i].tx; e4[4*i+2]=ent[i].ty; e4[4*i+3]=0; }
  float bg0 = background ? background[0] : 0.0f, bg1 = background ? background[1] : 0.0f, bg2 = background ? background[2] : 0.0f;
  tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dg=0, de=0, dim=0, da=0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto gf_finish;
    if (!tvdb_cuda_ok(ctx, err, "f", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_gaussian_forward"))) { st=err?err->status:TVDB_ERROR_IO; goto gf_finish; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dg, gpack, (size_t)num_gaussians*12u*sizeof(float), err)) != TVDB_OK) goto gf_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &de, e4, (ne?ne:1)*4u*sizeof(int32_t), err)) != TVDB_OK) goto gf_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dim, NULL, npix*num_features*sizeof(float), err)) != TVDB_OK) goto gf_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &da, NULL, npix*2u*sizeof(float), err)) != TVDB_OK) goto gf_dev;
    unsigned int W=width, H=height, NF=num_features, uTS=TS, une=(unsigned int)ne, block=64;
    void* args[] = {&dg,&de,&dim,&da,&W,&H,&NF,&uTS,&une,&alpha_threshold,&bg0,&bg1,&bg2};
    if (!tvdb_cuda_ok(ctx, err, "k", ctx->cuda.cuLaunchKernel(fn,((unsigned int)npix+block-1u)/block,1,1,block,1,1,0,NULL,args,NULL))) { st=err?err->status:TVDB_ERROR_IO; goto gf_dev; }
    if (!tvdb_cuda_ok(ctx, err, "s", ctx->cuda.cuCtxSynchronize())) { st=err?err->status:TVDB_ERROR_IO; goto gf_dev; }
    if (!tvdb_cuda_ok(ctx, err, "c", ctx->cuda.cuMemcpyDtoH(out->image, dim, npix*num_features*sizeof(float)))) { st=err?err->status:TVDB_ERROR_IO; goto gf_dev; }
    if (!tvdb_cuda_ok(ctx, err, "c", ctx->cuda.cuMemcpyDtoH(aux, da, npix*2u*sizeof(float)))) { st=err?err->status:TVDB_ERROR_IO; goto gf_dev; }
    st = TVDB_OK;
gf_dev:
    if (da) ctx->cuda.cuMemFree(da); if (dim) ctx->cuda.cuMemFree(dim); if (de) ctx->cuda.cuMemFree(de); if (dg) ctx->cuda.cuMemFree(dg);
    goto gf_finish;
  }
  {
    tvdb_vk_buffer bg, be, bim, ba, bu;
    if ((st = tvdb_vk_create_buffer(ctx, (size_t)num_gaussians*12u*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bg, err)) != TVDB_OK) goto gf_finish;
    if ((st = tvdb_vk_create_buffer(ctx, (ne?ne:1)*4u*sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &be, err)) != TVDB_OK) goto gd_g;
    if ((st = tvdb_vk_create_buffer(ctx, npix*num_features*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bim, err)) != TVDB_OK) goto gd_e;
    if ((st = tvdb_vk_create_buffer(ctx, npix*2u*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &ba, err)) != TVDB_OK) goto gd_im;
    if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto gd_a;
    memcpy(bg.mapped, gpack, (size_t)num_gaussians*12u*sizeof(float));
    if (ne) memcpy(be.mapped, e4, ne*4u*sizeof(int32_t));
    struct { uint32_t dim[4]; uint32_t num_entries; float alpha_threshold; float pad[2]; float background[4]; } par;
    memset(&par, 0, sizeof(par));
    par.dim[0]=width; par.dim[1]=height; par.dim[2]=num_features; par.dim[3]=TS; par.num_entries=(uint32_t)ne; par.alpha_threshold=alpha_threshold;
    par.background[0]=bg0; par.background[1]=bg1; par.background[2]=bg2;
    memcpy(bu.mapped, &par, sizeof(par));
    tvdb_vk_dispatch_desc d;
    memset(&d, 0, sizeof(d));
    d.spv = kTvdbGpuGaussianForwardSpv; d.spv_len = kTvdbGpuGaussianForwardSpv_len; d.descriptor_count = 5;
    d.buffers[0]=&bg; d.buffers[1]=&be; d.buffers[2]=&bim; d.buffers[3]=&ba; d.buffers[4]=&bu;
    for (int i = 0; i < 4; ++i) d.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    d.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    d.group_x = (uint32_t)((npix + 63u) / 64u);
    st = tvdb_vk_dispatch(ctx, &d, err);
    if (st == TVDB_OK) { memcpy(out->image, bim.mapped, npix*num_features*sizeof(float)); memcpy(aux, ba.mapped, npix*2u*sizeof(float)); }
    tvdb_vk_destroy_buffer(ctx, &bu);
gd_a: tvdb_vk_destroy_buffer(ctx, &ba);
gd_im: tvdb_vk_destroy_buffer(ctx, &bim);
gd_e: tvdb_vk_destroy_buffer(ctx, &be);
gd_g: tvdb_vk_destroy_buffer(ctx, &bg);
  }
gf_finish:
  if (st == TVDB_OK) {
    for (size_t p = 0; p < npix; ++p) { out->alpha[p] = aux[2*p+0]; int32_t bits; memcpy(&bits, &aux[2*p+1], sizeof(int32_t)); out->last_ids[p] = bits; }
  } else tvdb_raster_output_destroy(out);
  free(ent); free(gpack); free(e4); free(aux);
  return st;
}

// ---- Gaussian-splat rasterizer (backward) -----------------------------------

// Build + depth-sort the per-(gaussian,tile) entry list (same order as forward).
static int32_t* tvdb_gauss_build_entries(const tvdb_projected_gaussian_t* g, uint32_t ng,
                                         uint32_t width, uint32_t height, size_t* out_ne) {
  const uint32_t TS = TVDB_GPU_GAUSS_TILE;
  uint32_t ntx = (width + TS - 1) / TS, nty = (height + TS - 1) / TS;
  size_t cap = (size_t)ng * 16u + 1u;
  tvdb_gauss_entry* ent = (tvdb_gauss_entry*)malloc(cap * sizeof(tvdb_gauss_entry));
  if (!ent) { *out_ne = 0; return NULL; }
  size_t ne = 0;
  for (uint32_t i = 0; i < ng; ++i) {
    if (g[i].radius <= 0.0f || g[i].opacity <= 0.0f) continue;
    int32_t cx = (int32_t)g[i].x, cy = (int32_t)g[i].y, r = (int32_t)(g[i].radius + 0.5f);
    int32_t tx0 = cx/(int32_t)TS, ty0 = cy/(int32_t)TS, tx1 = (cx+r)/(int32_t)TS, ty1 = (cy+r)/(int32_t)TS;
    for (int32_t ty = ty0; ty <= ty1; ++ty) for (int32_t tx = tx0; tx <= tx1; ++tx) {
      if (tx < 0 || ty < 0 || (uint32_t)tx >= ntx || (uint32_t)ty >= nty) continue;
      if (ne >= cap) continue;
      ent[ne].gid = i; ent[ne].depth = g[i].depth; ent[ne].tx = tx; ent[ne].ty = ty; ++ne;
    }
  }
  qsort(ent, ne, sizeof(tvdb_gauss_entry), tvdb_gauss_entry_cmp);
  int32_t* e4 = (int32_t*)malloc((ne ? ne : 1) * 4u * sizeof(int32_t));
  if (!e4) { free(ent); *out_ne = 0; return NULL; }
  for (size_t i = 0; i < ne; ++i) { e4[4*i+0]=(int32_t)ent[i].gid; e4[4*i+1]=ent[i].tx; e4[4*i+2]=ent[i].ty; e4[4*i+3]=0; }
  free(ent);
  *out_ne = ne;
  return e4;
}

tvdb_status_t tvdb_gpu_gaussian_rasterize_backward(tvdb_gpu_context_t* ctx,
    const tvdb_projected_gaussian_t* gaussians, uint32_t num_gaussians,
    const tvdb_raster_output_t* fwd, const float* dL_dC, const float* dL_dA,
    float background[3], float alpha_threshold, tvdb_gaussian_grad_t* grad_out, tvdb_error_t* err) {
  if (!ctx || !gaussians || !fwd || !dL_dC || !grad_out ||
      grad_out->num_gaussians != num_gaussians || grad_out->num_features != fwd->num_features) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid gaussian backward arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  uint32_t W = fwd->width, H = fwd->height, F = fwd->num_features;
  if (alpha_threshold <= 0.0f) alpha_threshold = 0.005f;
  const uint32_t TS = TVDB_GPU_GAUSS_TILE;
  size_t npix = (size_t)W * H;
  int has_dLdA = dL_dA ? 1 : 0;
  size_t gstride = 6u + F;

  size_t ne = 0;
  int32_t* e4 = tvdb_gauss_build_entries(gaussians, num_gaussians, W, H, &ne);
  if (!e4) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }

  float* gpack = (float*)malloc((size_t)num_gaussians * 12u * sizeof(float));
  float* pix = (float*)malloc(npix * (F + 2u) * sizeof(float));
  float* gradf = (float*)calloc((size_t)num_gaussians * gstride, sizeof(float));
  if (!gpack || !pix || !gradf) { free(e4); free(gpack); free(pix); free(gradf); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  for (uint32_t i = 0; i < num_gaussians; ++i) {
    const tvdb_projected_gaussian_t* g = &gaussians[i]; float* d = &gpack[i*12u];
    d[0]=g->x; d[1]=g->y; d[2]=g->conic_a; d[3]=g->conic_b; d[4]=g->conic_c; d[5]=g->opacity;
    d[6]=g->depth; d[7]=g->radius; d[8]=g->feature[0]; d[9]=g->feature[1]; d[10]=g->feature[2]; d[11]=0.0f;
  }
  for (size_t p = 0; p < npix; ++p) {
    float* d = &pix[p * (F + 2u)];
    for (uint32_t f = 0; f < F; ++f) d[f] = dL_dC[p * F + f];
    d[F] = fwd->alpha[p];
    d[F + 1u] = has_dLdA ? dL_dA[p] : 0.0f;
  }
  float bg0 = background ? background[0] : 0.0f, bg1 = background ? background[1] : 0.0f, bg2 = background ? background[2] : 0.0f;
  tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dg=0, de=0, dp=0, dgr=0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto gb_done;
    if (!tvdb_cuda_ok(ctx, err, "f", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_gaussian_backward"))) { st=err?err->status:TVDB_ERROR_IO; goto gb_done; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dg, gpack, (size_t)num_gaussians*12u*sizeof(float), err)) != TVDB_OK) goto gb_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &de, e4, (ne?ne:1)*4u*sizeof(int32_t), err)) != TVDB_OK) goto gb_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dp, pix, npix*(F+2u)*sizeof(float), err)) != TVDB_OK) goto gb_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dgr, gradf, (size_t)num_gaussians*gstride*sizeof(float), err)) != TVDB_OK) goto gb_dev;
    unsigned int uW=W,uH=H,uF=F,uTS=TS,une=(unsigned int)ne,block=64;
    void* args[] = {&dg,&de,&dp,&dgr,&uW,&uH,&uF,&uTS,&une,&alpha_threshold,&has_dLdA,&bg0,&bg1,&bg2};
    if (!tvdb_cuda_ok(ctx, err, "k", ctx->cuda.cuLaunchKernel(fn,((unsigned int)npix+block-1u)/block,1,1,block,1,1,0,NULL,args,NULL))) { st=err?err->status:TVDB_ERROR_IO; goto gb_dev; }
    if (!tvdb_cuda_ok(ctx, err, "s", ctx->cuda.cuCtxSynchronize())) { st=err?err->status:TVDB_ERROR_IO; goto gb_dev; }
    if (!tvdb_cuda_ok(ctx, err, "c", ctx->cuda.cuMemcpyDtoH(gradf, dgr, (size_t)num_gaussians*gstride*sizeof(float)))) { st=err?err->status:TVDB_ERROR_IO; goto gb_dev; }
    st = TVDB_OK;
gb_dev:
    if (dgr) ctx->cuda.cuMemFree(dgr); if (dp) ctx->cuda.cuMemFree(dp); if (de) ctx->cuda.cuMemFree(de); if (dg) ctx->cuda.cuMemFree(dg);
    goto gb_accum;
  }
  {
    tvdb_vk_buffer bg, be, bp, bgr, bu;
    if ((st = tvdb_vk_create_buffer(ctx, (size_t)num_gaussians*12u*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bg, err)) != TVDB_OK) goto gb_done;
    if ((st = tvdb_vk_create_buffer(ctx, (ne?ne:1)*4u*sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &be, err)) != TVDB_OK) goto gbd_g;
    if ((st = tvdb_vk_create_buffer(ctx, npix*(F+2u)*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bp, err)) != TVDB_OK) goto gbd_e;
    if ((st = tvdb_vk_create_buffer(ctx, (size_t)num_gaussians*gstride*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bgr, err)) != TVDB_OK) goto gbd_p;
    if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto gbd_gr;
    memcpy(bg.mapped, gpack, (size_t)num_gaussians*12u*sizeof(float));
    if (ne) memcpy(be.mapped, e4, ne*4u*sizeof(int32_t));
    memcpy(bp.mapped, pix, npix*(F+2u)*sizeof(float));
    memset(bgr.mapped, 0, (size_t)num_gaussians*gstride*sizeof(float));
    struct { uint32_t dim[4]; uint32_t num_entries; float alpha_threshold; uint32_t has_dLdA; uint32_t pad; float background[4]; } par;
    memset(&par, 0, sizeof(par));
    par.dim[0]=W; par.dim[1]=H; par.dim[2]=F; par.dim[3]=TS; par.num_entries=(uint32_t)ne; par.alpha_threshold=alpha_threshold; par.has_dLdA=(uint32_t)has_dLdA;
    par.background[0]=bg0; par.background[1]=bg1; par.background[2]=bg2;
    memcpy(bu.mapped, &par, sizeof(par));
    tvdb_vk_dispatch_desc d;
    memset(&d, 0, sizeof(d));
    d.spv = kTvdbGpuGaussianBackwardSpv; d.spv_len = kTvdbGpuGaussianBackwardSpv_len; d.descriptor_count = 5;
    d.buffers[0]=&bg; d.buffers[1]=&be; d.buffers[2]=&bp; d.buffers[3]=&bgr; d.buffers[4]=&bu;
    for (int i = 0; i < 4; ++i) d.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    d.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    d.group_x = (uint32_t)((npix + 63u) / 64u);
    st = tvdb_vk_dispatch(ctx, &d, err);
    if (st == TVDB_OK) memcpy(gradf, bgr.mapped, (size_t)num_gaussians*gstride*sizeof(float));
    tvdb_vk_destroy_buffer(ctx, &bu);
gbd_gr: tvdb_vk_destroy_buffer(ctx, &bgr);
gbd_p: tvdb_vk_destroy_buffer(ctx, &bp);
gbd_e: tvdb_vk_destroy_buffer(ctx, &be);
gbd_g: tvdb_vk_destroy_buffer(ctx, &bg);
  }
gb_accum:
  if (st == TVDB_OK) {
    for (uint32_t i = 0; i < num_gaussians; ++i) {
      const float* d = &gradf[(size_t)i * gstride];
      grad_out->grad_x[i] += d[0]; grad_out->grad_y[i] += d[1];
      grad_out->grad_conic_a[i] += d[2]; grad_out->grad_conic_b[i] += d[3]; grad_out->grad_conic_c[i] += d[4];
      grad_out->grad_opacity[i] += d[5];
      for (uint32_t f = 0; f < F; ++f) grad_out->grad_feature[(size_t)i * F + f] += d[6 + f];
    }
  }
gb_done:
  free(e4); free(gpack); free(pix); free(gradf);
  return st;
}

// ---- SSIM (Gaussian-splat training helper) ----------------------------------

tvdb_status_t tvdb_gpu_ssim(tvdb_gpu_context_t* ctx, const float* img_a, const float* img_b,
                            uint32_t width, uint32_t height, uint32_t channels, float data_range,
                            float* out_mean, float* out_map, tvdb_error_t* err) {
  if (!ctx || !img_a || !img_b || !out_mean || width == 0 || height == 0 || channels == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid ssim arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (data_range <= 0.0f) data_range = 1.0f;
  const int R = 5;            // 11x11 window
  const int win_n = 2*R + 1;
  size_t nwin = (size_t)win_n * win_n;
  size_t npix = (size_t)width * height, nimg = npix * channels;
  float c1 = (0.01f*data_range)*(0.01f*data_range), c2 = (0.03f*data_range)*(0.03f*data_range);

  // Normalized Gaussian window (sigma 1.5), matching the standard SSIM kernel.
  float* win = (float*)malloc(nwin * sizeof(float));
  float* map = (float*)malloc(npix * sizeof(float));
  if (!win || !map) { free(win); free(map); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  {
    float sigma = 1.5f, sum = 0.0f;
    for (int dy = -R; dy <= R; ++dy) for (int dx = -R; dx <= R; ++dx) {
      float v = expf(-(float)(dx*dx + dy*dy) / (2.0f*sigma*sigma));
      win[(dy+R)*win_n + (dx+R)] = v; sum += v;
    }
    for (size_t i = 0; i < nwin; ++i) win[i] /= sum;
  }
  tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr da=0, db=0, dw=0, dm=0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto ss_host;
    if (!tvdb_cuda_ok(ctx, err, "f", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_ssim"))) { st=err?err->status:TVDB_ERROR_IO; goto ss_host; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &da, img_a, nimg*sizeof(float), err)) != TVDB_OK) goto ss_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &db, img_b, nimg*sizeof(float), err)) != TVDB_OK) goto ss_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dw, win, nwin*sizeof(float), err)) != TVDB_OK) goto ss_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dm, NULL, npix*sizeof(float), err)) != TVDB_OK) goto ss_dev;
    int W=(int)width, H=(int)height, C=(int)channels;
    void* args[] = {&da,&db,&dw,&dm,&W,&H,&C,(void*)&R,&c1,&c2};
    unsigned int block=64;
    if (!tvdb_cuda_ok(ctx, err, "k", ctx->cuda.cuLaunchKernel(fn,((unsigned int)npix+block-1u)/block,1,1,block,1,1,0,NULL,args,NULL))) { st=err?err->status:TVDB_ERROR_IO; goto ss_dev; }
    if (!tvdb_cuda_ok(ctx, err, "s", ctx->cuda.cuCtxSynchronize())) { st=err?err->status:TVDB_ERROR_IO; goto ss_dev; }
    if (!tvdb_cuda_ok(ctx, err, "c", ctx->cuda.cuMemcpyDtoH(map, dm, npix*sizeof(float)))) { st=err?err->status:TVDB_ERROR_IO; goto ss_dev; }
    st = TVDB_OK;
ss_dev:
    if (dm) ctx->cuda.cuMemFree(dm); if (dw) ctx->cuda.cuMemFree(dw); if (db) ctx->cuda.cuMemFree(db); if (da) ctx->cuda.cuMemFree(da);
    goto ss_finish;
  }
  {
    tvdb_vk_buffer ba, bb, bw, bm, bu;
    if ((st = tvdb_vk_create_buffer(ctx, nimg*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &ba, err)) != TVDB_OK) goto ss_host;
    if ((st = tvdb_vk_create_buffer(ctx, nimg*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bb, err)) != TVDB_OK) goto sd_a;
    if ((st = tvdb_vk_create_buffer(ctx, nwin*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bw, err)) != TVDB_OK) goto sd_b;
    if ((st = tvdb_vk_create_buffer(ctx, npix*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bm, err)) != TVDB_OK) goto sd_w;
    if ((st = tvdb_vk_create_buffer(ctx, 32, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto sd_m;
    memcpy(ba.mapped, img_a, nimg*sizeof(float)); memcpy(bb.mapped, img_b, nimg*sizeof(float)); memcpy(bw.mapped, win, nwin*sizeof(float));
    struct { uint32_t dim[4]; float c1; float c2; uint32_t pad[2]; } par;
    memset(&par, 0, sizeof(par));
    par.dim[0]=width; par.dim[1]=height; par.dim[2]=channels; par.dim[3]=(uint32_t)R; par.c1=c1; par.c2=c2;
    memcpy(bu.mapped, &par, sizeof(par));
    tvdb_vk_dispatch_desc d;
    memset(&d, 0, sizeof(d));
    d.spv = kTvdbGpuSsimSpv; d.spv_len = kTvdbGpuSsimSpv_len; d.descriptor_count = 5;
    d.buffers[0]=&ba; d.buffers[1]=&bb; d.buffers[2]=&bw; d.buffers[3]=&bm; d.buffers[4]=&bu;
    for (int i = 0; i < 4; ++i) d.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    d.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    d.group_x = (uint32_t)((npix + 63u) / 64u);
    st = tvdb_vk_dispatch(ctx, &d, err);
    if (st == TVDB_OK) memcpy(map, bm.mapped, npix*sizeof(float));
    tvdb_vk_destroy_buffer(ctx, &bu);
sd_m: tvdb_vk_destroy_buffer(ctx, &bm);
sd_w: tvdb_vk_destroy_buffer(ctx, &bw);
sd_b: tvdb_vk_destroy_buffer(ctx, &bb);
sd_a: tvdb_vk_destroy_buffer(ctx, &ba);
  }
ss_finish:
  if (st == TVDB_OK) {
    double sum = 0.0; for (size_t p = 0; p < npix; ++p) sum += map[p];
    *out_mean = (float)(sum / (double)npix);
    if (out_map) memcpy(out_map, map, npix*sizeof(float));
  }
ss_host:
  free(win); free(map);
  return st;
}

// ---- batched sparse conv (GridBatch / JaggedTensor demo) --------------------

static tvdb_status_t tvdb_gpu_sparse_conv3d_batched_impl(tvdb_gpu_context_t* ctx,
    const tvdb_sparse_grid* in, size_t n_grids, const float* kernel, int kx, int ky, int kz,
    float pad_value, tvdb_sparse_grid* out, tvdb_error_t* err) {
  if (!ctx || !in || !kernel || !out || n_grids == 0 || kx <= 0 || ky <= 0 || kz <= 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid batched conv arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  // Jagged concatenation: total voxels + per-grid [offset,offset+count).
  size_t total = 0;
  for (size_t g = 0; g < n_grids; ++g) total += in[g].count;
  for (size_t g = 0; g < n_grids; ++g) {
    out[g].count = 0; out[g].voxel_size = in[g].voxel_size; out[g].ox = in[g].ox; out[g].oy = in[g].oy; out[g].oz = in[g].oz;
  }
  if (total == 0) return TVDB_OK;
  size_t kn = (size_t)kx*ky*kz;

  int32_t* in4 = (int32_t*)malloc(total * 4u * sizeof(int32_t));
  int32_t* range = (int32_t*)malloc(total * 2u * sizeof(int32_t));
  float* outval = (float*)malloc(total * sizeof(float));
  if (!in4 || !range || !outval) { free(in4); free(range); free(outval); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  size_t w = 0;
  for (size_t g = 0; g < n_grids; ++g) {
    int lo = (int)w, hi = (int)(w + in[g].count);
    for (size_t k = 0; k < in[g].count; ++k) {
      in4[4*w+0]=in[g].coords[k].x; in4[4*w+1]=in[g].coords[k].y; in4[4*w+2]=in[g].coords[k].z;
      memcpy(&in4[4*w+3], &in[g].values[k], sizeof(float));
      range[2*w+0]=lo; range[2*w+1]=hi; ++w;
    }
  }
  tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr di=0, dr=0, dk=0, dov=0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto bc_host;
    if (!tvdb_cuda_ok(ctx, err, "f", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_sparse_conv_batched"))) { st=err?err->status:TVDB_ERROR_IO; goto bc_host; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &di, in4, total*4u*sizeof(int32_t), err)) != TVDB_OK) goto bc_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dr, range, total*2u*sizeof(int32_t), err)) != TVDB_OK) goto bc_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dk, kernel, kn*sizeof(float), err)) != TVDB_OK) goto bc_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dov, NULL, total*sizeof(float), err)) != TVDB_OK) goto bc_dev;
    unsigned int utot=(unsigned int)total, block=128;
    void* args[] = {&di,&dr,&dk,&dov,&utot,&kx,&ky,&kz,&pad_value};
    if (!tvdb_cuda_ok(ctx, err, "k", ctx->cuda.cuLaunchKernel(fn,(utot+block-1u)/block,1,1,block,1,1,0,NULL,args,NULL))) { st=err?err->status:TVDB_ERROR_IO; goto bc_dev; }
    if (!tvdb_cuda_ok(ctx, err, "s", ctx->cuda.cuCtxSynchronize())) { st=err?err->status:TVDB_ERROR_IO; goto bc_dev; }
    if (!tvdb_cuda_ok(ctx, err, "c", ctx->cuda.cuMemcpyDtoH(outval, dov, total*sizeof(float)))) { st=err?err->status:TVDB_ERROR_IO; goto bc_dev; }
    st = TVDB_OK;
bc_dev:
    if (dov) ctx->cuda.cuMemFree(dov); if (dk) ctx->cuda.cuMemFree(dk); if (dr) ctx->cuda.cuMemFree(dr); if (di) ctx->cuda.cuMemFree(di);
    goto bc_build;
  }
  {
    tvdb_vk_buffer bi, br, bk, bov, bu;
    if ((st = tvdb_vk_create_buffer(ctx, total*4u*sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bi, err)) != TVDB_OK) goto bc_host;
    if ((st = tvdb_vk_create_buffer(ctx, total*2u*sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &br, err)) != TVDB_OK) goto bd_i;
    if ((st = tvdb_vk_create_buffer(ctx, kn*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bk, err)) != TVDB_OK) goto bd_r;
    if ((st = tvdb_vk_create_buffer(ctx, total*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bov, err)) != TVDB_OK) goto bd_k;
    if ((st = tvdb_vk_create_buffer(ctx, 32, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto bd_ov;
    memcpy(bi.mapped, in4, total*4u*sizeof(int32_t)); memcpy(br.mapped, range, total*2u*sizeof(int32_t)); memcpy(bk.mapped, kernel, kn*sizeof(float));
    struct { int32_t kdim[4]; uint32_t total; float pad_value; uint32_t pad[2]; } par;
    memset(&par, 0, sizeof(par));
    par.kdim[0]=kx; par.kdim[1]=ky; par.kdim[2]=kz; par.total=(uint32_t)total; par.pad_value=pad_value;
    memcpy(bu.mapped, &par, sizeof(par));
    tvdb_vk_dispatch_desc d;
    memset(&d, 0, sizeof(d));
    d.spv = kTvdbGpuSparseConvBatchedSpv; d.spv_len = kTvdbGpuSparseConvBatchedSpv_len; d.descriptor_count = 5;
    d.buffers[0]=&bi; d.buffers[1]=&br; d.buffers[2]=&bk; d.buffers[3]=&bov; d.buffers[4]=&bu;
    for (int i = 0; i < 4; ++i) d.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    d.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    d.group_x = (uint32_t)((total + 127u) / 128u);
    st = tvdb_vk_dispatch(ctx, &d, err);
    if (st == TVDB_OK) memcpy(outval, bov.mapped, total*sizeof(float));
    tvdb_vk_destroy_buffer(ctx, &bu);
bd_ov: tvdb_vk_destroy_buffer(ctx, &bov);
bd_k: tvdb_vk_destroy_buffer(ctx, &bk);
bd_r: tvdb_vk_destroy_buffer(ctx, &br);
bd_i: tvdb_vk_destroy_buffer(ctx, &bi);
  }
bc_build:
  if (st == TVDB_OK) {
    size_t off = 0;
    for (size_t g = 0; g < n_grids; ++g) {
      if (!tvdb_sparse_grid_reserve(&out[g], in[g].count ? in[g].count : 1)) { st = TVDB_ERROR_OUT_OF_MEMORY; tvdb_gpu_set_error(err, st, "OOM"); break; }
      for (size_t k = 0; k < in[g].count; ++k) { out[g].coords[k] = in[g].coords[k]; out[g].values[k] = outval[off + k]; }
      out[g].count = in[g].count; off += in[g].count;
    }
  }
bc_host:
  free(in4); free(range); free(outval);
  return st;
}

// ---- multi-context (multi-GPU) scheduling -----------------------------------

tvdb_status_t tvdb_gpu_multi_sparse_conv3d_batched(tvdb_gpu_context_t* const* ctxs, size_t n_ctx,
    const tvdb_sparse_grid* in, size_t n_grids, const float* kernel, int kx, int ky, int kz,
    float pad_value, tvdb_sparse_grid* out, tvdb_error_t* err) {
  if (!ctxs || n_ctx == 0 || !in || !kernel || !out || n_grids == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid multi-batched conv arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  // Partition the batch into contiguous per-context chunks (proportional split).
  for (size_t c = 0; c < n_ctx; ++c) {
    if (!ctxs[c]) { tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "null context in multi-batched conv"); return TVDB_ERROR_INVALID_ARGUMENT; }
    size_t start = (n_grids * c) / n_ctx;
    size_t end = (n_grids * (c + 1)) / n_ctx;
    if (end <= start) continue;
    tvdb_status_t st = tvdb_gpu_sparse_conv3d_batched(ctxs[c], &in[start], end - start,
                                                      kernel, kx, ky, kz, pad_value, &out[start], err);
    if (st != TVDB_OK) return st;
  }
  return TVDB_OK;
}

static bool tvdb_gpu_sparse_input_valid(const tvdb_sparse_grid* in) {
  return in && in->count<=INT_MAX && (!in->count || (in->coords && in->values)) &&
    isfinite(in->voxel_size) && in->voxel_size>0 &&
    isfinite(in->ox) && isfinite(in->oy) && isfinite(in->oz);
}
static bool tvdb_gpu_sparse_output_valid(const tvdb_sparse_grid* in,const tvdb_sparse_grid* out) {
  size_t ic,iv,oc,ov;
  if(!out || out->count>out->capacity ||
      (out->capacity ? (!out->coords || !out->values) : (out->coords || out->values))) return false;
  if(in==out) return true;
  if(!tvdb_size_mul(in->count,sizeof(tvdb_vec3i),&ic) || !tvdb_size_mul(in->count,sizeof(float),&iv) ||
      !tvdb_size_mul(out->capacity,sizeof(tvdb_vec3i),&oc) || !tvdb_size_mul(out->capacity,sizeof(float),&ov)) return false;
  return !tvdb_buffers_overlap(in->coords,ic,out->coords,oc) && !tvdb_buffers_overlap(in->values,iv,out->values,ov) &&
    !tvdb_buffers_overlap(in->coords,ic,out->values,ov) && !tvdb_buffers_overlap(in->values,iv,out->coords,oc);
}

tvdb_status_t tvdb_gpu_sparse_conv3d(tvdb_gpu_context_t* ctx,const tvdb_sparse_grid* in,
 const float* kernel,int kx,int ky,int kz,float pad_value,tvdb_sparse_grid* out,tvdb_error_t* err) {
  if(!ctx || !tvdb_gpu_sparse_input_valid(in) || !tvdb_gpu_sparse_output_valid(in,out)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid sparse input/output"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  size_t kb;
  if(!kernel || !tvdb_grid_bytes(kx,ky,kz,sizeof(float),&kb) || kb/sizeof(float)>INT_MAX) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"kernel size overflow"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_sparse_grid tmp; tvdb_sparse_grid_init(&tmp);
  tvdb_status_t st=resident_sparse_host(ctx,in,kernel,kx,ky,kz,1,0,1,pad_value,&tmp,err);
  if(st==TVDB_OK) { tvdb_sparse_grid_free(out); *out=tmp; } else tvdb_sparse_grid_free(&tmp);
  return st;
}

tvdb_status_t tvdb_gpu_sparse_conv3d_strided(tvdb_gpu_context_t* ctx,const tvdb_sparse_grid* in,
 const float* kernel,int kx,int ky,int kz,int stride,float pad_value,tvdb_sparse_grid* out,tvdb_error_t* err) {
  if(!ctx || !tvdb_gpu_sparse_input_valid(in) || !tvdb_gpu_sparse_output_valid(in,out)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid sparse input/output"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  size_t kb;
  if(!kernel || !tvdb_grid_bytes(kx,ky,kz,sizeof(float),&kb) || kb/sizeof(float)>INT_MAX) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"kernel size overflow"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_sparse_grid tmp; tvdb_sparse_grid_init(&tmp);
  tvdb_status_t st=resident_sparse_host(ctx,in,kernel,kx,ky,kz,stride,1,1,pad_value,&tmp,err);
  if(st==TVDB_OK) { tvdb_sparse_grid_free(out); *out=tmp; } else tvdb_sparse_grid_free(&tmp);
  return st;
}

tvdb_status_t tvdb_gpu_sparse_conv3d_transpose(tvdb_gpu_context_t* ctx,const tvdb_sparse_grid* in,
 const float* kernel,int kx,int ky,int kz,int stride,tvdb_sparse_grid* out,tvdb_error_t* err) {
  if(!ctx || !tvdb_gpu_sparse_input_valid(in) || !tvdb_gpu_sparse_output_valid(in,out)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid sparse input/output"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  size_t kb;
  if(!kernel || !tvdb_grid_bytes(kx,ky,kz,sizeof(float),&kb) || kb/sizeof(float)>INT_MAX) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"kernel size overflow"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_sparse_grid tmp; tvdb_sparse_grid_init(&tmp);
  tvdb_error_t local_error={0};
  tvdb_status_t st=resident_sparse_host(ctx,in,kernel,kx,ky,kz,stride,2,1,0,&tmp,&local_error);
  /* Keep the legacy clipping contract at signed-coordinate boundaries. */
  if(st==TVDB_ERROR_INVALID_ARGUMENT && !strcmp(local_error.message,"sparse output coordinate overflow"))
    st=tvdb_gpu_sparse_conv3d_transpose_impl(ctx,in,kernel,kx,ky,kz,stride,&tmp,&local_error);
  if(err)*err=local_error;
  if(st==TVDB_OK) { tvdb_sparse_grid_free(out); *out=tmp; } else tvdb_sparse_grid_free(&tmp);
  return st;
}

tvdb_status_t tvdb_gpu_dilate_sparse(tvdb_gpu_context_t* ctx,const tvdb_sparse_grid* in,
 float background,int iterations,tvdb_sparse_grid* out,tvdb_error_t* err) {
  if(!ctx || !tvdb_gpu_sparse_input_valid(in) || !tvdb_gpu_sparse_output_valid(in,out)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid sparse input/output"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_sparse_grid tmp; tvdb_sparse_grid_init(&tmp);
  tvdb_status_t st=resident_sparse_host(ctx,in,NULL,1,1,1,1,3,iterations,background,&tmp,err);
  if(st==TVDB_OK) { tvdb_sparse_grid_free(out); *out=tmp; } else tvdb_sparse_grid_free(&tmp);
  return st;
}

tvdb_status_t tvdb_gpu_erode_sparse(tvdb_gpu_context_t* ctx,const tvdb_sparse_grid* in,
 int iterations,tvdb_sparse_grid* out,tvdb_error_t* err) {
  if(!ctx || !tvdb_gpu_sparse_input_valid(in) || !tvdb_gpu_sparse_output_valid(in,out)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid sparse input/output"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_sparse_grid tmp; tvdb_sparse_grid_init(&tmp);
  tvdb_status_t st=resident_sparse_host(ctx,in,NULL,1,1,1,1,4,iterations,0,&tmp,err);
  if(st==TVDB_OK) { tvdb_sparse_grid_free(out); *out=tmp; } else tvdb_sparse_grid_free(&tmp);
  return st;
}

tvdb_status_t tvdb_gpu_stencil_scalar_scalar(tvdb_gpu_context_t* ctx,const tvdb_dense_grid* in, int op,tvdb_dense_grid* out,tvdb_error_t* err) {
  size_t bytes;
  if(!ctx || !in || !out || !tvdb_gpu_shape_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,1*sizeof(float)) ||
      !tvdb_grid_bytes(in->nx,in->ny,in->nz,1*sizeof(float),&bytes)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid stencil grid"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_dense_grid tmp={0};
  tvdb_dense_grid view={0};view.nx=in->nx;view.ny=in->ny;view.nz=in->nz;
  view.ox=in->ox;view.oy=in->oy;view.oz=in->oz;view.voxel_size=in->voxel_size;view.data=in->data;
  tmp.nx=in->nx;tmp.ny=in->ny;tmp.nz=in->nz;tmp.ox=in->ox;tmp.oy=in->oy;tmp.oz=in->oz;tmp.voxel_size=in->voxel_size;
  tvdb_status_t st=resident_stencil_host(ctx,&view,1,1,op,&tmp.data,err);
  if(st!=TVDB_OK) { free(tmp.data); return st; }
  if ((const void*)in==(const void*)out) {
    memcpy(out->data,tmp.data,bytes); free(tmp.data);
  } else *out=tmp;
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_stencil_scalar_d(tvdb_gpu_context_t* ctx,const tvdb_dense_grid_d* in, int op,tvdb_dense_grid_d* out,tvdb_error_t* err) {
  size_t bytes;
  if(!ctx || !in || !out || !tvdb_gpu_shape_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,1*sizeof(double)) ||
      !tvdb_grid_bytes(in->nx,in->ny,in->nz,1*sizeof(double),&bytes)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid stencil grid"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_dense_grid_d tmp={0};
  tvdb_status_t st=resident_double_host(ctx,in,NULL,op,&tmp,err);
  if(st!=TVDB_OK) { free(tmp.data); return st; }
  if ((const void*)in==(const void*)out) {
    memcpy(out->data,tmp.data,bytes); free(tmp.data);
  } else *out=tmp;
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_gradient(tvdb_gpu_context_t* ctx,const tvdb_dense_grid* in,tvdb_dense_vec_grid* out,tvdb_error_t* err) {
  size_t bytes;
  if(!ctx || !in || !out || !tvdb_gpu_shape_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,1*sizeof(float)) ||
      !tvdb_grid_bytes(in->nx,in->ny,in->nz,3*sizeof(float),&bytes)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid stencil grid"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_dense_vec_grid tmp={0};
  tvdb_dense_grid view={0};view.nx=in->nx;view.ny=in->ny;view.nz=in->nz;
  view.ox=in->ox;view.oy=in->oy;view.oz=in->oz;view.voxel_size=in->voxel_size;view.data=in->data;
  tmp.nx=in->nx;tmp.ny=in->ny;tmp.nz=in->nz;tmp.ox=in->ox;tmp.oy=in->oy;tmp.oz=in->oz;tmp.voxel_size=in->voxel_size;
  tvdb_status_t st=resident_stencil_host(ctx,&view,1,3,0,&tmp.data,err);
  if(st!=TVDB_OK) { free(tmp.data); return st; }
  if ((const void*)in==(const void*)out) {
    memcpy(out->data,tmp.data,bytes); free(tmp.data);
  } else *out=tmp;
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_divergence(tvdb_gpu_context_t* ctx,const tvdb_dense_vec_grid* in,tvdb_dense_grid* out,tvdb_error_t* err) {
  size_t bytes;
  if(!ctx || !in || !out || !tvdb_gpu_shape_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,3*sizeof(float)) ||
      !tvdb_grid_bytes(in->nx,in->ny,in->nz,1*sizeof(float),&bytes)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid stencil grid"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_dense_grid tmp={0};
  tvdb_dense_grid view={0};view.nx=in->nx;view.ny=in->ny;view.nz=in->nz;
  view.ox=in->ox;view.oy=in->oy;view.oz=in->oz;view.voxel_size=in->voxel_size;view.data=in->data;
  tmp.nx=in->nx;tmp.ny=in->ny;tmp.nz=in->nz;tmp.ox=in->ox;tmp.oy=in->oy;tmp.oz=in->oz;tmp.voxel_size=in->voxel_size;
  tvdb_status_t st=resident_stencil_host(ctx,&view,3,1,0,&tmp.data,err);
  if(st!=TVDB_OK) { free(tmp.data); return st; }
  if ((const void*)in==(const void*)out) {
    memcpy(out->data,tmp.data,bytes); free(tmp.data);
  } else *out=tmp;
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_curl(tvdb_gpu_context_t* ctx,const tvdb_dense_vec_grid* in,tvdb_dense_vec_grid* out,tvdb_error_t* err) {
  size_t bytes;
  if(!ctx || !in || !out || !tvdb_gpu_shape_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,3*sizeof(float)) ||
      !tvdb_grid_bytes(in->nx,in->ny,in->nz,3*sizeof(float),&bytes)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid stencil grid"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_dense_vec_grid tmp={0};
  tvdb_dense_grid view={0};view.nx=in->nx;view.ny=in->ny;view.nz=in->nz;
  view.ox=in->ox;view.oy=in->oy;view.oz=in->oz;view.voxel_size=in->voxel_size;view.data=in->data;
  tmp.nx=in->nx;tmp.ny=in->ny;tmp.nz=in->nz;tmp.ox=in->ox;tmp.oy=in->oy;tmp.oz=in->oz;tmp.voxel_size=in->voxel_size;
  tvdb_status_t st=resident_stencil_host(ctx,&view,3,3,0,&tmp.data,err);
  if(st!=TVDB_OK) { free(tmp.data); return st; }
  if ((const void*)in==(const void*)out) {
    memcpy(out->data,tmp.data,bytes); free(tmp.data);
  } else *out=tmp;
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_normalize_vec(tvdb_gpu_context_t* ctx,const tvdb_dense_vec_grid* in,tvdb_dense_vec_grid* out,tvdb_error_t* err) {
  size_t bytes;
  if(!ctx || !in || !out || !tvdb_gpu_shape_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,3*sizeof(float)) ||
      !tvdb_grid_bytes(in->nx,in->ny,in->nz,3*sizeof(float),&bytes)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid stencil grid"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_dense_vec_grid tmp={0};
  tvdb_dense_grid view={0};view.nx=in->nx;view.ny=in->ny;view.nz=in->nz;
  view.ox=in->ox;view.oy=in->oy;view.oz=in->oz;view.voxel_size=in->voxel_size;view.data=in->data;
  tmp.nx=in->nx;tmp.ny=in->ny;tmp.nz=in->nz;tmp.ox=in->ox;tmp.oy=in->oy;tmp.oz=in->oz;tmp.voxel_size=in->voxel_size;
  tvdb_status_t st=resident_stencil_host(ctx,&view,3,3,1,&tmp.data,err);
  if(st!=TVDB_OK) { free(tmp.data); return st; }
  if ((const void*)in==(const void*)out) {
    memcpy(out->data,tmp.data,bytes); free(tmp.data);
  } else *out=tmp;
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_magnitude(tvdb_gpu_context_t* ctx,const tvdb_dense_vec_grid* in,tvdb_dense_grid* out,tvdb_error_t* err) {
  size_t bytes;
  if(!ctx || !in || !out || !tvdb_gpu_shape_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,3*sizeof(float)) ||
      !tvdb_grid_bytes(in->nx,in->ny,in->nz,1*sizeof(float),&bytes)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid stencil grid"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_dense_grid tmp={0};
  tvdb_dense_grid view={0};view.nx=in->nx;view.ny=in->ny;view.nz=in->nz;
  view.ox=in->ox;view.oy=in->oy;view.oz=in->oz;view.voxel_size=in->voxel_size;view.data=in->data;
  tmp.nx=in->nx;tmp.ny=in->ny;tmp.nz=in->nz;tmp.ox=in->ox;tmp.oy=in->oy;tmp.oz=in->oz;tmp.voxel_size=in->voxel_size;
  tvdb_status_t st=resident_stencil_host(ctx,&view,3,1,1,&tmp.data,err);
  if(st!=TVDB_OK) { free(tmp.data); return st; }
  if ((const void*)in==(const void*)out) {
    memcpy(out->data,tmp.data,bytes); free(tmp.data);
  } else *out=tmp;
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_cpt(tvdb_gpu_context_t* ctx,const tvdb_dense_grid* in,tvdb_dense_vec_grid* out,tvdb_error_t* err) {
  size_t bytes;
  if(!ctx || !in || !out || !tvdb_gpu_shape_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,1*sizeof(float)) ||
      !tvdb_grid_bytes(in->nx,in->ny,in->nz,3*sizeof(float),&bytes)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid stencil grid"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_dense_vec_grid tmp={0};
  tvdb_dense_grid view={0};view.nx=in->nx;view.ny=in->ny;view.nz=in->nz;
  view.ox=in->ox;view.oy=in->oy;view.oz=in->oz;view.voxel_size=in->voxel_size;view.data=in->data;
  tmp.nx=in->nx;tmp.ny=in->ny;tmp.nz=in->nz;tmp.ox=in->ox;tmp.oy=in->oy;tmp.oz=in->oz;tmp.voxel_size=in->voxel_size;
  tvdb_status_t st=resident_stencil_host(ctx,&view,1,3,1,&tmp.data,err);
  if(st!=TVDB_OK) { free(tmp.data); return st; }
  if ((const void*)in==(const void*)out) {
    memcpy(out->data,tmp.data,bytes); free(tmp.data);
  } else *out=tmp;
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_solve_poisson_ex(tvdb_gpu_context_t* ctx,const tvdb_dense_grid* rhs,tvdb_dense_grid* x,
 int max_iters,float tolerance,tvdb_poisson_result_t* result,tvdb_error_t* err) {
  if(result) memset(result,0,sizeof(*result));
  if(!ctx || !rhs || !x || !tvdb_gpu_shape_valid(rhs->nx,rhs->ny,rhs->nz,rhs->voxel_size,rhs->data,sizeof(float)) ||
      rhs->nx!=x->nx || rhs->ny!=x->ny || rhs->nz!=x->nz || rhs->voxel_size!=x->voxel_size) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid Poisson grid"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if(false && !tvdb_gpu_supports_fp64(ctx)) { tvdb_gpu_set_error(err,TVDB_ERROR_UNIMPLEMENTED,"device lacks fp64"); return TVDB_ERROR_UNIMPLEMENTED; }
  if(ctx->backend==TVDB_GPU_BACKEND_VULKAN && !tvdb_gpu_spirv_available()) {
    tvdb_gpu_set_error(err,TVDB_ERROR_UNIMPLEMENTED,"Poisson SPIR-V unavailable"); return TVDB_ERROR_UNIMPLEMENTED;
  }
  if(tvdb_gpu_supports_fp64(ctx)) {
    tvdb_gpu_grid_desc_t d={rhs->nx,rhs->ny,rhs->nz,1,TVDB_GPU_F32,rhs->ox,rhs->oy,rhs->oz,rhs->voxel_size};
    return resident_poisson_host(ctx,rhs->data,x->data,&d,0,max_iters,tolerance,result,err);
  }
  tvdb_gpu_poisson_workspace workspace; memset(&workspace,0,sizeof(workspace)); workspace.ctx=ctx;
  tvdb_status_t st=tvdb_poisson_solve_core(rhs->data,x->data,rhs->nx,rhs->ny,rhs->nz,rhs->voxel_size,
    false,false,max_iters,tolerance,false,result,err,tvdb_gpu_poisson_apply,&workspace);
  tvdb_gpu_poisson_release(&workspace); return st;
}
int tvdb_gpu_solve_poisson(tvdb_gpu_context_t* ctx,const tvdb_dense_grid* rhs,tvdb_dense_grid* x,
 int max_iters,float tolerance,tvdb_error_t* err) {
  tvdb_poisson_result_t result;
  return tvdb_gpu_solve_poisson_ex(ctx,rhs,x,max_iters,tolerance,&result,err)==TVDB_OK ? result.iterations : 0;
}

tvdb_status_t tvdb_gpu_solve_poisson_d_ex(tvdb_gpu_context_t* ctx,const tvdb_dense_grid* rhs,tvdb_dense_grid* x,
 int max_iters,double tolerance,tvdb_poisson_result_t* result,tvdb_error_t* err) {
  if(result) memset(result,0,sizeof(*result));
  if(!ctx || !rhs || !x || !tvdb_gpu_shape_valid(rhs->nx,rhs->ny,rhs->nz,rhs->voxel_size,rhs->data,sizeof(float)) ||
      rhs->nx!=x->nx || rhs->ny!=x->ny || rhs->nz!=x->nz || rhs->voxel_size!=x->voxel_size) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid Poisson grid"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if(true && !tvdb_gpu_supports_fp64(ctx)) { tvdb_gpu_set_error(err,TVDB_ERROR_UNIMPLEMENTED,"device lacks fp64"); return TVDB_ERROR_UNIMPLEMENTED; }
  if(ctx->backend==TVDB_GPU_BACKEND_VULKAN && !tvdb_gpu_spirv_available()) {
    tvdb_gpu_set_error(err,TVDB_ERROR_UNIMPLEMENTED,"Poisson SPIR-V unavailable"); return TVDB_ERROR_UNIMPLEMENTED;
  }
  if(tvdb_gpu_supports_fp64(ctx)) {
    tvdb_gpu_grid_desc_t d={rhs->nx,rhs->ny,rhs->nz,1,TVDB_GPU_F32,rhs->ox,rhs->oy,rhs->oz,rhs->voxel_size};
    return resident_poisson_host(ctx,rhs->data,x->data,&d,1,max_iters,tolerance,result,err);
  }
  tvdb_gpu_poisson_workspace workspace; memset(&workspace,0,sizeof(workspace)); workspace.ctx=ctx;
  tvdb_status_t st=tvdb_poisson_solve_core(rhs->data,x->data,rhs->nx,rhs->ny,rhs->nz,rhs->voxel_size,
    false,true,max_iters,tolerance,false,result,err,tvdb_gpu_poisson_apply,&workspace);
  tvdb_gpu_poisson_release(&workspace); return st;
}
int tvdb_gpu_solve_poisson_d(tvdb_gpu_context_t* ctx,const tvdb_dense_grid* rhs,tvdb_dense_grid* x,
 int max_iters,double tolerance,tvdb_error_t* err) {
  tvdb_poisson_result_t result;
  return tvdb_gpu_solve_poisson_d_ex(ctx,rhs,x,max_iters,tolerance,&result,err)==TVDB_OK ? result.iterations : 0;
}

tvdb_status_t tvdb_gpu_solve_poisson_dd_ex(tvdb_gpu_context_t* ctx,const tvdb_dense_grid_d* rhs,tvdb_dense_grid_d* x,
 int max_iters,double tolerance,tvdb_poisson_result_t* result,tvdb_error_t* err) {
  if(result) memset(result,0,sizeof(*result));
  if(!ctx || !rhs || !x || !tvdb_gpu_shape_valid(rhs->nx,rhs->ny,rhs->nz,rhs->voxel_size,rhs->data,sizeof(double)) ||
      rhs->nx!=x->nx || rhs->ny!=x->ny || rhs->nz!=x->nz || rhs->voxel_size!=x->voxel_size) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid Poisson grid"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if(true && !tvdb_gpu_supports_fp64(ctx)) { tvdb_gpu_set_error(err,TVDB_ERROR_UNIMPLEMENTED,"device lacks fp64"); return TVDB_ERROR_UNIMPLEMENTED; }
  if(ctx->backend==TVDB_GPU_BACKEND_VULKAN && !tvdb_gpu_spirv_available()) {
    tvdb_gpu_set_error(err,TVDB_ERROR_UNIMPLEMENTED,"Poisson SPIR-V unavailable"); return TVDB_ERROR_UNIMPLEMENTED;
  }
  if(tvdb_gpu_supports_fp64(ctx)) {
    tvdb_gpu_grid_desc_t d={rhs->nx,rhs->ny,rhs->nz,1,TVDB_GPU_F64,rhs->ox,rhs->oy,rhs->oz,rhs->voxel_size};
    return resident_poisson_host(ctx,rhs->data,x->data,&d,2,max_iters,tolerance,result,err);
  }
  tvdb_gpu_poisson_workspace workspace; memset(&workspace,0,sizeof(workspace)); workspace.ctx=ctx;
  tvdb_status_t st=tvdb_poisson_solve_core(rhs->data,x->data,rhs->nx,rhs->ny,rhs->nz,rhs->voxel_size,
    true,true,max_iters,tolerance,true,result,err,tvdb_gpu_poisson_apply,&workspace);
  tvdb_gpu_poisson_release(&workspace); return st;
}
int tvdb_gpu_solve_poisson_dd(tvdb_gpu_context_t* ctx,const tvdb_dense_grid_d* rhs,tvdb_dense_grid_d* x,
 int max_iters,double tolerance,tvdb_error_t* err) {
  tvdb_poisson_result_t result;
  return tvdb_gpu_solve_poisson_dd_ex(ctx,rhs,x,max_iters,tolerance,&result,err)==TVDB_OK ? result.iterations : 0;
}

tvdb_status_t tvdb_gpu_advect(tvdb_gpu_context_t* ctx,const tvdb_dense_grid* field,
 const tvdb_dense_vec_grid* velocity,float dt,int scheme,int clamp,tvdb_dense_grid* out,tvdb_error_t* err) {
  size_t bytes;
  if(!ctx || !field || !velocity || !out || !out->data || !isfinite(dt) ||
      !tvdb_gpu_shape_valid(field->nx,field->ny,field->nz,field->voxel_size,field->data,sizeof(float)) ||
      !tvdb_gpu_shape_valid(velocity->nx,velocity->ny,velocity->nz,velocity->voxel_size,velocity->data,3*sizeof(float)) ||
      field->nx!=velocity->nx || field->ny!=velocity->ny || field->nz!=velocity->nz ||
      field->nx!=out->nx || field->ny!=out->ny || field->nz!=out->nz ||
      scheme<TVDB_ADVECT_RK1 || scheme>TVDB_ADVECT_BFECC ||
      !tvdb_grid_bytes(out->nx,out->ny,out->nz,sizeof(float),&bytes)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid advection input/output"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_dense_grid tmp=*out; tmp.data=(float*)malloc(bytes);
  if(!tmp.data) { tvdb_gpu_set_error(err,TVDB_ERROR_OUT_OF_MEMORY,"advection scratch"); return TVDB_ERROR_OUT_OF_MEMORY; }
  tvdb_status_t st=resident_advect_host(ctx,field,velocity,dt,scheme,clamp,&tmp,err);
  if(st==TVDB_OK) memcpy(out->data,tmp.data,bytes);
  free(tmp.data); return st;
}

tvdb_status_t tvdb_gpu_csg_dense(tvdb_gpu_context_t* ctx,const tvdb_dense_grid* a,const tvdb_dense_grid* b,
 int op,tvdb_dense_grid* out,tvdb_error_t* err) {
  if(!ctx || !a || !b || !out || !tvdb_dense_same_shape(a,b,out) || op<0 || op>2 ||
      !tvdb_gpu_shape_valid(a->nx,a->ny,a->nz,a->voxel_size,a->data,sizeof(float)) ||
      !tvdb_gpu_shape_valid(b->nx,b->ny,b->nz,b->voxel_size,b->data,sizeof(float)) ||
      a->nx!=b->nx || a->ny!=b->ny || a->nz!=b->nz) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid CSG grids"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  size_t bytes; tvdb_grid_bytes(a->nx,a->ny,a->nz,sizeof(float),&bytes);
  tvdb_dense_grid tmp=*out; tmp.data=malloc(bytes);
  if(!tmp.data) { tvdb_gpu_set_error(err,TVDB_ERROR_OUT_OF_MEMORY,"CSG scratch allocation failed"); return TVDB_ERROR_OUT_OF_MEMORY; }
  tvdb_status_t st=resident_binary_host(ctx,a,b,op,1,&tmp,err);
  if(st!=TVDB_OK) { free(tmp.data); return st; }
  memcpy(out->data,tmp.data,bytes); free(tmp.data);
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_csg_dense_d(tvdb_gpu_context_t* ctx,const tvdb_dense_grid_d* a,const tvdb_dense_grid_d* b,
 int op,tvdb_dense_grid_d* out,tvdb_error_t* err) {
  if(!ctx || !a || !b || !out || op<0 || op>2 ||
      !tvdb_gpu_shape_valid(a->nx,a->ny,a->nz,a->voxel_size,a->data,sizeof(double)) ||
      !tvdb_gpu_shape_valid(b->nx,b->ny,b->nz,b->voxel_size,b->data,sizeof(double)) ||
      a->nx!=b->nx || a->ny!=b->ny || a->nz!=b->nz) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid CSG grids"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_dense_grid_d tmp={0};
  tvdb_status_t st=resident_double_host(ctx,a,b,op,&tmp,err);
  if(st!=TVDB_OK) { free(tmp.data); return st; }
  if(out==a || out==b) { size_t bytes; tvdb_grid_bytes(a->nx,a->ny,a->nz,sizeof(double),&bytes); memcpy(out->data,tmp.data,bytes); free(tmp.data); }
  else *out=tmp;
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_sparse_conv3d_batched(tvdb_gpu_context_t* ctx,
 const tvdb_sparse_grid* in,size_t n_grids,const float* kernel,int kx,int ky,int kz,
 float pad_value,tvdb_sparse_grid* out,tvdb_error_t* err) {
  size_t bytes,kbytes,total=0;
  if(!ctx || !in || !out || !kernel || !n_grids ||
     !tvdb_size_mul(n_grids,sizeof(tvdb_sparse_grid),&bytes) ||
     !tvdb_grid_bytes(kx,ky,kz,sizeof(float),&kbytes) || kbytes/sizeof(float)>INT_MAX) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid sparse batch"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  for(size_t i=0;i<n_grids;++i) {
    if(!tvdb_gpu_sparse_input_valid(&in[i]) || !tvdb_gpu_sparse_output_valid(&in[i],&out[i]) || in[i].count>(size_t)INT_MAX-total) {
      tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid sparse batch grid/count"); return TVDB_ERROR_INVALID_ARGUMENT;
    }
    total+=in[i].count;
    for(size_t j=0;j<i;++j) {
      size_t ic=in[i].count*sizeof(tvdb_vec3i),iv=in[i].count*sizeof(float);
      size_t jc=out[j].capacity*sizeof(tvdb_vec3i),jv=out[j].capacity*sizeof(float);
      size_t oc=out[i].capacity*sizeof(tvdb_vec3i),ov=out[i].capacity*sizeof(float);
      if(tvdb_buffers_overlap(in[i].coords,ic,out[j].coords,jc) || tvdb_buffers_overlap(in[i].values,iv,out[j].values,jv) ||
         tvdb_buffers_overlap(out[i].coords,oc,out[j].coords,jc) || tvdb_buffers_overlap(out[i].values,ov,out[j].values,jv)) {
        tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"overlapping sparse batch grids"); return TVDB_ERROR_INVALID_ARGUMENT;
      }
    }
  }
  tvdb_sparse_grid* tmp=calloc(n_grids,sizeof(*tmp));
  if(!tmp) { tvdb_gpu_set_error(err,TVDB_ERROR_OUT_OF_MEMORY,"batch staging allocation failed"); return TVDB_ERROR_OUT_OF_MEMORY; }
  tvdb_status_t st=tvdb_gpu_sparse_conv3d_batched_impl(ctx,in,n_grids,kernel,kx,ky,kz,pad_value,tmp,err);
  for(size_t i=0;i<n_grids;++i) {
    if(st==TVDB_OK) { tvdb_sparse_grid_free(&out[i]); out[i]=tmp[i]; }
    else tvdb_sparse_grid_free(&tmp[i]);
  }
  free(tmp); return st;
}

tvdb_status_t tvdb_gpu_advect_semi_lagrangian(tvdb_gpu_context_t* ctx,const tvdb_dense_grid* field,
 const tvdb_dense_vec_grid* velocity,float dt,tvdb_dense_grid* out,tvdb_error_t* err) {
  size_t bytes;
  if(!ctx || !field || !velocity || !out || !out->data || !isfinite(dt) ||
      !tvdb_gpu_shape_valid(field->nx,field->ny,field->nz,field->voxel_size,field->data,sizeof(float)) ||
      !tvdb_gpu_shape_valid(velocity->nx,velocity->ny,velocity->nz,velocity->voxel_size,velocity->data,3*sizeof(float)) ||
      field->nx!=velocity->nx || field->ny!=velocity->ny || field->nz!=velocity->nz ||
      field->nx!=out->nx || field->ny!=out->ny || field->nz!=out->nz ||
      !tvdb_grid_bytes(out->nx,out->ny,out->nz,sizeof(float),&bytes)) {
    tvdb_gpu_set_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid advection input/output"); return TVDB_ERROR_INVALID_ARGUMENT;
  }
  tvdb_dense_grid tmp=*out; tmp.data=(float*)malloc(bytes);
  if(!tmp.data) { tvdb_gpu_set_error(err,TVDB_ERROR_OUT_OF_MEMORY,"advection scratch"); return TVDB_ERROR_OUT_OF_MEMORY; }
  tvdb_status_t st=resident_advect_host(ctx,field,velocity,dt,-1,0,&tmp,err);
  if(st==TVDB_OK) memcpy(out->data,tmp.data,bytes);
  free(tmp.data); return st;
}

#include "tinyvdb_gpu_resident.inl"
