#include "tinyvdb_gpu.h"

#include <math.h>
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
#include "tinyvdb_gpu_mesh_to_sdf_spv.inc"
#include "tinyvdb_gpu_marching_cubes_spv.inc"
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
#define VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO 33
#define VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO 34
#define VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET 35
#define VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO 39
#define VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO 40
#define VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO 42
#define VK_STRUCTURE_TYPE_IMAGE_MEMORY_BARRIER 44
#define VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO 100
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
#define VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT 0x00000001u
#define VK_MEMORY_PROPERTY_HOST_COHERENT_BIT 0x00000002u
#define VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT 0x00000004u
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
#define VK_FILTER_LINEAR 1
#define VK_SAMPLER_MIPMAP_MODE_NEAREST 0
#define VK_SAMPLER_ADDRESS_MODE_CLAMP_TO_EDGE 2
#define VK_BORDER_COLOR_FLOAT_TRANSPARENT_BLACK 0
#define VK_ACCESS_TRANSFER_WRITE_BIT 0x00001000u
#define VK_ACCESS_SHADER_READ_BIT 0x00000020u
#define VK_PIPELINE_STAGE_TOP_OF_PIPE_BIT 0x00000001u
#define VK_PIPELINE_STAGE_TRANSFER_BIT 0x00001000u
#define VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT 0x00000800u
#define VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT 0x00000001u
#define VK_SPARSE_MEMORY_BIND_METADATA_BIT 0x00000001u
#define VK_SHADER_STAGE_COMPUTE_BIT 0x00000020u
#define VK_PIPELINE_BIND_POINT_COMPUTE 1
#define VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT 0x00000002u
#define VK_COMMAND_BUFFER_LEVEL_PRIMARY 0

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
typedef struct { VkFlags queueFlags; uint32_t queueCount; uint32_t timestampValidBits; uint64_t minImageTransferGranularity[3]; } VkQueueFamilyProperties;
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
typedef struct { int32_t x; int32_t y; int32_t z; } VkOffset3D;
typedef struct { uint32_t aspectMask; uint32_t mipLevel; uint32_t arrayLayer; } VkImageSubresource;
typedef struct { uint32_t aspectMask; uint32_t mipLevel; uint32_t baseArrayLayer; uint32_t layerCount; } VkImageSubresourceLayers;
typedef struct { uint32_t aspectMask; uint32_t baseMipLevel; uint32_t levelCount; uint32_t baseArrayLayer; uint32_t layerCount; } VkImageSubresourceRange;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; uint32_t imageType; uint32_t format; VkExtent3D extent; uint32_t mipLevels; uint32_t arrayLayers; uint32_t samples; uint32_t tiling; VkFlags usage; uint32_t sharingMode; uint32_t queueFamilyIndexCount; const uint32_t* pQueueFamilyIndices; uint32_t initialLayout; } VkImageCreateInfo;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; VkImage image; uint32_t viewType; uint32_t format; uint32_t components[4]; VkImageSubresourceRange subresourceRange; } VkImageViewCreateInfo;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; uint32_t magFilter; uint32_t minFilter; uint32_t mipmapMode; uint32_t addressModeU; uint32_t addressModeV; uint32_t addressModeW; float mipLodBias; VkBool32 anisotropyEnable; float maxAnisotropy; VkBool32 compareEnable; uint32_t compareOp; float minLod; float maxLod; uint32_t borderColor; VkBool32 unnormalizedCoordinates; } VkSamplerCreateInfo;
typedef struct { uint32_t sType; const void* pNext; VkFlags srcAccessMask; VkFlags dstAccessMask; uint32_t oldLayout; uint32_t newLayout; uint32_t srcQueueFamilyIndex; uint32_t dstQueueFamilyIndex; VkImage image; VkImageSubresourceRange subresourceRange; } VkImageMemoryBarrier;
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
typedef void (*PFN_vkCmdPipelineBarrier)(VkCommandBuffer, VkFlags, VkFlags, VkFlags, uint32_t, const void*, uint32_t, const void*, uint32_t, const VkImageMemoryBarrier*);
typedef void (*PFN_vkCmdCopyBufferToImage)(VkCommandBuffer, VkBuffer, VkImage, uint32_t, uint32_t, const VkBufferImageCopy*);
typedef void (*PFN_vkCmdCopyBuffer)(VkCommandBuffer, VkBuffer, VkBuffer, uint32_t, const VkBufferCopy*);
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

struct tvdb_gpu_context {
  tvdb_gpu_backend_t backend;
  tvdb_vk_table vk;
  VkInstance instance;
  VkPhysicalDevice physical_device;
  VkDevice device;
  VkQueue queue;
  uint32_t queue_family;
  VkPhysicalDeviceMemoryProperties memory_props;
  int supports_sparse_3d_images;
  int supports_sparse_aliased;   // sparseResidencyAliased: legal sparse memory aliasing
  int supports_external_memory;
  char device_name[128];
  tvdb_cuda_table cuda;
  CUcontext cu_ctx;
  CUdevice cu_device;
  CUmodule cu_module;
};
struct tvdb_gpu_buffer { tvdb_vk_buffer vk; tvdb_gpu_context_t* ctx; tvdb_gpu_backend_t backend; CUdeviceptr cu; size_t size;
                         CUexternalMemory ext_mem; int imported; };
struct tvdb_gpu_dense_grid { tvdb_gpu_buffer_t values; int nx, ny, nz; };
struct tvdb_gpu_sparse_grid { tvdb_gpu_buffer_t coords; tvdb_gpu_buffer_t values; size_t count; };
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
  TVDB_LOAD_DEV(ctx, AllocateDescriptorSets); TVDB_LOAD_DEV(ctx, UpdateDescriptorSets);
  TVDB_LOAD_DEV(ctx, CreateShaderModule); TVDB_LOAD_DEV(ctx, DestroyShaderModule);
  TVDB_LOAD_DEV(ctx, CreatePipelineLayout); TVDB_LOAD_DEV(ctx, DestroyPipelineLayout);
  TVDB_LOAD_DEV(ctx, CreateComputePipelines); TVDB_LOAD_DEV(ctx, DestroyPipeline);
  TVDB_LOAD_DEV(ctx, CreateCommandPool); TVDB_LOAD_DEV(ctx, DestroyCommandPool);
  TVDB_LOAD_DEV(ctx, AllocateCommandBuffers); TVDB_LOAD_DEV(ctx, BeginCommandBuffer);
  TVDB_LOAD_DEV(ctx, EndCommandBuffer); TVDB_LOAD_DEV(ctx, ResetCommandBuffer);
  TVDB_LOAD_DEV(ctx, CmdBindPipeline); TVDB_LOAD_DEV(ctx, CmdBindDescriptorSets);
  TVDB_LOAD_DEV(ctx, CmdDispatch); TVDB_LOAD_DEV(ctx, CmdPipelineBarrier);
  TVDB_LOAD_DEV(ctx, CmdCopyBufferToImage); TVDB_LOAD_DEV(ctx, CmdCopyBuffer); TVDB_LOAD_DEV(ctx, CreateFence);
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
  if (!tvdb_vk_ok(ctx->vk.CreateBuffer(ctx->device, &bci, NULL, &out->buffer), err, "vkCreateBuffer")) return err ? err->status : TVDB_ERROR_IO;
  VkMemoryRequirements req;
  ctx->vk.GetBufferMemoryRequirements(ctx->device, out->buffer, &req);
  uint32_t mt = tvdb_vk_find_memory_type(ctx, req.memoryTypeBits, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT);
  if (mt == UINT32_MAX) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "no host-visible coherent Vulkan memory type");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  VkMemoryAllocateInfo mai;
  memset(&mai, 0, sizeof(mai));
  mai.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
  mai.allocationSize = req.size;
  mai.memoryTypeIndex = mt;
  if (!tvdb_vk_ok(ctx->vk.AllocateMemory(ctx->device, &mai, NULL, &out->memory), err, "vkAllocateMemory")) return err ? err->status : TVDB_ERROR_IO;
  if (!tvdb_vk_ok(ctx->vk.BindBufferMemory(ctx->device, out->buffer, out->memory, 0), err, "vkBindBufferMemory")) return err ? err->status : TVDB_ERROR_IO;
  if (!tvdb_vk_ok(ctx->vk.MapMemory(ctx->device, out->memory, 0, size ? size : 4, 0, &out->mapped), err, "vkMapMemory")) return err ? err->status : TVDB_ERROR_IO;
  out->size = size ? size : 4;
  return TVDB_OK;
}

static void tvdb_vk_destroy_buffer(tvdb_gpu_context_t* ctx, tvdb_vk_buffer* buf) {
  if (!ctx || !ctx->device || !buf) return;
  if (buf->mapped) ctx->vk.UnmapMemory(ctx->device, buf->memory);
  if (buf->buffer) ctx->vk.DestroyBuffer(ctx->device, buf->buffer, NULL);
  if (buf->memory) ctx->vk.FreeMemory(ctx->device, buf->memory, NULL);
  memset(buf, 0, sizeof(*buf));
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
  const tvdb_vk_buffer* buffers[6];
  const tvdb_vk_image3d* images[6];
  uint32_t descriptor_types[6];
  uint32_t group_x;
} tvdb_vk_dispatch_desc;

static tvdb_status_t tvdb_vk_dispatch(tvdb_gpu_context_t* ctx, const tvdb_vk_dispatch_desc* d, tvdb_error_t* err) {
  if (!d->spv || d->spv_len == 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_UNIMPLEMENTED, "Vulkan SPIR-V blobs are unavailable; rebuild with glslangValidator or use generated include");
    return TVDB_ERROR_UNIMPLEMENTED;
  }
  VkDescriptorSetLayoutBinding bindings[6];
  memset(bindings, 0, sizeof(bindings));
  for (uint32_t i = 0; i < d->descriptor_count; ++i) {
    bindings[i].binding = i;
    bindings[i].descriptorCount = 1;
    bindings[i].descriptorType = d->descriptor_types[i];
    bindings[i].stageFlags = VK_SHADER_STAGE_COMPUTE_BIT;
  }
  VkDescriptorSetLayoutCreateInfo dlci;
  memset(&dlci, 0, sizeof(dlci));
  dlci.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO;
  dlci.bindingCount = d->descriptor_count;
  dlci.pBindings = bindings;
  VkDescriptorSetLayout layout = VK_NULL_HANDLE;
  if (!tvdb_vk_ok(ctx->vk.CreateDescriptorSetLayout(ctx->device, &dlci, NULL, &layout), err, "vkCreateDescriptorSetLayout")) return err ? err->status : TVDB_ERROR_IO;

  VkDescriptorPoolSize pool_sizes[3];
  memset(pool_sizes, 0, sizeof(pool_sizes));
  uint32_t storage_count = 0, uniform_count = 0, image_count = 0;
  for (uint32_t i = 0; i < d->descriptor_count; ++i) {
    if (d->descriptor_types[i] == VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER) ++uniform_count;
    else if (d->descriptor_types[i] == VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER) ++image_count;
    else ++storage_count;
  }
  pool_sizes[0].type = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER; pool_sizes[0].descriptorCount = storage_count;
  pool_sizes[1].type = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER; pool_sizes[1].descriptorCount = uniform_count;
  pool_sizes[2].type = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER; pool_sizes[2].descriptorCount = image_count;
  VkDescriptorPoolCreateInfo dpci;
  memset(&dpci, 0, sizeof(dpci));
  dpci.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO;
  dpci.maxSets = 1;
  dpci.poolSizeCount = image_count ? 3 : (uniform_count ? 2 : 1);
  dpci.pPoolSizes = pool_sizes;
  VkDescriptorPool pool = VK_NULL_HANDLE;
  if (!tvdb_vk_ok(ctx->vk.CreateDescriptorPool(ctx->device, &dpci, NULL, &pool), err, "vkCreateDescriptorPool")) goto fail_layout;
  VkDescriptorSetAllocateInfo dsai;
  memset(&dsai, 0, sizeof(dsai));
  dsai.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
  dsai.descriptorPool = pool;
  dsai.descriptorSetCount = 1;
  dsai.pSetLayouts = &layout;
  VkDescriptorSet set = VK_NULL_HANDLE;
  if (!tvdb_vk_ok(ctx->vk.AllocateDescriptorSets(ctx->device, &dsai, &set), err, "vkAllocateDescriptorSets")) goto fail_pool;

  VkDescriptorBufferInfo infos[6];
  VkDescriptorImageInfo image_infos[6];
  VkWriteDescriptorSet writes[6];
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

  VkShaderModule shader = VK_NULL_HANDLE;
  VkShaderModuleCreateInfo smci;
  memset(&smci, 0, sizeof(smci));
  smci.sType = VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO;
  smci.codeSize = d->spv_len;
  smci.pCode = (const uint32_t*)d->spv;
  if (!tvdb_vk_ok(ctx->vk.CreateShaderModule(ctx->device, &smci, NULL, &shader), err, "vkCreateShaderModule")) goto fail_pool;

  VkPipelineLayout pipeline_layout = VK_NULL_HANDLE;
  VkPipelineLayoutCreateInfo plci;
  memset(&plci, 0, sizeof(plci));
  plci.sType = VK_STRUCTURE_TYPE_PIPELINE_LAYOUT_CREATE_INFO;
  plci.setLayoutCount = 1;
  plci.pSetLayouts = &layout;
  if (!tvdb_vk_ok(ctx->vk.CreatePipelineLayout(ctx->device, &plci, NULL, &pipeline_layout), err, "vkCreatePipelineLayout")) goto fail_shader;

  VkPipeline pipeline = VK_NULL_HANDLE;
  VkComputePipelineCreateInfo cpci;
  memset(&cpci, 0, sizeof(cpci));
  cpci.sType = VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO;
  cpci.stage.sType = VK_STRUCTURE_TYPE_PIPELINE_SHADER_STAGE_CREATE_INFO;
  cpci.stage.stage = VK_SHADER_STAGE_COMPUTE_BIT;
  cpci.stage.module = shader;
  cpci.stage.pName = "main";
  cpci.layout = pipeline_layout;
  if (!tvdb_vk_ok(ctx->vk.CreateComputePipelines(ctx->device, VK_NULL_HANDLE, 1, &cpci, NULL, &pipeline), err, "vkCreateComputePipelines")) goto fail_pl;

  VkCommandPool cmd_pool = VK_NULL_HANDLE;
  VkCommandPoolCreateInfo cp;
  memset(&cp, 0, sizeof(cp));
  cp.sType = VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO;
  cp.flags = VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT;
  cp.queueFamilyIndex = ctx->queue_family;
  if (!tvdb_vk_ok(ctx->vk.CreateCommandPool(ctx->device, &cp, NULL, &cmd_pool), err, "vkCreateCommandPool")) goto fail_pipe;
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
  ctx->vk.CmdBindDescriptorSets(cmd, VK_PIPELINE_BIND_POINT_COMPUTE, pipeline_layout, 0, 1, &set, 0, NULL);
  ctx->vk.CmdDispatch(cmd, d->group_x, 1, 1);
  if (!tvdb_vk_ok(ctx->vk.EndCommandBuffer(cmd), err, "vkEndCommandBuffer")) goto fail_fence;
  VkSubmitInfo si;
  memset(&si, 0, sizeof(si));
  si.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
  si.commandBufferCount = 1;
  si.pCommandBuffers = &cmd;
  if (!tvdb_vk_ok(ctx->vk.QueueSubmit(ctx->queue, 1, &si, fence), err, "vkQueueSubmit")) goto fail_fence;
  if (!tvdb_vk_ok(ctx->vk.WaitForFences(ctx->device, 1, &fence, VK_TRUE, UINT64_MAX), err, "vkWaitForFences")) goto fail_fence;

  ctx->vk.DestroyFence(ctx->device, fence, NULL);
  ctx->vk.DestroyCommandPool(ctx->device, cmd_pool, NULL);
  ctx->vk.DestroyPipeline(ctx->device, pipeline, NULL);
  ctx->vk.DestroyPipelineLayout(ctx->device, pipeline_layout, NULL);
  ctx->vk.DestroyShaderModule(ctx->device, shader, NULL);
  ctx->vk.DestroyDescriptorPool(ctx->device, pool, NULL);
  ctx->vk.DestroyDescriptorSetLayout(ctx->device, layout, NULL);
  return TVDB_OK;

fail_fence:
  if (fence) ctx->vk.DestroyFence(ctx->device, fence, NULL);
fail_cmdpool:
  if (cmd_pool) ctx->vk.DestroyCommandPool(ctx->device, cmd_pool, NULL);
fail_pipe:
  if (pipeline) ctx->vk.DestroyPipeline(ctx->device, pipeline, NULL);
fail_pl:
  if (pipeline_layout) ctx->vk.DestroyPipelineLayout(ctx->device, pipeline_layout, NULL);
fail_shader:
  if (shader) ctx->vk.DestroyShaderModule(ctx->device, shader, NULL);
fail_pool:
  if (pool) ctx->vk.DestroyDescriptorPool(ctx->device, pool, NULL);
fail_layout:
  if (layout) ctx->vk.DestroyDescriptorSetLayout(ctx->device, layout, NULL);
  return err ? err->status : TVDB_ERROR_IO;
}

static const char* kTvdbCudaSource =
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
"__device__ float tvdb_sparse_lookup(const tvdb_int4* coords, const float* values, unsigned int count, int x, int y, int z, float pad_value) {\n"
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
"        acc += kernel[ki] * tvdb_sparse_lookup(coords, values, count, c.x + di - ax, c.y + dj - ay, c.z + dk - az, pad_value);\n"
"      }\n"
"    }\n"
"  }\n"
"  out_values[i] = acc;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_sparse_index_scatter(const tvdb_int4* coords, int* idx_grid,\n"
"    int bx, int by, int bz, int dx, int dy, int dz, unsigned int count) {\n"
"  unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (i >= count) return;\n"
"  tvdb_int4 c = coords[i];\n"
"  int lx = c.x - bx, ly = c.y - by, lz = c.z - bz;\n"
"  idx_grid[(lz * dy + ly) * dx + lx] = (int)i;\n"
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
"        int lx = c.x + di - ax - bx, ly = c.y + dj - ay - by, lz = c.z + dk - az - bz;\n"
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
"__device__ int tvdb_active_index(const tvdb_int4* active, unsigned int na, int x, int y, int z) {\n"
"  for (unsigned int i = 0; i < na; ++i) {\n"
"    tvdb_int4 c = active[i];\n"
"    if (c.x == x && c.y == y && c.z == z) return (int)i;\n"
"  }\n"
"  return -1;\n"
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
"          if (tvdb_active_index(active, na, c.x + dx, c.y + dy, c.z + dz) >= 0) ++cnt;\n"
"        }\n"
"  } else {\n"
"    const int o[6][3] = {{1,0,0},{-1,0,0},{0,1,0},{0,-1,0},{0,0,1},{0,0,-1}};\n"
"    for (int t = 0; t < 6; ++t)\n"
"      if (tvdb_active_index(active, na, c.x + o[t][0], c.y + o[t][1], c.z + o[t][2]) >= 0) ++cnt;\n"
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
"extern \"C\" __global__ void tvdb_cuda_stats(const float* data, float4* partials,\n"
"                                            unsigned int count, unsigned int nthreads) {\n"
"  unsigned int t = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (t >= nthreads) return;\n"
"  float mn = 0.0f, mx = 0.0f, sum = 0.0f, sumsq = 0.0f; bool any = false;\n"
"  for (unsigned int i = t; i < count; i += nthreads) {\n"
"    float v = data[i];\n"
"    if (!any) { mn = v; mx = v; any = true; } else { mn = fminf(mn, v); mx = fmaxf(mx, v); }\n"
"    sum += v; sumsq += v * v;\n"
"  }\n"
"  float4 p; p.x = mn; p.y = mx; p.z = sum; p.w = sumsq; partials[t] = p;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_levelset_check(const float* data, float4* partials,\n"
"    int nx, int ny, int nz, float inv2vs, float band_world, float tol, unsigned int count, unsigned int nthreads) {\n"
"  unsigned int t = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (t >= nthreads) return;\n"
"  int inx = nx - 2, iny = ny - 2; unsigned int sl = (unsigned int)(nx * ny);\n"
"  float sum_mag = 0.0f, max_err = 0.0f, bad = 0.0f, band = 0.0f;\n"
"  for (unsigned int m = t; m < count; m += nthreads) {\n"
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
"  float4 p; p.x = sum_mag; p.y = max_err; p.z = bad; p.w = band; partials[t] = p;\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_flood(const float* data, unsigned int* vis, unsigned int* changed,\n"
"                                            int nx, int ny, int nz, float thresh) {\n"
"  unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  unsigned int total = (unsigned int)(nx * ny * nz);\n"
"  if (gid >= total) return;\n"
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
"  if (reached) { vis[gid] = 1u; changed[0] = 1u; }\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_splat(float* data, const tvdb_float4* pts, const float* vals,\n"
"    float* wdata, int nx, int ny, int nz, float ox, float oy, float oz, float vs,\n"
"    unsigned int count, int has_weights) {\n"
"  unsigned int p = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (p >= count) return;\n"
"  tvdb_float4 q = pts[p];\n"
"  float vx = (q.x - ox) / vs - 0.5f, vy = (q.y - oy) / vs - 0.5f, vz = (q.z - oz) / vs - 0.5f;\n"
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
"extern \"C\" __global__ void tvdb_cuda_hash_insert(unsigned int* state, int* keys, const tvdb_float4* pts,\n"
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
"    if (prev == 0u) { keys[slot*3u+0u]=ix; keys[slot*3u+1u]=iy; keys[slot*3u+2u]=iz; return; }\n"
"    if (keys[slot*3u+0u]==ix && keys[slot*3u+1u]==iy && keys[slot*3u+2u]==iz) return;\n"
"    slot = (slot + 1u) & mask;\n"
"  }\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_hash_compact(const unsigned int* state, const int* keys,\n"
"    unsigned int* counter, int* out_coords, unsigned int cap) {\n"
"  unsigned int s = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (s >= cap) return;\n"
"  if (state[s] == 0u) return;\n"
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
"  int* a = (int*)addr; int old = *a, assumed;\n"
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
"    unsigned int lin = (unsigned int)((qz * dy + qy) * dx + qx);\n"
"    tvdb_atomic_min_f(&v2[lin], vs); outocc[lin] = 1u;\n"
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
"extern \"C\" __global__ void tvdb_cuda_checksum(const unsigned int* data, unsigned int* partials,\n"
"                                               unsigned int count, unsigned int nthreads) {\n"
"  unsigned int t = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (t >= nthreads) return;\n"
"  unsigned int s = 0u;\n"
"  for (unsigned int i = t; i < count; i += nthreads) {\n"
"    unsigned int h = data[i] ^ (i * 2654435761u); h *= 2654435761u; h ^= h >> 15; s += h;\n"
"  }\n"
"  partials[t] = s;\n"
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
"    int nx, int ny, int nz, float ox, float oy, float oz, float vs, float band, unsigned int face_count) {\n"
"  unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  unsigned int total = (unsigned int)(nx * ny * nz);\n"
"  if (gid >= total) return;\n"
"  int iz=(int)(gid/(unsigned int)(nx*ny)); int rem=(int)(gid-(unsigned int)(iz*nx*ny)); int iy=rem/nx; int ix=rem-iy*nx;\n"
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
"  float v=s*dist; if (v>band) v=band; if (v<-band) v=-band; out_sdf[gid]=v;\n"
"}\n"
"__device__ void tvdb_mc_interp(float iso, const float* p1, const float* p2, float v1, float v2, float* o) {\n"
"  if (fabsf(v1 - v2) < 1e-10f) { o[0]=p1[0]; o[1]=p1[1]; o[2]=p1[2]; return; }\n"
"  float mu=(iso-v1)/(v2-v1); o[0]=p1[0]+mu*(p2[0]-p1[0]); o[1]=p1[1]+mu*(p2[1]-p1[1]); o[2]=p1[2]+mu*(p2[2]-p1[2]);\n"
"}\n"
"extern \"C\" __global__ void tvdb_cuda_marching_cubes(const float* grid, const int* tables,\n"
"    float* out_verts, int* tri_counts, int nx, int ny, int nz, float ox, float oy, float oz, float vs,\n"
"    float isovalue, unsigned int cell_count) {\n"
"  unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;\n"
"  if (gid >= cell_count) return;\n"
"  const int CN[8][3]={{0,0,0},{1,0,0},{1,1,0},{0,1,0},{0,0,1},{1,0,1},{1,1,1},{0,1,1}};\n"
"  const int EA[12]={0,1,2,3,4,5,6,7,0,1,2,3}; const int EB[12]={1,2,3,0,5,6,7,4,4,5,6,7};\n"
"  int cnx=nx-1, cny=ny-1;\n"
"  int cz=(int)(gid/(unsigned int)(cnx*cny)); int rem=(int)(gid-(unsigned int)(cz*cnx*cny)); int cy=rem/cnx; int cx=rem-cy*cnx;\n"
"  float val[8]; int gc[8][3]; int cube=0;\n"
"  for (int i=0;i<8;++i){ gc[i][0]=cx+CN[i][0]; gc[i][1]=cy+CN[i][1]; gc[i][2]=cz+CN[i][2];\n"
"    val[i]=grid[(gc[i][2]*ny+gc[i][1])*nx+gc[i][0]]; if (val[i]<isovalue) cube|=(1<<i); }\n"
"  int edges=tables[cube]; if (edges==0){ tri_counts[gid]=0; return; }\n"
"  float ev[12][3];\n"
"  for (int e=0;e<12;++e){ if((edges&(1<<e))==0) continue; int a=EA[e],b=EB[e];\n"
"    float pa[3]={ox+((float)gc[a][0]+0.5f)*vs, oy+((float)gc[a][1]+0.5f)*vs, oz+((float)gc[a][2]+0.5f)*vs};\n"
"    float pb[3]={ox+((float)gc[b][0]+0.5f)*vs, oy+((float)gc[b][1]+0.5f)*vs, oz+((float)gc[b][2]+0.5f)*vs};\n"
"    tvdb_mc_interp(isovalue,pa,pb,val[a],val[b],ev[e]); }\n"
"  int tc=0;\n"
"  for (int i=0;i<16 && tables[256+cube*16+i]!=-1; i+=3){\n"
"    int e0=tables[256+cube*16+i],e1=tables[256+cube*16+i+1],e2=tables[256+cube*16+i+2];\n"
"    unsigned int base=(gid*5u+(unsigned int)tc)*9u;\n"
"    out_verts[base+0]=ev[e0][0];out_verts[base+1]=ev[e0][1];out_verts[base+2]=ev[e0][2];\n"
"    out_verts[base+3]=ev[e1][0];out_verts[base+4]=ev[e1][1];out_verts[base+5]=ev[e1][2];\n"
"    out_verts[base+6]=ev[e2][0];out_verts[base+7]=ev[e2][1];out_verts[base+8]=ev[e2][2]; ++tc; }\n"
"  tri_counts[gid]=tc;\n"
"}\n"
"__device__ float tvdb_strided_lookup(const tvdb_int4* in_data, unsigned int n_in, int x, int y, int z, float pad) {\n"
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
"    acc += kernel[ki]*tvdb_strided_lookup(in_data, n_in, oc.x*stride+di-ax, oc.y*stride+dj-ay, oc.z*stride+dk-az, pad_value);\n"
"  }\n"
"  out_values[i]=acc;\n"
"}\n"
"__device__ void tvdb_atomic_add_f(float* addr, float val) {\n"
"  int* a=(int*)addr; int old=*a, assumed;\n"
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
"    int ox=c.x*stride+di-ax-bx, oy=c.y*stride+dj-ay-by, oz=c.z*stride+dk-az-bz;\n"
"    unsigned int lin=(unsigned int)((oz*dy+oy)*dx+ox);\n"
"    tvdb_atomic_add_f(&v2[lin], kernel[ki]*v); occ[lin]=1u;\n"
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
"    acc += kernel[ki]*tvdb_batched_lookup(in_data, lo, hi, c.x+di-ax, c.y+dj-ay, c.z+dk-az, pad_value);\n"
"  }\n"
"  out_values[i]=acc;\n"
"}\n";

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
  ctx->supports_sparse_aliased =
      (ctx->supports_sparse_3d_images && features.sparseResidencyAliased) ? 1 : 0;
  ctx->vk.GetPhysicalDeviceMemoryProperties(ctx->physical_device, &ctx->memory_props);
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
    if (ctx->device && ctx->vk.DestroyDevice) ctx->vk.DestroyDevice(ctx->device, NULL);
    if (ctx->instance && ctx->vk.DestroyInstance) ctx->vk.DestroyInstance(ctx->instance, NULL);
    tvdb_dyn_close(ctx->vk.lib);
  }
  free(ctx);
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

tvdb_status_t tvdb_gpu_csg_dense(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* a,
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
  if (!ctx || !grid || !grid->data || !pts || !out_values) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid sample arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
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
  if (!ctx || !grid || !grid->data || !pts || !out_values) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid quadratic sample arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (n == 0) return TVDB_OK;
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
    dims[a] = (int32_t)d;
    vol *= d;
    if (vol <= 0 || vol > (long long)400000000) return 0;  // too large for dense index grid
  }
  return (size_t)vol;
}

tvdb_status_t tvdb_gpu_sparse_conv3d(tvdb_gpu_context_t* ctx, const tvdb_sparse_grid* in,
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
    return tvdb_cuda_sparse_conv(ctx, in, kernel, kx, ky, kz, pad_value, out, err);
  }
  if (volume) {
    return tvdb_vk_sparse_conv_dense(ctx, in, kernel, kx, ky, kz, pad_value, bbmin, dims, volume, out, err);
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
static tvdb_status_t tvdb_cuda_index_query(tvdb_gpu_context_t* ctx,
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

static tvdb_status_t tvdb_vk_index_query(tvdb_gpu_context_t* ctx,
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

static tvdb_status_t tvdb_gpu_index_query(tvdb_gpu_context_t* ctx,
    const int32_t* active, size_t na, const int32_t* query, size_t nq,
    int32_t* out, tvdb_error_t* err) {
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA)
    return tvdb_cuda_index_query(ctx, active, na, query, nq, out, err);
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
static tvdb_status_t tvdb_cuda_points_query(tvdb_gpu_context_t* ctx,
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

tvdb_status_t tvdb_gpu_points_in_grid(tvdb_gpu_context_t* ctx,
    const float* points, size_t np, const float voxel_size[3], const float origin[3],
    const int32_t* active, size_t na, uint8_t* out, tvdb_error_t* err) {
  if (!ctx || (!points && np) || !voxel_size || !origin || (!active && na) || (!out && np)) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid points_in_grid arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (voxel_size[0] <= 0.0f || voxel_size[1] <= 0.0f || voxel_size[2] <= 0.0f) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "voxel_size must be positive");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  if (np == 0) return TVDB_OK;
  int32_t* idx = (int32_t*)malloc(np * sizeof(int32_t));
  if (!idx) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  tvdb_status_t st = (ctx->backend == TVDB_GPU_BACKEND_CUDA)
      ? tvdb_cuda_points_query(ctx, points, np, voxel_size, origin, active, na, idx, err)
      : tvdb_vk_points_query(ctx, points, np, voxel_size, origin, active, na, idx, err);
  if (st == TVDB_OK)
    for (size_t i = 0; i < np; ++i) out[i] = idx[i] >= 0 ? 1 : 0;
  free(idx);
  return st;
}

// neighbor kernel: out[i] = # active neighbors of active[i] (6- or 26-conn).
static tvdb_status_t tvdb_cuda_neighbor_counts_impl(tvdb_gpu_context_t* ctx,
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
    return tvdb_cuda_neighbor_counts_impl(ctx, active, na, connectivity, out_counts, err);
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
    st = tvdb_vk_dispatch(ctx, &d, err);
    if (st != TVDB_OK) goto done_p;
    tvdb_vk_buffer* tmp = src; src = dst; dst = tmp;
  }
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
  for (int it = 0; it < iterations; ++it) {
    void* args[] = {&src, &dst, &nx, &ny, &nz, &is_dilate};
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid_blocks, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto done; }
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
  return tvdb_gpu_morph(ctx, grid, iterations, 1, err);
}
tvdb_status_t tvdb_gpu_erode(tvdb_gpu_context_t* ctx, tvdb_dense_grid* grid,
                             int iterations, tvdb_error_t* err) {
  return tvdb_gpu_morph(ctx, grid, iterations, 0, err);
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
  size_t bytes = (size_t)nx * (size_t)ny * (size_t)nz * sizeof(float);
  out->nx = nx; out->ny = ny; out->nz = nz;
  out->voxel_size = vs; out->ox = ox; out->oy = oy; out->oz = oz;
  out->data = (float*)malloc(bytes);
  if (!out->data) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  memset(out->data, 0, bytes);
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_coarsen(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* in,
                               int factor, tvdb_dense_grid* out, tvdb_error_t* err) {
  if (!ctx || !in || !in->data || !out || factor <= 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid coarsen arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  int onx = (in->nx + factor - 1) / factor;
  int ony = (in->ny + factor - 1) / factor;
  int onz = (in->nz + factor - 1) / factor;
  tvdb_status_t st = tvdb_gpu_init_out_grid(out, onx, ony, onz, in->voxel_size * (float)factor,
                                            in->ox, in->oy, in->oz, err);
  if (st != TVDB_OK) return st;
  size_t nin = (size_t)in->nx * (size_t)in->ny * (size_t)in->nz;
  size_t nout = (size_t)onx * (size_t)ony * (size_t)onz;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr di = 0, dou = 0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) return st;
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_coarsen"))) return err ? err->status : TVDB_ERROR_IO;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &di, in->data, nin * sizeof(float), err)) != TVDB_OK) goto cdone;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dou, NULL, nout * sizeof(float), err)) != TVDB_OK) goto cdone;
    int inx = in->nx, iny = in->ny, inz = in->nz;
    void* args[] = {&di, &dou, &inx, &iny, &inz, &onx, &ony, &onz, &factor};
    unsigned int block = 128, grid = ((unsigned int)nout + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto cdone; }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto cdone; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out->data, dou, nout * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto cdone; }
    st = TVDB_OK;
cdone:
    if (dou) ctx->cuda.cuMemFree(dou);
    if (di) ctx->cuda.cuMemFree(di);
    return st;
  }

  tvdb_vk_buffer bi, bo, bp;
  if ((st = tvdb_vk_create_buffer(ctx, nin * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bi, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, nout * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto done_i;
  if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bp, err)) != TVDB_OK) goto done_o;
  memcpy(bi.mapped, in->data, nin * sizeof(float));
  struct { int32_t in_dim[4]; int32_t out_dim[4]; int32_t factor; int32_t pad[3]; } par;
  memset(&par, 0, sizeof(par));
  par.in_dim[0] = in->nx; par.in_dim[1] = in->ny; par.in_dim[2] = in->nz;
  par.out_dim[0] = onx; par.out_dim[1] = ony; par.out_dim[2] = onz; par.factor = factor;
  memcpy(bp.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuCoarsenSpv; d.spv_len = kTvdbGpuCoarsenSpv_len; d.descriptor_count = 3;
  d.buffers[0] = &bi; d.buffers[1] = &bo; d.buffers[2] = &bp;
  d.descriptor_types[0] = d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((nout + 127u) / 128u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(out->data, bo.mapped, nout * sizeof(float));
  tvdb_vk_destroy_buffer(ctx, &bp);
done_o: tvdb_vk_destroy_buffer(ctx, &bo);
done_i: tvdb_vk_destroy_buffer(ctx, &bi);
  return st;
}

tvdb_status_t tvdb_gpu_refine(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* in,
                              int factor, tvdb_dense_grid* out, tvdb_error_t* err) {
  if (!ctx || !in || !in->data || !out || factor <= 0) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid refine arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  int onx = in->nx * factor, ony = in->ny * factor, onz = in->nz * factor;
  float ovs = in->voxel_size / (float)factor;
  tvdb_status_t st = tvdb_gpu_init_out_grid(out, onx, ony, onz, ovs, in->ox, in->oy, in->oz, err);
  if (st != TVDB_OK) return st;
  size_t nin = (size_t)in->nx * (size_t)in->ny * (size_t)in->nz;
  size_t nout = (size_t)onx * (size_t)ony * (size_t)onz;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr di = 0, dou = 0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) return st;
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_refine"))) return err ? err->status : TVDB_ERROR_IO;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &di, in->data, nin * sizeof(float), err)) != TVDB_OK) goto rdone;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dou, NULL, nout * sizeof(float), err)) != TVDB_OK) goto rdone;
    int inx = in->nx, iny = in->ny, inz = in->nz;
    float iox = in->ox, ioy = in->oy, ioz = in->oz, ivs = in->voxel_size;
    float oox = out->ox, ooy = out->oy, ooz = out->oz;
    void* args[] = {&di, &dou, &inx, &iny, &inz, &onx, &ony, &onz, &iox, &ioy, &ioz, &ivs, &oox, &ooy, &ooz, &ovs};
    unsigned int block = 128, grid = ((unsigned int)nout + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto rdone; }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto rdone; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(out->data, dou, nout * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto rdone; }
    st = TVDB_OK;
rdone:
    if (dou) ctx->cuda.cuMemFree(dou);
    if (di) ctx->cuda.cuMemFree(di);
    return st;
  }

  tvdb_vk_buffer bi, bo, bp;
  if ((st = tvdb_vk_create_buffer(ctx, nin * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bi, err)) != TVDB_OK) return st;
  if ((st = tvdb_vk_create_buffer(ctx, nout * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto rdone_i;
  if ((st = tvdb_vk_create_buffer(ctx, 80, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bp, err)) != TVDB_OK) goto rdone_o;
  memcpy(bi.mapped, in->data, nin * sizeof(float));
  struct { int32_t in_dim[4]; int32_t out_dim[4]; float in_origin[4]; float out_origin[4]; float in_vs; float out_vs; float pad[2]; } par;
  memset(&par, 0, sizeof(par));
  par.in_dim[0] = in->nx; par.in_dim[1] = in->ny; par.in_dim[2] = in->nz;
  par.out_dim[0] = onx; par.out_dim[1] = ony; par.out_dim[2] = onz;
  par.in_origin[0] = in->ox; par.in_origin[1] = in->oy; par.in_origin[2] = in->oz;
  par.out_origin[0] = out->ox; par.out_origin[1] = out->oy; par.out_origin[2] = out->oz;
  par.in_vs = in->voxel_size; par.out_vs = ovs;
  memcpy(bp.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuRefineSpv; d.spv_len = kTvdbGpuRefineSpv_len; d.descriptor_count = 3;
  d.buffers[0] = &bi; d.buffers[1] = &bo; d.buffers[2] = &bp;
  d.descriptor_types[0] = d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((nout + 127u) / 128u);
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) memcpy(out->data, bo.mapped, nout * sizeof(float));
  tvdb_vk_destroy_buffer(ctx, &bp);
rdone_o: tvdb_vk_destroy_buffer(ctx, &bo);
rdone_i: tvdb_vk_destroy_buffer(ctx, &bi);
  return st;
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
  if (!out) { tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "null stats out"); return TVDB_ERROR_INVALID_ARGUMENT; }
  memset(out, 0, sizeof(*out));
  if (!ctx || !grid || !grid->data) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid grid_statistics arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  size_t n = (size_t)grid->nx * (size_t)grid->ny * (size_t)grid->nz;
  if (n == 0) { tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "empty grid"); return TVDB_ERROR_INVALID_ARGUMENT; }
  uint32_t nthreads = n < 256 ? (uint32_t)n : 256u;
  float* partials = (float*)malloc((size_t)nthreads * 4u * sizeof(float));
  if (!partials) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }

  tvdb_status_t st;
  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dd = 0, dp = 0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto cu_ret;
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_stats"))) { st = err ? err->status : TVDB_ERROR_IO; goto cu_ret; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dd, grid->data, n * sizeof(float), err)) != TVDB_OK) goto cu_free;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dp, NULL, (size_t)nthreads * 4u * sizeof(float), err)) != TVDB_OK) goto cu_free;
    unsigned int uc = (unsigned int)n, unt = nthreads;
    void* args[] = {&dd, &dp, &uc, &unt};
    unsigned int block = 256, gridb = (nthreads + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, gridb, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto cu_free; }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto cu_free; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(partials, dp, (size_t)nthreads * 4u * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto cu_free; }
    st = TVDB_OK;
cu_free:
    if (dp) ctx->cuda.cuMemFree(dp);
    if (dd) ctx->cuda.cuMemFree(dd);
cu_ret:
    if (st == TVDB_OK) tvdb_finalize_stats(partials, nthreads, n, out);
    free(partials);
    return st;
  }

  tvdb_vk_buffer bi, bp, bu;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bi, err)) != TVDB_OK) { free(partials); return st; }
  if ((st = tvdb_vk_create_buffer(ctx, (size_t)nthreads * 4u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bp, err)) != TVDB_OK) goto vk_i;
  if ((st = tvdb_vk_create_buffer(ctx, 16, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto vk_p;
  memcpy(bi.mapped, grid->data, n * sizeof(float));
  struct { uint32_t count, nthreads, pad[2]; } par = {(uint32_t)n, nthreads, {0, 0}};
  memcpy(bu.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuStatsSpv; d.spv_len = kTvdbGpuStatsSpv_len; d.descriptor_count = 3;
  d.buffers[0] = &bi; d.buffers[1] = &bp; d.buffers[2] = &bu;
  d.descriptor_types[0] = d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (nthreads + 255u) / 256u;
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) {
    memcpy(partials, bp.mapped, (size_t)nthreads * 4u * sizeof(float));
    tvdb_finalize_stats(partials, nthreads, n, out);
  }
  tvdb_vk_destroy_buffer(ctx, &bu);
vk_p: tvdb_vk_destroy_buffer(ctx, &bp);
vk_i: tvdb_vk_destroy_buffer(ctx, &bi);
  free(partials);
  return st;
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
  if (!out) { tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "null check out"); return TVDB_ERROR_INVALID_ARGUMENT; }
  out->mean_grad_mag = 0.0; out->max_grad_error = 0.0; out->bad_fraction = 0.0; out->band_count = 0;
  if (!ctx || !grid || !grid->data || grid->nx < 3 || grid->ny < 3 || grid->nz < 3) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid check_level_set arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  size_t n = (size_t)grid->nx * (size_t)grid->ny * (size_t)grid->nz;
  size_t interior = (size_t)(grid->nx - 2) * (size_t)(grid->ny - 2) * (size_t)(grid->nz - 2);
  uint32_t nthreads = interior < 256 ? (uint32_t)interior : 256u;
  if (nthreads == 0) return TVDB_OK;
  float inv2vs = (float)(1.0 / (2.0 * (double)grid->voxel_size));
  float bw = (float)band_world, ftol = (float)tol;
  float* partials = (float*)malloc((size_t)nthreads * 4u * sizeof(float));
  if (!partials) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dd = 0, dp = 0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto lcu_ret;
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_levelset_check"))) { st = err ? err->status : TVDB_ERROR_IO; goto lcu_ret; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dd, grid->data, n * sizeof(float), err)) != TVDB_OK) goto lcu_free;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dp, NULL, (size_t)nthreads * 4u * sizeof(float), err)) != TVDB_OK) goto lcu_free;
    int nx = grid->nx, ny = grid->ny, nz = grid->nz;
    unsigned int uc = (unsigned int)interior, unt = nthreads;
    void* args[] = {&dd, &dp, &nx, &ny, &nz, &inv2vs, &bw, &ftol, &uc, &unt};
    unsigned int block = 256, gridb = (nthreads + block - 1u) / block;
    if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, gridb, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto lcu_free; }
    if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto lcu_free; }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(partials, dp, (size_t)nthreads * 4u * sizeof(float)))) { st = err ? err->status : TVDB_ERROR_IO; goto lcu_free; }
    st = TVDB_OK;
lcu_free:
    if (dp) ctx->cuda.cuMemFree(dp);
    if (dd) ctx->cuda.cuMemFree(dd);
lcu_ret:
    if (st == TVDB_OK) tvdb_finalize_ls_check(partials, nthreads, interior, out);
    free(partials);
    return st;
  }

  tvdb_vk_buffer bi, bp, bu;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bi, err)) != TVDB_OK) { free(partials); return st; }
  if ((st = tvdb_vk_create_buffer(ctx, (size_t)nthreads * 4u * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bp, err)) != TVDB_OK) goto lvk_i;
  if ((st = tvdb_vk_create_buffer(ctx, 64, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto lvk_p;
  memcpy(bi.mapped, grid->data, n * sizeof(float));
  struct { int32_t dim[4]; float cfg[4]; uint32_t count; uint32_t nthreads; uint32_t pad[2]; } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = grid->nx; par.dim[1] = grid->ny; par.dim[2] = grid->nz;
  par.cfg[0] = inv2vs; par.cfg[1] = bw; par.cfg[2] = ftol;
  par.count = (uint32_t)interior; par.nthreads = nthreads;
  memcpy(bu.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuLevelsetCheckSpv; d.spv_len = kTvdbGpuLevelsetCheckSpv_len; d.descriptor_count = 3;
  d.buffers[0] = &bi; d.buffers[1] = &bp; d.buffers[2] = &bu;
  d.descriptor_types[0] = d.descriptor_types[1] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (nthreads + 255u) / 256u;
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) {
    memcpy(partials, bp.mapped, (size_t)nthreads * 4u * sizeof(float));
    tvdb_finalize_ls_check(partials, nthreads, interior, out);
  }
  tvdb_vk_destroy_buffer(ctx, &bu);
lvk_p: tvdb_vk_destroy_buffer(ctx, &bp);
lvk_i: tvdb_vk_destroy_buffer(ctx, &bi);
  free(partials);
  return st;
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
  if (!ctx || !grid || !grid->data || band_world <= 0.0f) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid signed_flood_fill arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  size_t n = (size_t)nx * (size_t)ny * (size_t)nz;
  if (n == 0) return TVDB_OK;
  float thresh = band_world - 1e-5f;
  uint32_t* vis = (uint32_t*)calloc(n, sizeof(uint32_t));
  if (!vis) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  tvdb_flood_seed(grid->data, vis, nx, ny, nz, thresh);
  size_t max_iter = n + 1;  // worst-case label-propagation depth
  tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dg = 0, dv = 0, dc = 0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto fcu_ret;
    if (!tvdb_cuda_ok(ctx, err, "cuModuleGetFunction", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_flood"))) { st = err ? err->status : TVDB_ERROR_IO; goto fcu_ret; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dg, grid->data, n * sizeof(float), err)) != TVDB_OK) goto fcu_free;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dv, vis, n * sizeof(uint32_t), err)) != TVDB_OK) goto fcu_free;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dc, NULL, sizeof(uint32_t), err)) != TVDB_OK) goto fcu_free;
    unsigned int block = 128, gridb = ((unsigned int)n + block - 1u) / block;
    for (size_t it = 0; it < max_iter; ++it) {
      uint32_t zero = 0;
      if (!tvdb_cuda_ok(ctx, err, "cuMemcpyHtoD", ctx->cuda.cuMemcpyHtoD(dc, &zero, sizeof(uint32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto fcu_free; }
      void* args[] = {&dg, &dv, &dc, &nx, &ny, &nz, &thresh};
      if (!tvdb_cuda_ok(ctx, err, "cuLaunchKernel", ctx->cuda.cuLaunchKernel(fn, gridb, 1, 1, block, 1, 1, 0, NULL, args, NULL))) { st = err ? err->status : TVDB_ERROR_IO; goto fcu_free; }
      if (!tvdb_cuda_ok(ctx, err, "cuCtxSynchronize", ctx->cuda.cuCtxSynchronize())) { st = err ? err->status : TVDB_ERROR_IO; goto fcu_free; }
      uint32_t changed = 0;
      if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(&changed, dc, sizeof(uint32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto fcu_free; }
      if (!changed) break;
    }
    if (!tvdb_cuda_ok(ctx, err, "cuMemcpyDtoH", ctx->cuda.cuMemcpyDtoH(vis, dv, n * sizeof(uint32_t)))) { st = err ? err->status : TVDB_ERROR_IO; goto fcu_free; }
    st = TVDB_OK;
fcu_free:
    if (dc) ctx->cuda.cuMemFree(dc);
    if (dv) ctx->cuda.cuMemFree(dv);
    if (dg) ctx->cuda.cuMemFree(dg);
fcu_ret:
    if (st == TVDB_OK) tvdb_flood_assign(grid->data, vis, n, thresh, band_world);
    free(vis);
    return st;
  }

  tvdb_vk_buffer bg, bv, bc, bu;
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bg, err)) != TVDB_OK) { free(vis); return st; }
  if ((st = tvdb_vk_create_buffer(ctx, n * sizeof(uint32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bv, err)) != TVDB_OK) goto fvk_g;
  if ((st = tvdb_vk_create_buffer(ctx, sizeof(uint32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bc, err)) != TVDB_OK) goto fvk_v;
  if ((st = tvdb_vk_create_buffer(ctx, 32, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto fvk_c;
  memcpy(bg.mapped, grid->data, n * sizeof(float));
  memcpy(bv.mapped, vis, n * sizeof(uint32_t));
  struct { int32_t dim[4]; float thresh; float pad[3]; } par;
  memset(&par, 0, sizeof(par));
  par.dim[0] = nx; par.dim[1] = ny; par.dim[2] = nz; par.thresh = thresh;
  memcpy(bu.mapped, &par, sizeof(par));
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuFloodSpv; d.spv_len = kTvdbGpuFloodSpv_len; d.descriptor_count = 4;
  d.buffers[0] = &bg; d.buffers[1] = &bv; d.buffers[2] = &bc; d.buffers[3] = &bu;
  d.descriptor_types[0] = d.descriptor_types[1] = d.descriptor_types[2] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[3] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (uint32_t)((n + 127u) / 128u);
  for (size_t it = 0; it < max_iter; ++it) {
    *(uint32_t*)bc.mapped = 0u;
    st = tvdb_vk_dispatch(ctx, &d, err);
    if (st != TVDB_OK) goto fvk_done;
    if (*(uint32_t*)bc.mapped == 0u) break;
  }
  memcpy(vis, bv.mapped, n * sizeof(uint32_t));
  tvdb_flood_assign(grid->data, vis, n, thresh, band_world);
  st = TVDB_OK;
fvk_done:
  tvdb_vk_destroy_buffer(ctx, &bu);
fvk_c: tvdb_vk_destroy_buffer(ctx, &bc);
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
  if (!ctx || !grid || !grid->data || (!points && n) || (!vals && n)) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid splat arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
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
    st = tvdb_vk_dispatch(ctx, &dm, err);
    if (st == TVDB_OK) {
      tvdb_vk_dispatch_desc de;
      memset(&de, 0, sizeof(de));
      de.spv = kTvdbGpuSparseErodeSpv; de.spv_len = kTvdbGpuSparseErodeSpv_len; de.descriptor_count = 5;
      de.buffers[0]=&bocc; de.buffers[1]=&bval; de.buffers[2]=&bcnt; de.buffers[3]=&bout; de.buffers[4]=&bue;
      for (int i = 0; i < 4; ++i) de.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
      de.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
      de.group_x = (uint32_t)((volume + 127u) / 128u);
      st = tvdb_vk_dispatch(ctx, &de, err);
    }
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
  for (int a = 0; a < 3; ++a) { bbmin[a] -= 1; bbmax[a] += 1; }  // room for grown neighbors
  long long dx = (long long)bbmax[0]-bbmin[0]+1, dy = (long long)bbmax[1]-bbmin[1]+1, dz = (long long)bbmax[2]-bbmin[2]+1;
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
    st = tvdb_vk_dispatch(ctx, &dm, err);
    if (st == TVDB_OK) {
      tvdb_vk_dispatch_desc ds;
      memset(&ds, 0, sizeof(ds));
      ds.spv = kTvdbGpuSparseDilateScatterSpv; ds.spv_len = kTvdbGpuSparseDilateScatterSpv_len; ds.descriptor_count = 5;
      ds.buffers[0]=&bval; ds.buffers[1]=&boutocc; ds.buffers[2]=&bc; ds.buffers[3]=&biv; ds.buffers[4]=&buc;
      for (int i = 0; i < 4; ++i) ds.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
      ds.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
      ds.group_x = (uint32_t)((cnt + 127u) / 128u);
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
      st = tvdb_vk_dispatch(ctx, &df, err);
    }
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

tvdb_status_t tvdb_gpu_dilate_sparse(tvdb_gpu_context_t* ctx, const tvdb_sparse_grid* in,
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
  for (size_t i = 0; i < cnt; ++i) { cc[3*i+0]=in->coords[i].x; cc[3*i+1]=in->coords[i].y; cc[3*i+2]=in->coords[i].z; cv[i]=in->values[i]; }

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
  if (!ctx || !dense || !dense->data || !out) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid active_grid_coords arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  out->count = 0; out->voxel_size = dense->voxel_size; out->ox = dense->ox; out->oy = dense->oy; out->oz = dense->oz;
  size_t n = (size_t)dense->nx * (size_t)dense->ny * (size_t)dense->nz;
  if (n == 0) return TVDB_OK;
  int32_t* outd = (int32_t*)malloc(n * 4u * sizeof(int32_t));
  if (!outd) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  uint32_t m = 0;
  tvdb_status_t st;
  int nx = dense->nx, ny = dense->ny, nz = dense->nz;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dd = 0, dcnt = 0, dout = 0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) { free(outd); return st; }
    if (!tvdb_cuda_ok(ctx, err, "f", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_active_coords"))) { free(outd); return err?err->status:TVDB_ERROR_IO; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dd, dense->data, n*sizeof(float), err)) != TVDB_OK) goto acu;
    { uint32_t zero = 0; if ((st = tvdb_cuda_alloc_copy_in(ctx, &dcnt, &zero, sizeof(uint32_t), err)) != TVDB_OK) goto acu; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, n*4u*sizeof(int32_t), err)) != TVDB_OK) goto acu;
    unsigned int uc=(unsigned int)n, ucap=(unsigned int)n, block=128;
    void* args[] = {&dd,&dcnt,&dout,&nx,&ny,&nz,&background,&tolerance,&ucap};
    if (!tvdb_cuda_ok(ctx, err, "k", ctx->cuda.cuLaunchKernel(fn,(uc+block-1u)/block,1,1,block,1,1,0,NULL,args,NULL))) { st=err?err->status:TVDB_ERROR_IO; goto acu; }
    if (!tvdb_cuda_ok(ctx, err, "s", ctx->cuda.cuCtxSynchronize())) { st=err?err->status:TVDB_ERROR_IO; goto acu; }
    if (!tvdb_cuda_ok(ctx, err, "c", ctx->cuda.cuMemcpyDtoH(&m, dcnt, sizeof(uint32_t)))) { st=err?err->status:TVDB_ERROR_IO; goto acu; }
    if (m > n) m = (uint32_t)n;
    if (m && !tvdb_cuda_ok(ctx, err, "c", ctx->cuda.cuMemcpyDtoH(outd, dout, (size_t)m*4u*sizeof(int32_t)))) { st=err?err->status:TVDB_ERROR_IO; goto acu; }
    st = TVDB_OK;
acu:
    if (dout) ctx->cuda.cuMemFree(dout);
    if (dcnt) ctx->cuda.cuMemFree(dcnt);
    if (dd) ctx->cuda.cuMemFree(dd);
    goto afinish;
  }
  {
    tvdb_vk_buffer bd, bcnt, bout, bu;
    if ((st = tvdb_vk_create_buffer(ctx, n*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bd, err)) != TVDB_OK) { free(outd); return st; }
    if ((st = tvdb_vk_create_buffer(ctx, sizeof(uint32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bcnt, err)) != TVDB_OK) goto avk_d;
    if ((st = tvdb_vk_create_buffer(ctx, n*4u*sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bout, err)) != TVDB_OK) goto avk_cnt;
    if ((st = tvdb_vk_create_buffer(ctx, 32, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto avk_out;
    memcpy(bd.mapped, dense->data, n*sizeof(float));
    *(uint32_t*)bcnt.mapped = 0u;
    struct { int32_t dim[4]; float background; float tolerance; uint32_t cap; uint32_t pad; } par;
    memset(&par, 0, sizeof(par));
    par.dim[0]=nx; par.dim[1]=ny; par.dim[2]=nz; par.background=background; par.tolerance=tolerance; par.cap=(uint32_t)n;
    memcpy(bu.mapped, &par, sizeof(par));
    tvdb_vk_dispatch_desc d;
    memset(&d, 0, sizeof(d));
    d.spv = kTvdbGpuActiveCoordsSpv; d.spv_len = kTvdbGpuActiveCoordsSpv_len; d.descriptor_count = 4;
    d.buffers[0]=&bd; d.buffers[1]=&bcnt; d.buffers[2]=&bout; d.buffers[3]=&bu;
    d.descriptor_types[0]=d.descriptor_types[1]=d.descriptor_types[2]=VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    d.descriptor_types[3]=VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    d.group_x = (uint32_t)((n + 127u) / 128u);
    st = tvdb_vk_dispatch(ctx, &d, err);
    if (st == TVDB_OK) { m = *(uint32_t*)bcnt.mapped; if (m > n) m = (uint32_t)n; memcpy(outd, bout.mapped, (size_t)m*4u*sizeof(int32_t)); }
    tvdb_vk_destroy_buffer(ctx, &bu);
avk_out: tvdb_vk_destroy_buffer(ctx, &bout);
avk_cnt: tvdb_vk_destroy_buffer(ctx, &bcnt);
avk_d: tvdb_vk_destroy_buffer(ctx, &bd);
  }
afinish:
  if (st == TVDB_OK) {
    if (!tvdb_sparse_grid_reserve(out, m ? m : 1)) { st = TVDB_ERROR_OUT_OF_MEMORY; tvdb_gpu_set_error(err, st, "OOM"); }
    else {
      for (uint32_t i = 0; i < m; ++i) {
        out->coords[i].x = outd[4*i+0]; out->coords[i].y = outd[4*i+1]; out->coords[i].z = outd[4*i+2];
        int32_t bits = outd[4*i+3]; memcpy(&out->values[i], &bits, sizeof(float));
      }
      out->count = m;
    }
  }
  free(outd);
  return st;
}

tvdb_status_t tvdb_gpu_grid_checksum(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                                     uint32_t* out_checksum, tvdb_error_t* err) {
  if (!out_checksum) { tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "null checksum out"); return TVDB_ERROR_INVALID_ARGUMENT; }
  *out_checksum = 0;
  if (!ctx || !grid || !grid->data) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid grid_checksum arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  size_t n = (size_t)grid->nx * (size_t)grid->ny * (size_t)grid->nz;
  if (n == 0) return TVDB_OK;
  uint32_t nthreads = n < 256 ? (uint32_t)n : 256u;
  uint32_t* partials = (uint32_t*)malloc((size_t)nthreads * sizeof(uint32_t));
  if (!partials) { tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dd = 0, dp = 0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) { free(partials); return st; }
    if (!tvdb_cuda_ok(ctx, err, "f", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_checksum"))) { free(partials); return err?err->status:TVDB_ERROR_IO; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dd, grid->data, n*sizeof(float), err)) != TVDB_OK) goto kcu;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dp, NULL, (size_t)nthreads*sizeof(uint32_t), err)) != TVDB_OK) goto kcu;
    unsigned int uc=(unsigned int)n, unt=nthreads, block=256;
    void* args[] = {&dd,&dp,&uc,&unt};
    if (!tvdb_cuda_ok(ctx, err, "k", ctx->cuda.cuLaunchKernel(fn,(nthreads+block-1u)/block,1,1,block,1,1,0,NULL,args,NULL))) { st=err?err->status:TVDB_ERROR_IO; goto kcu; }
    if (!tvdb_cuda_ok(ctx, err, "s", ctx->cuda.cuCtxSynchronize())) { st=err?err->status:TVDB_ERROR_IO; goto kcu; }
    if (!tvdb_cuda_ok(ctx, err, "c", ctx->cuda.cuMemcpyDtoH(partials, dp, (size_t)nthreads*sizeof(uint32_t)))) { st=err?err->status:TVDB_ERROR_IO; goto kcu; }
    st = TVDB_OK;
kcu:
    if (dp) ctx->cuda.cuMemFree(dp);
    if (dd) ctx->cuda.cuMemFree(dd);
    if (st == TVDB_OK) { uint32_t s = 0; for (uint32_t i = 0; i < nthreads; ++i) s += partials[i]; *out_checksum = s; }
    free(partials);
    return st;
  }

  tvdb_vk_buffer bd, bp, bu;
  if ((st = tvdb_vk_create_buffer(ctx, n*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bd, err)) != TVDB_OK) { free(partials); return st; }
  if ((st = tvdb_vk_create_buffer(ctx, (size_t)nthreads*sizeof(uint32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bp, err)) != TVDB_OK) goto kvk_d;
  if ((st = tvdb_vk_create_buffer(ctx, 16, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto kvk_p;
  memcpy(bd.mapped, grid->data, n*sizeof(float));
  { struct { uint32_t count, nthreads, pad[2]; } par = {(uint32_t)n, nthreads, {0,0}}; memcpy(bu.mapped, &par, sizeof(par)); }
  tvdb_vk_dispatch_desc d;
  memset(&d, 0, sizeof(d));
  d.spv = kTvdbGpuChecksumSpv; d.spv_len = kTvdbGpuChecksumSpv_len; d.descriptor_count = 3;
  d.buffers[0]=&bd; d.buffers[1]=&bp; d.buffers[2]=&bu;
  d.descriptor_types[0]=d.descriptor_types[1]=VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  d.descriptor_types[2]=VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  d.group_x = (nthreads + 255u) / 256u;
  st = tvdb_vk_dispatch(ctx, &d, err);
  if (st == TVDB_OK) {
    memcpy(partials, bp.mapped, (size_t)nthreads*sizeof(uint32_t));
    uint32_t s = 0; for (uint32_t i = 0; i < nthreads; ++i) s += partials[i]; *out_checksum = s;
  }
  tvdb_vk_destroy_buffer(ctx, &bu);
kvk_p: tvdb_vk_destroy_buffer(ctx, &bp);
kvk_d: tvdb_vk_destroy_buffer(ctx, &bd);
  free(partials);
  return st;
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
  if (!ctx || !a || !b || !out || !a->data || !b->data || fabsf(a->voxel_size - b->voxel_size) > 1e-6f) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid merge_grids arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  float vs = a->voxel_size;
  float ax1 = a->ox + a->nx*vs, ay1 = a->oy + a->ny*vs, az1 = a->oz + a->nz*vs;
  float bx1 = b->ox + b->nx*vs, by1 = b->oy + b->ny*vs, bz1 = b->oz + b->nz*vs;
  float ox = a->ox < b->ox ? a->ox : b->ox, oy = a->oy < b->oy ? a->oy : b->oy, oz = a->oz < b->oz ? a->oz : b->oz;
  float mx = ax1 > bx1 ? ax1 : bx1, my = ay1 > by1 ? ay1 : by1, mz = az1 > bz1 ? az1 : bz1;
  int nx = (int)ceilf((mx-ox)/vs), ny = (int)ceilf((my-oy)/vs), nz = (int)ceilf((mz-oz)/vs);
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

tvdb_status_t tvdb_gpu_erode_sparse(tvdb_gpu_context_t* ctx, const tvdb_sparse_grid* in,
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
  for (size_t i = 0; i < cnt; ++i) { cc[3*i+0]=in->coords[i].x; cc[3*i+1]=in->coords[i].y; cc[3*i+2]=in->coords[i].z; cv[i]=in->values[i]; }

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

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dv=0, dn=0, dout=0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto ms_host;
    if (!tvdb_cuda_ok(ctx, err, "f", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_mesh_to_sdf"))) { st=err?err->status:TVDB_ERROR_IO; goto ms_host; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dv, verts, nf*9u*sizeof(float), err)) != TVDB_OK) goto ms_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dn, normals, nf*3u*sizeof(float), err)) != TVDB_OK) goto ms_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dout, NULL, nvox*sizeof(float), err)) != TVDB_OK) goto ms_dev;
    float ox=out->ox, oy=out->oy, oz=out->oz;
    unsigned int unf=(unsigned int)nf, uvox=(unsigned int)nvox, block=64;
    void* args[] = {&dv,&dn,&dout,&nx,&ny,&nz,&ox,&oy,&oz,&voxel_size,&band_width,&unf};
    if (!tvdb_cuda_ok(ctx, err, "k", ctx->cuda.cuLaunchKernel(fn,(uvox+block-1u)/block,1,1,block,1,1,0,NULL,args,NULL))) { st=err?err->status:TVDB_ERROR_IO; goto ms_dev; }
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

  tvdb_vk_buffer bv, bn, bo, bu;
  if ((st = tvdb_vk_create_buffer(ctx, nf*9u*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bv, err)) != TVDB_OK) { free(verts); free(normals); return st; }
  if ((st = tvdb_vk_create_buffer(ctx, nf*3u*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bn, err)) != TVDB_OK) goto mvd_v;
  if ((st = tvdb_vk_create_buffer(ctx, nvox*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bo, err)) != TVDB_OK) goto mvd_n;
  if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto mvd_o;
  memcpy(bv.mapped, verts, nf*9u*sizeof(float));
  memcpy(bn.mapped, normals, nf*3u*sizeof(float));
  {
    struct { int32_t dim[4]; float grid_o[4]; float band; uint32_t face_count; uint32_t pad[2]; } par;
    memset(&par, 0, sizeof(par));
    par.dim[0]=nx; par.dim[1]=ny; par.dim[2]=nz;
    par.grid_o[0]=out->ox; par.grid_o[1]=out->oy; par.grid_o[2]=out->oz; par.grid_o[3]=voxel_size;
    par.band=band_width; par.face_count=(uint32_t)nf;
    memcpy(bu.mapped, &par, sizeof(par));
  }
  {
    tvdb_vk_dispatch_desc d;
    memset(&d, 0, sizeof(d));
    d.spv = kTvdbGpuMeshToSdfSpv; d.spv_len = kTvdbGpuMeshToSdfSpv_len; d.descriptor_count = 4;
    d.buffers[0]=&bv; d.buffers[1]=&bn; d.buffers[2]=&bo; d.buffers[3]=&bu;
    d.descriptor_types[0]=d.descriptor_types[1]=d.descriptor_types[2]=VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    d.descriptor_types[3]=VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    d.group_x = (uint32_t)((nvox + 63u) / 64u);
    st = tvdb_vk_dispatch(ctx, &d, err);
  }
  if (st == TVDB_OK) memcpy(out->data, bo.mapped, nvox*sizeof(float));
  tvdb_vk_destroy_buffer(ctx, &bu);
mvd_o: tvdb_vk_destroy_buffer(ctx, &bo);
mvd_n: tvdb_vk_destroy_buffer(ctx, &bn);
mvd_v: tvdb_vk_destroy_buffer(ctx, &bv);
  free(verts); free(normals);
  return st;
}

// ---- marching cubes (GPU) ---------------------------------------------------

static void tvdb_mc_gather(const int32_t* tri_counts, const float* cell_verts, size_t cells,
                           float* out, size_t* total) {
  size_t w = 0;
  for (size_t c = 0; c < cells; ++c) {
    int tc = tri_counts[c];
    for (int t = 0; t < tc && t < 5; ++t) {
      const float* src = &cell_verts[(c * 5 + (size_t)t) * 9];
      for (int k = 0; k < 9; ++k) out[w++] = src[k];
    }
  }
  *total = w / 9;
}

tvdb_status_t tvdb_gpu_marching_cubes(tvdb_gpu_context_t* ctx, const tvdb_dense_grid* grid,
                                      float isovalue, float** out_verts, size_t* out_tri_count,
                                      tvdb_error_t* err) {
  if (out_verts) *out_verts = NULL;
  if (out_tri_count) *out_tri_count = 0;
  if (!ctx || !grid || !grid->data || !out_verts || !out_tri_count || grid->nx < 2 || grid->ny < 2 || grid->nz < 2) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid marching_cubes arguments");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  size_t nvox = (size_t)nx*(size_t)ny*(size_t)nz;
  size_t cells = (size_t)(nx-1)*(size_t)(ny-1)*(size_t)(nz-1);
  int* tab = (int*)malloc((256 + 256*16) * sizeof(int));
  float* cellv = (float*)malloc(cells * 5u * 9u * sizeof(float));
  int32_t* tcounts = (int32_t*)malloc(cells * sizeof(int32_t));
  if (!tab || !cellv || !tcounts) { free(tab); free(cellv); free(tcounts); tvdb_gpu_set_error(err, TVDB_ERROR_OUT_OF_MEMORY, "OOM"); return TVDB_ERROR_OUT_OF_MEMORY; }
  memcpy(tab, tvdb_mc_edge_table(), 256 * sizeof(int));
  memcpy(tab + 256, tvdb_mc_tri_table_flat(), 256*16 * sizeof(int));
  tvdb_status_t st;

  if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
    CUmodule module = NULL; CUfunction fn = NULL; CUdeviceptr dg=0, dt=0, dv=0, dc=0;
    if ((st = tvdb_cuda_get_module(ctx, &module, err)) != TVDB_OK) goto mc_dev;
    if (!tvdb_cuda_ok(ctx, err, "f", ctx->cuda.cuModuleGetFunction(&fn, module, "tvdb_cuda_marching_cubes"))) { st=err?err->status:TVDB_ERROR_IO; goto mc_dev; }
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dg, grid->data, nvox*sizeof(float), err)) != TVDB_OK) goto mc_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dt, tab, (256+256*16)*sizeof(int), err)) != TVDB_OK) goto mc_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dv, NULL, cells*5u*9u*sizeof(float), err)) != TVDB_OK) goto mc_dev;
    if ((st = tvdb_cuda_alloc_copy_in(ctx, &dc, NULL, cells*sizeof(int32_t), err)) != TVDB_OK) goto mc_dev;
    float ox=grid->ox, oy=grid->oy, oz=grid->oz, vs=grid->voxel_size;
    unsigned int ucells=(unsigned int)cells, block=64;
    void* args[] = {&dg,&dt,&dv,&dc,&nx,&ny,&nz,&ox,&oy,&oz,&vs,&isovalue,&ucells};
    if (!tvdb_cuda_ok(ctx, err, "k", ctx->cuda.cuLaunchKernel(fn,(ucells+block-1u)/block,1,1,block,1,1,0,NULL,args,NULL))) { st=err?err->status:TVDB_ERROR_IO; goto mc_dev; }
    if (!tvdb_cuda_ok(ctx, err, "s", ctx->cuda.cuCtxSynchronize())) { st=err?err->status:TVDB_ERROR_IO; goto mc_dev; }
    if (!tvdb_cuda_ok(ctx, err, "c", ctx->cuda.cuMemcpyDtoH(tcounts, dc, cells*sizeof(int32_t)))) { st=err?err->status:TVDB_ERROR_IO; goto mc_dev; }
    if (!tvdb_cuda_ok(ctx, err, "c", ctx->cuda.cuMemcpyDtoH(cellv, dv, cells*5u*9u*sizeof(float)))) { st=err?err->status:TVDB_ERROR_IO; goto mc_dev; }
    st = TVDB_OK;
mc_dev:
    if (dc) ctx->cuda.cuMemFree(dc);
    if (dv) ctx->cuda.cuMemFree(dv);
    if (dt) ctx->cuda.cuMemFree(dt);
    if (dg) ctx->cuda.cuMemFree(dg);
    goto mc_finish;
  }
  {
    tvdb_vk_buffer bg, bt, bv, bc, bu;
    if ((st = tvdb_vk_create_buffer(ctx, nvox*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bg, err)) != TVDB_OK) { free(tab); free(cellv); free(tcounts); return st; }
    if ((st = tvdb_vk_create_buffer(ctx, (256+256*16)*sizeof(int), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bt, err)) != TVDB_OK) goto mvk_g;
    if ((st = tvdb_vk_create_buffer(ctx, cells*5u*9u*sizeof(float), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bv, err)) != TVDB_OK) goto mvk_t;
    if ((st = tvdb_vk_create_buffer(ctx, cells*sizeof(int32_t), VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &bc, err)) != TVDB_OK) goto mvk_v;
    if ((st = tvdb_vk_create_buffer(ctx, 48, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, &bu, err)) != TVDB_OK) goto mvk_c;
    memcpy(bg.mapped, grid->data, nvox*sizeof(float));
    memcpy(bt.mapped, tab, (256+256*16)*sizeof(int));
    struct { int32_t dim[4]; float grid_o[4]; float isovalue; uint32_t cell_count; uint32_t pad[2]; } par;
    memset(&par, 0, sizeof(par));
    par.dim[0]=nx; par.dim[1]=ny; par.dim[2]=nz;
    par.grid_o[0]=grid->ox; par.grid_o[1]=grid->oy; par.grid_o[2]=grid->oz; par.grid_o[3]=grid->voxel_size;
    par.isovalue=isovalue; par.cell_count=(uint32_t)cells;
    memcpy(bu.mapped, &par, sizeof(par));
    tvdb_vk_dispatch_desc d;
    memset(&d, 0, sizeof(d));
    d.spv = kTvdbGpuMarchingCubesSpv; d.spv_len = kTvdbGpuMarchingCubesSpv_len; d.descriptor_count = 5;
    d.buffers[0]=&bg; d.buffers[1]=&bt; d.buffers[2]=&bv; d.buffers[3]=&bc; d.buffers[4]=&bu;
    for (int i = 0; i < 4; ++i) d.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    d.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    d.group_x = (uint32_t)((cells + 63u) / 64u);
    st = tvdb_vk_dispatch(ctx, &d, err);
    if (st == TVDB_OK) { memcpy(tcounts, bc.mapped, cells*sizeof(int32_t)); memcpy(cellv, bv.mapped, cells*5u*9u*sizeof(float)); }
    tvdb_vk_destroy_buffer(ctx, &bu);
mvk_c: tvdb_vk_destroy_buffer(ctx, &bc);
mvk_v: tvdb_vk_destroy_buffer(ctx, &bv);
mvk_t: tvdb_vk_destroy_buffer(ctx, &bt);
mvk_g: tvdb_vk_destroy_buffer(ctx, &bg);
  }
mc_finish:
  if (st == TVDB_OK) {
    size_t total_tris = 0;
    for (size_t c = 0; c < cells; ++c) { int tc = tcounts[c]; total_tris += (tc < 0 ? 0 : (tc > 5 ? 5 : tc)); }
    float* out = (float*)malloc((total_tris ? total_tris : 1) * 9u * sizeof(float));
    if (!out) { st = TVDB_ERROR_OUT_OF_MEMORY; tvdb_gpu_set_error(err, st, "OOM"); }
    else { size_t total = 0; tvdb_mc_gather(tcounts, cellv, cells, out, &total); *out_verts = out; *out_tri_count = total; }
  }
  free(tab); free(cellv); free(tcounts);
  return st;
}

// ---- strided sparse convolution (output-grid building) ----------------------

static int tvdb_floordiv(int a, int b) { int q = a / b, r = a % b; return (r != 0 && ((r < 0) != (b < 0))) ? q - 1 : q; }

typedef struct { int64_t key; int32_t c[3]; } tvdb_oc_entry;
static int tvdb_oc_cmp(const void* a, const void* b) {
  int64_t x = ((const tvdb_oc_entry*)a)->key, y = ((const tvdb_oc_entry*)b)->key;
  return (x > y) - (x < y);
}

tvdb_status_t tvdb_gpu_sparse_conv3d_strided(tvdb_gpu_context_t* ctx, const tvdb_sparse_grid* in,
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
    ent[i].key = (((int64_t)ox + (1<<20)) << 42) | (((int64_t)oy + (1<<20)) << 21) | ((int64_t)oz + (1<<20));
  }
  qsort(ent, n_in, sizeof(tvdb_oc_entry), tvdb_oc_cmp);
  size_t n_out = 0;
  for (size_t i = 0; i < n_in; ++i) if (i == 0 || ent[i].key != ent[i-1].key) {
    ent[n_out].key = ent[i].key; ent[n_out].c[0] = ent[i].c[0]; ent[n_out].c[1] = ent[i].c[1]; ent[n_out].c[2] = ent[i].c[2]; ++n_out;
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

tvdb_status_t tvdb_gpu_sparse_conv3d_transpose(tvdb_gpu_context_t* ctx, const tvdb_sparse_grid* in,
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
  int32_t bbmin[3], bbmax[3];
  for (int a = 0; a < 3; ++a) { bbmin[a] = 0x7fffffff; bbmax[a] = -0x7fffffff; }
  for (size_t i = 0; i < n_in; ++i) {
    int b[3] = {in->coords[i].x*stride, in->coords[i].y*stride, in->coords[i].z*stride};
    int lo[3] = {b[0]-ax, b[1]-ay, b[2]-az}, hi[3] = {b[0]+(kx-1-ax), b[1]+(ky-1-ay), b[2]+(kz-1-az)};
    for (int a = 0; a < 3; ++a) { if (lo[a]<bbmin[a]) bbmin[a]=lo[a]; if (hi[a]>bbmax[a]) bbmax[a]=hi[a]; }
  }
  long long dx=(long long)bbmax[0]-bbmin[0]+1, dy=(long long)bbmax[1]-bbmin[1]+1, dz=(long long)bbmax[2]-bbmin[2]+1;
  long long vol = dx*dy*dz;
  if (vol <= 0 || vol > (long long)400000000) { tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "transpose conv bbox too large"); return TVDB_ERROR_INVALID_ARGUMENT; }
  size_t volume = (size_t)vol, kn = (size_t)kx*ky*kz;
  size_t capll = n_in * kn; if (capll > volume) capll = volume; size_t cap = capll;
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
    st = tvdb_vk_dispatch(ctx, &ds, err);
    if (st == TVDB_OK) {
      tvdb_vk_dispatch_desc df;
      memset(&df, 0, sizeof(df));
      df.spv = kTvdbGpuSparseFinalizeSpv; df.spv_len = kTvdbGpuSparseFinalizeSpv_len; df.descriptor_count = 5;
      df.buffers[0]=&bv; df.buffers[1]=&boc; df.buffers[2]=&bcnt; df.buffers[3]=&bout; df.buffers[4]=&buf;
      for (int i = 0; i < 4; ++i) df.descriptor_types[i] = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
      df.descriptor_types[4] = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
      df.group_x = (uint32_t)((volume + 127u) / 128u);
      st = tvdb_vk_dispatch(ctx, &df, err);
    }
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

tvdb_status_t tvdb_gpu_dispatch(tvdb_gpu_context_t* ctx, const tvdb_gpu_dispatch_spec_t* spec,
                                tvdb_error_t* err) {
  if (!ctx || !spec || spec->num_bindings > 6 || (spec->num_bindings && !spec->bindings)) {
    tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid dispatch spec");
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  for (unsigned int i = 0; i < spec->num_bindings; ++i) {
    const tvdb_gpu_binding_t* b = &spec->bindings[i];
    if (b->size_bytes == 0 || (b->kind != TVDB_GPU_BIND_STORAGE_OUT && !b->host_data) ||
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
    st = tvdb_vk_dispatch(ctx, &d, err);
    if (st == TVDB_OK) {
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
    VkCommandBuffer cmd; VkCommandPool pool; VkFence fence;
    st = tvdb_vk_submit_one_time(buf->ctx, &cmd, &pool, &fence, err);
    if (st == TVDB_OK) {
      VkBufferCopy region; region.srcOffset = 0; region.dstOffset = 0; region.size = size;
      buf->ctx->vk.CmdCopyBuffer(cmd, staging.buffer, buf->vk.buffer, 1, &region);
      st = tvdb_vk_end_submit_wait(buf->ctx, cmd, pool, fence, err);
    }
    tvdb_vk_destroy_buffer(buf->ctx, &staging);
    if (st != TVDB_OK) return st;
  }
  return TVDB_OK;
}

tvdb_status_t tvdb_gpu_buffer_download(tvdb_gpu_buffer_t* buf, void* dst, size_t size, tvdb_error_t* err) {
  if (!buf || !dst || size > buf->size) { tvdb_gpu_set_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid buffer_download arguments"); return TVDB_ERROR_INVALID_ARGUMENT; }
  if (buf->backend == TVDB_GPU_BACKEND_CUDA) {
    if (!tvdb_cuda_ok(buf->ctx, err, "cuMemcpyDtoH", buf->ctx->cuda.cuMemcpyDtoH(dst, buf->cu, size))) return err ? err->status : TVDB_ERROR_IO;
  } else if (buf->vk.mapped) {
    memcpy(dst, buf->vk.mapped, size);
  } else {
    // Device-local (e.g. exportable) buffer: stage through a host-visible buffer.
    tvdb_vk_buffer staging;
    tvdb_status_t st = tvdb_vk_create_buffer(buf->ctx, size, VK_BUFFER_USAGE_TRANSFER_DST_BIT, &staging, err);
    if (st != TVDB_OK) return st;
    VkCommandBuffer cmd; VkCommandPool pool; VkFence fence;
    st = tvdb_vk_submit_one_time(buf->ctx, &cmd, &pool, &fence, err);
    if (st == TVDB_OK) {
      VkBufferCopy region; region.srcOffset = 0; region.dstOffset = 0; region.size = size;
      buf->ctx->vk.CmdCopyBuffer(cmd, buf->vk.buffer, staging.buffer, 1, &region);
      st = tvdb_vk_end_submit_wait(buf->ctx, cmd, pool, fence, err);
    }
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

tvdb_status_t tvdb_gpu_sparse_conv3d_batched(tvdb_gpu_context_t* ctx,
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
