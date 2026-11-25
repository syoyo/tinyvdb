/* Hardware-gated regression for caller-recorded resident dispatches and
 * borrowed Vulkan storage buffers.
 *
 * The VkBuffer objects are created by tinyvdb and handed back as borrowed
 * wrappers through tvdb_gpu_buffer_wrap_vulkan, so this test needs no Vulkan
 * SDK headers. Only the few core command-buffer and fence calls needed to
 * record and submit are declared here, in the dynamic-loading style of
 * src/tinyvdb_gpu.c. Returns 77 when there is no Vulkan device or no SPIR-V.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "tinyvdb_gpu.h"
#include "tinyvdb_gpu_resident.h"
#ifdef TVDB_TEST_GENERATED_SPV
#include "tinyvdb_gpu_axpy_spv.inc"
#else
#include "tinyvdb_gpu_spv_fallback.inc"
#endif

typedef uint32_t VkFlags;
typedef int32_t VkResult;
typedef struct VkInstance_T* VkInstance;
typedef struct VkDevice_T* VkDevice;
typedef struct VkQueue_T* VkQueue;
typedef struct VkCommandBuffer_T* VkCommandBuffer;
typedef uint64_t VkCommandPool;
typedef uint64_t VkFence;

#define VK_SUCCESS 0
#define VK_STRUCTURE_TYPE_SUBMIT_INFO 4
#define VK_STRUCTURE_TYPE_FENCE_CREATE_INFO 8
#define VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO 39
#define VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO 40
#define VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO 42
#define VK_COMMAND_BUFFER_LEVEL_PRIMARY 0

typedef struct { uint32_t sType; const void* pNext; VkFlags flags; uint32_t queueFamilyIndex; } VkCommandPoolCreateInfo;
typedef struct { uint32_t sType; const void* pNext; VkCommandPool commandPool; uint32_t level; uint32_t commandBufferCount; } VkCommandBufferAllocateInfo;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; const void* pInheritanceInfo; } VkCommandBufferBeginInfo;
typedef struct { uint32_t sType; const void* pNext; VkFlags flags; } VkFenceCreateInfo;
typedef struct { uint32_t sType; const void* pNext; uint32_t waitSemaphoreCount; const void* pWaitSemaphores;
                 const void* pWaitDstStageMask; uint32_t commandBufferCount; const VkCommandBuffer* pCommandBuffers;
                 uint32_t signalSemaphoreCount; const void* pSignalSemaphores; } VkSubmitInfo;

typedef void (*vk_proc)(void);
typedef vk_proc (*PFN_vkGetInstanceProcAddr)(VkInstance, const char*);
typedef VkResult (*PFN_vkCreateCommandPool)(VkDevice, const VkCommandPoolCreateInfo*, const void*, VkCommandPool*);
typedef void (*PFN_vkDestroyCommandPool)(VkDevice, VkCommandPool, const void*);
typedef VkResult (*PFN_vkAllocateCommandBuffers)(VkDevice, const VkCommandBufferAllocateInfo*, VkCommandBuffer*);
typedef void (*PFN_vkFreeCommandBuffers)(VkDevice, VkCommandPool, uint32_t, const VkCommandBuffer*);
typedef VkResult (*PFN_vkBeginCommandBuffer)(VkCommandBuffer, const VkCommandBufferBeginInfo*);
typedef VkResult (*PFN_vkEndCommandBuffer)(VkCommandBuffer);
typedef VkResult (*PFN_vkCreateFence)(VkDevice, const VkFenceCreateInfo*, const void*, VkFence*);
typedef void (*PFN_vkDestroyFence)(VkDevice, VkFence, const void*);
typedef VkResult (*PFN_vkQueueSubmit)(VkQueue, uint32_t, const VkSubmitInfo*, VkFence);
typedef VkResult (*PFN_vkWaitForFences)(VkDevice, uint32_t, const VkFence*, uint32_t, uint64_t);

typedef struct {
  PFN_vkCreateCommandPool CreateCommandPool;
  PFN_vkDestroyCommandPool DestroyCommandPool;
  PFN_vkAllocateCommandBuffers AllocateCommandBuffers;
  PFN_vkFreeCommandBuffers FreeCommandBuffers;
  PFN_vkBeginCommandBuffer BeginCommandBuffer;
  PFN_vkEndCommandBuffer EndCommandBuffer;
  PFN_vkCreateFence CreateFence;
  PFN_vkDestroyFence DestroyFence;
  PFN_vkQueueSubmit QueueSubmit;
  PFN_vkWaitForFences WaitForFences;
} vk_fns;

static int failures = 0;
#define CHECK(c) do { if (!(c)) { fprintf(stderr, "line %d: %s (%s)\n", __LINE__, #c, err.message); ++failures; } } while (0)

static int load_vk(vk_proc raw, VkInstance inst, vk_fns* v) {
  PFN_vkGetInstanceProcAddr gipa = (PFN_vkGetInstanceProcAddr)raw;
  v->CreateCommandPool = (PFN_vkCreateCommandPool)gipa(inst, "vkCreateCommandPool");
  v->DestroyCommandPool = (PFN_vkDestroyCommandPool)gipa(inst, "vkDestroyCommandPool");
  v->AllocateCommandBuffers = (PFN_vkAllocateCommandBuffers)gipa(inst, "vkAllocateCommandBuffers");
  v->FreeCommandBuffers = (PFN_vkFreeCommandBuffers)gipa(inst, "vkFreeCommandBuffers");
  v->BeginCommandBuffer = (PFN_vkBeginCommandBuffer)gipa(inst, "vkBeginCommandBuffer");
  v->EndCommandBuffer = (PFN_vkEndCommandBuffer)gipa(inst, "vkEndCommandBuffer");
  v->CreateFence = (PFN_vkCreateFence)gipa(inst, "vkCreateFence");
  v->DestroyFence = (PFN_vkDestroyFence)gipa(inst, "vkDestroyFence");
  v->QueueSubmit = (PFN_vkQueueSubmit)gipa(inst, "vkQueueSubmit");
  v->WaitForFences = (PFN_vkWaitForFences)gipa(inst, "vkWaitForFences");
  return v->CreateCommandPool && v->DestroyCommandPool && v->AllocateCommandBuffers &&
         v->FreeCommandBuffers && v->BeginCommandBuffer && v->EndCommandBuffer &&
         v->CreateFence && v->DestroyFence && v->QueueSubmit && v->WaitForFences;
}

static int begin_cmd(const vk_fns* v, VkDevice dev, uint32_t qfam, VkCommandPool* pool, VkCommandBuffer* cb) {
  VkCommandPoolCreateInfo pci; memset(&pci, 0, sizeof pci);
  pci.sType = VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO; pci.queueFamilyIndex = qfam;
  if (v->CreateCommandPool(dev, &pci, NULL, pool) != VK_SUCCESS) return 0;
  VkCommandBufferAllocateInfo ai; memset(&ai, 0, sizeof ai);
  ai.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
  ai.commandPool = *pool; ai.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY; ai.commandBufferCount = 1;
  if (v->AllocateCommandBuffers(dev, &ai, cb) != VK_SUCCESS) return 0;
  VkCommandBufferBeginInfo bi; memset(&bi, 0, sizeof bi);
  bi.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;
  return v->BeginCommandBuffer(*cb, &bi) == VK_SUCCESS;
}

static void submit_cmd(const vk_fns* v, VkDevice dev, VkQueue queue, VkCommandPool pool, VkCommandBuffer cb) {
  VkFence fence = 0;
  VkFenceCreateInfo fi; memset(&fi, 0, sizeof fi); fi.sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO;
  if (v->CreateFence(dev, &fi, NULL, &fence) != VK_SUCCESS) { ++failures; return; }
  VkSubmitInfo si; memset(&si, 0, sizeof si);
  si.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
  si.commandBufferCount = 1; si.pCommandBuffers = &cb;
  if (v->QueueSubmit(queue, 1, &si, fence) != VK_SUCCESS) ++failures;
  if (v->WaitForFences(dev, 1, &fence, 1, UINT64_MAX) != VK_SUCCESS) ++failures;
  v->DestroyFence(dev, fence, NULL);
  v->FreeCommandBuffers(dev, pool, 1, &cb);
  v->DestroyCommandPool(dev, pool, NULL);
}

static int lock_calls, unlock_calls;
static void lock_cb(void* u) { (void)u; ++lock_calls; }
static void unlock_cb(void* u) { (void)u; ++unlock_calls; }

static void seed(tvdb_gpu_buffer_t* b, float v, tvdb_error_t* err) {
  float data[4] = { v, v, v, v };
  if (tvdb_gpu_buffer_upload(b, data, sizeof data, err) != TVDB_OK) ++failures;
}

/* axpy: x = i+1, y = 10*(i+1), out = alpha*x + y. */
static int output_ok(tvdb_gpu_buffer_t* out, float alpha, tvdb_error_t* err) {
  float got[4];
  if (tvdb_gpu_buffer_download(out, got, sizeof got, err) != TVDB_OK) return 0;
  for (int i = 0; i < 4; ++i) {
    float want = alpha * (float)(i + 1) + 10.f * (float)(i + 1);
    if (got[i] != want) {
      fprintf(stderr, "out[%d]=%g want %g\n", i, got[i], want);
      return 0;
    }
  }
  return 1;
}

int main(void) {
  tvdb_error_t err; memset(&err, 0, sizeof err);
  tvdb_gpu_context_t* ctx = NULL;
  if (tvdb_gpu_context_create(TVDB_GPU_BACKEND_VULKAN, 0, &ctx, &err) != TVDB_OK || !tvdb_gpu_spirv_available()) {
    printf("SKIP: no Vulkan device or GPU SPIR-V\n");
    tvdb_gpu_context_destroy(ctx);
    return 77;
  }
  tvdb_gpu_vulkan_device_t dev;
  CHECK(tvdb_gpu_context_vulkan_device(ctx, &dev, &err) == TVDB_OK);
  vk_fns vk; memset(&vk, 0, sizeof vk);
  if (!load_vk(dev.get_instance_proc_addr, (VkInstance)dev.instance, &vk)) {
    printf("SKIP: Vulkan entry points unavailable\n");
    tvdb_gpu_context_destroy(ctx);
    return 77;
  }
  if (failures) return 1;

  float xdata[4], ydata[4];
  for (int i = 0; i < 4; ++i) { xdata[i] = (float)(i + 1); ydata[i] = 10.f * (float)(i + 1); }
  tvdb_gpu_buffer_t *x = NULL, *y = NULL, *o = NULL;
  tvdb_gpu_buffer_t *wx = NULL, *wy = NULL, *wo = NULL;
  CHECK(tvdb_gpu_buffer_create(ctx, sizeof xdata, &x, &err) == TVDB_OK);
  CHECK(tvdb_gpu_buffer_create(ctx, sizeof ydata, &y, &err) == TVDB_OK);
  CHECK(tvdb_gpu_buffer_create(ctx, sizeof xdata, &o, &err) == TVDB_OK);
  if (failures) goto done;
  CHECK(tvdb_gpu_buffer_wrap_vulkan(ctx, tvdb_gpu_buffer_native_handle(x), sizeof xdata, &wx, &err) == TVDB_OK);
  CHECK(tvdb_gpu_buffer_wrap_vulkan(ctx, tvdb_gpu_buffer_native_handle(y), sizeof ydata, &wy, &err) == TVDB_OK);
  CHECK(tvdb_gpu_buffer_wrap_vulkan(ctx, tvdb_gpu_buffer_native_handle(o), sizeof xdata, &wo, &err) == TVDB_OK);
  CHECK(tvdb_gpu_buffer_upload(x, xdata, sizeof xdata, &err) == TVDB_OK);
  CHECK(tvdb_gpu_buffer_upload(y, ydata, sizeof ydata, &err) == TVDB_OK);
  if (failures) goto done;

  struct { uint32_t n; float alpha; uint32_t pad[2]; } u = { 4, 2.f, { 0, 0 } };
  tvdb_gpu_resident_dispatch_t spec; memset(&spec, 0, sizeof spec);
  spec.spv = kTvdbGpuAxpySpv; spec.spv_len = kTvdbGpuAxpySpv_len;
  spec.num_bindings = 4;
  spec.bindings[0].buffer = wx; spec.bindings[1].buffer = wy; spec.bindings[2].buffer = wo;
  spec.bindings[3].uniform = &u; spec.bindings[3].uniform_size = sizeof u;
  spec.groups[0] = spec.groups[1] = spec.groups[2] = 1;
  spec.local_size[0] = 128; spec.local_size[1] = spec.local_size[2] = 1;

  /* Synchronous path with borrowed buffers as inputs and output. */
  seed(o, -1.f, &err);
  CHECK(tvdb_gpu_dispatch_resident(ctx, &spec, 1, &err) == TVDB_OK);
  CHECK(output_ok(o, 2.f, &err));

  /* Caller records the dispatch, submits it itself, then releases the handle. */
  {
    VkCommandPool pool = 0; VkCommandBuffer cb = NULL;
    if (!begin_cmd(&vk, (VkDevice)dev.device, dev.queue_family, &pool, &cb)) { ++failures; goto done; }
    u.alpha = 3.f;
    seed(o, -1.f, &err);
    tvdb_gpu_resident_recording_t* rec = NULL;
    CHECK(tvdb_gpu_dispatch_resident_record(ctx, (void*)cb, &spec, 1, &rec, &err) == TVDB_OK);
    CHECK(rec != NULL);
    CHECK(vk.EndCommandBuffer(cb) == VK_SUCCESS);
    submit_cmd(&vk, (VkDevice)dev.device, (VkQueue)dev.queue, pool, cb);
    CHECK(output_ok(o, 3.f, &err));
    tvdb_gpu_resident_recording_destroy(rec);
    /* count == 0 succeeds with a NULL handle. */
    rec = (tvdb_gpu_resident_recording_t*)(uintptr_t)1;
    CHECK(tvdb_gpu_dispatch_resident_record(ctx, (void*)(uintptr_t)1, NULL, 0, &rec, &err) == TVDB_OK);
    CHECK(rec == NULL);
  }

  /* Same thing on an adopted device, with shared-queue lock callbacks. */
  {
    tvdb_gpu_vulkan_device_t shared = dev;
    shared.lock_queue = lock_cb; shared.unlock_queue = unlock_cb;
    tvdb_gpu_context_t* guest = NULL;
    CHECK(tvdb_gpu_context_create_vulkan_external(&shared, &guest, &err) == TVDB_OK);
    if (guest) {
      tvdb_gpu_buffer_t *gx = NULL, *gy = NULL, *go = NULL;
      CHECK(tvdb_gpu_buffer_wrap_vulkan(guest, tvdb_gpu_buffer_native_handle(x), sizeof xdata, &gx, &err) == TVDB_OK);
      CHECK(tvdb_gpu_buffer_wrap_vulkan(guest, tvdb_gpu_buffer_native_handle(y), sizeof ydata, &gy, &err) == TVDB_OK);
      CHECK(tvdb_gpu_buffer_wrap_vulkan(guest, tvdb_gpu_buffer_native_handle(o), sizeof xdata, &go, &err) == TVDB_OK);
      if (!failures) {
        tvdb_gpu_resident_dispatch_t gs = spec;
        gs.bindings[0].buffer = gx; gs.bindings[1].buffer = gy; gs.bindings[2].buffer = go;
        VkCommandPool pool = 0; VkCommandBuffer cb = NULL;
        if (!begin_cmd(&vk, (VkDevice)dev.device, dev.queue_family, &pool, &cb)) ++failures;
        else {
          u.alpha = 4.f;
          seed(o, -1.f, &err);
          tvdb_gpu_resident_recording_t* rec = NULL;
          const int before = lock_calls;
          CHECK(tvdb_gpu_dispatch_resident_record(guest, (void*)cb, &gs, 1, &rec, &err) == TVDB_OK);
          CHECK(rec != NULL);
          CHECK(lock_calls == before);  /* recording must not submit or take the queue lock */
          CHECK(vk.EndCommandBuffer(cb) == VK_SUCCESS);
          submit_cmd(&vk, (VkDevice)dev.device, (VkQueue)dev.queue, pool, cb);
          CHECK(output_ok(o, 4.f, &err));
          tvdb_gpu_resident_recording_destroy(rec);
        }
      }
      tvdb_gpu_buffer_destroy(go); tvdb_gpu_buffer_destroy(gy); tvdb_gpu_buffer_destroy(gx);
      tvdb_gpu_context_destroy(guest);
    }
    CHECK(lock_calls == 0 && unlock_calls == 0);
  }

done:
  tvdb_gpu_buffer_destroy(wo); tvdb_gpu_buffer_destroy(wy); tvdb_gpu_buffer_destroy(wx);
  tvdb_gpu_buffer_destroy(o); tvdb_gpu_buffer_destroy(y); tvdb_gpu_buffer_destroy(x);
  tvdb_gpu_context_destroy(ctx);
  if (failures) { fprintf(stderr, "resident recording regression failed\n"); return 1; }
  return 0;
}
