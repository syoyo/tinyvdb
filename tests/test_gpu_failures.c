/* A fake Vulkan driver exercises cleanup without hardware or public hooks. */
#include "../src/tinyvdb_gpu.c"
static int fail_step, live_buffers, live_memory, live_maps;
static unsigned char host[64];
static VkResult create_buffer(VkDevice d, const VkBufferCreateInfo *i, const void *a, VkBuffer *b) {
    (void)d; (void)i; (void)a;
    if (fail_step == 1) return -2;
    *b = 1; ++live_buffers; return VK_SUCCESS;
}
static void destroy_buffer(VkDevice d, VkBuffer b, const void *a) { (void)d; (void)b; (void)a; --live_buffers; }
static void requirements(VkDevice d, VkBuffer b, VkMemoryRequirements *r) {
    (void)d; (void)b; r->size = 64; r->alignment = 8; r->memoryTypeBits = fail_step == 2 ? 0 : 1;
}
static VkResult allocate_memory(VkDevice d, const VkMemoryAllocateInfo *i, const void *a, VkDeviceMemory *m) {
    (void)d; (void)i; (void)a;
    if (fail_step == 3) return -2;
    *m = 1; ++live_memory; return VK_SUCCESS;
}
static void free_memory(VkDevice d, VkDeviceMemory m, const void *a) { (void)d; (void)m; (void)a; --live_memory; }
static VkResult bind_memory(VkDevice d, VkBuffer b, VkDeviceMemory m, VkDeviceSize o) {
    (void)d; (void)b; (void)m; (void)o; return fail_step == 4 ? -2 : VK_SUCCESS;
}
static VkResult map_memory(VkDevice d, VkDeviceMemory m, VkDeviceSize o, VkDeviceSize n, VkFlags f, void **p) {
    (void)d; (void)m; (void)o; (void)n; (void)f;
    if (fail_step == 5) return -2;
    *p = host; ++live_maps; return VK_SUCCESS;
}
static void unmap_memory(VkDevice d, VkDeviceMemory m) { (void)d; (void)m; --live_maps; }
int main(void) {
    tvdb_gpu_context_t ctx; memset(&ctx, 0, sizeof(ctx));
    ctx.device = (VkDevice)(uintptr_t)1;
    ctx.backend = TVDB_GPU_BACKEND_VULKAN;
    ctx.vk.CreateBuffer = create_buffer; ctx.vk.DestroyBuffer = destroy_buffer;
    ctx.vk.GetBufferMemoryRequirements = requirements; ctx.vk.AllocateMemory = allocate_memory;
    ctx.vk.FreeMemory = free_memory; ctx.vk.BindBufferMemory = bind_memory;
    ctx.vk.MapMemory = map_memory; ctx.vk.UnmapMemory = unmap_memory;
    ctx.memory_props.memoryTypeCount = 1;
    ctx.memory_props.memoryTypes[0].propertyFlags = VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT |
        VK_MEMORY_PROPERTY_HOST_COHERENT_BIT | VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT;
    for (int device = 0; device <= 1; ++device) {
        for (int step = 0; step <= (device ? 4 : 5); ++step) {
            fail_step = step;
            tvdb_vk_buffer buffer; tvdb_error_t error = {0};
            tvdb_status_t status = device ? tvdb_vk_create_device_buffer(&ctx, 64, &buffer, &error) :
                tvdb_vk_create_buffer(&ctx, 64, VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &buffer, &error);
            if ((step == 0) != (status == TVDB_OK)) return 1;
            if (step == 0) tvdb_vk_destroy_buffer(&ctx, &buffer);
            if (buffer.buffer || buffer.memory || buffer.mapped || live_buffers || live_memory || live_maps) {
                fprintf(stderr, "buffer cleanup failed: device=%d step=%d\n", device, step); return 1;
            }
        }
    }
    float data = 0;
    tvdb_gpu_binding_t binding = {(tvdb_gpu_binding_kind_t)99, &data, sizeof(data)};
    tvdb_gpu_dispatch_spec_t spec; memset(&spec, 0, sizeof(spec));
    spec.bindings = &binding; spec.num_bindings = 1;
    if (tvdb_gpu_dispatch(&ctx, &spec, NULL) != TVDB_ERROR_INVALID_ARGUMENT) return 1;
    return 0;
}
