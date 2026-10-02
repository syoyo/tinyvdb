/* Fake drivers exercise cleanup and backend selection without hardware. */
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
/* Stop at CUDA kernel lookup: reaching it proves SPIR-V did not gate CUDA. */
static int cuda_lookup_calls;
static CUresult fail_cuda_lookup(CUfunction* function, CUmodule module, const char* name) {
    (void)function;
    if (module != (CUmodule)(uintptr_t)1 || strcmp(name, "tvdb_cuda_comp")) return 1;
    ++cuda_lookup_calls;
    return 1; /* Inject a driver error before allocation or kernel execution. */
}
static int test_composite_backend_selection(void) {
    tvdb_gpu_context_t ctx; memset(&ctx, 0, sizeof(ctx));
    ctx.backend = TVDB_GPU_BACKEND_CUDA;
    ctx.cu_module = (CUmodule)(uintptr_t)1;
    ctx.cuda.cuModuleGetFunction = fail_cuda_lookup;
    float av = 2, bv = 3, value = 42;
    tvdb_dense_grid a = {0}, b = {0}, out = {0};
    a.nx = a.ny = a.nz = b.nx = b.ny = b.nz = out.nx = out.ny = out.nz = 1;
    a.voxel_size = b.voxel_size = out.voxel_size = 1;
    a.data = &av; b.data = &bv; out.data = &value;
    tvdb_status_t (*ops[])(tvdb_gpu_context_t*, const tvdb_dense_grid*,
        const tvdb_dense_grid*, tvdb_dense_grid*, tvdb_error_t*) = {
        tvdb_gpu_comp_max, tvdb_gpu_comp_min, tvdb_gpu_comp_sum, tvdb_gpu_comp_mult
    };
    for (size_t i = 0; i < sizeof(ops)/sizeof(ops[0]); ++i) {
        tvdb_error_t error = {0}; cuda_lookup_calls = 0;
        tvdb_status_t status = ops[i](&ctx, &a, &b, &out, &error);
        if (status != TVDB_ERROR_IO || error.status != status || cuda_lookup_calls != 1 || value != 42) {
            fprintf(stderr, "composite CUDA dispatch failed: op=%zu status=%d lookups=%d\n",
                i, (int)status, cuda_lookup_calls);
            return 1;
        }
        if (kTvdbGpuCompSpv_len == 0) {
            ctx.backend = TVDB_GPU_BACKEND_VULKAN;
            status = ops[i](&ctx, &a, &b, &out, &error);
            ctx.backend = TVDB_GPU_BACKEND_CUDA;
            if (status != TVDB_ERROR_UNIMPLEMENTED || value != 42 || cuda_lookup_calls != 1) return 1;
        }
    }
    return 0;
}
static int resident_live, resident_launches, resident_fail_launch, resident_pending, resident_early_free;
static int resident_alloc_calls,resident_fail_alloc,resident_poisson_probe;
static CUresult resident_alloc(CUdeviceptr* p,size_t n){if(++resident_alloc_calls==resident_fail_alloc)return 2;void* v=malloc(n);if(!v)return 2;*p=(CUdeviceptr)(uintptr_t)v;++resident_live;return 0;}
static CUresult resident_free(CUdeviceptr p){if(resident_pending)++resident_early_free;free((void*)(uintptr_t)p);--resident_live;return 0;}
static CUresult resident_upload(CUdeviceptr p,const void* src,size_t n){memcpy((void*)(uintptr_t)p,src,n);return 0;}
static CUresult resident_download(void* dst,CUdeviceptr p,size_t n){(void)p;memset(dst,0,n);return 0;}
static CUresult resident_lookup(CUfunction* f,CUmodule m,const char* name){(void)m;(void)name;*f=(CUfunction)(uintptr_t)1;return 0;}
static CUresult resident_launch(CUfunction f,unsigned int x,unsigned int y,unsigned int z,unsigned int bx,unsigned int by,unsigned int bz,unsigned int sh,void* stream,void** args,void** extra){
    (void)f;(void)x;(void)y;(void)z;(void)bx;(void)by;(void)bz;(void)sh;(void)stream;(void)extra;
    if(++resident_launches==resident_fail_launch)return 1;
    resident_pending=1;
    /* Deliberately clobber the scratch output before a subsequent launch fails. */
    CUdeviceptr dst=*(CUdeviceptr*)args[resident_poisson_probe?2:1];*(float*)(uintptr_t)dst=-99;return 0;
}
static CUresult resident_sync(void){resident_pending=0;return 0;}
static int test_poisson_failure(void){
    /* Failure at workspace/uniform allocation or any launch in the first batch
     * must retain the input/output handles and release every temporary. */
    for(int precision=0;precision<3;++precision)for(int allocation=0;allocation<=1;++allocation)
    for(int step=1;step<=(allocation?7:4);++step){
        tvdb_gpu_context_t ctx;memset(&ctx,0,sizeof(ctx));ctx.backend=TVDB_GPU_BACKEND_CUDA;ctx.cu_module=(CUmodule)(uintptr_t)1;
        ctx.cuda.cuMemAlloc=resident_alloc;ctx.cuda.cuMemFree=resident_free;ctx.cuda.cuMemcpyHtoD=resident_upload;ctx.cuda.cuMemcpyDtoH=resident_download;
        ctx.cuda.cuModuleGetFunction=resident_lookup;ctx.cuda.cuLaunchKernel=resident_launch;ctx.cuda.cuCtxSynchronize=resident_sync;
        tvdb_gpu_grid_desc_t desc={2,1,1,1,precision==2?TVDB_GPU_F64:TVDB_GPU_F32,0,0,0,1};
        tvdb_gpu_dense_grid_t *r=NULL,*x=NULL;size_t bytes=precision==2?16:8;
        float rf[2]={1,-1},xf[2]={42,42};double rd[2]={1,-1},xd[2]={42,42};
        resident_fail_alloc=0;resident_fail_launch=0;
        if(tvdb_gpu_dense_grid_create(&ctx,&desc,&r,NULL)!=TVDB_OK || tvdb_gpu_dense_grid_create(&ctx,&desc,&x,NULL)!=TVDB_OK)return 1;
        if(tvdb_gpu_dense_grid_upload(r,precision==2?(const void*)rd:(const void*)rf,bytes,NULL)!=TVDB_OK ||
           tvdb_gpu_dense_grid_upload(x,precision==2?(const void*)xd:(const void*)xf,bytes,NULL)!=TVDB_OK)return 1;
        resident_alloc_calls=resident_launches=0;resident_fail_alloc=allocation?step:0;resident_fail_launch=allocation?0:step;resident_poisson_probe=1;
        tvdb_gpu_buffer_t* original=x->values;tvdb_poisson_result_t result;
        if(tvdb_gpu_poisson_resident(&ctx,r,x,precision,2,1e-6,&result,NULL)!=TVDB_ERROR_IO || x->values!=original ||
           memcmp((void*)(uintptr_t)x->values->cu,precision==2?(const void*)xd:(const void*)xf,bytes) ||
           memcmp((void*)(uintptr_t)r->values->cu,precision==2?(const void*)rd:(const void*)rf,bytes) ||
           resident_live!=2 || ctx.resident_metrics.live_bytes!=2*bytes || resident_early_free)return 1;
        resident_poisson_probe=resident_fail_alloc=resident_fail_launch=0;
        tvdb_gpu_dense_grid_destroy(r);tvdb_gpu_dense_grid_destroy(x);
        if(resident_live || resident_pending || ctx.resident_metrics.live_bytes)return 1;
    }
    /* The shader uses uint word offsets; reject overflow before allocating. */
    for(int precision=0;precision<3;++precision){
        tvdb_gpu_context_t ctx;memset(&ctx,0,sizeof(ctx));ctx.backend=TVDB_GPU_BACKEND_CUDA;
        tvdb_gpu_dense_grid_t g;memset(&g,0,sizeof(g));g.ctx=&ctx;g.desc.channels=1;g.desc.voxel_size=1;
        g.desc.type=precision==2?TVDB_GPU_F64:TVDB_GPU_F32;
        g.count=UINT32_MAX/(precision==0?10u:precision==1?16u:18u)+1u;
        tvdb_poisson_result_t result;
        if(tvdb_gpu_poisson_resident(&ctx,&g,&g,precision,1,1e-6,&result,NULL)!=TVDB_ERROR_INVALID_ARGUMENT)return 1;
    }
    return 0;
}
static int test_resident_failure(void){
    for(int step=1;step<=3;++step){
        tvdb_gpu_context_t ctx;memset(&ctx,0,sizeof(ctx));ctx.backend=TVDB_GPU_BACKEND_CUDA;ctx.cu_module=(CUmodule)(uintptr_t)1;
        ctx.cuda.cuMemAlloc=resident_alloc;ctx.cuda.cuMemFree=resident_free;ctx.cuda.cuMemcpyHtoD=resident_upload;
        ctx.cuda.cuModuleGetFunction=resident_lookup;ctx.cuda.cuLaunchKernel=resident_launch;ctx.cuda.cuCtxSynchronize=resident_sync;
        tvdb_gpu_grid_desc_t desc={1,1,1,1,TVDB_GPU_F32,0,0,0,1};tvdb_gpu_dense_grid_t* g=NULL;
        if(tvdb_gpu_dense_grid_create(&ctx,&desc,&g,NULL)!=TVDB_OK)return 1;
        float value=42;if(tvdb_gpu_dense_grid_upload(g,&value,4,NULL)!=TVDB_OK)return 1;
        resident_launches=0;resident_fail_launch=step;tvdb_gpu_buffer_t* original=g->values;
        if(tvdb_gpu_filter_resident(&ctx,g,0,1,1,NULL)!=TVDB_ERROR_IO || g->values!=original || *(float*)(uintptr_t)original->cu!=42)return 1;
        tvdb_gpu_dense_grid_destroy(g);
        if(resident_live || resident_early_free || ctx.resident_metrics.live_bytes)return 1;
    }
    tvdb_gpu_context_t ctx;memset(&ctx,0,sizeof(ctx));ctx.backend=TVDB_GPU_BACKEND_VULKAN;
    tvdb_gpu_buffer_t* overflow=NULL;ctx.resident_metrics.live_bytes=SIZE_MAX;
    if(tvdb_gpu_buffer_create_device(&ctx,4,&overflow,NULL)!=TVDB_ERROR_INVALID_ARGUMENT || overflow)return 1;
    ctx.resident_metrics.live_bytes=0;
    tvdb_resident_topology* topology=NULL;
    if(resident_topology_alloc(&ctx,(size_t)(1u<<29)+1,&topology,NULL)!=TVDB_ERROR_INVALID_ARGUMENT || topology)return 1;
    ctx.pipeline_cache_count=TVDB_VK_PIPELINE_CACHE_MAX;
    uint32_t types[1]={VK_DESCRIPTOR_TYPE_STORAGE_BUFFER};tvdb_vk_pipeline_entry* pe=NULL;
    static const unsigned char code[4]={1,2,3,4};
    if(tvdb_vk_get_pipeline(&ctx,code,4,1,types,&pe,NULL,NULL)!=TVDB_ERROR_OUT_OF_MEMORY || pe)return 1;
    tvdb_gpu_resident_dispatch_t spec;memset(&spec,0,sizeof(spec));
    if(tvdb_gpu_dispatch_resident(&ctx,&spec,1,NULL)!=TVDB_ERROR_INVALID_ARGUMENT)return 1;
    return 0;
}
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
    return test_composite_backend_selection() || test_resident_failure() || test_poisson_failure();
}
