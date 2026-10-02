/* Included by tinyvdb_gpu.c: shared runtime-loaded backend implementation. */
static tvdb_status_t resident_error(tvdb_error_t* err, tvdb_status_t s, const char* msg) {
    tvdb_gpu_set_error(err, s, msg); return s;
}
void tvdb_gpu_resident_metrics(tvdb_gpu_context_t* ctx, tvdb_gpu_resident_metrics_t* out) {
    if (ctx && out) *out = ctx->resident_metrics;
}
void tvdb_gpu_resident_metrics_reset(tvdb_gpu_context_t* ctx) {
    if (!ctx) return;
    size_t live = ctx->resident_metrics.live_bytes;
    memset(&ctx->resident_metrics, 0, sizeof(ctx->resident_metrics));
    ctx->resident_metrics.live_bytes = ctx->resident_metrics.peak_bytes = live;
}
tvdb_status_t tvdb_gpu_buffer_create_device(tvdb_gpu_context_t* ctx, size_t size,
    tvdb_gpu_buffer_t** out, tvdb_error_t* err) {
    if (!ctx || !out || !size || size>SIZE_MAX-ctx->resident_metrics.live_bytes) return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resident buffer size");
    *out = NULL;
    tvdb_gpu_buffer_t* b = calloc(1,sizeof(*b));
    if (!b) return resident_error(err,TVDB_ERROR_OUT_OF_MEMORY,"resident buffer allocation failed");
    b->ctx=ctx; b->backend=ctx->backend; b->size=size;
    tvdb_status_t st = TVDB_OK;
    if (ctx->backend == TVDB_GPU_BACKEND_CUDA) {
        if (!tvdb_cuda_ok(ctx,err,"cuMemAlloc",ctx->cuda.cuMemAlloc(&b->cu,size))) st=TVDB_ERROR_IO;
    } else st=tvdb_vk_create_device_buffer(ctx,size,&b->vk,err);
    if (st != TVDB_OK) { free(b); return st; }
    b->resident=1; ++ctx->resident_metrics.allocations;
    ctx->resident_metrics.live_bytes += size;
    if(ctx->resident_metrics.live_bytes > ctx->resident_metrics.peak_bytes)
        ctx->resident_metrics.peak_bytes=ctx->resident_metrics.live_bytes;
    *out=b; return TVDB_OK;
}
static int resident_desc_valid(const tvdb_gpu_grid_desc_t* d, size_t* bytes, size_t* count) {
    size_t n, c;
    if (!d || (d->type!=TVDB_GPU_F32 && d->type!=TVDB_GPU_F64) ||
        (d->channels!=1 && d->channels!=3) || (d->type==TVDB_GPU_F64 && d->channels!=1) ||
        !isfinite(d->voxel_size) || d->voxel_size<=0 ||
        !isfinite(d->ox) || !isfinite(d->oy) || !isfinite(d->oz) ||
        !tvdb_grid_bytes(d->nx,d->ny,d->nz,1,&n) || n>INT_MAX ||
        !tvdb_size_mul(n,(size_t)d->channels,&c) || c>INT_MAX ||
        !tvdb_size_mul(c,d->type==TVDB_GPU_F64?8:4,bytes)) return 0;
    if(d->type==TVDB_GPU_F32 && (!isfinite((float)d->ox) || !isfinite((float)d->oy) || !isfinite((float)d->oz) ||
        !isfinite((float)d->voxel_size) || (float)d->voxel_size<=0))return 0;
    *count=n; return 1;
}
tvdb_status_t tvdb_gpu_dense_grid_create(tvdb_gpu_context_t* ctx, const tvdb_gpu_grid_desc_t* d,
    tvdb_gpu_dense_grid_t** out, tvdb_error_t* err) {
    size_t bytes,n;
    if (!ctx || !out || !resident_desc_valid(d,&bytes,&n)) return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resident grid descriptor");
    *out=NULL;
    tvdb_gpu_dense_grid_t* g=calloc(1,sizeof(*g));
    if(!g) return resident_error(err,TVDB_ERROR_OUT_OF_MEMORY,"resident grid allocation failed");
    g->ctx=ctx; g->desc=*d; g->count=n; g->bytes=bytes;
    tvdb_status_t st=tvdb_gpu_buffer_create_device(ctx,bytes?bytes:4,&g->values,err);
    if(st!=TVDB_OK) { free(g); return st; }
    *out=g; return TVDB_OK;
}
void tvdb_gpu_dense_grid_destroy(tvdb_gpu_dense_grid_t* g) {
    if(!g) return;
    tvdb_gpu_buffer_destroy(g->values);
    for(int i=0;i<3;++i) tvdb_gpu_buffer_destroy(g->scratch[i]);
    free(g);
}
tvdb_status_t tvdb_gpu_dense_grid_upload(tvdb_gpu_dense_grid_t* g,const void* data,size_t bytes,tvdb_error_t* err) {
    if(!g || bytes!=g->bytes || (bytes && !data)) return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"resident upload size mismatch");
    return bytes ? tvdb_gpu_buffer_upload(g->values,data,bytes,err) : TVDB_OK;
}
tvdb_status_t tvdb_gpu_dense_grid_download(const tvdb_gpu_dense_grid_t* g,void* data,size_t bytes,tvdb_error_t* err) {
    if(!g || bytes!=g->bytes || (bytes && !data)) return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"resident download size mismatch");
    return bytes ? tvdb_gpu_buffer_download(g->values,data,bytes,err) : TVDB_OK;
}
tvdb_status_t tvdb_gpu_dense_grid_description(const tvdb_gpu_dense_grid_t* g,tvdb_gpu_grid_desc_t* d) {
    if(!g || !d) return TVDB_ERROR_INVALID_ARGUMENT;
    *d=g->desc; return TVDB_OK;
}
tvdb_gpu_buffer_t* tvdb_gpu_dense_grid_buffer(const tvdb_gpu_dense_grid_t* g) { return g?g->values:NULL; }

/* Vulkan resources are retained until the entire command buffer completes. */
typedef struct {
    tvdb_gpu_buffer_t* uniforms[8];
    tvdb_gpu_buffer_t* buffers[8];
    VkDescriptorSet set;
    tvdb_vk_pipeline_entry* pipeline;
} resident_dispatch_resources;

tvdb_status_t tvdb_gpu_dispatch_resident(tvdb_gpu_context_t* ctx,
    const tvdb_gpu_resident_dispatch_t* specs,size_t count,tvdb_error_t* err) {
    if(!ctx || (count && !specs) || count>1024)
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resident dispatch batch");
    if(!count) return TVDB_OK;
    /* Validate the entire batch before any device work. */
    for(size_t j=0;j<count;++j) {
        const tvdb_gpu_resident_dispatch_t* s=&specs[j];
        if(!s->num_bindings || s->num_bindings>8 || !s->groups[0] || !s->groups[1] || !s->groups[2] ||
           !s->local_size[0] || !s->local_size[1] || !s->local_size[2] ||
           (uint64_t)s->local_size[0]*s->local_size[1]*s->local_size[2]>1024)
            return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resident dispatch shape");
        if(ctx->backend==TVDB_GPU_BACKEND_VULKAN && (!s->spv || !s->spv_len))
            return resident_error(err,TVDB_ERROR_UNIMPLEMENTED,"resident SPIR-V unavailable");
        if(ctx->backend==TVDB_GPU_BACKEND_CUDA && !s->cuda_kernel)
            return resident_error(err,TVDB_ERROR_UNIMPLEMENTED,"resident CUDA kernel unavailable");
        for(unsigned i=0;i<s->num_bindings;++i) {
            const tvdb_gpu_resident_binding_t* b=&s->bindings[i];
            if(b->buffer ? (b->uniform || b->uniform_size || b->buffer->ctx!=ctx) : (!b->uniform || !b->uniform_size))
                return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resident binding or context");
        }
    }
    resident_dispatch_resources* r=calloc(count,sizeof(*r));
    if(!r) return resident_error(err,TVDB_ERROR_OUT_OF_MEMORY,"resident batch allocation failed");
    tvdb_status_t st=TVDB_OK;
    VkCommandBuffer cmd=NULL; VkFence fence=0; VkCommandPool pool=0;
    int submitted=0, cuda_launched=0;
    CUmodule module=NULL;
    if(ctx->backend==TVDB_GPU_BACKEND_CUDA) {
        st=tvdb_cuda_get_module(ctx,&module,err);
        if(st!=TVDB_OK) goto done;
    } else {
        st=tvdb_vk_drain_pending(ctx,err);
        if(st!=TVDB_OK) goto done;
        st=tvdb_vk_ensure_pools(ctx,err);
        if(st!=TVDB_OK) goto done;
        pool=ctx->cmd_pool;
        VkCommandBufferAllocateInfo ai; memset(&ai,0,sizeof(ai));
        ai.sType=VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO; ai.commandPool=pool;
        ai.level=VK_COMMAND_BUFFER_LEVEL_PRIMARY; ai.commandBufferCount=1;
        if(!tvdb_vk_ok(ctx->vk.AllocateCommandBuffers(ctx->device,&ai,&cmd),err,"resident command allocation")) {st=TVDB_ERROR_IO;goto done;}
        VkCommandBufferBeginInfo bi;memset(&bi,0,sizeof(bi));bi.sType=VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;
        if(!tvdb_vk_ok(ctx->vk.BeginCommandBuffer(cmd,&bi),err,"resident begin")) {st=TVDB_ERROR_IO;goto done;}
    }
    for(size_t j=0;j<count;++j) {
        const tvdb_gpu_resident_dispatch_t* s=&specs[j];
        tvdb_gpu_buffer_t** buffers=r[j].buffers;
        for(unsigned i=0;i<s->num_bindings;++i) {
            const tvdb_gpu_resident_binding_t* b=&s->bindings[i];
            buffers[i]=b->buffer;
            if(!buffers[i]) {
                if(ctx->backend==TVDB_GPU_BACKEND_CUDA) {
                    st=tvdb_gpu_buffer_create_device(ctx,b->uniform_size,&r[j].uniforms[i],err);
                } else {
                    r[j].uniforms[i]=calloc(1,sizeof(tvdb_gpu_buffer_t));
                    if(!r[j].uniforms[i]) {st=resident_error(err,TVDB_ERROR_OUT_OF_MEMORY,"resident uniform allocation failed");goto done;}
                    r[j].uniforms[i]->ctx=ctx; r[j].uniforms[i]->backend=ctx->backend;
                    st=tvdb_vk_create_buffer(ctx,b->uniform_size,VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT,&r[j].uniforms[i]->vk,err);
                    r[j].uniforms[i]->size=b->uniform_size;
                }
                if(st!=TVDB_OK) goto done;
                buffers[i]=r[j].uniforms[i];
                st=tvdb_gpu_buffer_upload(buffers[i],b->uniform,b->uniform_size,err);
                if(st!=TVDB_OK) goto done;
            }
        }
    }
    /* Upload every uniform before launching CUDA work: a blocking upload between
       launches otherwise serializes the stream once per pass. */
    for(size_t j=0;j<count;++j) {
        const tvdb_gpu_resident_dispatch_t* s=&specs[j];
        tvdb_gpu_buffer_t** buffers=r[j].buffers;
        uint32_t types[8];
        for(unsigned i=0;i<s->num_bindings;++i)
            types[i]=s->bindings[i].buffer?VK_DESCRIPTOR_TYPE_STORAGE_BUFFER:VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
        if(ctx->backend==TVDB_GPU_BACKEND_CUDA) {
            CUfunction fn=NULL; void* args[8];
            for(unsigned i=0;i<s->num_bindings;++i) args[i]=&buffers[i]->cu;
            if(!tvdb_cuda_ok(ctx,err,"resident kernel lookup",ctx->cuda.cuModuleGetFunction(&fn,module,s->cuda_kernel)) ||
               !tvdb_cuda_ok(ctx,err,"resident kernel launch",ctx->cuda.cuLaunchKernel(fn,s->groups[0],s->groups[1],s->groups[2],
                    s->local_size[0],s->local_size[1],s->local_size[2],0,NULL,args,NULL))) {st=TVDB_ERROR_IO;goto done;}
            cuda_launched=1;
        } else {
            int cached=0;
            st=tvdb_vk_get_pipeline(ctx,s->spv,s->spv_len,s->num_bindings,types,&r[j].pipeline,&cached,err);
            if(st!=TVDB_OK) goto done;
            VkDescriptorSetAllocateInfo ai;memset(&ai,0,sizeof(ai));ai.sType=VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
            ai.descriptorPool=ctx->desc_pool;ai.descriptorSetCount=1;ai.pSetLayouts=&r[j].pipeline->set_layout;
            if(!tvdb_vk_ok(ctx->vk.AllocateDescriptorSets(ctx->device,&ai,&r[j].set),err,"resident descriptors")) {st=TVDB_ERROR_IO;goto done;}
            VkDescriptorBufferInfo info[8]; VkWriteDescriptorSet writes[8]; VkBufferMemoryBarrier barriers[8];
            memset(info,0,sizeof(info));memset(writes,0,sizeof(writes));memset(barriers,0,sizeof(barriers));
            for(unsigned i=0;i<s->num_bindings;++i) {
                info[i].buffer=buffers[i]->vk.buffer; info[i].range=buffers[i]->size;
                writes[i].sType=VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;writes[i].dstSet=r[j].set;
                writes[i].dstBinding=i;writes[i].descriptorCount=1;writes[i].descriptorType=types[i];writes[i].pBufferInfo=&info[i];
                barriers[i].sType=VK_STRUCTURE_TYPE_BUFFER_MEMORY_BARRIER;
                barriers[i].srcAccessMask=VK_ACCESS_SHADER_WRITE_BIT|VK_ACCESS_TRANSFER_WRITE_BIT|VK_ACCESS_HOST_WRITE_BIT;
                barriers[i].dstAccessMask=VK_ACCESS_SHADER_READ_BIT|VK_ACCESS_SHADER_WRITE_BIT|VK_ACCESS_UNIFORM_READ_BIT;
                barriers[i].srcQueueFamilyIndex=barriers[i].dstQueueFamilyIndex=VK_QUEUE_FAMILY_IGNORED;
                barriers[i].buffer=info[i].buffer;barriers[i].size=info[i].range;
            }
            ctx->vk.UpdateDescriptorSets(ctx->device,s->num_bindings,writes,0,NULL);
            ctx->vk.CmdPipelineBarrier(cmd,VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT|VK_PIPELINE_STAGE_TRANSFER_BIT|VK_PIPELINE_STAGE_HOST_BIT,
                VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,0,0,NULL,s->num_bindings,barriers,0,NULL);
            ctx->vk.CmdBindPipeline(cmd,VK_PIPELINE_BIND_POINT_COMPUTE,r[j].pipeline->pipeline);
            ctx->vk.CmdBindDescriptorSets(cmd,VK_PIPELINE_BIND_POINT_COMPUTE,r[j].pipeline->pipeline_layout,0,1,&r[j].set,0,NULL);
            ctx->vk.CmdDispatch(cmd,s->groups[0],s->groups[1],s->groups[2]);
        }
    }
    if(ctx->backend==TVDB_GPU_BACKEND_CUDA) {
        if(!tvdb_cuda_ok(ctx,err,"resident synchronize",ctx->cuda.cuCtxSynchronize())) st=TVDB_ERROR_IO;
        cuda_launched=0;
        ++ctx->resident_metrics.submissions;
    } else {
        if(!tvdb_vk_ok(ctx->vk.EndCommandBuffer(cmd),err,"resident end")) {st=TVDB_ERROR_IO;goto done;}
        VkFenceCreateInfo fi;memset(&fi,0,sizeof(fi));fi.sType=VK_STRUCTURE_TYPE_FENCE_CREATE_INFO;
        if(!tvdb_vk_ok(ctx->vk.CreateFence(ctx->device,&fi,NULL,&fence),err,"resident fence")) {st=TVDB_ERROR_IO;goto done;}
        VkSubmitInfo si;memset(&si,0,sizeof(si));si.sType=VK_STRUCTURE_TYPE_SUBMIT_INFO;si.commandBufferCount=1;si.pCommandBuffers=&cmd;
        if(!tvdb_vk_ok(ctx->vk.QueueSubmit(ctx->queue,1,&si,fence),err,"resident submit")) {st=TVDB_ERROR_IO;goto done;}
        submitted=1; ++ctx->resident_metrics.submissions;
        if(!tvdb_vk_ok(ctx->vk.WaitForFences(ctx->device,1,&fence,VK_TRUE,UINT64_MAX),err,"resident wait")) st=TVDB_ERROR_IO;
    }
done:
    if(cuda_launched) ctx->cuda.cuCtxSynchronize();
    if(submitted && st!=TVDB_OK) ctx->vk.DeviceWaitIdle(ctx->device);
    if(cmd) ctx->vk.FreeCommandBuffers(ctx->device,pool,1,&cmd);
    if(fence) ctx->vk.DestroyFence(ctx->device,fence,NULL);
    for(size_t j=0;j<count;++j) {
        if(r[j].set) ctx->vk.FreeDescriptorSets(ctx->device,ctx->desc_pool,1,&r[j].set);
        for(int i=0;i<8;++i) tvdb_gpu_buffer_destroy(r[j].uniforms[i]);
    }
    free(r);return st;
}
static int resident_same(const tvdb_gpu_dense_grid_t* a,const tvdb_gpu_dense_grid_t* b) {
    return a && b && a->ctx==b->ctx && a->desc.nx==b->desc.nx && a->desc.ny==b->desc.ny && a->desc.nz==b->desc.nz &&
        a->desc.channels==b->desc.channels && a->desc.type==b->desc.type;
}
static tvdb_status_t resident_scratch(tvdb_gpu_dense_grid_t* g,int slot,tvdb_error_t* err) {
    return g->scratch[slot] ? TVDB_OK : tvdb_gpu_buffer_create_device(g->ctx,g->bytes?g->bytes:4,&g->scratch[slot],err);
}
static void resident_commit(tvdb_gpu_dense_grid_t* g,int slot) {
    tvdb_gpu_buffer_t* old=g->values;g->values=g->scratch[slot];g->scratch[slot]=old;
}
static void resident_spec(tvdb_gpu_resident_dispatch_t* s,const unsigned char* spv,unsigned len,const char* kernel,
    unsigned local,size_t n,unsigned bindings) {
    memset(s,0,sizeof(*s));s->spv=spv;s->spv_len=len;s->cuda_kernel=kernel;s->num_bindings=bindings;
    s->groups[0]=(unsigned)((n+local-1)/local);s->groups[1]=s->groups[2]=1;
    /* Linear kernels flatten the second dispatch axis. Stay within Vulkan's
       guaranteed workgroup-count limit, including software implementations. */
    if(local!=8 && s->groups[0]>65535u){unsigned groups=s->groups[0];s->groups[0]=65535u;s->groups[1]=(groups+65534u)/65535u;}
    s->local_size[0]=local;s->local_size[1]=s->local_size[2]=1;
}
tvdb_status_t tvdb_gpu_comp_resident(tvdb_gpu_context_t* ctx,const tvdb_gpu_dense_grid_t* a,
    const tvdb_gpu_dense_grid_t* b,int op,tvdb_gpu_dense_grid_t* out,tvdb_error_t* err) {
    if(!ctx || !resident_same(a,b) || !resident_same(a,out) || a->ctx!=ctx || a->desc.type!=TVDB_GPU_F32 || op<0 || op>3)
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"resident comp shape/type/context mismatch");
    if(!a->count) return TVDB_OK;
    tvdb_status_t st=resident_scratch(out,0,err);if(st!=TVDB_OK)return st;
    int32_t u[4]={a->desc.nx,a->desc.ny,a->desc.nz*a->desc.channels,op};
    tvdb_gpu_resident_dispatch_t s;resident_spec(&s,kTvdbGpuCompSpv,kTvdbGpuCompSpv_len,"tvdb_cuda_comp",64,a->count*a->desc.channels,4);
    s.bindings[0].buffer=a->values;s.bindings[1].buffer=b->values;s.bindings[2].buffer=out->scratch[0];
    s.bindings[3].uniform=u;s.bindings[3].uniform_size=sizeof(u);
    st=tvdb_gpu_dispatch_resident(ctx,&s,1,err);if(st==TVDB_OK)resident_commit(out,0);return st;
}

tvdb_status_t tvdb_gpu_filter_resident(tvdb_gpu_context_t* ctx,tvdb_gpu_dense_grid_t* g,
    int kind,int width,int iterations,tvdb_error_t* err) {
    if(!ctx || !g || g->ctx!=ctx || g->desc.type!=TVDB_GPU_F32 || g->desc.channels!=1 || kind<0 || kind>3)
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resident filter");
    if(!g->count || iterations<=0 || (kind!=2 && width<=0)) return TVDB_OK;
    if(kind==3 && width>2) return resident_error(err,TVDB_ERROR_UNIMPLEMENTED,"resident median radius exceeds 2");
    if(width>(INT_MAX-1)/2) return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"resident filter width overflow");
    tvdb_status_t st=resident_scratch(g,0,err);if(st!=TVDB_OK)return st;
    st=resident_scratch(g,1,err);if(st!=TVDB_OK)return st;
    tvdb_gpu_buffer_t* kernel=NULL;
    if(kind<2) {
        size_t len=(size_t)width*2+1;
        float* k=malloc(len*sizeof(float));
        if(!k)return resident_error(err,TVDB_ERROR_OUT_OF_MEMORY,"filter weights allocation failed");
        float sum=0,sigma=width*0.5f,two=2*sigma*sigma;
        for(int i=-width;i<=width;++i) {float v=kind==0?1.0f/(float)len:expf(-((float)i*(float)i)/two);k[i+width]=v;sum+=v;}
        if(kind==1)for(size_t i=0;i<len;++i)k[i]/=sum;
        st=tvdb_gpu_buffer_create_device(ctx,len*sizeof(float),&kernel,err);
        if(st==TVDB_OK)st=tvdb_gpu_buffer_upload(kernel,k,len*sizeof(float),err);
        free(k);if(st!=TVDB_OK){tvdb_gpu_buffer_destroy(kernel);return st;}
    }
    typedef struct { int32_t dim[4],cfg[4];float inv_h,dt;uint32_t nvox,pad; } params;
    tvdb_gpu_resident_dispatch_t specs[96];params u[96];
    size_t passes=(size_t)iterations*(kind<2?3u:1u),step=0;
    tvdb_gpu_buffer_t* current=g->values;
    while(step<passes && st==TVDB_OK) {
        size_t count=passes-step;if(count>96)count=96;
        for(size_t j=0;j<count;++j) {
            size_t p=step+j;
            memset(&u[j],0,sizeof(u[j]));u[j].dim[0]=g->desc.nx;u[j].dim[1]=g->desc.ny;u[j].dim[2]=g->desc.nz;
            u[j].dim[3]=kind<2?0:kind==2?1:3;u[j].cfg[0]=(int)(p%3);u[j].cfg[1]=kind==2?0:width;u[j].nvox=(uint32_t)g->count;
            resident_spec(&specs[j],kTvdbGpuFilterSpv,kTvdbGpuFilterSpv_len,"tvdb_cuda_filter",32,g->count,5);
            specs[j].bindings[0].buffer=current;specs[j].bindings[1].buffer=g->scratch[p%2];
            specs[j].bindings[2].buffer=current;specs[j].bindings[3].buffer=kernel?kernel:current;
            specs[j].bindings[4].uniform=&u[j];specs[j].bindings[4].uniform_size=sizeof(params);
            current=g->scratch[p%2];
        }
        st=tvdb_gpu_dispatch_resident(ctx,specs,count,err);step+=count;
    }
    if(st==TVDB_OK)resident_commit(g,(int)((passes-1)%2));
    tvdb_gpu_buffer_destroy(kernel);return st;
}

/* In-place exclusive scan. Only the four-byte total leaves the device. */
static tvdb_status_t resident_scan(tvdb_gpu_context_t* ctx,tvdb_gpu_buffer_t* data,
    uint32_t n,uint32_t* total,tvdb_error_t* err) {
    tvdb_gpu_buffer_t* levels[8]={data};uint32_t sizes[8]={n};
    tvdb_gpu_resident_dispatch_t specs[16];uint32_t params[16][4];
    int depth=0,ns=0;tvdb_status_t st=TVDB_OK;
    if(!n){*total=0;return TVDB_OK;}
    do {
        uint32_t groups=(sizes[depth]+127u)/128u;
        st=tvdb_gpu_buffer_create_device(ctx,(size_t)groups*4,&levels[depth+1],err);
        if(st!=TVDB_OK)goto done;
        params[ns][0]=sizes[depth];params[ns][1]=0;params[ns][2]=params[ns][3]=0;
        resident_spec(&specs[ns],kTvdbGpuScanSpv,kTvdbGpuScanSpv_len,"tvdb_cuda_scan",128,sizes[depth],3);
        specs[ns].bindings[0].buffer=levels[depth];specs[ns].bindings[1].buffer=levels[depth+1];
        specs[ns].bindings[2].uniform=params[ns];specs[ns].bindings[2].uniform_size=16;++ns;
        sizes[++depth]=groups;
    }while(sizes[depth]>1);
    for(int k=depth-2;k>=0;--k) {
        params[ns][0]=sizes[k];params[ns][1]=1;params[ns][2]=params[ns][3]=0;
        resident_spec(&specs[ns],kTvdbGpuScanSpv,kTvdbGpuScanSpv_len,"tvdb_cuda_scan",128,sizes[k],3);
        specs[ns].bindings[0].buffer=levels[k];specs[ns].bindings[1].buffer=levels[k+1];
        specs[ns].bindings[2].uniform=params[ns];specs[ns].bindings[2].uniform_size=16;++ns;
    }
    st=tvdb_gpu_dispatch_resident(ctx,specs,(size_t)ns,err);
    if(st==TVDB_OK)st=tvdb_gpu_buffer_download(levels[depth],total,4,err);
done:
    for(int k=1;k<8;++k)tvdb_gpu_buffer_destroy(levels[k]);
    return st;
}

tvdb_status_t tvdb_gpu_marching_cubes_resident(tvdb_gpu_context_t* ctx,const tvdb_gpu_dense_grid_t* g,
    float iso,tvdb_gpu_buffer_t** output,size_t* triangle_count,tvdb_error_t* err) {
    if(!ctx || !g || g->ctx!=ctx || !output || !triangle_count || g->desc.type!=TVDB_GPU_F32 ||
       g->desc.channels!=1 || g->desc.nx<2 || g->desc.ny<2 || g->desc.nz<2 || !isfinite(iso))
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resident marching cubes input");
    size_t cells=(size_t)(g->desc.nx-1)*(g->desc.ny-1)*(g->desc.nz-1);
    if(cells>UINT32_MAX/5u)return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"marching cubes scan overflow");
    int32_t table[256+256*16];
    memcpy(table,tvdb_mc_edge_table(),256*4);memcpy(table+256,tvdb_mc_tri_table_flat(),256*16*4);
    tvdb_gpu_buffer_t *offsets=NULL,*tables=NULL,*mesh=NULL;
    tvdb_status_t st=tvdb_gpu_buffer_create_device(ctx,cells*4,&offsets,err);
    if(st!=TVDB_OK)goto done;
    st=tvdb_gpu_buffer_create_device(ctx,sizeof(table),&tables,err);if(st!=TVDB_OK)goto done;
    st=tvdb_gpu_buffer_upload(tables,table,sizeof(table),err);if(st!=TVDB_OK)goto done;
    struct {int32_t dim[4];float origin[4];float iso;uint32_t cells,mode,pad;} u;
    memset(&u,0,sizeof(u));u.dim[0]=g->desc.nx;u.dim[1]=g->desc.ny;u.dim[2]=g->desc.nz;
    u.origin[0]=(float)g->desc.ox;u.origin[1]=(float)g->desc.oy;u.origin[2]=(float)g->desc.oz;u.origin[3]=(float)g->desc.voxel_size;
    u.iso=iso;u.cells=(uint32_t)cells;
    tvdb_gpu_resident_dispatch_t s;
    resident_spec(&s,kTvdbGpuMarchingCubesSpv,kTvdbGpuMarchingCubesSpv_len,"tvdb_cuda_marching_cubes_resident",64,cells,5);
    s.bindings[0].buffer=g->values;s.bindings[1].buffer=tables;
    s.bindings[2].buffer=offsets;s.bindings[3].buffer=offsets;
    s.bindings[4].uniform=&u;s.bindings[4].uniform_size=sizeof(u);
    st=tvdb_gpu_dispatch_resident(ctx,&s,1,err);if(st!=TVDB_OK)goto done;
    uint32_t total=0;st=resident_scan(ctx,offsets,(uint32_t)cells,&total,err);if(st!=TVDB_OK)goto done;
    size_t bytes;
    if(total>UINT32_MAX/9u || !tvdb_size_mul((size_t)total,36,&bytes)) {st=resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"mesh output indexing overflow");goto done;}
    st=tvdb_gpu_buffer_create_device(ctx,bytes?bytes:4,&mesh,err);if(st!=TVDB_OK)goto done;
    if(total) {
        u.mode=1;s.bindings[2].buffer=mesh;
        st=tvdb_gpu_dispatch_resident(ctx,&s,1,err);if(st!=TVDB_OK)goto done;
    }
    *output=mesh;*triangle_count=total;mesh=NULL;
done:
    tvdb_gpu_buffer_destroy(mesh);tvdb_gpu_buffer_destroy(offsets);tvdb_gpu_buffer_destroy(tables);return st;
}
static int resident_shape(const tvdb_gpu_dense_grid_t* a,const tvdb_gpu_dense_grid_t* b) {
    return a && b && a->ctx==b->ctx && a->desc.nx==b->desc.nx && a->desc.ny==b->desc.ny && a->desc.nz==b->desc.nz;
}
tvdb_status_t tvdb_gpu_stencil_resident(tvdb_gpu_context_t* ctx,const tvdb_gpu_dense_grid_t* in,
    int op,tvdb_gpu_dense_grid_t* out,tvdb_error_t* err) {
    if(!ctx || !resident_shape(in,out) || in->ctx!=ctx || in->desc.type!=out->desc.type || op<0 ||
       op>(in->desc.channels==1 && out->desc.channels==1?3:1))
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resident stencil");
    int fp64=in->desc.type==TVDB_GPU_F64;
    if(fp64 && !tvdb_gpu_supports_fp64(ctx))return resident_error(err,TVDB_ERROR_UNIMPLEMENTED,"device lacks fp64");
    if(!in->count)return TVDB_OK;
    tvdb_status_t st=resident_scratch(out,0,err);if(st!=TVDB_OK)return st;
    const unsigned char* spv;unsigned len;const char* kernel;
    if(fp64){spv=kTvdbGpuStencilScalarDSpv;len=kTvdbGpuStencilScalarDSpv_len;kernel="tvdb_cuda_stencil_scalar_d_resident";}
    else if(in->desc.channels==1 && out->desc.channels==1){spv=kTvdbGpuStencilScalarScalarSpv;len=kTvdbGpuStencilScalarScalarSpv_len;kernel="tvdb_cuda_stencil_scalar_scalar_resident";}
    else if(in->desc.channels==1){spv=kTvdbGpuStencilScalarVecSpv;len=kTvdbGpuStencilScalarVecSpv_len;kernel="tvdb_cuda_stencil_scalar_vec_resident";}
    else if(out->desc.channels==1){spv=kTvdbGpuStencilVecScalarSpv;len=kTvdbGpuStencilVecScalarSpv_len;kernel="tvdb_cuda_stencil_vec_scalar_resident";}
    else {spv=kTvdbGpuStencilVecVecSpv;len=kTvdbGpuStencilVecVecSpv_len;kernel="tvdb_cuda_stencil_vec_vec_resident";}
    unsigned char u[48]={0};int32_t dim[4]={in->desc.nx,in->desc.ny,in->desc.nz,op};memcpy(u,dim,16);
    double h=in->desc.voxel_size,scale=in->desc.channels==1 && out->desc.channels==1 && op==0 ? 1/(h*h):1/(2*h);
    if(fp64)memcpy(u+16,&scale,8);else{float f=(float)scale;memcpy(u+16,&f,4);}
    float origin[4]={(float)in->desc.ox,(float)in->desc.oy,(float)in->desc.oz,(float)h};memcpy(u+32,origin,16);
    tvdb_gpu_resident_dispatch_t s;resident_spec(&s,spv,len,kernel,8,in->desc.nx,3);
    s.groups[1]=((unsigned)in->desc.ny+7)/8;s.groups[2]=(unsigned)in->desc.nz;s.local_size[1]=8;
    s.bindings[0].buffer=in->values;s.bindings[1].buffer=out->scratch[0];s.bindings[2].uniform=u;s.bindings[2].uniform_size=48;
    st=tvdb_gpu_dispatch_resident(ctx,&s,1,err);
    if(st==TVDB_OK){resident_commit(out,0);tvdb_gpu_grid_desc_t d=in->desc;d.channels=out->desc.channels;out->desc=d;}
    return st;
}
tvdb_status_t tvdb_gpu_csg_resident(tvdb_gpu_context_t* ctx,const tvdb_gpu_dense_grid_t* a,
    const tvdb_gpu_dense_grid_t* b,int op,tvdb_gpu_dense_grid_t* out,tvdb_error_t* err) {
    if(!ctx || !resident_same(a,b) || !resident_same(a,out) || a->ctx!=ctx || a->desc.channels!=1 || op<0 || op>2)
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resident CSG");
    int d=a->desc.type==TVDB_GPU_F64;
    if(d && !tvdb_gpu_supports_fp64(ctx))return resident_error(err,TVDB_ERROR_UNIMPLEMENTED,"device lacks fp64");
    if(!a->count)return TVDB_OK;
    tvdb_status_t st=resident_scratch(out,0,err);if(st!=TVDB_OK)return st;
    int32_t u[4]={(int32_t)a->count,op,0,0};tvdb_gpu_resident_dispatch_t s;
    resident_spec(&s,d?kTvdbGpuCsgDSpv:kTvdbGpuCsgSpv,d?kTvdbGpuCsgDSpv_len:kTvdbGpuCsgSpv_len,
        d?"tvdb_cuda_csg_d_resident":"tvdb_cuda_csg_resident",d?8:256,d?(size_t)a->desc.nx:a->count,4);
    if(d){u[0]=a->desc.nx;u[1]=a->desc.ny;u[2]=a->desc.nz;u[3]=op;s.groups[1]=((unsigned)a->desc.ny+7)/8;s.groups[2]=a->desc.nz;s.local_size[1]=8;}
    s.bindings[0].buffer=a->values;s.bindings[1].buffer=b->values;s.bindings[2].buffer=out->scratch[0];s.bindings[3].uniform=u;s.bindings[3].uniform_size=16;
    st=tvdb_gpu_dispatch_resident(ctx,&s,1,err);if(st==TVDB_OK)resident_commit(out,0);return st;
}
tvdb_status_t tvdb_gpu_morph_resident(tvdb_gpu_context_t* ctx,tvdb_gpu_dense_grid_t* g,int kind,int iterations,tvdb_error_t* err) {
    if(!ctx || !g || g->ctx!=ctx || g->desc.channels!=1 || g->desc.type!=TVDB_GPU_F32 || kind<0 || kind>3)
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resident morphology");
    if(iterations<=0 || !g->count)return TVDB_OK;
    tvdb_status_t st=resident_scratch(g,0,err);if(st!=TVDB_OK)return st;
    st=resident_scratch(g,1,err);if(st!=TVDB_OK)return st;
    size_t total=(size_t)iterations*(kind>=2?2:1),step=0;tvdb_gpu_buffer_t* current=g->values;
    tvdb_gpu_resident_dispatch_t specs[96];int32_t u[96][8];
    while(step<total && st==TVDB_OK){size_t n=total-step;if(n>96)n=96;
      for(size_t j=0;j<n;++j){size_t p=step+j;memset(u[j],0,sizeof(u[j]));u[j][0]=g->desc.nx;u[j][1]=g->desc.ny;u[j][2]=g->desc.nz;
        u[j][4]=kind==0 || (kind==2 && p>=(size_t)iterations) || (kind==3 && p<(size_t)iterations);
        resident_spec(&specs[j],kTvdbGpuMorphSpv,kTvdbGpuMorphSpv_len,"tvdb_cuda_morph_resident",128,g->count,3);
        specs[j].bindings[0].buffer=current;specs[j].bindings[1].buffer=g->scratch[p%2];specs[j].bindings[2].uniform=u[j];specs[j].bindings[2].uniform_size=32;
        current=g->scratch[p%2];}
      st=tvdb_gpu_dispatch_resident(ctx,specs,n,err);step+=n;}
    if(st==TVDB_OK)resident_commit(g,(int)((total-1)%2));return st;
}
tvdb_status_t tvdb_gpu_resample_resident(tvdb_gpu_context_t* ctx,const tvdb_gpu_dense_grid_t* in,int factor,int refine,
    tvdb_gpu_dense_grid_t* out,tvdb_error_t* err) {
    if(!ctx || !in || !out || in->ctx!=ctx || out->ctx!=ctx || factor<1 || in->desc.type!=TVDB_GPU_F32 ||
       out->desc.type!=TVDB_GPU_F32 || in->desc.channels!=1 || out->desc.channels!=1)
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resident resample");
    double spacing=refine?in->desc.voxel_size/factor:in->desc.voxel_size*factor;
    if(!isfinite((float)spacing) || (float)spacing<=0)return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"resampled spacing out of range");
    int32_t u[20]={in->desc.nx,in->desc.ny,in->desc.nz,0,out->desc.nx,out->desc.ny,out->desc.nz,0,factor,0,0,0};
    for(int i=0;i<3;++i)if((refine?(int64_t)u[i]*factor:((int64_t)u[i]+factor-1)/factor)!=u[4+i])
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"resident resample shape mismatch");
    if(refine) {
      float f[12]={(float)in->desc.ox,(float)in->desc.oy,(float)in->desc.oz,0,
        (float)in->desc.ox,(float)in->desc.oy,(float)in->desc.oz,0,
        (float)in->desc.voxel_size,(float)(in->desc.voxel_size/factor),0,0};
      memcpy(u+8,f,sizeof(f));
    }
    if(!out->count)return TVDB_OK;
    tvdb_status_t st=resident_scratch(out,0,err);if(st!=TVDB_OK)return st;
    tvdb_gpu_resident_dispatch_t s;resident_spec(&s,refine?kTvdbGpuRefineSpv:kTvdbGpuCoarsenSpv,
        refine?kTvdbGpuRefineSpv_len:kTvdbGpuCoarsenSpv_len,refine?"tvdb_cuda_refine_resident":"tvdb_cuda_coarsen_resident",128,out->count,3);
    s.bindings[0].buffer=in->values;s.bindings[1].buffer=out->scratch[0];s.bindings[2].uniform=u;s.bindings[2].uniform_size=sizeof(u);
    st=tvdb_gpu_dispatch_resident(ctx,&s,1,err);if(st==TVDB_OK){resident_commit(out,0);out->desc.ox=in->desc.ox;out->desc.oy=in->desc.oy;out->desc.oz=in->desc.oz;out->desc.voxel_size=refine?in->desc.voxel_size/factor:in->desc.voxel_size*factor;}return st;
}
tvdb_status_t tvdb_gpu_advect_resident(tvdb_gpu_context_t* ctx,const tvdb_gpu_dense_grid_t* field,
    const tvdb_gpu_dense_grid_t* velocity,float dt,int scheme,int clamp,tvdb_gpu_dense_grid_t* out,tvdb_error_t* err) {
    if(!ctx || !resident_same(field,out) || !resident_shape(field,velocity) || field->ctx!=ctx ||
        field->desc.channels!=1 || field->desc.type!=TVDB_GPU_F32 || velocity->desc.type!=TVDB_GPU_F32 ||
        velocity->desc.channels!=3 || !isfinite(dt) || scheme< -1 || scheme>TVDB_ADVECT_BFECC)
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resident advection");
    if(!field->count)return TVDB_OK;
    if(scheme==-1){
        tvdb_status_t st=resident_scratch(out,0,err);if(st!=TVDB_OK)return st;
        int32_t u[12]={field->desc.nx,field->desc.ny,field->desc.nz,2,0,0,0,0,0,0,(int32_t)field->count,0};
        float inv_h=1.0f/(float)field->desc.voxel_size;memcpy(u+8,&inv_h,4);memcpy(u+9,&dt,4);
        tvdb_gpu_resident_dispatch_t s;resident_spec(&s,kTvdbGpuFilterSpv,kTvdbGpuFilterSpv_len,"tvdb_cuda_filter",32,field->count,5);
        s.bindings[0].buffer=field->values;s.bindings[1].buffer=out->scratch[0];s.bindings[2].buffer=velocity->values;
        s.bindings[3].buffer=field->values;s.bindings[4].uniform=u;s.bindings[4].uniform_size=48;
        st=tvdb_gpu_dispatch_resident(ctx,&s,1,err);if(st==TVDB_OK)resident_commit(out,0);return st;
    }
    tvdb_status_t st;int n=scheme<=TVDB_ADVECT_RK4?1:scheme==TVDB_ADVECT_MACCORMACK?3:clamp?5:4;
    for(int i=0;i<(n==1?1:3);++i){st=resident_scratch(out,i,err);if(st!=TVDB_OK)return st;}
    typedef struct{int32_t dim[4],cfg[4];float inv_h,dt;uint32_t count,pad;} params;
    params u[5];tvdb_gpu_resident_dispatch_t specs[5];
    for(int i=0;i<n;++i){memset(&u[i],0,sizeof(u[i]));u[i].dim[0]=field->desc.nx;u[i].dim[1]=field->desc.ny;u[i].dim[2]=field->desc.nz;
        u[i].cfg[0]=n==1?scheme+1:2;u[i].cfg[1]=clamp;u[i].inv_h=1.0f/(float)field->desc.voxel_size;u[i].dt=i==1?-dt:dt;u[i].count=(uint32_t)field->count;
        resident_spec(&specs[i],kTvdbGpuAdvectSpv,kTvdbGpuAdvectSpv_len,"tvdb_cuda_advect",64,field->count,6);
        specs[i].bindings[0].buffer=field->values;specs[i].bindings[1].buffer=velocity->values;
        specs[i].bindings[2].buffer=n==1?field->values:out->scratch[1];specs[i].bindings[3].buffer=n==1?field->values:out->scratch[2];
        specs[i].bindings[4].buffer=out->scratch[0];specs[i].bindings[5].uniform=&u[i];specs[i].bindings[5].uniform_size=sizeof(params);
    }
    if(n>1){specs[0].bindings[4].buffer=out->scratch[1];specs[1].bindings[0].buffer=out->scratch[1];specs[1].bindings[4].buffer=out->scratch[2];
        if(scheme==TVDB_ADVECT_MACCORMACK)u[2].dim[3]=1;
        else{u[2].dim[3]=2;specs[2].bindings[4].buffer=out->scratch[1];specs[3].bindings[0].buffer=out->scratch[1];if(n==5)u[4].dim[3]=3;}}
    st=tvdb_gpu_dispatch_resident(ctx,specs,(size_t)n,err);if(st==TVDB_OK)resident_commit(out,0);return st;
}

static tvdb_status_t resident_upload_host(tvdb_gpu_context_t* ctx,const tvdb_dense_grid* h,
    int channels,tvdb_gpu_dense_grid_t** out,tvdb_error_t* err) {
    tvdb_gpu_grid_desc_t d={h->nx,h->ny,h->nz,channels,TVDB_GPU_F32,h->ox,h->oy,h->oz,h->voxel_size};
    tvdb_status_t st=tvdb_gpu_dense_grid_create(ctx,&d,out,err);
    if(st==TVDB_OK)st=tvdb_gpu_dense_grid_upload(*out,h->data,(*out)->bytes,err);
    return st;
}
static tvdb_status_t resident_commit_host(const tvdb_gpu_dense_grid_t* g,float* destination,tvdb_error_t* err) {
    if(!g->bytes)return TVDB_OK;
    void* tmp=malloc(g->bytes);if(!tmp)return resident_error(err,TVDB_ERROR_OUT_OF_MEMORY,"resident readback allocation failed");
    tvdb_status_t st=tvdb_gpu_dense_grid_download(g,tmp,g->bytes,err);
    if(st==TVDB_OK)memcpy(destination,tmp,g->bytes);
    free(tmp);return st;
}
static tvdb_status_t resident_binary_host(tvdb_gpu_context_t* ctx,const tvdb_dense_grid* a,const tvdb_dense_grid* b,
    int op,int csg,tvdb_dense_grid* out,tvdb_error_t* err) {
    /* Resolve the kernel before allocations, also preserving unsupported-build
       behavior and driver-failure output preservation. */
    tvdb_status_t st=TVDB_OK;
    if(ctx->backend==TVDB_GPU_BACKEND_CUDA) {
        CUmodule module;CUfunction fn;
        st=tvdb_cuda_get_module(ctx,&module,err);if(st!=TVDB_OK)return st;
        if(!tvdb_cuda_ok(ctx,err,"resident kernel lookup",ctx->cuda.cuModuleGetFunction(&fn,module,csg?"tvdb_cuda_csg_resident":"tvdb_cuda_comp")))return TVDB_ERROR_IO;
    } else if(csg?!kTvdbGpuCsgSpv_len:!kTvdbGpuCompSpv_len)return resident_error(err,TVDB_ERROR_UNIMPLEMENTED,"resident SPIR-V unavailable");
    tvdb_gpu_dense_grid_t *ga=NULL,*gb=NULL,*go=NULL;
    st=resident_upload_host(ctx,a,1,&ga,err);
    if(st==TVDB_OK)st=resident_upload_host(ctx,b,1,&gb,err);
    if(st==TVDB_OK)st=tvdb_gpu_dense_grid_create(ctx,&ga->desc,&go,err);
    if(st==TVDB_OK)st=csg?tvdb_gpu_csg_resident(ctx,ga,gb,op,go,err):tvdb_gpu_comp_resident(ctx,ga,gb,op,go,err);
    if(st==TVDB_OK)st=resident_commit_host(go,out->data,err);
    tvdb_gpu_dense_grid_destroy(ga);tvdb_gpu_dense_grid_destroy(gb);tvdb_gpu_dense_grid_destroy(go);return st;
}
static tvdb_status_t resident_filter_host(tvdb_gpu_context_t* ctx,tvdb_dense_grid* grid,int kind,int width,int iterations,tvdb_error_t* err) {
    if(!ctx || !grid || !tvdb_gpu_shape_valid(grid->nx,grid->ny,grid->nz,grid->voxel_size,grid->data,4))
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid filter grid");
    if(iterations<=0 || (kind!=2 && width<=0))return TVDB_OK;
    tvdb_gpu_dense_grid_t* g=NULL;tvdb_status_t st=resident_upload_host(ctx,grid,1,&g,err);
    if(st==TVDB_OK)st=tvdb_gpu_filter_resident(ctx,g,kind,width,iterations,err);
    if(st==TVDB_OK)st=resident_commit_host(g,grid->data,err);
    tvdb_gpu_dense_grid_destroy(g);return st;
}
static tvdb_status_t resident_advect_host(tvdb_gpu_context_t* ctx,const tvdb_dense_grid* field,
    const tvdb_dense_vec_grid* velocity,float dt,int scheme,int clamp,tvdb_dense_grid* out,tvdb_error_t* err) {
    tvdb_gpu_dense_grid_t *f=NULL,*v=NULL,*o=NULL;
    tvdb_dense_grid hv={0};hv.nx=velocity->nx;hv.ny=velocity->ny;hv.nz=velocity->nz;hv.ox=velocity->ox;hv.oy=velocity->oy;hv.oz=velocity->oz;hv.voxel_size=velocity->voxel_size;hv.data=velocity->data;
    tvdb_status_t st=resident_upload_host(ctx,field,1,&f,err);
    if(st==TVDB_OK)st=resident_upload_host(ctx,&hv,3,&v,err);
    if(st==TVDB_OK)st=tvdb_gpu_dense_grid_create(ctx,&f->desc,&o,err);
    if(st==TVDB_OK)st=tvdb_gpu_advect_resident(ctx,f,v,dt,scheme,clamp,o,err);
    if(st==TVDB_OK)st=resident_commit_host(o,out->data,err);
    tvdb_gpu_dense_grid_destroy(f);tvdb_gpu_dense_grid_destroy(v);tvdb_gpu_dense_grid_destroy(o);return st;
}

static tvdb_status_t resident_read_word(tvdb_gpu_buffer_t* b,size_t index,uint32_t* out,tvdb_error_t* err) {
    tvdb_gpu_context_t* c=b->ctx;
    if(index>=b->size/4)return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"word offset outside buffer");
    c->resident_metrics.download_bytes+=4;
    if(c->backend==TVDB_GPU_BACKEND_CUDA)
        return tvdb_cuda_ok(c,err,"cuMemcpyDtoH",c->cuda.cuMemcpyDtoH(out,b->cu+4*index,4))?TVDB_OK:TVDB_ERROR_IO;
    tvdb_vk_buffer stage;tvdb_status_t st=tvdb_vk_create_buffer(c,4,VK_BUFFER_USAGE_TRANSFER_DST_BIT,&stage,err);
    if(st!=TVDB_OK)return st;
    tvdb_vk_copy cp={0};cp.src=b->vk.buffer;cp.dst=stage.buffer;cp.size=4;cp.src_offset=4*index;
    cp.src_stage=VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT;cp.src_access=VK_ACCESS_SHADER_WRITE_BIT;
    cp.dst_stage=VK_PIPELINE_STAGE_HOST_BIT;cp.dst_access=VK_ACCESS_HOST_READ_BIT;
    st=tvdb_vk_run_copies(c,&cp,1,err);if(st==TVDB_OK)memcpy(out,stage.mapped,4);
    tvdb_vk_destroy_buffer(c,&stage);return st;
}
static void resident_topology_release(tvdb_resident_topology* t) {
    if(t && !--t->refs){tvdb_gpu_buffer_destroy(t->coords);tvdb_gpu_buffer_destroy(t->map);free(t);}
}
void tvdb_gpu_sparse_grid_destroy(tvdb_gpu_sparse_grid_t* g) {
    if(g){resident_topology_release(g->topology);tvdb_gpu_buffer_destroy(g->values);free(g);}
}
size_t tvdb_gpu_sparse_grid_count(const tvdb_gpu_sparse_grid_t* g){return g?g->topology->count:0;}
static tvdb_status_t resident_topology_alloc(tvdb_gpu_context_t* c,size_t n,tvdb_resident_topology** out,tvdb_error_t* err) {
    size_t coordinate_bytes;
    if(n>INT_MAX || n>(1u<<29) || !tvdb_size_mul(n,12,&coordinate_bytes))
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"resident sparse count exceeds index capacity");
    tvdb_resident_topology* t=calloc(1,sizeof(*t));
    if(!t)return resident_error(err,TVDB_ERROR_OUT_OF_MEMORY,"sparse topology allocation failed");
    t->refs=1;t->count=n;t->capacity=1;while(t->capacity<n*2)t->capacity*=2;
    size_t map_bytes;
    if(!tvdb_size_mul((size_t)t->capacity+n,4,&map_bytes)){resident_topology_release(t);return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"sparse map size overflow");}
    tvdb_status_t st=tvdb_gpu_buffer_create_device(c,coordinate_bytes?coordinate_bytes:4,&t->coords,err);
    if(st==TVDB_OK)st=tvdb_gpu_buffer_create_device(c,map_bytes,&t->map,err);
    if(st!=TVDB_OK){resident_topology_release(t);return st;}*out=t;return TVDB_OK;
}
static tvdb_status_t resident_topology_build(tvdb_gpu_context_t* c,tvdb_resident_topology* t,tvdb_error_t* err) {
    tvdb_gpu_resident_dispatch_t s[2];uint32_t u[2][4]={{(uint32_t)t->count,t->capacity,0,0},{(uint32_t)t->count,t->capacity,1,0}};
    for(int j=0;j<2;++j){resident_spec(&s[j],kTvdbGpuResidentMapSpv,kTvdbGpuResidentMapSpv_len,"tvdb_cuda_resident_map",128,j?(t->count?t->count:1):t->capacity,3);
        s[j].bindings[0].buffer=t->coords;s[j].bindings[1].buffer=t->map;s[j].bindings[2].uniform=u[j];s[j].bindings[2].uniform_size=16;}
    return tvdb_gpu_dispatch_resident(c,s,2,err);
}
static tvdb_gpu_sparse_grid_t* resident_sparse_new(tvdb_gpu_context_t* c,const tvdb_gpu_sparse_grid_t* in) {
    tvdb_gpu_sparse_grid_t* g=calloc(1,sizeof(*g));if(!g)return NULL;
    g->ctx=c;g->voxel_size=in?in->voxel_size:1;
    if(in){g->ox=in->ox;g->oy=in->oy;g->oz=in->oz;}return g;
}
static void resident_sparse_commit(tvdb_gpu_sparse_grid_t** out,tvdb_gpu_sparse_grid_t* g) {
    tvdb_gpu_sparse_grid_destroy(*out);*out=g;
}
tvdb_status_t tvdb_gpu_sparse_grid_upload(tvdb_gpu_context_t* c,const tvdb_sparse_grid* in,
    tvdb_gpu_sparse_grid_t** out,tvdb_error_t* err) {
    if(!c || !out || (*out && (*out)->ctx!=c) || !tvdb_gpu_sparse_input_valid(in))
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid sparse upload");
    tvdb_gpu_sparse_grid_t* g=resident_sparse_new(c,NULL);
    if(!g)return resident_error(err,TVDB_ERROR_OUT_OF_MEMORY,"sparse handle allocation failed");
    g->ox=in->ox;g->oy=in->oy;g->oz=in->oz;g->voxel_size=in->voxel_size;
    tvdb_status_t st=resident_topology_alloc(c,in->count,&g->topology,err);
    if(st==TVDB_OK)st=tvdb_gpu_buffer_create_device(c,in->count?in->count*4:4,&g->values,err);
    if(st==TVDB_OK && in->count)st=tvdb_gpu_buffer_upload(g->topology->coords,in->coords,in->count*12,err);
    if(st==TVDB_OK && in->count)st=tvdb_gpu_buffer_upload(g->values,in->values,in->count*4,err);
    if(st==TVDB_OK)st=resident_topology_build(c,g->topology,err);
    if(st==TVDB_OK)resident_sparse_commit(out,g);else tvdb_gpu_sparse_grid_destroy(g);
    return st;
}
tvdb_status_t tvdb_gpu_sparse_grid_download(const tvdb_gpu_sparse_grid_t* g,tvdb_sparse_grid* out,tvdb_error_t* err) {
    tvdb_sparse_grid empty;tvdb_sparse_grid_init(&empty);
    if(!g || !tvdb_gpu_sparse_output_valid(&empty,out))return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid sparse download output");
    tvdb_sparse_grid tmp;tvdb_sparse_grid_init(&tmp);size_t n=g->topology->count;
    if(!tvdb_sparse_grid_reserve(&tmp,n?n:1))return resident_error(err,TVDB_ERROR_OUT_OF_MEMORY,"sparse download allocation failed");
    tmp.count=n;tmp.ox=g->ox;tmp.oy=g->oy;tmp.oz=g->oz;tmp.voxel_size=g->voxel_size;
    tvdb_status_t st=TVDB_OK;
    if(n)st=tvdb_gpu_buffer_download(g->topology->coords,tmp.coords,n*12,err);
    if(st==TVDB_OK && n)st=tvdb_gpu_buffer_download(g->values,tmp.values,n*4,err);
    if(st==TVDB_OK){tvdb_sparse_grid_free(out);*out=tmp;}else tvdb_sparse_grid_free(&tmp);return st;
}
static tvdb_status_t resident_sparse_dispatch(tvdb_gpu_context_t* c,const tvdb_resident_topology* t,
    tvdb_gpu_buffer_t* values,tvdb_gpu_buffer_t* coords_out,tvdb_gpu_buffer_t* values_out,
    tvdb_gpu_buffer_t* weights,tvdb_gpu_buffer_t* flags,int32_t* u,tvdb_error_t* err) {
    tvdb_gpu_resident_dispatch_t s;size_t n=(size_t)u[2]+(u[0]==4);
    resident_spec(&s,kTvdbGpuResidentSparseSpv,kTvdbGpuResidentSparseSpv_len,"tvdb_cuda_resident_sparse",128,n?n:1,8);
    s.bindings[0].buffer=t->coords;s.bindings[1].buffer=values;s.bindings[2].buffer=t->map;
    s.bindings[3].buffer=coords_out;s.bindings[4].buffer=values_out;s.bindings[5].buffer=weights;
    s.bindings[6].buffer=flags;s.bindings[7].uniform=u;s.bindings[7].uniform_size=64;
    return tvdb_gpu_dispatch_resident(c,&s,1,err);
}
static tvdb_status_t resident_sparse_step(tvdb_gpu_context_t* c,const tvdb_gpu_sparse_grid_t* in,
    tvdb_gpu_buffer_t* weights,int kx,int ky,int kz,int stride,int kind,float pad,
    tvdb_gpu_sparse_grid_t** out,tvdb_error_t* err) {
    size_t n=in->topology->count,candidates=n,kv=(size_t)kx*ky*kz;
    if(!tvdb_size_mul(n,kind==2?kv:kind==3?7:1,&candidates) || candidates>(1u<<29))
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"sparse candidate count overflow");
    tvdb_gpu_sparse_grid_t* g=resident_sparse_new(c,in);tvdb_resident_topology* cand=NULL;
    tvdb_gpu_buffer_t* flags=NULL;tvdb_status_t st=TVDB_OK;uint32_t count=0,error=0;
    if(!g)return resident_error(err,TVDB_ERROR_OUT_OF_MEMORY,"sparse result allocation failed");
    int32_t u[16]={0,(int32_t)n,(int32_t)candidates,(int32_t)in->topology->capacity,kx,ky,kz,stride,0,0,0,0,kind,0,0,0};memcpy(&u[8],&pad,4);
    if(kind==0){g->topology=in->topology;++g->topology->refs;count=(uint32_t)n;}
    else {
        st=tvdb_gpu_buffer_create_device(c,(candidates+1)*4,&flags,err);if(st!=TVDB_OK)goto done;
        if(kind==4){cand=in->topology;++cand->refs;}
        else {
            st=resident_topology_alloc(c,candidates,&cand,err);if(st!=TVDB_OK)goto done;
            u[0]=4;st=resident_sparse_dispatch(c,in->topology,in->values,cand->coords,in->values,weights,flags,u,err);if(st!=TVDB_OK)goto done;
            u[0]=0;st=resident_sparse_dispatch(c,in->topology,in->values,cand->coords,in->values,weights,flags,u,err);if(st!=TVDB_OK)goto done;
            st=resident_read_word(flags,candidates,&error,err);if(st!=TVDB_OK)goto done;
            if(error){st=resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"sparse output coordinate overflow");goto done;}
            st=resident_topology_build(c,cand,err);if(st!=TVDB_OK)goto done;
        }
        u[0]=1;u[3]=(int32_t)cand->capacity;
        st=resident_sparse_dispatch(c,cand,in->values,cand->coords,in->values,weights,flags,u,err);if(st!=TVDB_OK)goto done;
        st=resident_scan(c,flags,(uint32_t)candidates,&count,err);if(st!=TVDB_OK)goto done;
        st=resident_topology_alloc(c,count,&g->topology,err);if(st!=TVDB_OK)goto done;
        u[0]=2;st=resident_sparse_dispatch(c,cand,in->values,g->topology->coords,in->values,weights,flags,u,err);if(st!=TVDB_OK)goto done;
        st=resident_topology_build(c,g->topology,err);if(st!=TVDB_OK)goto done;
    }
    st=tvdb_gpu_buffer_create_device(c,count?(size_t)count*4:4,&g->values,err);if(st!=TVDB_OK)goto done;
    u[0]=3;u[2]=(int32_t)count;u[3]=(int32_t)in->topology->capacity;
    if(count)st=resident_sparse_dispatch(c,in->topology,in->values,g->topology->coords,g->values,weights,flags?flags:g->values,u,err);
    if(st==TVDB_OK){if(kind==1)g->voxel_size*=stride;else if(kind==2)g->voxel_size/=stride;
        resident_sparse_commit(out,g);g=NULL;}
done:
    tvdb_gpu_sparse_grid_destroy(g);resident_topology_release(cand);tvdb_gpu_buffer_destroy(flags);return st;
}
tvdb_status_t tvdb_gpu_sparse_conv_resident(tvdb_gpu_context_t* c,const tvdb_gpu_sparse_grid_t* in,
    const float* kernel,int kx,int ky,int kz,int stride,int kind,float pad,tvdb_gpu_sparse_grid_t** out,tvdb_error_t* err) {
    size_t kb;
    if(!c || !in || in->ctx!=c || !out || (*out && (*out)->ctx!=c) || !kernel ||
        kx<=0 || ky<=0 || kz<=0 || !tvdb_grid_bytes(kx,ky,kz,4,&kb) || kb/4>INT_MAX || stride<=0 || kind<0 || kind>2 ||
        (kind==1 && !isfinite(in->voxel_size*stride)))return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resident sparse convolution");
    tvdb_gpu_buffer_t* weights=NULL;tvdb_status_t st=tvdb_gpu_buffer_create_device(c,kb,&weights,err);
    if(st==TVDB_OK)st=tvdb_gpu_buffer_upload(weights,kernel,kb,err);
    if(st==TVDB_OK)st=resident_sparse_step(c,in,weights,kx,ky,kz,stride,kind,pad,out,err);
    tvdb_gpu_buffer_destroy(weights);return st;
}
tvdb_status_t tvdb_gpu_sparse_morph_resident(tvdb_gpu_context_t* c,const tvdb_gpu_sparse_grid_t* in,
    int kind,int iterations,float background,tvdb_gpu_sparse_grid_t** out,tvdb_error_t* err) {
    if(!c || !in || in->ctx!=c || !out || (*out && (*out)->ctx!=c) || kind<0 || kind>1 || iterations<=0)
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resident sparse morphology");
    tvdb_gpu_sparse_grid_t* tmp=NULL;tvdb_status_t st=TVDB_OK;
    float identity=1;tvdb_gpu_buffer_t* weights=NULL;
    st=tvdb_gpu_buffer_create_device(c,4,&weights,err);
    if(st==TVDB_OK)st=tvdb_gpu_buffer_upload(weights,&identity,4,err);
    for(int i=0;st==TVDB_OK && i<iterations;++i)st=resident_sparse_step(c,i?tmp:in,weights,1,1,1,1,kind+3,background,&tmp,err);
    tvdb_gpu_buffer_destroy(weights);
    if(st==TVDB_OK)resident_sparse_commit(out,tmp);else tvdb_gpu_sparse_grid_destroy(tmp);return st;
}

/* PCG vectors and reductions stay on device. Host decisions use four reduced
 * doubles, never a grid-sized transfer. Word-addressed workspaces store PCG
 * vectors in their arithmetic precision, candidates in the returned precision,
 * and the true residual in double precision (40/64/72 bytes per voxel). */
typedef struct {
    int32_t dim[4],cfg[4],mode[4];
    double h2,alpha,beta,mean;
} resident_poisson_params;
_Static_assert(sizeof(resident_poisson_params)==80, "Poisson uniform size");
_Static_assert(offsetof(resident_poisson_params,h2)==48, "Poisson uniform double alignment");
_Static_assert(sizeof(tvdb_vec3i)==12, "Sparse coordinate storage stride");
typedef struct {
    tvdb_gpu_context_t* ctx;
    const tvdb_gpu_dense_grid_t *rhs,*x;
    tvdb_gpu_buffer_t *work,*reduce[2];
    resident_poisson_params u;
    /* Snapshot uniforms while recording dependent kernels; submit only at
     * scalar readback or output commit. Backend dispatch inserts barriers. */
    tvdb_gpu_resident_dispatch_t pending[16];
    resident_poisson_params params[16];
    size_t pending_count;
} resident_poisson_state;
static tvdb_status_t resident_poisson_flush(resident_poisson_state* p,tvdb_error_t* err) {
    if(!p->pending_count)return TVDB_OK;
    tvdb_status_t st=tvdb_gpu_dispatch_resident(p->ctx,p->pending,p->pending_count,err);
    p->pending_count=0;return st;
}
static tvdb_status_t resident_poisson_enqueue(resident_poisson_state* p,
    const tvdb_gpu_resident_dispatch_t* s,tvdb_error_t* err) {
    if(p->pending_count==16){tvdb_status_t st=resident_poisson_flush(p,err);if(st!=TVDB_OK)return st;}
    size_t i=p->pending_count++;
    p->pending[i]=*s;p->params[i]=p->u;
    p->pending[i].bindings[6].uniform=&p->params[i];
    return TVDB_OK;
}
static tvdb_status_t resident_poisson_run(resident_poisson_state* p,int op,int a,int b,int dst,
    tvdb_gpu_buffer_t* output,tvdb_error_t* err) {
    p->u.cfg[0]=op;p->u.cfg[1]=a;p->u.cfg[2]=b;p->u.cfg[3]=dst;
    tvdb_gpu_resident_dispatch_t s;
    resident_spec(&s,kTvdbGpuResidentPoissonSpv,kTvdbGpuResidentPoissonSpv_len,"tvdb_cuda_resident_poisson",128,p->rhs->count,7);
    s.bindings[0].buffer=p->rhs->values;s.bindings[1].buffer=p->x->values;s.bindings[2].buffer=p->work;
    s.bindings[3].buffer=p->reduce[0];s.bindings[4].buffer=p->reduce[1];s.bindings[5].buffer=output?output:p->work;
    s.bindings[6].uniform=&p->u;s.bindings[6].uniform_size=sizeof(p->u);
    return resident_poisson_enqueue(p,&s,err);
}
static tvdb_status_t resident_poisson_reduce(resident_poisson_state* p,int op,int a,int b,double result[4],tvdb_error_t* err) {
    tvdb_status_t st=resident_poisson_run(p,op,a,b,0,NULL,err);if(st!=TVDB_OK)return st;
    size_t count=(p->rhs->count+127)/128;int src=1;
    while(count>1){
        p->u.cfg[0]=100;p->u.mode[2]=(int32_t)count;
        tvdb_gpu_resident_dispatch_t s;resident_spec(&s,kTvdbGpuResidentPoissonSpv,kTvdbGpuResidentPoissonSpv_len,"tvdb_cuda_resident_poisson",128,count,7);
        s.bindings[0].buffer=p->rhs->values;s.bindings[1].buffer=p->x->values;s.bindings[2].buffer=p->work;
        s.bindings[3].buffer=p->reduce[src];s.bindings[4].buffer=p->reduce[1-src];s.bindings[5].buffer=p->work;
        s.bindings[6].uniform=&p->u;s.bindings[6].uniform_size=sizeof(p->u);
        st=resident_poisson_enqueue(p,&s,err);if(st!=TVDB_OK)return st;
        count=(count+127)/128;src=1-src;
    }
    st=resident_poisson_flush(p,err);if(st!=TVDB_OK)return st;
    return tvdb_gpu_buffer_download(p->reduce[src],result,32,err);
}
static tvdb_status_t resident_poisson_project(resident_poisson_state* p,int slot,tvdb_error_t* err) {
    double v[4];tvdb_status_t st=resident_poisson_reduce(p,90,slot,slot,v,err);if(st!=TVDB_OK)return st;
    if(!isfinite(v[1]) || v[3])return resident_error(err,TVDB_ERROR_INVALID_DATA,"Poisson nonfinite iterate");
    p->u.alpha=v[1]/p->rhs->count;
    return resident_poisson_run(p,5,slot,0,slot,NULL,err);
}
tvdb_status_t tvdb_gpu_poisson_resident(tvdb_gpu_context_t* c,const tvdb_gpu_dense_grid_t* rhs,
    tvdb_gpu_dense_grid_t* x,int precision,int max_iters,double tolerance,tvdb_poisson_result_t* result,tvdb_error_t* err) {
    if(result)memset(result,0,sizeof(*result));
    if(!c || !rhs || !x || !result || !resident_same(rhs,x) || rhs->ctx!=c || rhs->desc.channels!=1 || rhs->desc.voxel_size!=x->desc.voxel_size || !rhs->count ||
        precision<0 || precision>2 || (rhs->desc.type==TVDB_GPU_F64)!=(precision==2) || max_iters<0 || !isfinite(tolerance) || tolerance<0 ||
        !isfinite(rhs->desc.voxel_size*rhs->desc.voxel_size) || rhs->desc.voxel_size*rhs->desc.voxel_size==0 ||
        !isfinite(1/(rhs->desc.voxel_size*rhs->desc.voxel_size)))
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resident Poisson inputs");
    size_t words_per_voxel=precision==0?10u:precision==1?16u:18u;
    if(rhs->count>UINT32_MAX/words_per_voxel)
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"Poisson workspace index overflow");
    if(!tvdb_gpu_supports_fp64(c))return resident_error(err,TVDB_ERROR_UNIMPLEMENTED,"resident Poisson requires fp64 reductions");
    resident_poisson_state p;memset(&p,0,sizeof(p));p.ctx=c;p.rhs=rhs;p.x=x;
    p.u.dim[0]=rhs->desc.nx;p.u.dim[1]=rhs->desc.ny;p.u.dim[2]=rhs->desc.nz;p.u.dim[3]=(int32_t)rhs->count;
    p.u.mode[0]=precision!=0;p.u.mode[1]=precision==2;p.u.h2=rhs->desc.voxel_size*rhs->desc.voxel_size;
    size_t wb;tvdb_status_t st=TVDB_OK;double v[4],rhs_mean=0,x_mean=0,rz=0,best=0,target=0;
    if(!tvdb_size_mul(rhs->count,words_per_voxel*sizeof(uint32_t),&wb))return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"Poisson workspace overflow");
    st=tvdb_gpu_buffer_create_device(c,wb,&p.work,err);if(st!=TVDB_OK)goto done;
    for(int i=0;i<2;++i){st=tvdb_gpu_buffer_create_device(c,((rhs->count+127)/128)*32,&p.reduce[i],err);if(st!=TVDB_OK)goto done;}
#define RP_RUN(op,a,b,d) do{st=resident_poisson_run(&p,op,a,b,d,NULL,err);if(st!=TVDB_OK)goto done;}while(0)
#define RP_REDUCE(op,a,b) do{st=resident_poisson_reduce(&p,op,a,b,v,err);if(st!=TVDB_OK)goto done;}while(0)
#define RP_PROJECT(slot) do{st=resident_poisson_project(&p,slot,err);if(st!=TVDB_OK)goto done;}while(0)
    RP_REDUCE(91,0,0);
    if(!isfinite(v[0]) || !isfinite(v[1]) || !isfinite(v[2]) || v[3] || fabs(v[0])>64*(precision==2?DBL_EPSILON:FLT_EPSILON)*v[1]){
        st=resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"Poisson nonfinite input or incompatible RHS mean");goto done;}
    rhs_mean=v[0]/rhs->count;x_mean=v[2]/rhs->count;p.u.alpha=rhs_mean;p.u.mean=x_mean;RP_RUN(0,0,0,0);
    p.u.mode[3]=1;p.u.mean=rhs_mean;RP_RUN(2,6,0,8);RP_REDUCE(90,8,8);
    best=sqrt(v[0]);target=precision==2?tolerance:tolerance*best;
    result->initial_residual_norm=result->final_residual_norm=best;
    if(!isfinite(best) || !isfinite(target)){st=resident_error(err,TVDB_ERROR_INVALID_DATA,"Poisson nonfinite residual");goto done;}
    if(best<=target){result->converged=true;goto done;}
    if(!max_iters)goto done;
    p.u.mode[3]=0;RP_RUN(2,0,0,2);RP_PROJECT(2);RP_RUN(4,2,0,3);RP_PROJECT(3);RP_RUN(8,3,0,4);RP_REDUCE(90,2,3);rz=v[0];
    for(int it=0;it<max_iters;++it){
        RP_RUN(1,4,0,5);RP_PROJECT(5);RP_REDUCE(90,4,5);
        double alpha=rz/v[0];
        if(!(v[0]>0) || !(rz>0) || !isfinite(alpha)){st=resident_error(err,TVDB_ERROR_INVALID_DATA,"Poisson conjugate-gradient breakdown");goto done;}
        p.u.alpha=1;p.u.beta=alpha;RP_RUN(3,0,4,0);
        p.u.alpha=1;p.u.beta=-alpha;RP_RUN(3,2,5,2);
        result->iterations=it+1;RP_REDUCE(90,2,2);double rr=v[0];
        if(!isfinite(rr)){st=resident_error(err,TVDB_ERROR_INVALID_DATA,"Poisson nonfinite iterate");goto done;}
        int cheap=sqrt(rr)<=target;
        if(it%8==0 || it+1==max_iters || cheap){
            p.u.mean=x_mean;RP_RUN(6,0,0,7);
            p.u.mode[3]=1;p.u.mean=rhs_mean;RP_RUN(2,7,0,8);RP_REDUCE(90,8,8);double candidate=sqrt(v[0]);p.u.mode[3]=0;
            if(!isfinite(candidate)){st=resident_error(err,TVDB_ERROR_INVALID_DATA,"Poisson output precision overflow");goto done;}
            if(candidate<best){best=candidate;RP_RUN(8,7,0,6);}
        }
        int restart=((it+1)%32==0 || cheap);
        if(restart){RP_RUN(2,0,0,2);RP_REDUCE(90,2,2);if(sqrt(v[0])<=target)break;}
        RP_PROJECT(2);RP_RUN(4,2,0,3);RP_PROJECT(3);RP_REDUCE(90,2,3);
        double next=v[0];p.u.alpha=1;p.u.beta=restart?0:next/rz;RP_RUN(3,3,4,4);RP_PROJECT(4);rz=next;
    }
    result->final_residual_norm=best;result->converged=best<=target;
    st=resident_scratch(x,0,err);if(st!=TVDB_OK)goto done;
    st=resident_poisson_run(&p,7,6,0,0,x->scratch[0],err);
    if(st==TVDB_OK)st=resident_poisson_flush(&p,err);
    if(st==TVDB_OK)resident_commit(x,0);
done:
    tvdb_gpu_buffer_destroy(p.work);tvdb_gpu_buffer_destroy(p.reduce[0]);tvdb_gpu_buffer_destroy(p.reduce[1]);return st;
#undef RP_RUN
#undef RP_REDUCE
#undef RP_PROJECT
}

static tvdb_status_t resident_poisson_host(tvdb_gpu_context_t* c,const void* rhs,void* x,
    const tvdb_gpu_grid_desc_t* d,int precision,int iterations,double tolerance,tvdb_poisson_result_t* result,tvdb_error_t* err) {
    tvdb_gpu_dense_grid_t *r=NULL,*g=NULL;tvdb_status_t st;
    if(!result || !rhs || !x || iterations<0 || !isfinite(tolerance) || tolerance<0)
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid Poisson arguments");
    st=tvdb_gpu_dense_grid_create(c,d,&r,err);
    if(st==TVDB_OK)st=tvdb_gpu_dense_grid_create(c,d,&g,err);
    if(st==TVDB_OK)st=tvdb_gpu_dense_grid_upload(r,rhs,r->bytes,err);
    if(st==TVDB_OK)st=tvdb_gpu_dense_grid_upload(g,x,g->bytes,err);
    if(st==TVDB_OK)st=tvdb_gpu_poisson_resident(c,r,g,precision,iterations,tolerance,result,err);
    if(st==TVDB_OK)st=resident_commit_host(g,x,err);
    tvdb_gpu_dense_grid_destroy(r);tvdb_gpu_dense_grid_destroy(g);return st;
}

static tvdb_status_t resident_stencil_host(tvdb_gpu_context_t* c,const tvdb_dense_grid* in,
    int input_channels,int output_channels,int op,float** output,tvdb_error_t* err) {
    tvdb_gpu_dense_grid_t *g=NULL,*o=NULL;tvdb_status_t st=resident_upload_host(c,in,input_channels,&g,err);
    float* data=NULL;
    if(st==TVDB_OK){tvdb_gpu_grid_desc_t d=g->desc;d.channels=output_channels;st=tvdb_gpu_dense_grid_create(c,&d,&o,err);}
    if(st==TVDB_OK)st=tvdb_gpu_stencil_resident(c,g,op,o,err);
    if(st==TVDB_OK){data=malloc(o->bytes?o->bytes:4);if(!data)st=resident_error(err,TVDB_ERROR_OUT_OF_MEMORY,"stencil readback allocation failed");}
    if(st==TVDB_OK)st=tvdb_gpu_dense_grid_download(o,data,o->bytes,err);
    if(st==TVDB_OK)*output=data;else free(data);
    tvdb_gpu_dense_grid_destroy(g);tvdb_gpu_dense_grid_destroy(o);return st;
}
static tvdb_status_t resident_morph_host(tvdb_gpu_context_t* c,tvdb_dense_grid* h,int iterations,int kind,tvdb_error_t* err) {
    if(!c || !h || !tvdb_gpu_shape_valid(h->nx,h->ny,h->nz,h->voxel_size,h->data,4))
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid morphology grid");
    if(iterations<=0)return TVDB_OK;
    tvdb_gpu_dense_grid_t* g=NULL;tvdb_status_t st=resident_upload_host(c,h,1,&g,err);
    if(st==TVDB_OK)st=tvdb_gpu_morph_resident(c,g,kind,iterations,err);
    if(st==TVDB_OK)st=resident_commit_host(g,h->data,err);
    tvdb_gpu_dense_grid_destroy(g);return st;
}
static tvdb_status_t resident_resample_host(tvdb_gpu_context_t* c,const tvdb_dense_grid* in,int factor,int refine,
    tvdb_dense_grid* out,tvdb_error_t* err) {
    if(!c || !in || !out || in==out || factor<1 || !tvdb_gpu_shape_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,4))
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resampling grid");
    int shape[3]={in->nx,in->ny,in->nz};
    for(int i=0;i<3;++i){if(refine && shape[i]>INT_MAX/factor)return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"resampled dimensions overflow");
        shape[i]=refine?shape[i]*factor:shape[i]/factor+(shape[i]%factor!=0);}
    tvdb_gpu_dense_grid_t *g=NULL,*o=NULL;tvdb_dense_grid tmp={0};
    tvdb_status_t st=resident_upload_host(c,in,1,&g,err);
    if(st==TVDB_OK){tvdb_gpu_grid_desc_t d=g->desc;d.nx=shape[0];d.ny=shape[1];d.nz=shape[2];st=tvdb_gpu_dense_grid_create(c,&d,&o,err);}
    if(st==TVDB_OK)st=tvdb_gpu_resample_resident(c,g,factor,refine,o,err);
    if(st==TVDB_OK)st=tvdb_gpu_init_out_grid(&tmp,shape[0],shape[1],shape[2],(float)o->desc.voxel_size,in->ox,in->oy,in->oz,err);
    if(st==TVDB_OK)st=tvdb_gpu_dense_grid_download(o,tmp.data,o->bytes,err);
    if(st==TVDB_OK)*out=tmp;else free(tmp.data);
    tvdb_gpu_dense_grid_destroy(g);tvdb_gpu_dense_grid_destroy(o);return st;
}
static tvdb_status_t resident_sparse_host(tvdb_gpu_context_t* c,const tvdb_sparse_grid* in,const float* kernel,
    int kx,int ky,int kz,int stride,int kind,int iterations,float background,tvdb_sparse_grid* out,tvdb_error_t* err) {
    tvdb_gpu_sparse_grid_t *g=NULL,*o=NULL;tvdb_status_t st=tvdb_gpu_sparse_grid_upload(c,in,&g,err);
    if(st==TVDB_OK)st=kind<3?tvdb_gpu_sparse_conv_resident(c,g,kernel,kx,ky,kz,stride,kind,background,&o,err):
        tvdb_gpu_sparse_morph_resident(c,g,kind-3,iterations,background,&o,err);
    if(st==TVDB_OK)st=tvdb_gpu_sparse_grid_download(o,out,err);
    tvdb_gpu_sparse_grid_destroy(g);tvdb_gpu_sparse_grid_destroy(o);return st;
}

tvdb_status_t tvdb_gpu_dense_to_sparse_resident(tvdb_gpu_context_t* c,const tvdb_gpu_dense_grid_t* in,
    float background,float tolerance,tvdb_gpu_sparse_grid_t** out,tvdb_error_t* err) {
    if(!c || !in || in->ctx!=c || !out || (*out && (*out)->ctx!=c) || in->desc.type!=TVDB_GPU_F32 || in->desc.channels!=1 ||
        !isfinite(background) || !isfinite(tolerance) || tolerance<0)
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid dense-to-sparse conversion");
    tvdb_gpu_sparse_grid_t* g=resident_sparse_new(c,NULL);tvdb_gpu_buffer_t* flags=NULL;uint32_t count=0;
    if(!g)return resident_error(err,TVDB_ERROR_OUT_OF_MEMORY,"sparse handle allocation failed");
    g->ox=(float)in->desc.ox;g->oy=(float)in->desc.oy;g->oz=(float)in->desc.oz;g->voxel_size=(float)in->desc.voxel_size;
    tvdb_resident_topology dummy={1,0,1,in->values,in->values};
    int32_t u[16]={5,(int32_t)in->count,(int32_t)in->count,1,in->desc.nx,in->desc.ny,in->desc.nz,1};
    memcpy(&u[8],&background,4);memcpy(&u[9],&tolerance,4);
    tvdb_status_t st=tvdb_gpu_buffer_create_device(c,in->count?in->count*4:4,&flags,err);
    if(st==TVDB_OK)st=resident_sparse_dispatch(c,&dummy,in->values,in->values,in->values,in->values,flags,u,err);
    if(st==TVDB_OK)st=resident_scan(c,flags,(uint32_t)in->count,&count,err);
    if(st==TVDB_OK)st=resident_topology_alloc(c,count,&g->topology,err);
    if(st==TVDB_OK)st=tvdb_gpu_buffer_create_device(c,count?(size_t)count*4:4,&g->values,err);
    u[0]=6;
    if(st==TVDB_OK)st=resident_sparse_dispatch(c,&dummy,in->values,g->topology->coords,g->values,in->values,flags,u,err);
    if(st==TVDB_OK)st=resident_topology_build(c,g->topology,err);
    if(st==TVDB_OK)resident_sparse_commit(out,g);else tvdb_gpu_sparse_grid_destroy(g);
    tvdb_gpu_buffer_destroy(flags);return st;
}
tvdb_status_t tvdb_gpu_sparse_to_dense_resident(tvdb_gpu_context_t* c,const tvdb_gpu_sparse_grid_t* in,
    float background,tvdb_gpu_dense_grid_t* out,tvdb_error_t* err) {
    if(!c || !in || in->ctx!=c || !out || out->ctx!=c || out->desc.type!=TVDB_GPU_F32 || out->desc.channels!=1)
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid sparse-to-dense conversion");
    if(!out->count)return TVDB_OK;
    tvdb_status_t st=resident_scratch(out,0,err);if(st!=TVDB_OK)return st;
    int32_t u[16]={7,(int32_t)in->topology->count,(int32_t)out->count,(int32_t)in->topology->capacity,out->desc.nx,out->desc.ny,out->desc.nz,1};memcpy(&u[8],&background,4);
    st=resident_sparse_dispatch(c,in->topology,in->values,in->topology->coords,out->scratch[0],in->values,in->values,u,err);
    if(st==TVDB_OK)resident_commit(out,0);return st;
}
tvdb_status_t tvdb_gpu_voxelize_resident(tvdb_gpu_context_t* c,tvdb_gpu_buffer_t* points,size_t n,
    const float origin[3],float voxel_size,tvdb_gpu_sparse_grid_t** out,tvdb_error_t* err) {
    size_t bytes;
    if(!c || !points || points->ctx!=c || !out || (*out && (*out)->ctx!=c) || !origin ||
        !isfinite(origin[0]) || !isfinite(origin[1]) || !isfinite(origin[2]) || !isfinite(voxel_size) || voxel_size<=0 ||
        !tvdb_size_mul(n,12,&bytes) || bytes>points->size || n>(1u<<29))
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resident voxelization");
    tvdb_gpu_sparse_grid_t* g=resident_sparse_new(c,NULL);tvdb_gpu_sparse_grid_t* result=NULL;tvdb_gpu_buffer_t* flags=NULL;
    if(!g)return resident_error(err,TVDB_ERROR_OUT_OF_MEMORY,"voxelization handle allocation failed");
    g->ox=origin[0];g->oy=origin[1];g->oz=origin[2];g->voxel_size=voxel_size;
    tvdb_status_t st=resident_topology_alloc(c,n,&g->topology,err);uint32_t bad=0;
    if(st==TVDB_OK)st=tvdb_gpu_buffer_create_device(c,n?n*4:4,&g->values,err);
    if(st==TVDB_OK)st=tvdb_gpu_buffer_create_device(c,(n+1)*4,&flags,err);
    int32_t u[16]={4,(int32_t)n,(int32_t)n,1};memcpy(u+8,origin,12);memcpy(u+11,&voxel_size,4);
    if(st==TVDB_OK)st=resident_sparse_dispatch(c,g->topology,g->values,g->topology->coords,g->values,points,flags,u,err);
    u[0]=8;if(st==TVDB_OK)st=resident_sparse_dispatch(c,g->topology,g->values,g->topology->coords,g->values,points,flags,u,err);
    if(st==TVDB_OK)st=resident_read_word(flags,n,&bad,err);
    if(st==TVDB_OK && bad)st=resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"voxelization coordinate outside int32 range");
    if(st==TVDB_OK)st=resident_topology_build(c,g->topology,err);
    float identity=1;
    if(st==TVDB_OK)st=tvdb_gpu_sparse_conv_resident(c,g,&identity,1,1,1,1,1,0,&result,err);
    if(st==TVDB_OK)resident_sparse_commit(out,result);else tvdb_gpu_sparse_grid_destroy(result);
    tvdb_gpu_sparse_grid_destroy(g);tvdb_gpu_buffer_destroy(flags);return st;
}

static tvdb_status_t resident_reduce_grid(tvdb_gpu_context_t* c,const tvdb_gpu_dense_grid_t* g,
    int kind,double band,double tolerance,void* output,tvdb_error_t* err) {
    if(!c || !g || g->ctx!=c || g->desc.type!=TVDB_GPU_F32 || g->desc.channels!=1 || !g->count || !output ||
       (kind==1 && (g->desc.nx<3 || g->desc.ny<3 || g->desc.nz<3 || !isfinite(band) || !isfinite(tolerance))))
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resident reduction");
    size_t n=kind==1?(size_t)(g->desc.nx-2)*(g->desc.ny-2)*(g->desc.nz-2):g->count;
    uint32_t groups=tvdb_gpu_reduce_groups(n),u[12]={0},v[4]={groups,(uint32_t)kind,0,0};
    if(kind==1){u[0]=g->desc.nx;u[1]=g->desc.ny;u[2]=g->desc.nz;float f[4]={(float)(1/(2*g->desc.voxel_size)),(float)band,(float)tolerance,0};memcpy(u+4,f,16);u[8]=(uint32_t)n;u[9]=groups;}
    else {u[0]=(uint32_t)n;u[1]=groups;}
    tvdb_gpu_buffer_t *part=NULL,*result=NULL;tvdb_status_t st=tvdb_gpu_buffer_create_device(c,(size_t)groups*16,&part,err);
    if(st==TVDB_OK)st=tvdb_gpu_buffer_create_device(c,16,&result,err);
    if(st!=TVDB_OK)goto done;
    tvdb_gpu_resident_dispatch_t s[2];
    resident_spec(&s[0],kind==0?kTvdbGpuStatsSpv:kind==1?kTvdbGpuLevelsetCheckSpv:kTvdbGpuChecksumSpv,
        kind==0?kTvdbGpuStatsSpv_len:kind==1?kTvdbGpuLevelsetCheckSpv_len:kTvdbGpuChecksumSpv_len,
        kind==0?"tvdb_cuda_stats_resident":kind==1?"tvdb_cuda_levelset_check_resident":"tvdb_cuda_checksum_resident",256,(size_t)groups*256,3);
    s[0].bindings[0].buffer=g->values;s[0].bindings[1].buffer=part;s[0].bindings[2].uniform=u;s[0].bindings[2].uniform_size=48;
    resident_spec(&s[1],kTvdbGpuResidentReduceSpv,kTvdbGpuResidentReduceSpv_len,"tvdb_cuda_resident_reduce",256,256,3);
    s[1].bindings[0].buffer=part;s[1].bindings[1].buffer=result;s[1].bindings[2].uniform=v;s[1].bindings[2].uniform_size=16;
    st=tvdb_gpu_dispatch_resident(c,s,2,err);
    if(st==TVDB_OK)st=tvdb_gpu_buffer_download(result,output,kind==2?4:16,err);
done:
    tvdb_gpu_buffer_destroy(part);tvdb_gpu_buffer_destroy(result);return st;
}
tvdb_status_t tvdb_gpu_statistics_resident(tvdb_gpu_context_t* c,const tvdb_gpu_dense_grid_t* g,tvdb_grid_stats_t* out,tvdb_error_t* err) {
    if(!out)return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"null resident statistics output");
    float values[4];tvdb_status_t st=resident_reduce_grid(c,g,0,0,0,values,err);
    if(st==TVDB_OK)tvdb_finalize_stats(values,1,g->count,out);return st;
}
tvdb_status_t tvdb_gpu_levelset_check_resident(tvdb_gpu_context_t* c,const tvdb_gpu_dense_grid_t* g,
    double band,double tolerance,tvdb_level_set_check_t* out,tvdb_error_t* err) {
    if(!out)return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"null resident level-set output");
    float values[4];tvdb_status_t st=resident_reduce_grid(c,g,1,band,tolerance,values,err);
    if(st==TVDB_OK){memset(out,0,sizeof(*out));tvdb_finalize_ls_check(values,1,0,out);}return st;
}
tvdb_status_t tvdb_gpu_checksum_resident(tvdb_gpu_context_t* c,const tvdb_gpu_dense_grid_t* g,uint32_t* out,tvdb_error_t* err) {
    uint32_t value;tvdb_status_t st=out?resident_reduce_grid(c,g,2,0,0,&value,err):resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"null checksum output");
    if(st==TVDB_OK)*out=value;return st;
}
tvdb_status_t tvdb_gpu_measure_resident(tvdb_gpu_context_t* c,const tvdb_gpu_dense_grid_t* g,int volume,double* out,tvdb_error_t* err) {
    if(!c || !g || g->ctx!=c || !out || g->desc.channels!=1 || (volume!=0 && volume!=1))return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid resident measurement");
    if(!tvdb_gpu_supports_fp64(c))return resident_error(err,TVDB_ERROR_UNIMPLEMENTED,"measurement requires fp64");
    if(!g->count){*out=0;return TVDB_OK;}
    uint32_t groups=tvdb_gpu_reduce_groups(g->count),u[2][8]={{(uint32_t)g->desc.nx,(uint32_t)g->desc.ny,(uint32_t)g->desc.nz,(uint32_t)volume,(uint32_t)g->count,0,groups,0}};
    memcpy(u[1],u[0],sizeof(u[0]));u[1][5]=1;
    tvdb_gpu_buffer_t* part=NULL;tvdb_status_t st=tvdb_gpu_buffer_create_device(c,(size_t)groups*8,&part,err);if(st!=TVDB_OK)return st;
    tvdb_gpu_resident_dispatch_t s[2];int d=g->desc.type==TVDB_GPU_F64;
    for(int i=0;i<2;++i){resident_spec(&s[i],d?kTvdbGpuMeasureDSpv:kTvdbGpuMeasureSpv,d?kTvdbGpuMeasureDSpv_len:kTvdbGpuMeasureSpv_len,
        d?"tvdb_cuda_measure_d_resident":"tvdb_cuda_measure_resident",256,i?256:(size_t)groups*256,3);
        s[i].bindings[0].buffer=g->values;s[i].bindings[1].buffer=part;s[i].bindings[2].uniform=u[i];s[i].bindings[2].uniform_size=32;}
    st=tvdb_gpu_dispatch_resident(c,s,2,err);double count=0;
    if(st==TVDB_OK)st=tvdb_gpu_buffer_download(part,&count,8,err);
    if(st==TVDB_OK){double h=g->desc.voxel_size;*out=count*h*h*(volume?h:1);}
    tvdb_gpu_buffer_destroy(part);return st;
}

static tvdb_status_t resident_reduce_host(tvdb_gpu_context_t* c,const tvdb_dense_grid* in,
    int kind,double band,double tolerance,void* output,tvdb_error_t* err) {
    if(!c || !in || !output)return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid reduction arguments");
    tvdb_gpu_dense_grid_t* g=NULL;tvdb_status_t st=resident_upload_host(c,in,1,&g,err);
    if(st==TVDB_OK)st=kind==0?tvdb_gpu_statistics_resident(c,g,output,err):kind==1?tvdb_gpu_levelset_check_resident(c,g,band,tolerance,output,err):tvdb_gpu_checksum_resident(c,g,output,err);
    tvdb_gpu_dense_grid_destroy(g);return st;
}
static tvdb_status_t resident_measure_host(tvdb_gpu_context_t* c,const void* data,int is_double,
    int nx,int ny,int nz,int op,double* count,tvdb_error_t* err) {
    tvdb_gpu_grid_desc_t d={nx,ny,nz,1,is_double?TVDB_GPU_F64:TVDB_GPU_F32,0,0,0,1};
    tvdb_gpu_dense_grid_t* g=NULL;tvdb_status_t st=tvdb_gpu_dense_grid_create(c,&d,&g,err);
    if(st==TVDB_OK)st=tvdb_gpu_dense_grid_upload(g,data,g->bytes,err);
    if(st==TVDB_OK)st=tvdb_gpu_measure_resident(c,g,op,count,err);
    tvdb_gpu_dense_grid_destroy(g);return st;
}
static tvdb_status_t resident_active_host(tvdb_gpu_context_t* c,const tvdb_dense_grid* in,
    float background,float tolerance,tvdb_sparse_grid* out,tvdb_error_t* err) {
    if(!c || !in || !out)return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid active-grid arguments");
    tvdb_gpu_dense_grid_t* g=NULL;tvdb_gpu_sparse_grid_t* s=NULL;
    tvdb_status_t st=resident_upload_host(c,in,1,&g,err);
    if(st==TVDB_OK)st=tvdb_gpu_dense_to_sparse_resident(c,g,background,tolerance,&s,err);
    if(st==TVDB_OK)st=tvdb_gpu_sparse_grid_download(s,out,err);
    tvdb_gpu_dense_grid_destroy(g);tvdb_gpu_sparse_grid_destroy(s);return st;
}

tvdb_status_t tvdb_gpu_sparse_grid_update_values(tvdb_gpu_sparse_grid_t* g,const float* values,size_t count,tvdb_error_t* err) {
    if(!g || count!=g->topology->count || (count && !values))
        return resident_error(err,TVDB_ERROR_INVALID_ARGUMENT,"sparse value count mismatch");
    if(!count)return TVDB_OK;
    tvdb_gpu_buffer_t* next=NULL;tvdb_status_t st=tvdb_gpu_buffer_create_device(g->ctx,count*4,&next,err);
    if(st==TVDB_OK)st=tvdb_gpu_buffer_upload(next,values,count*4,err);
    if(st==TVDB_OK){tvdb_gpu_buffer_destroy(g->values);g->values=next;}else tvdb_gpu_buffer_destroy(next);return st;
}

static tvdb_status_t resident_double_host(tvdb_gpu_context_t* c,const tvdb_dense_grid_d* a,
    const tvdb_dense_grid_d* b,int op,tvdb_dense_grid_d* out,tvdb_error_t* err) {
    tvdb_gpu_grid_desc_t d={a->nx,a->ny,a->nz,1,TVDB_GPU_F64,a->ox,a->oy,a->oz,a->voxel_size};
    tvdb_gpu_dense_grid_t *ga=NULL,*gb=NULL,*go=NULL;double* data=NULL;
    tvdb_status_t st=tvdb_gpu_dense_grid_create(c,&d,&ga,err);
    if(st==TVDB_OK)st=tvdb_gpu_dense_grid_upload(ga,a->data,ga->bytes,err);
    if(st==TVDB_OK && b)st=tvdb_gpu_dense_grid_create(c,&d,&gb,err);
    if(st==TVDB_OK && b)st=tvdb_gpu_dense_grid_upload(gb,b->data,gb->bytes,err);
    if(st==TVDB_OK)st=tvdb_gpu_dense_grid_create(c,&d,&go,err);
    if(st==TVDB_OK)st=b?tvdb_gpu_csg_resident(c,ga,gb,op,go,err):tvdb_gpu_stencil_resident(c,ga,op,go,err);
    if(st==TVDB_OK){data=malloc(go->bytes);if(!data)st=resident_error(err,TVDB_ERROR_OUT_OF_MEMORY,"fp64 result allocation failed");}
    if(st==TVDB_OK)st=tvdb_gpu_dense_grid_download(go,data,go->bytes,err);
    if(st==TVDB_OK){*out=*a;out->data=data;}else free(data);
    tvdb_gpu_dense_grid_destroy(ga);tvdb_gpu_dense_grid_destroy(gb);tvdb_gpu_dense_grid_destroy(go);return st;
}
