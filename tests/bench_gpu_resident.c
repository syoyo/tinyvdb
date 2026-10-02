/* Procedural, asset-free GPU residency/compaction benchmark. Not a CTest. */
#if !defined(_WIN32)
#define _POSIX_C_SOURCE 200809L
#endif
#include "tinyvdb_gpu.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#if defined(_WIN32)
#include <windows.h>
#endif
static double now(void){
#if defined(_WIN32)
    LARGE_INTEGER frequency,counter;QueryPerformanceFrequency(&frequency);QueryPerformanceCounter(&counter);
    return (double)counter.QuadPart/(double)frequency.QuadPart;
#else
    struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;
#endif
}
#define TRY(x) do{if((x)!=TVDB_OK){fprintf(stderr,"%s\n",err.message);status=1;goto done;}}while(0)
int main(int argc,char** argv){
    int dim=argc>2?atoi(argv[2]):128,status=0;
    if(dim<2 || dim>256){fprintf(stderr,"dimension must be 2..256\n");return 1;}
    size_t n=(size_t)dim*dim*dim,cells=(size_t)(dim-1)*(dim-1)*(dim-1);
    float* data=malloc(n*4);float* host=malloc(n*4);float* ones=malloc(n*4);
    if(!data || !host || !ones){free(data);free(host);free(ones);return 1;}
    for(int z=0;z<dim;++z)for(int y=0;y<dim;++y)for(int x=0;x<dim;++x){size_t i=((size_t)z*dim+y)*dim+x;
        float dx=x-(dim-1)*.5f,dy=y-(dim-1)*.5f,dz=z-(dim-1)*.5f;data[i]=sqrtf(dx*dx+dy*dy+dz*dz)-dim*.3f;ones[i]=.01f;}
    tvdb_gpu_context_t* c=NULL;tvdb_gpu_dense_grid_t *g=NULL,*b=NULL;tvdb_gpu_buffer_t* mesh=NULL;tvdb_error_t err={0};
    tvdb_gpu_backend_t backend=argc>1 && argv[1][0]=='c'?TVDB_GPU_BACKEND_CUDA:TVDB_GPU_BACKEND_VULKAN;
    if(tvdb_gpu_context_create(backend,0,&c,&err)!=TVDB_OK){fprintf(stderr,"unavailable: %s\n",err.message);status=77;goto done;}
    if(backend==TVDB_GPU_BACKEND_VULKAN && !tvdb_gpu_spirv_available()){status=77;goto done;}
    tvdb_gpu_context_info_t info;TRY(tvdb_gpu_context_info(c,&info,&err));
    printf("backend=%d device=%s dimension=%d\n",backend,info.device_name,dim);
    tvdb_gpu_grid_desc_t d={dim,dim,dim,1,TVDB_GPU_F32,0,0,0,1};
    TRY(tvdb_gpu_dense_grid_create(c,&d,&g,&err));TRY(tvdb_gpu_dense_grid_upload(g,data,n*4,&err));
    size_t triangles=0;TRY(tvdb_gpu_marching_cubes_resident(c,g,0,&mesh,&triangles,&err));tvdb_gpu_buffer_destroy(mesh);mesh=NULL;
    tvdb_gpu_resident_metrics_reset(c);double start=now();
    TRY(tvdb_gpu_marching_cubes_resident(c,g,0,&mesh,&triangles,&err));double elapsed=now()-start;
    tvdb_gpu_resident_metrics_t m;tvdb_gpu_resident_metrics(c,&m);
    printf("marching_cubes_ms=%.3f triangles=%zu peak_logical_bytes=%zu download_bytes=%llu old_fixed_vertex_temp_bytes=%zu\n",elapsed*1000,triangles,m.peak_bytes,(unsigned long long)m.download_bytes,cells*180);
    tvdb_gpu_buffer_destroy(mesh);mesh=NULL;
    TRY(tvdb_gpu_dense_grid_create(c,&d,&b,&err));TRY(tvdb_gpu_dense_grid_upload(b,ones,n*4,&err));
    TRY(tvdb_gpu_comp_resident(c,g,b,2,g,&err));TRY(tvdb_gpu_filter_resident(c,g,0,1,1,&err));
    TRY(tvdb_gpu_dense_grid_upload(g,data,n*4,&err));tvdb_gpu_resident_metrics_reset(c);start=now();
    for(int i=0;i<5;++i){TRY(tvdb_gpu_comp_resident(c,g,b,2,g,&err));TRY(tvdb_gpu_filter_resident(c,g,0,1,1,&err));}
    elapsed=now()-start;tvdb_gpu_resident_metrics(c,&m);
    printf("resident_pipeline_ms=%.3f upload_bytes=%llu download_bytes=%llu submissions=%llu\n",elapsed*1000,(unsigned long long)m.upload_bytes,(unsigned long long)m.download_bytes,(unsigned long long)m.submissions);
    TRY(tvdb_gpu_dense_grid_download(g,host,n*4,&err));
    tvdb_dense_grid hg={0},hb={0};hg.nx=hb.nx=dim;hg.ny=hb.ny=dim;hg.nz=hb.nz=dim;hg.voxel_size=hb.voxel_size=1;hg.data=data;hb.data=ones;
    tvdb_gpu_resident_metrics_reset(c);start=now();
    for(int i=0;i<5;++i){TRY(tvdb_gpu_comp_sum(c,&hg,&hb,&hg,&err));TRY(tvdb_gpu_mean_filter(c,&hg,1,1,&err));}
    elapsed=now()-start;tvdb_gpu_resident_metrics(c,&m);
    printf("host_pipeline_ms=%.3f upload_bytes=%llu download_bytes=%llu submissions=%llu\n",elapsed*1000,(unsigned long long)m.upload_bytes,(unsigned long long)m.download_bytes,(unsigned long long)m.submissions);
    for(size_t i=0;i<n;++i)if(fabsf(data[i]-host[i])>1e-5f){fprintf(stderr,"pipeline mismatch at %zu\n",i);status=1;break;}
done:
    tvdb_gpu_buffer_destroy(mesh);tvdb_gpu_dense_grid_destroy(g);tvdb_gpu_dense_grid_destroy(b);tvdb_gpu_context_destroy(c);
    free(data);free(host);free(ones);return status;
}
