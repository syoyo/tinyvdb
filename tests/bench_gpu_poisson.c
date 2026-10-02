/* Procedural resident Poisson memory/time benchmark. Not a CTest.
 * Usage: bench_gpu_poisson [vulkan|cuda] [dimension] [precision 0..2] [iterations]
 * Checks the reported residual against an independent Neumann stencil. */
#if !defined(_WIN32)
#define _POSIX_C_SOURCE 200809L
#endif
#include "tinyvdb_gpu.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#if defined(_WIN32)
#include <windows.h>
#endif
static double now(void) {
#if defined(_WIN32)
    LARGE_INTEGER f,c;QueryPerformanceFrequency(&f);QueryPerformanceCounter(&c);
    return (double)c.QuadPart/(double)f.QuadPart;
#else
    struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;
#endif
}
static double lap(const double* data,size_t i,int dim) {
    size_t plane=(size_t)dim*dim;int x=(int)(i%dim),y=(int)((i/dim)%dim),z=(int)(i/plane);
    double v=0,c=data[i];
    if(x)v+=data[i-1]-c;if(x+1<dim)v+=data[i+1]-c;
    if(y)v+=data[i-dim]-c;if(y+1<dim)v+=data[i+dim]-c;
    if(z)v+=data[i-plane]-c;if(z+1<dim)v+=data[i+plane]-c;
    return v;
}
#define TRY(call) do{if((call)!=TVDB_OK){fprintf(stderr,"%s\n",err.message);status=1;goto done;}}while(0)
int main(int argc,char** argv) {
    int dim=argc>2?atoi(argv[2]):64,precision=argc>3?atoi(argv[3]):0,budget=argc>4?atoi(argv[4]):32,status=0;
    if(dim<2 || dim>256 || precision<0 || precision>2 || budget<1 || budget>10000) {
        fprintf(stderr,"dimension 2..256, precision 0..2, iterations 1..10000 required\n");return 1;
    }
    tvdb_gpu_backend_t backend=argc>1 && argv[1][0]=='c'?TVDB_GPU_BACKEND_CUDA:TVDB_GPU_BACKEND_VULKAN;
    size_t n=(size_t)dim*dim*dim,bytes=n*(precision==2?sizeof(double):sizeof(float));
    void *rhs=calloc(1,bytes),*output=calloc(1,bytes);
    double* reference=malloc(n*sizeof(double));
    tvdb_gpu_context_t* ctx=NULL;tvdb_gpu_dense_grid_t *r=NULL,*x=NULL;tvdb_error_t err={0};
    if(!rhs || !output || !reference){status=1;goto done;}
    for(size_t i=0;i<n;++i)reference[i]=sin(i*.037)+cos(i*.011);
    double mean=0;
    for(size_t i=0;i<n;++i) {
        double v=lap(reference,i,dim);if(precision==2)((double*)rhs)[i]=v;else ((float*)rhs)[i]=(float)v;
        mean+=precision==2?v:(double)(float)v;
    }
    mean/=n;
    if(tvdb_gpu_context_create(backend,0,&ctx,&err)!=TVDB_OK) {
        fprintf(stderr,"unavailable: %s\n",err.message);status=77;goto done;
    }
    if(!tvdb_gpu_supports_fp64(ctx) || (backend==TVDB_GPU_BACKEND_VULKAN && !tvdb_gpu_spirv_available())){status=77;goto done;}
    tvdb_gpu_context_info_t info;TRY(tvdb_gpu_context_info(ctx,&info,&err));
    printf("backend=%d device=%s dimension=%d precision=%d\n",backend,info.device_name,dim,precision);
    tvdb_gpu_grid_desc_t desc={dim,dim,dim,1,precision==2?TVDB_GPU_F64:TVDB_GPU_F32,0,0,0,1};
    TRY(tvdb_gpu_dense_grid_create(ctx,&desc,&r,&err));TRY(tvdb_gpu_dense_grid_create(ctx,&desc,&x,&err));
    TRY(tvdb_gpu_dense_grid_upload(r,rhs,bytes,&err));TRY(tvdb_gpu_dense_grid_upload(x,output,bytes,&err));
    tvdb_poisson_result_t result;
    TRY(tvdb_gpu_poisson_resident(ctx,r,x,precision,budget,1e-6,&result,&err));
    TRY(tvdb_gpu_dense_grid_upload(x,output,bytes,&err));
    tvdb_gpu_resident_metrics_reset(ctx);double start=now();
    TRY(tvdb_gpu_poisson_resident(ctx,r,x,precision,budget,1e-6,&result,&err));
    double elapsed=now()-start;tvdb_gpu_resident_metrics_t metrics;tvdb_gpu_resident_metrics(ctx,&metrics);
    TRY(tvdb_gpu_dense_grid_download(x,output,bytes,&err));
    for(size_t i=0;i<n;++i)reference[i]=precision==2?((double*)output)[i]:((float*)output)[i];
    double norm=0;
    for(size_t i=0;i<n;++i){double v=(precision==2?((double*)rhs)[i]:((float*)rhs)[i])-mean-lap(reference,i,dim);norm+=v*v;}
    norm=sqrt(norm);
    uint64_t hash=UINT64_C(14695981039346656037);
    for(size_t i=0;i<bytes;++i){hash^=((unsigned char*)output)[i];hash*=UINT64_C(1099511628211);}
    printf("poisson_ms=%.3f iterations=%d peak_logical_bytes=%zu download_bytes=%llu submissions=%llu residual=%.17g independently_checked_residual=%.17g output_hash=%016llx\n",
        elapsed*1000,result.iterations,metrics.peak_bytes,(unsigned long long)metrics.download_bytes,
        (unsigned long long)metrics.submissions,result.final_residual_norm,norm,(unsigned long long)hash);
    if(!isfinite(norm) || fabs(norm-result.final_residual_norm)>1e-5*(1+norm)) {
        fprintf(stderr,"reported residual mismatch\n");status=1;
    }
done:
    tvdb_gpu_dense_grid_destroy(r);tvdb_gpu_dense_grid_destroy(x);tvdb_gpu_context_destroy(ctx);
    free(rhs);free(output);free(reference);return status;
}
