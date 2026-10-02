#include "tinyvdb_gpu.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#define CHECK(x) do{if(!(x)){fprintf(stderr,"line %d: %s (%s)\n",__LINE__,#x,err.message);failed=1;goto done;}}while(0)
int main(int argc,char** argv) {
    tvdb_gpu_context_t* ctx=NULL;tvdb_error_t err={0};int failed=0;
    tvdb_gpu_backend_t backend=argc>1 && argv[1][0]=='c'?TVDB_GPU_BACKEND_CUDA:TVDB_GPU_BACKEND_VULKAN;
    if(tvdb_gpu_context_create(backend,0,&ctx,&err)!=TVDB_OK){fprintf(stderr,"SKIP: %s\n",err.message);return 77;}
    if(backend==TVDB_GPU_BACKEND_VULKAN && !tvdb_gpu_spirv_available()){tvdb_gpu_context_destroy(ctx);return 77;}
    tvdb_gpu_context_info_t info;tvdb_gpu_context_info(ctx,&info,&err);printf("backend=%d device=%s\n",info.backend,info.device_name);
    enum{N=31*5*3};float av[N],bv[N],got[N],ref[N];
    for(int i=0;i<N;++i){av[i]=sinf(i*.13f);bv[i]=cosf(i*.19f);ref[i]=av[i]+bv[i];}
    tvdb_gpu_grid_desc_t d={31,5,3,1,TVDB_GPU_F32,0,0,0,.5};
    tvdb_gpu_dense_grid_t *a=NULL,*b=NULL,*out=NULL;
    CHECK(tvdb_gpu_dense_grid_create(ctx,&d,&a,&err)==TVDB_OK);
    CHECK(tvdb_gpu_dense_grid_create(ctx,&d,&b,&err)==TVDB_OK);
    CHECK(tvdb_gpu_dense_grid_create(ctx,&d,&out,&err)==TVDB_OK);
    CHECK(tvdb_gpu_dense_grid_upload(a,av,sizeof(av),&err)==TVDB_OK);
    CHECK(tvdb_gpu_dense_grid_upload(b,bv,sizeof(bv),&err)==TVDB_OK);
    tvdb_gpu_resident_metrics_reset(ctx);
    CHECK(tvdb_gpu_comp_resident(ctx,a,b,2,out,&err)==TVDB_OK);
    CHECK(tvdb_gpu_filter_resident(ctx,out,1,2,2,&err)==TVDB_OK);
    tvdb_dense_grid cpu={0};cpu.nx=31;cpu.ny=5;cpu.nz=3;cpu.voxel_size=.5f;cpu.data=ref;
    tvdb_gaussian_filter(&cpu,2,2);
    tvdb_gpu_resident_metrics_t m;tvdb_gpu_resident_metrics(ctx,&m);
    CHECK(m.download_bytes==0);CHECK(m.submissions==2);
    CHECK(tvdb_gpu_dense_grid_download(out,got,sizeof(got),&err)==TVDB_OK);
    for(int i=0;i<N;++i)CHECK(fabsf(got[i]-ref[i])<2e-5f);
    CHECK(tvdb_gpu_comp_resident(ctx,a,b,2,a,&err)==TVDB_OK);
    CHECK(tvdb_gpu_dense_grid_download(a,got,sizeof(got),&err)==TVDB_OK);
    for(int i=0;i<N;++i)CHECK(got[i]==av[i]+bv[i]);
    CHECK(tvdb_gpu_comp_resident(ctx,a,b,99,a,&err)==TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(tvdb_gpu_dense_grid_download(a,got,sizeof(got),&err)==TVDB_OK);
    for(int i=0;i<N;++i)CHECK(got[i]==av[i]+bv[i]);
    /* Warmed elementwise pipelines reuse the output scratch. */
    tvdb_gpu_resident_metrics_reset(ctx);
    for(int i=0;i<10;++i)CHECK(tvdb_gpu_comp_resident(ctx,a,b,0,a,&err)==TVDB_OK);
    tvdb_gpu_resident_metrics(ctx,&m);
    CHECK(m.download_bytes==0);
    /* CUDA uniforms are allocations; full grids must not grow. */
    CHECK(m.peak_bytes<=m.live_bytes+64);
    CHECK(tvdb_gpu_dense_grid_upload(a,av,sizeof(av),&err)==TVDB_OK);
    cpu.data=av;
    tvdb_grid_stats_t stats,expected_stats;
    tvdb_level_set_check_t ls,expected_ls;uint32_t checksum,expected_checksum;
    CHECK(tvdb_gpu_grid_statistics(ctx,&cpu,&expected_stats,&err)==TVDB_OK);
    CHECK(tvdb_gpu_check_level_set(ctx,&cpu,2,.1,&expected_ls,&err)==TVDB_OK);
    CHECK(tvdb_gpu_grid_checksum(ctx,&cpu,&expected_checksum,&err)==TVDB_OK);
    tvdb_gpu_resident_metrics_reset(ctx);
    CHECK(tvdb_gpu_statistics_resident(ctx,a,&stats,&err)==TVDB_OK);
    CHECK(tvdb_gpu_levelset_check_resident(ctx,a,2,.1,&ls,&err)==TVDB_OK);
    CHECK(tvdb_gpu_checksum_resident(ctx,a,&checksum,&err)==TVDB_OK);
    CHECK(checksum==expected_checksum && stats.count==N);
    CHECK(fabs(stats.sum-expected_stats.sum)<1e-4 && stats.min==expected_stats.min && stats.max==expected_stats.max);
    CHECK(ls.band_count==expected_ls.band_count && fabs(ls.mean_grad_mag-expected_ls.mean_grad_mag)<1e-5);
    tvdb_gpu_resident_metrics(ctx,&m);CHECK(m.download_bytes==36);
    if(tvdb_gpu_supports_fp64(ctx)){
        double area,volume;
        CHECK(tvdb_gpu_measure_resident(ctx,a,0,&area,&err)==TVDB_OK);
        CHECK(tvdb_gpu_measure_resident(ctx,a,1,&volume,&err)==TVDB_OK);
        CHECK(area==tvdb_surface_area(&cpu));CHECK(volume==tvdb_volume(&cpu));
    }
done:
    tvdb_gpu_dense_grid_destroy(a);tvdb_gpu_dense_grid_destroy(b);tvdb_gpu_dense_grid_destroy(out);
    tvdb_gpu_resident_metrics_t final;tvdb_gpu_resident_metrics(ctx,&final);
    if(final.live_bytes){fprintf(stderr,"resident buffers leaked: %zu\n",final.live_bytes);failed=1;}
    tvdb_gpu_context_destroy(ctx);return failed;
}
