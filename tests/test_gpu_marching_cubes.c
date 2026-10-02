/* Procedural fixtures: no external volume files or shared test assets. */
#include "tinyvdb_gpu.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <float.h>
static int run(tvdb_gpu_context_t* ctx,int nx,int ny,int nz,int pattern) {
    tvdb_dense_grid g={0};tvdb_dense_grid_init(&g,nx,ny,nz);
    if(!g.data)return 1;g.ox=-2;g.oy=.5f;g.oz=3;g.voxel_size=.3f;
    const int corner[8]={0,1,3,2,4,5,7,6};
    size_t n=(size_t)nx*ny*nz,cells=(size_t)(nx-1)*(ny-1)*(nz-1);
    unsigned seed=0x315a92u;
    for(size_t i=0;i<n;++i) {
        int x=(int)(i%nx),y=(int)((i/nx)%ny),z=(int)(i/(nx*ny));
        seed=1664525u*seed+1013904223u;
        if(pattern<256)g.data[corner[i]]=(pattern&(1u<<i))?-.25f:.75f;
        else if(pattern==256)g.data[i]=1;
        else if(pattern==257)g.data[i]=(float)x-(nx-1)*.5f;
        else if(pattern==258)g.data[i]=sqrtf((x-nx*.5f)*(x-nx*.5f)+(y-ny*.5f)*(y-ny*.5f)+(z-nz*.5f)*(z-nz*.5f))-nz*.3f;
        else if(pattern==259)g.data[i]=((x+y+z)&1)?-1:1;
        else if(pattern==261)g.data[i]=x<nx/2?-1e-30f:1e-30f;
        else if(pattern==262)g.data[i]=x<nx/2?-FLT_MAX:FLT_MAX;
        else if(pattern==263)g.data[i]=x<nx/2?-FLT_MAX:FLT_MAX*.25f;
        else g.data[i]=(float)(seed>>8)/8388608.0f-1;
    }
    tvdb_triangle_mesh ref={0};tvdb_error_t err={0};int bad=0;
    if(!tvdb_sdf_to_mesh(&g,0,&ref,NULL)){bad=1;goto done;}
    tvdb_gpu_grid_desc_t d={nx,ny,nz,1,TVDB_GPU_F32,g.ox,g.oy,g.oz,g.voxel_size};
    tvdb_gpu_dense_grid_t* resident=NULL;tvdb_gpu_buffer_t* mesh=NULL;float* vertices=NULL;size_t total=0;
    if(tvdb_gpu_dense_grid_create(ctx,&d,&resident,&err)!=TVDB_OK ||
       tvdb_gpu_dense_grid_upload(resident,g.data,n*4,&err)!=TVDB_OK){bad=1;goto gpu_done;}
    tvdb_gpu_resident_metrics_reset(ctx);
    if(tvdb_gpu_marching_cubes_resident(ctx,resident,0,&mesh,&total,&err)!=TVDB_OK){bad=1;goto gpu_done;}
    tvdb_gpu_resident_metrics_t metrics;tvdb_gpu_resident_metrics(ctx,&metrics);
    if(metrics.download_bytes!=4 || total!=ref.face_count){bad=1;goto gpu_done;}
    /* Full output plus offsets, tables, scan hierarchy, and small uniforms.
       There must be no 180*cells temporary (even for an empty field). */
    size_t bound=n*4+cells*5+total*36+65536;
    if(metrics.peak_bytes>bound){fprintf(stderr,"peak %zu > bound %zu\n",metrics.peak_bytes,bound);bad=1;goto gpu_done;}
    if(total) {
        vertices=malloc(total*36);if(!vertices){bad=1;goto gpu_done;}
        if(tvdb_gpu_buffer_download(mesh,vertices,total*36,&err)!=TVDB_OK){bad=1;goto gpu_done;}
        for(size_t t=0;t<total;++t) {
            tvdb_triangle f=ref.faces[t];unsigned indices[3]={f.v0,f.v1,f.v2};
            for(int k=0;k<3;++k) {
                tvdb_vec3f p=ref.vertices[indices[k]];
                if(!isfinite(vertices[t*9+k*3]) || !isfinite(vertices[t*9+k*3+1]) ||
                   !isfinite(vertices[t*9+k*3+2]) || fabsf(vertices[t*9+k*3]-p.x)>2e-5f ||
                   fabsf(vertices[t*9+k*3+1]-p.y)>2e-5f || fabsf(vertices[t*9+k*3+2]-p.z)>2e-5f){
                    fprintf(stderr,"triangle=%zu corner=%d got=(%g,%g,%g) expected=(%g,%g,%g)\n",t,k,
                        vertices[t*9+k*3],vertices[t*9+k*3+1],vertices[t*9+k*3+2],p.x,p.y,p.z);
                    bad=1;goto gpu_done;}
            }
        }
    }
gpu_done:
    free(vertices);tvdb_gpu_buffer_destroy(mesh);tvdb_gpu_dense_grid_destroy(resident);
done:
    if(bad)fprintf(stderr,"MC %dx%dx%d pattern=%d failed: %s\n",nx,ny,nz,pattern,err.message);
    tvdb_triangle_mesh_free(&ref);tvdb_dense_grid_free(&g);return bad;
}
int main(int argc,char** argv) {
    tvdb_gpu_context_t* ctx=NULL;tvdb_error_t err={0};int bad=0;
    tvdb_gpu_backend_t b=argc>1 && argv[1][0]=='c'?TVDB_GPU_BACKEND_CUDA:TVDB_GPU_BACKEND_VULKAN;
    if(tvdb_gpu_context_create(b,0,&ctx,&err)!=TVDB_OK){fprintf(stderr,"SKIP: %s\n",err.message);return 77;}
    if(b==TVDB_GPU_BACKEND_VULKAN && !tvdb_gpu_spirv_available()){tvdb_gpu_context_destroy(ctx);return 77;}
    tvdb_gpu_context_info_t info;tvdb_gpu_context_info(ctx,&info,&err);printf("backend=%d device=%s\n",info.backend,info.device_name);
    for(int p=0;p<256 && !bad;++p)bad=run(ctx,2,2,2,p);
    for(int p=256;p<=263 && !bad;++p) {
        bad=run(ctx,33,17,9,p);if(!bad)bad=run(ctx,66,3,2,p);
    }
    if(!bad)bad=run(ctx,65,65,17,258); /* multiple scan hierarchy levels */
    if(!bad)bad=run(ctx,205,205,205,258); /* exceed 65535 groups in classification and scan */
    tvdb_gpu_context_destroy(ctx);return bad;
}
