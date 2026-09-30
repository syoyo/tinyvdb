#include "tinyvdb_gpu.h"
#include "tinyvdb_sample.h"
#include <float.h>
#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <string.h>
static int failures;
#define CHECK(c) do { if(!(c)) { fprintf(stderr,"%s:%d: %s\n",__FILE__,__LINE__,#c); ++failures; } } while(0)
static float lookup(const tvdb_sparse_grid* g,int x,int y,int z) {
  for(size_t i=0;i<g->count;++i) if(g->coords[i].x==x && g->coords[i].y==y && g->coords[i].z==z) return g->values[i];
  return NAN;
}
int main(int argc,char** argv) {
  tvdb_gpu_context_t* ctx=NULL; tvdb_error_t err;
  tvdb_gpu_backend_t backend=argc>1 && argv[1][0]=='c' ? TVDB_GPU_BACKEND_CUDA : TVDB_GPU_BACKEND_VULKAN;
  if(tvdb_gpu_context_create(backend,0,&ctx,&err)!=TVDB_OK) return 77;
  if(backend==TVDB_GPU_BACKEND_VULKAN && !tvdb_gpu_spirv_available()) { tvdb_gpu_context_destroy(ctx); return 77; }
  tvdb_gpu_context_info_t device; tvdb_gpu_context_info(ctx,&device,&err);
  printf("backend=%d device=%s\n",(int)device.backend,device.device_name);
  int32_t active[]={INT32_MAX,0,0,INT32_MIN,0,0}; int32_t counts[2]={-1,-1};
  CHECK(tvdb_gpu_neighbor_counts(ctx,active,2,6,counts,&err)==TVDB_OK);
  CHECK(counts[0]==0 && counts[1]==0);
  tvdb_gpu_index_map_t* map=NULL;
  CHECK(tvdb_gpu_index_map_create(ctx,active,2,&map,&err)==TVDB_OK);
  if(map) {
    CHECK(tvdb_gpu_neighbor_counts_mapped(ctx,map,26,counts,&err)==TVDB_OK);
    CHECK(counts[0]==0 && counts[1]==0);
    float world[]={FLT_MAX,0,0},spacing[]={1,1,1},origin[]={0,0,0}; int32_t result=42;
    CHECK(tvdb_gpu_points_in_grid_mapped(ctx,map,world,1,spacing,origin,&result,&err)==TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(result==42); tvdb_gpu_index_map_destroy(ctx,map);
  }
  tvdb_vec3i coords[]={{INT32_MAX,0,0},{INT32_MIN,0,0}}; float values[]={2,7};
  tvdb_sparse_grid in={coords,values,2,0,1,0,0,0},out; tvdb_sparse_grid_init(&out);
  float kernel[]={0,0,1};
  CHECK(tvdb_gpu_sparse_conv3d(ctx,&in,kernel,3,1,1,5,&out,&err)==TVDB_OK);
  CHECK(out.count==2 && out.values[0]==5 && out.values[1]==5);
  tvdb_sparse_grid_free(&out);
  coords[0].x=0; coords[1].x=1<<22; float identity=1;
  CHECK(tvdb_gpu_sparse_conv3d_strided(ctx,&in,&identity,1,1,1,1,0,&out,&err)==TVDB_OK);
  CHECK(out.count==2 && lookup(&out,0,0,0)==2 && lookup(&out,1<<22,0,0)==7);
  CHECK(tvdb_gpu_sparse_conv3d(ctx,&out,&identity,1,1,1,0,&out,&err)==TVDB_OK);
  CHECK(out.count==2 && lookup(&out,0,0,0)==2 && lookup(&out,1<<22,0,0)==7);
  tvdb_sparse_grid_free(&out);
  /* Duplicate values are resolved before morphology's dense scatter. */
  coords[0]=coords[1]=(tvdb_vec3i){0,0,0}; values[0]=-1; values[1]=-9;
  CHECK(tvdb_gpu_dilate_sparse(ctx,&in,5,1,&out,&err)==TVDB_OK);
  CHECK(out.count==7 && lookup(&out,0,0,0)==-1 && lookup(&out,1,0,0)==-1);
  tvdb_sparse_grid_free(&out);
  in.count=1; coords[0].x=INT32_MAX;
  CHECK(tvdb_gpu_dilate_sparse(ctx,&in,5,1,&out,&err)==TVDB_OK);
  CHECK(out.count==6 && lookup(&out,INT32_MAX-1,0,0)==-1);
  tvdb_sparse_grid_free(&out);
  CHECK(tvdb_gpu_sparse_conv3d_transpose(ctx,&in,&identity,1,1,1,2,&out,&err)==TVDB_OK);
  CHECK(out.count==0); tvdb_sparse_grid_free(&out);
  tvdb_dense_grid g,ref; tvdb_dense_grid_init(&g,3,2,2); memset(&ref,0,sizeof(ref));
  for(int i=0;i<12;++i) g.data[i]=(float)(i*i%17);
  CHECK(tvdb_gpu_stencil_scalar_scalar(ctx,&g,0,&ref,&err)==TVDB_OK);
  CHECK(tvdb_gpu_stencil_scalar_scalar(ctx,&g,0,&g,&err)==TVDB_OK);
  CHECK(memcmp(g.data,ref.data,12*sizeof(float))==0);
  g.data[0]=4; g.data[2]=9;
  tvdb_vec3f pts[]={{FLT_MAX,0.5f,0.5f},{-FLT_MAX,0.5f,0.5f}}; float sampled[]={-1,-1};
  CHECK(tvdb_gpu_sample_trilinear_dense_batch(ctx,&g,pts,2,sampled,&err)==TVDB_OK);
  CHECK(sampled[0]==9 && sampled[1]==4);
  CHECK(tvdb_gpu_sample_quadratic_dense_batch(ctx,&g,pts,2,sampled,&err)==TVDB_OK);
  CHECK(sampled[0]==9 && sampled[1]==4);
  float world_points[]={FLT_MAX,0.5f,0.5f,-FLT_MAX,0.5f,0.5f},splat_values[]={1,1};
  float saved_grid[12]; memcpy(saved_grid,g.data,sizeof(saved_grid));
  CHECK(tvdb_gpu_splat_trilinear_dense(ctx,&g,world_points,splat_values,2,NULL,&err)==TVDB_OK);
  CHECK(memcmp(saved_grid,g.data,sizeof(saved_grid))==0);
  CHECK(tvdb_gpu_splat_quadratic_dense(ctx,&g,world_points,splat_values,2,NULL,&err)==TVDB_OK);
  CHECK(memcmp(saved_grid,g.data,sizeof(saved_grid))==0);
  pts[0].x=NAN; sampled[0]=sampled[1]=42;
  CHECK(tvdb_gpu_sample_trilinear_dense_batch(ctx,&g,pts,2,sampled,&err)!=TVDB_OK);
  CHECK(sampled[0]==42 && sampled[1]==42);
  memset(g.data,0,12*sizeof(float)); CHECK(tvdb_gpu_signed_flood_fill(ctx,&g,1e-6f,&err)==TVDB_OK);
  for(int i=0;i<12;++i) CHECK(g.data[i]==0);
  tvdb_dense_grid temporary;
  CHECK(tvdb_gpu_refine(ctx,&g,INT_MAX,&temporary,&err)!=TVDB_OK);
  CHECK(tvdb_gpu_coarsen(ctx,&g,2,&g,&err)!=TVDB_OK); CHECK(g.nx==3);
  tvdb_dense_vec_grid velocity; tvdb_dense_vec_grid_init(&velocity,3,2,2);
  for(int i=0;i<36;++i) velocity.data[i]=0.3f*sinf((float)i);
  for(int scheme=TVDB_ADVECT_RK1;scheme<=TVDB_ADVECT_BFECC;++scheme) {
    for(int i=0;i<12;++i) g.data[i]=(float)(i*i%17);
    CHECK(tvdb_gpu_advect(ctx,&g,&velocity,0.2f,scheme,1,&ref,&err)==TVDB_OK);
    CHECK(tvdb_gpu_advect(ctx,&g,&velocity,0.2f,scheme,1,&g,&err)==TVDB_OK);
    CHECK(memcmp(g.data,ref.data,12*sizeof(float))==0);
  }
  tvdb_dense_vec_grid_free(&velocity);
  tvdb_dense_grid_free(&g); tvdb_dense_grid_free(&ref); tvdb_gpu_context_destroy(ctx);
  return failures ? 1 : 0;
}
