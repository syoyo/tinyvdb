#include "tinyvdb_gpu.h"
#include <stdio.h>
#include <math.h>
#include <limits.h>
#define CHECK(x) do{if(!(x)){fprintf(stderr,"line %d: %s (%s)\n",__LINE__,#x,err.message);failed=1;goto done;}}while(0)
static int equal(const tvdb_sparse_grid* a,const tvdb_sparse_grid* b){
    if(a->count!=b->count){fprintf(stderr,"counts %zu != %zu\n",a->count,b->count);return 0;}
    for(size_t i=0;i<a->count;++i){size_t j;
        for(j=0;j<b->count;++j)if(a->coords[i].x==b->coords[j].x && a->coords[i].y==b->coords[j].y && a->coords[i].z==b->coords[j].z)break;
        if(j==b->count || fabsf(a->values[i]-b->values[j])>2e-4f){fprintf(stderr,"value mismatch at %d,%d,%d: %g / %g\n",a->coords[i].x,a->coords[i].y,a->coords[i].z,a->values[i],j==b->count?0:b->values[j]);return 0;}
    }return 1;
}
static int lookup(const tvdb_sparse_grid* g,int x,int y,int z){
    for(size_t i=0;i<g->count;++i)if(g->coords[i].x==x && g->coords[i].y==y && g->coords[i].z==z)return (int)i;
    return -1;
}
/* Independent scalar reference, including duplicate transpose contributions. */
static int reference_conv(const tvdb_sparse_grid* in,const float* w,int stride,int transpose,float pad,tvdb_sparse_grid* out){
    if(!tvdb_sparse_grid_reserve(out,in->count*27+1))return 0;
    out->count=0;out->voxel_size=transpose?in->voxel_size/stride:in->voxel_size*stride;
    for(size_t i=0;i<in->count;++i){
        for(int k=0;k<(transpose?27:1);++k){
            int64_t x=in->coords[i].x,y=in->coords[i].y,z=in->coords[i].z;
            if(transpose){x=x*stride+k%3-1;y=y*stride+(k/3)%3-1;z=z*stride+k/9-1;}
            else{x=x/stride-(x%stride<0);y=y/stride-(y%stride<0);z=z/stride-(z%stride<0);}
            if(x<INT_MIN || x>INT_MAX || y<INT_MIN || y>INT_MAX || z<INT_MIN || z>INT_MAX)continue;
            int j=lookup(out,(int)x,(int)y,(int)z);
            if(j<0){j=(int)out->count++;out->coords[j]=(tvdb_vec3i){(int)x,(int)y,(int)z};out->values[j]=0;}
            if(transpose)out->values[j]+=w[k]*in->values[i];
        }
    }
    if(!transpose)for(size_t i=0;i<out->count;++i)for(int k=0;k<27;++k){
        int x=out->coords[i].x*stride+k%3-1,y=out->coords[i].y*stride+(k/3)%3-1,z=out->coords[i].z*stride+k/9-1;
        int j=lookup(in,x,y,z);out->values[i]+=w[k]*(j<0?pad:in->values[j]);}
    return 1;
}
int main(int argc,char** argv){
    tvdb_gpu_context_t* c=NULL;tvdb_error_t err={0};int failed=0;
    tvdb_gpu_sparse_grid_t *g=NULL,*o=NULL;tvdb_gpu_dense_grid_t* dense=NULL;tvdb_gpu_buffer_t* points=NULL;tvdb_sparse_grid in,ref,got;
    tvdb_sparse_grid_init(&in);tvdb_sparse_grid_init(&ref);tvdb_sparse_grid_init(&got);
    tvdb_gpu_backend_t backend=argc>1 && argv[1][0]=='c'?TVDB_GPU_BACKEND_CUDA:TVDB_GPU_BACKEND_VULKAN;
    if(tvdb_gpu_context_create(backend,0,&c,&err)!=TVDB_OK){fprintf(stderr,"SKIP: %s\n",err.message);return 77;}
    if(backend==TVDB_GPU_BACKEND_VULKAN && !tvdb_gpu_spirv_available()){tvdb_gpu_context_destroy(c);return 77;}
    tvdb_gpu_context_info_t info;tvdb_gpu_context_info(c,&info,&err);printf("backend=%d device=%s\n",info.backend,info.device_name);
    CHECK(tvdb_sparse_grid_reserve(&in,128));
    for(int z=-2;z<=2;++z)for(int y=-2;y<=2;++y)for(int x=-2;x<=2;++x){size_t i=in.count++;in.coords[i]=(tvdb_vec3i){x,y,z};in.values[i]=(x+2*y+3*z)*.07f;}
    in.voxel_size=.5f;in.ox=1;in.oy=-2;
    float w[27];for(int i=0;i<27;++i)w[i]=(i%5-2)*.01f;
    CHECK(tvdb_gpu_sparse_grid_upload(c,&in,&g,&err)==TVDB_OK);
    tvdb_gpu_resident_metrics_reset(c);
    CHECK(tvdb_gpu_sparse_conv_resident(c,g,w,3,3,3,1,0,.4f,&o,&err)==TVDB_OK);
    tvdb_gpu_resident_metrics_t m;tvdb_gpu_resident_metrics(c,&m);CHECK(m.download_bytes==0);
    CHECK(tvdb_gpu_sparse_grid_download(o,&got,&err)==TVDB_OK);
    CHECK(tvdb_sparse_conv3d(&in,w,3,3,3,.4f,&ref));CHECK(equal(&got,&ref));
    for(int kind=0;kind<2;++kind){
        tvdb_gpu_resident_metrics_reset(c);
        CHECK(tvdb_gpu_sparse_morph_resident(c,g,kind,2,.4f,&o,&err)==TVDB_OK);
        tvdb_gpu_resident_metrics(c,&m);CHECK(m.download_bytes<=16);
        CHECK(tvdb_gpu_sparse_grid_download(o,&got,&err)==TVDB_OK);
        CHECK(kind?tvdb_erode_sparse(&in,2,&ref):tvdb_dilate_sparse(&in,.4f,2,&ref));CHECK(equal(&got,&ref));
    }
    for(int kind=1;kind<=2;++kind){
        CHECK(tvdb_gpu_sparse_conv_resident(c,g,w,3,3,3,2,kind,.4f,&o,&err)==TVDB_OK);
        CHECK(tvdb_gpu_sparse_grid_download(o,&got,&err)==TVDB_OK);
        CHECK(reference_conv(&in,w,2,kind==2,.4f,&ref));
        CHECK(equal(&got,&ref));CHECK(got.voxel_size==ref.voxel_size);
    }
    in.coords[in.count]=in.coords[0];in.values[in.count++]=2;
    CHECK(tvdb_gpu_sparse_grid_upload(c,&in,&g,&err)==TVDB_OK);
    CHECK(tvdb_gpu_sparse_conv_resident(c,g,w,3,3,3,2,2,0,&o,&err)==TVDB_OK);
    CHECK(tvdb_gpu_sparse_grid_download(o,&got,&err)==TVDB_OK);
    CHECK(reference_conv(&in,w,2,1,0,&ref));CHECK(equal(&got,&ref));
    tvdb_gpu_resident_metrics_reset(c);
    for(size_t i=0;i<in.count;++i)in.values[i]*=2;
    CHECK(tvdb_gpu_sparse_grid_update_values(g,in.values,in.count,&err)==TVDB_OK);
    tvdb_gpu_resident_metrics(c,&m);CHECK(m.upload_bytes==in.count*4 && m.download_bytes==0 && m.submissions==0);
    CHECK(tvdb_gpu_sparse_grid_download(g,&got,&err)==TVDB_OK);
    for(size_t i=0;i<in.count;++i)CHECK(got.values[i]==in.values[i]);
    /* Duplicate lookup, full signed coordinates, and boundary-neighbor skipping. */
    in.count=4;in.coords[0]=(tvdb_vec3i){INT_MIN,0,0};in.coords[1]=in.coords[0];in.coords[2]=(tvdb_vec3i){INT_MAX,0,0};in.coords[3]=(tvdb_vec3i){0,0,0};
    in.values[0]=2;in.values[1]=-99;in.values[2]=3;in.values[3]=4;
    CHECK(tvdb_gpu_sparse_grid_upload(c,&in,&g,&err)==TVDB_OK);
    CHECK(tvdb_gpu_sparse_morph_resident(c,g,0,1,10,&g,&err)==TVDB_OK);
    CHECK(tvdb_gpu_sparse_grid_download(g,&got,&err)==TVDB_OK);
    CHECK(tvdb_dilate_sparse(&in,10,1,&ref));CHECK(equal(&got,&ref));
    size_t previous=tvdb_gpu_sparse_grid_count(g);
    CHECK(tvdb_gpu_sparse_morph_resident(c,g,0,0,0,&g,&err)==TVDB_ERROR_INVALID_ARGUMENT);

    CHECK(tvdb_gpu_sparse_conv_resident(c,g,w,3,3,3,0,1,0,&g,&err)==TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(tvdb_gpu_sparse_grid_count(g)==previous);
    in.count=0;CHECK(tvdb_gpu_sparse_grid_upload(c,&in,&g,&err)==TVDB_OK);
    CHECK(tvdb_gpu_sparse_morph_resident(c,g,1,1,0,&o,&err)==TVDB_OK);CHECK(tvdb_gpu_sparse_grid_count(o)==0);
    /* Resident materialization round trip and point voxelization. */
    tvdb_gpu_grid_desc_t desc={7,5,3,1,TVDB_GPU_F32,1,-2,3,.5};
    float dense_data[105],dense_got[105];for(int i=0;i<105;++i)dense_data[i]=i%3?0:(float)i;
    CHECK(tvdb_gpu_dense_grid_create(c,&desc,&dense,&err)==TVDB_OK);
    CHECK(tvdb_gpu_dense_grid_upload(dense,dense_data,sizeof(dense_data),&err)==TVDB_OK);
    tvdb_gpu_resident_metrics_reset(c);
    CHECK(tvdb_gpu_dense_to_sparse_resident(c,dense,0,0,&g,&err)==TVDB_OK);
    CHECK(tvdb_gpu_sparse_to_dense_resident(c,g,0,dense,&err)==TVDB_OK);
    tvdb_gpu_resident_metrics(c,&m);CHECK(m.download_bytes==4);
    CHECK(tvdb_gpu_dense_grid_download(dense,dense_got,sizeof(dense_got),&err)==TVDB_OK);
    for(int i=0;i<105;++i)CHECK(dense_data[i]==dense_got[i]);
    float pts[12]={0,0,0,.1f,.2f,.3f,-.1f,0,0,1048576,0,0},origin[3]={0,0,0};
    CHECK(tvdb_gpu_buffer_create_device(c,sizeof(pts),&points,&err)==TVDB_OK);
    CHECK(tvdb_gpu_buffer_upload(points,pts,sizeof(pts),&err)==TVDB_OK);
    CHECK(tvdb_gpu_voxelize_resident(c,points,4,origin,1,&g,&err)==TVDB_OK);
    CHECK(tvdb_gpu_sparse_grid_count(g)==3);
    CHECK(tvdb_gpu_sparse_grid_download(g,&got,&err)==TVDB_OK);
    CHECK(got.coords[0].x==0 && got.coords[1].x==-1 && got.coords[2].x==1048576);
    pts[0]=NAN;CHECK(tvdb_gpu_buffer_upload(points,pts,sizeof(pts),&err)==TVDB_OK);
    CHECK(tvdb_gpu_voxelize_resident(c,points,4,origin,1,&g,&err)==TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(tvdb_gpu_sparse_grid_count(g)==3);
done:
    tvdb_sparse_grid_free(&in);tvdb_sparse_grid_free(&ref);tvdb_sparse_grid_free(&got);
    tvdb_gpu_dense_grid_destroy(dense);tvdb_gpu_buffer_destroy(points);
    tvdb_gpu_sparse_grid_destroy(g);tvdb_gpu_sparse_grid_destroy(o);
    tvdb_gpu_resident_metrics_t final;tvdb_gpu_resident_metrics(c,&final);if(final.live_bytes){fprintf(stderr,"leak: %zu\n",final.live_bytes);failed=1;}
    tvdb_gpu_context_destroy(c);return failed;
}
