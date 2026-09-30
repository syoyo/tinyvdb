/* CPU-parity checks for the PDE stencils (laplacian, central differences,
 * gradient, divergence, curl) on both backends.
 *
 * The contract is the CPU reference in tinyvdb_ops.c, including its edge
 * handling (reads clamp at the grid boundary). Comparison is absolute, matching
 * the tolerance convention the rest of the GPU test suite uses: the shader
 * contracts multiply-add into FMA, so a relative tolerance would be misleading
 * at voxels where the stencil result cancels to near zero.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "tinyvdb_gpu.h"
static int g_failures = 0;
#define EXPECT(cond) do { if (!(cond)) { \
  fprintf(stderr, "FAIL [%s:%d]: %s\n", __FILE__, __LINE__, #cond); ++g_failures; } } while (0)
static int fails=0;
static void cmp(const char*name,const float*a,const float*b,size_t n,float tol){ (void)n;
    double worst=0; size_t wi=0; double worstd=0; double maxabs=0; double scale=0;
    for(size_t i=0;i<n;i++){ double d=fabs((double)a[i]-(double)b[i]); double s=fabs(b[i])>1e-6?fabs(b[i]):1.0;
        double r=d/s; if(r>worst){worst=r;wi=i;} if(d>maxabs)maxabs=d; if(fabs(b[i])>scale)scale=fabs(b[i]); }
    (void)worst; (void)wi;
    if(maxabs>tol){ printf("  FAIL %-22s maxabs %.3e > tol %.1e\n",name,maxabs,tol); fails++; }
    else printf("  ok   %-22s maxabs %.3e (tol %.0e)\n",name,maxabs,tol);
}
int main(int argc,char**argv){
    setvbuf(stdout,NULL,_IONBF,0);
    int backend = (argc>1&&argv[1][0]=='c')?TVDB_GPU_BACKEND_CUDA:TVDB_GPU_BACKEND_VULKAN;
    tvdb_error_t e; memset(&e,0,sizeof e);
    tvdb_gpu_context_t*ctx=NULL;
    if(tvdb_gpu_context_create(backend,0,&ctx,&e)!=TVDB_OK){printf("SKIP: no GPU context: %s\n", e.message);return 77;}
    printf("backend=%s\n", backend==TVDB_GPU_BACKEND_CUDA?"cuda":"vulkan");
    if(backend==TVDB_GPU_BACKEND_VULKAN && !tvdb_gpu_spirv_available()){
        printf("SKIP: built without GPU SPIR-V\n");tvdb_gpu_context_destroy(ctx);return 77;}
    /* non-cubic dims so x/y/z are distinguishable, and a non-round voxel size */
    int nx=17,ny=11,nz=5; float h=0.37f;
    size_t n=(size_t)nx*ny*nz;
    tvdb_dense_grid in; memset(&in,0,sizeof in);
    in.nx=nx;in.ny=ny;in.nz=nz;in.voxel_size=h;in.ox=-1.f;in.oy=0.5f;in.oz=2.f;
    in.data=malloc(n*sizeof(float));
    for(int iz=0;iz<nz;iz++)for(int iy=0;iy<ny;iy++)for(int ix=0;ix<nx;ix++)
        in.data[((size_t)iz*ny+iy)*nx+ix] = sinf(0.7f*ix+0.3f*iy-0.11f*iz)*2.0f + cosf(0.05f*ix*iy)*0.5f;
    tvdb_dense_vec_grid vin; memset(&vin,0,sizeof vin);
    vin.nx=nx;vin.ny=ny;vin.nz=nz;vin.voxel_size=h;vin.ox=in.ox;vin.oy=in.oy;vin.oz=in.oz;
    vin.data=malloc(n*3*sizeof(float));
    for(size_t i=0;i<n;i++)for(int c=0;c<3;c++)
        vin.data[3*i+c] = sinf(0.3f*(float)i+0.7f*c)*1.5f + cosf(0.02f*(float)i)*0.25f;

    const char* snames[4]={"laplacian","central_diff_x","central_diff_y","central_diff_z"};
    for(int op=0;op<4;op++){
        tvdb_dense_grid cpu; memset(&cpu,0,sizeof cpu);
        tvdb_dense_grid gpu; memset(&gpu,0,sizeof gpu);
        tvdb_dense_grid ref; memset(&ref,0,sizeof ref);
        /* CPU reference */
        ref.nx=nx;ref.ny=ny;ref.nz=nz;ref.voxel_size=h;
        ref.data=malloc(n*sizeof(float));
        if(op==0) tvdb_laplacian(&in,&ref);
        else if(op==1) for(int iz=0;iz<nz;iz++)for(int iy=0;iy<ny;iy++)for(int ix=0;ix<nx;ix++) ref.data[((size_t)iz*ny+iy)*nx+ix]=tvdb_central_diff_x(&in,ix,iy,iz);
        else if(op==2) for(int iz=0;iz<nz;iz++)for(int iy=0;iy<ny;iy++)for(int ix=0;ix<nx;ix++) ref.data[((size_t)iz*ny+iy)*nx+ix]=tvdb_central_diff_y(&in,ix,iy,iz);
        else          for(int iz=0;iz<nz;iz++)for(int iy=0;iy<ny;iy++)for(int ix=0;ix<nx;ix++) ref.data[((size_t)iz*ny+iy)*nx+ix]=tvdb_central_diff_z(&in,ix,iy,iz);
        if(tvdb_gpu_stencil_scalar_scalar(ctx,&in,op,&gpu,&e)!=TVDB_OK){printf("  FAIL %s: %s\n",snames[op],e.message);fails++;continue;}
        if(gpu.nx!=nx||gpu.ny!=ny||gpu.nz!=nz){printf("  FAIL %s dims (%d,%d,%d)\n",snames[op],gpu.nx,gpu.ny,gpu.nz);fails++;}
        else if(!gpu.data||!ref.data){printf("  FAIL %s null data\n",snames[op]);fails++;}
        else cmp(snames[op],gpu.data,ref.data,n,2e-5f);
        free(ref.data); free(gpu.data); free(cpu.data);
    }
    { tvdb_dense_vec_grid gref; memset(&gref,0,sizeof gref);
      gref.nx=nx;gref.ny=ny;gref.nz=nz;gref.voxel_size=h;gref.data=malloc(n*3*sizeof(float));
      tvdb_gradient(&in,&gref);
      tvdb_dense_vec_grid gg; memset(&gg,0,sizeof gg);
      if(tvdb_gpu_gradient(ctx,&in,&gg,&e)!=TVDB_OK){printf("  FAIL gradient: %s\n",e.message);fails++;}
      else { if(gg.nx!=nx||gg.ny!=ny||gg.nz!=nz){printf("  FAIL gradient dims\n");fails++;} else cmp("gradient",gg.data,gref.data,n*3,2e-5f); }
      free(gref.data); free(gg.data); }
    { tvdb_dense_grid dref; memset(&dref,0,sizeof dref);
      dref.nx=nx;dref.ny=ny;dref.nz=nz;dref.voxel_size=h;dref.data=malloc(n*sizeof(float));
      tvdb_divergence(&vin,&dref);
      tvdb_dense_grid dg; memset(&dg,0,sizeof dg);
      if(tvdb_gpu_divergence(ctx,&vin,&dg,&e)!=TVDB_OK){printf("  FAIL divergence: %s\n",e.message);fails++;}
      else cmp("divergence",dg.data,dref.data,n,2e-5f);
      free(dref.data); free(dg.data); }
    { tvdb_dense_vec_grid cref; memset(&cref,0,sizeof cref);
      cref.nx=nx;cref.ny=ny;cref.nz=nz;cref.voxel_size=h;cref.data=malloc(n*3*sizeof(float));
      tvdb_curl(&vin,&cref);
      tvdb_dense_vec_grid cg; memset(&cg,0,sizeof cg);
      if(tvdb_gpu_curl(ctx,&vin,&cg,&e)!=TVDB_OK){printf("  FAIL curl: %s\n",e.message);fails++;}
      else cmp("curl",cg.data,cref.data,n*3,2e-5f);
      free(cref.data); free(cg.data); }

    /* vec3 elementwise ops. Seed a zero vector so normalize's magnitude==0 edge
     * case is actually exercised, not just the generic path. */
    { tvdb_dense_vec_grid zref; memset(&zref,0,sizeof zref);
      zref.nx=nx;zref.ny=ny;zref.nz=nz;zref.voxel_size=h;zref.data=calloc(n*3,sizeof(float));
      for(size_t i=0;i<n;i++){ zref.data[3*i+0]=0.f; zref.data[3*i+1]=0.f; zref.data[3*i+2]=0.f; }
      tvdb_dense_vec_grid gz; memset(&gz,0,sizeof gz);
      if(tvdb_gpu_normalize_vec(ctx,&zref,&gz,&e)!=TVDB_OK){printf("  FAIL normalize(zero): %s\n",e.message);fails++;}
      else { int allzero=1; for(size_t i=0;i<n*3;i++) if(gz.data[i]!=0.0f) allzero=0;
             if(!allzero){printf("  FAIL normalize(zero) should be all zero\n");fails++;}
             else printf("  ok   normalize(zero)     all zero as expected\n"); }
      free(zref.data); free(gz.data); }
    { tvdb_dense_grid mref; memset(&mref,0,sizeof mref);
      mref.nx=nx;mref.ny=ny;mref.nz=nz;mref.voxel_size=h;mref.data=malloc(n*sizeof(float));
      tvdb_magnitude(&vin,&mref);
      tvdb_dense_grid mg; memset(&mg,0,sizeof mg);
      if(tvdb_gpu_magnitude(ctx,&vin,&mg,&e)!=TVDB_OK){printf("  FAIL magnitude: %s\n",e.message);fails++;}
      else cmp("magnitude",mg.data,mref.data,n,2e-5f);
      free(mref.data); free(mg.data); }
    { tvdb_dense_vec_grid nref; memset(&nref,0,sizeof nref);
      nref.nx=nx;nref.ny=ny;nref.nz=nz;nref.voxel_size=h;nref.data=malloc(n*3*sizeof(float));
      tvdb_normalize_vec(&vin,&nref);
      tvdb_dense_vec_grid ng; memset(&ng,0,sizeof ng);
      if(tvdb_gpu_normalize_vec(ctx,&vin,&ng,&e)!=TVDB_OK){printf("  FAIL normalize: %s\n",e.message);fails++;}
      else cmp("normalize",ng.data,nref.data,n*3,2e-5f);
      free(nref.data); free(ng.data); }
    { tvdb_dense_vec_grid cref; memset(&cref,0,sizeof cref);
      cref.nx=nx;cref.ny=ny;cref.nz=nz;cref.voxel_size=h;cref.ox=in.ox;cref.oy=in.oy;cref.oz=in.oz;
      cref.data=malloc(n*3*sizeof(float));
      tvdb_cpt(&in,&cref);
      tvdb_dense_vec_grid cg; memset(&cg,0,sizeof cg);
      if(tvdb_gpu_cpt(ctx,&in,&cg,&e)!=TVDB_OK){printf("  FAIL cpt: %s\n",e.message);fails++;}
      else cmp("cpt",cg.data,cref.data,n*3,2e-5f);
      free(cref.data); free(cg.data); }

    /* Mean curvature flow: Jacobi, so the GPU runs `iterations` dispatches
     * ping-ponging buffers. Compared against the CPU reference after several
     * iterations, which is where a stencil-order or boundary mistake shows up. */
    { int nx3=13, ny3=11, nz3=9, ITERS=4; float h3=0.4f, dt3=0.05f;
      size_t n3=(size_t)nx3*ny3*nz3;
      tvdb_dense_grid m; memset(&m,0,sizeof m);
      m.nx=nx3;m.ny=ny3;m.nz=nz3;m.voxel_size=h3;m.ox=-0.7f;m.oy=0.3f;m.oz=1.1f;
      m.data=malloc(n3*sizeof(float));
      for(int z=0;z<nz3;z++)for(int y=0;y<ny3;y++)for(int x=0;x<nx3;x++)
          m.data[((size_t)z*ny3+y)*nx3+x]= sinf(0.9f*x+0.4f*y-0.7f*z)+0.25f*cosf(0.3f*x*y);
      tvdb_dense_grid cref; memset(&cref,0,sizeof cref);
      cref.nx=nx3;cref.ny=ny3;cref.nz=nz3;cref.voxel_size=h3;cref.data=malloc(n3*sizeof(float));
      memcpy(cref.data,m.data,n3*sizeof(float));
      tvdb_mean_curvature_flow(&cref,dt3,ITERS);
      tvdb_dense_grid mg3; memset(&mg3,0,sizeof mg3);
      if(tvdb_gpu_mean_curvature_flow(ctx,&m,dt3,ITERS,&mg3,&e)!=TVDB_OK){printf("  FAIL mcf: %s\n",e.message);fails++;}
      else cmp("mean_curvature_flow",mg3.data,cref.data,n3,1e-4f);
      free(m.data); free(cref.data); free(mg3.data); }
    tvdb_gpu_context_destroy(ctx);
    EXPECT(fails == 0);
    if (!fails) printf("PDE stencil parity: OK (%s)\n", backend==TVDB_GPU_BACKEND_CUDA?"cuda":"vulkan");
    return fails?1:0;
}
