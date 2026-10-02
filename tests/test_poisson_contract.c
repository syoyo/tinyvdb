/* Independent residual and failure-contract tests, shared by CPU and GPU. */
#include "tinyvdb_ops.h"
#ifdef TVDB_TEST_GPU
#include "tinyvdb_gpu.h"
#endif
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures;
#define CHECK(c) do { if (!(c)) { fprintf(stderr,"%s:%d: %s\n",__FILE__,__LINE__,#c); ++failures; } } while(0)
#ifdef TVDB_TEST_GPU
static tvdb_gpu_context_t* ctx;
#endif
static double lap(const double* x,int i,int nx,int ny,int nz,double h) {
  int a=i%nx,b=(i/nx)%ny,c=i/(nx*ny); double s=0;
  if(a) s+=x[i-1]-x[i]; if(a+1<nx) s+=x[i+1]-x[i];
  if(b) s+=x[i-nx]-x[i]; if(b+1<ny) s+=x[i+nx]-x[i];
  if(c) s+=x[i-nx*ny]-x[i]; if(c+1<nz) s+=x[i+nx*ny]-x[i];
  return s/(h*h);
}
static tvdb_status_t solve(int precision,tvdb_dense_grid* rhs,tvdb_dense_grid* x,
 tvdb_dense_grid_d* rd,tvdb_dense_grid_d* xd,int budget,double tol,tvdb_poisson_result_t* info) {
  tvdb_error_t err;
#ifdef TVDB_TEST_GPU
#ifdef TVDB_TEST_RESIDENT
  tvdb_gpu_grid_desc_t d={rhs->nx,rhs->ny,rhs->nz,1,precision==2?TVDB_GPU_F64:TVDB_GPU_F32,0,0,0,precision==2?rd->voxel_size:rhs->voxel_size};
  tvdb_gpu_dense_grid_t *r=NULL,*g=NULL;
  tvdb_status_t st=tvdb_gpu_dense_grid_create(ctx,&d,&r,&err);
  size_t bytes=(size_t)d.nx*d.ny*d.nz*(precision==2?8:4);
  if(st==TVDB_OK)st=tvdb_gpu_dense_grid_create(ctx,&d,&g,&err);
  if(st==TVDB_OK)st=tvdb_gpu_dense_grid_upload(r,precision==2?(const void*)rd->data:(const void*)rhs->data,bytes,&err);
  if(st==TVDB_OK)st=tvdb_gpu_dense_grid_upload(g,precision==2?(const void*)xd->data:(const void*)x->data,bytes,&err);
  tvdb_gpu_resident_metrics_reset(ctx);
  if(st==TVDB_OK)st=tvdb_gpu_poisson_resident(ctx,r,g,precision,budget,tol,info,&err);
  tvdb_gpu_resident_metrics_t metrics;tvdb_gpu_resident_metrics(ctx,&metrics);
  CHECK(metrics.download_bytes<=32u*(12u*(unsigned)info->iterations+8u));
  /* Include both inputs, transactional output scratch, partial reductions,
   * and a batch of CUDA uniforms. Float work vectors must not occupy double storage. */
  size_t count=(size_t)d.nx*d.ny*d.nz;
  size_t work_bytes_per_voxel=precision==0?40u:precision==1?64u:72u;
  CHECK(metrics.peak_bytes<=3*bytes+count*work_bytes_per_voxel+64*((count+127)/128)+16*80);
  /* A reduction result is the synchronization boundary, rather than each
   * stencil/vector kernel and each level of its device reduction. */
  CHECK(metrics.submissions<=metrics.download_bytes/32+1);
  /* Read back on failure too: the device output must retain its old values. */
  if(g)CHECK(tvdb_gpu_dense_grid_download(g,precision==2?(void*)xd->data:(void*)x->data,bytes,&err)==TVDB_OK);
  tvdb_gpu_dense_grid_destroy(r);tvdb_gpu_dense_grid_destroy(g);
  if(st!=TVDB_OK && budget>=0 && isfinite(tol))fprintf(stderr,"resident solve status=%d: %s\n",st,err.message);
  return st;
#else
  if(precision==2) return tvdb_gpu_solve_poisson_dd_ex(ctx,rd,xd,budget,tol,info,&err);
  if(precision==1) return tvdb_gpu_solve_poisson_d_ex(ctx,rhs,x,budget,tol,info,&err);
  return tvdb_gpu_solve_poisson_ex(ctx,rhs,x,budget,(float)tol,info,&err);
#endif
#else
  if(precision==2) return tvdb_solve_poisson_dd_ex(rd,xd,budget,tol,info,&err);
  if(precision==1) return tvdb_solve_poisson_d_ex(rhs,x,budget,tol,info,&err);
  return tvdb_solve_poisson_ex(rhs,x,budget,(float)tol,info,&err);
#endif
}
static void run(int precision,int nx,int ny,int nz,int budget) {
  int n=nx*ny*nz; double h=precision==2 ? 0.7000000000000001 : 0.5;
  tvdb_dense_grid r={0},x={0}; tvdb_dense_grid_d rd={0},xd={0};
  r.nx=x.nx=rd.nx=xd.nx=nx; r.ny=x.ny=rd.ny=xd.ny=ny; r.nz=x.nz=rd.nz=xd.nz=nz;
  r.voxel_size=x.voxel_size=(float)h; rd.voxel_size=xd.voxel_size=h;
  r.data=calloc(n,sizeof(float)); x.data=calloc(n,sizeof(float));
  rd.data=calloc(n,sizeof(double)); xd.data=calloc(n,sizeof(double));
  double* exact=malloc(n*sizeof(double)); double* returned=malloc(n*sizeof(double));
  CHECK(r.data && x.data && rd.data && xd.data && exact && returned);
  if(!r.data || !x.data || !rd.data || !xd.data || !exact || !returned) exit(1);
  for(int i=0;i<n;++i) exact[i]=sin(i*0.37)+cos(i*0.11);
  for(int i=0;i<n;++i) { rd.data[i]=lap(exact,i,nx,ny,nz,h); r.data[i]=(float)rd.data[i]; x.data[i]=3; xd.data[i]=3; }
  tvdb_poisson_result_t info;
  double tol=precision==2 ? 1e-9 : 2e-5;
  CHECK(solve(precision,&r,&x,&rd,&xd,budget,tol,&info)==TVDB_OK);
  double rhsmean=0,mean=0,norm=0;
  for(int i=0;i<n;++i) { rhsmean+=precision==2 ? rd.data[i] : r.data[i]; returned[i]=precision==2 ? xd.data[i] : x.data[i]; mean+=returned[i]; }
  rhsmean/=n;
  for(int i=0;i<n;++i) { double d=(precision==2 ? rd.data[i] : r.data[i])-rhsmean-lap(returned,i,nx,ny,nz,h); norm+=d*d; }
  norm=sqrt(norm);
  double target=precision==2 ? tol : tol*info.initial_residual_norm;
  if(budget==500) CHECK(info.converged);
  CHECK(info.iterations<=budget); CHECK(fabs(mean/n-3)<2e-6);
  CHECK(norm <= info.initial_residual_norm*1.05+1e-12);
  if(info.converged) CHECK(norm<=target*1.05+1e-12);
  else CHECK(norm>=target*.95);
  CHECK(fabs(info.final_residual_norm-norm)<1e-5*(1+norm));
  /* A finite iteration budget returns a finite, honestly reported iterate. */
  if(n>1) {
    for(int i=0;i<n;++i) x.data[i]=xd.data[i]=0;
    CHECK(solve(precision,&r,&x,&rd,&xd,1,tol,&info)==TVDB_OK);
    CHECK(info.iterations==1 && !info.converged && isfinite(info.final_residual_norm));
    /* The best returned iterate can remain the warm start for a short budget. */
    CHECK(info.final_residual_norm<=info.initial_residual_norm);
    /* fp64 internal convergence may be lost when restoring a large float mean. */
    if(precision==1) {
      for(int i=0;i<n;++i) x.data[i]=1e8f;
      CHECK(solve(precision,&r,&x,&rd,&xd,budget,1e-9,&info)==TVDB_OK);
      CHECK(!info.converged && info.final_residual_norm>1e-9*info.initial_residual_norm);
    }
  }
  /* Nonzero constant RHS is incompatible; failure must preserve every voxel. */
  for(int i=0;i<n;++i) { r.data[i]=rd.data[i]=1; x.data[i]=xd.data[i]=7; }
  CHECK(solve(precision,&r,&x,&rd,&xd,10,tol,&info)!=TVDB_OK);
  for(int i=0;i<n;++i) CHECK(x.data[i]==7 && xd.data[i]==7);
  /* Reject a nonfinite RHS, including the final partial reduction group. */
  r.data[n-1]=NAN;rd.data[n-1]=NAN;
  CHECK(solve(precision,&r,&x,&rd,&xd,10,tol,&info)!=TVDB_OK);
  for(int i=0;i<n;++i) CHECK(x.data[i]==7 && xd.data[i]==7);
  /* Constant warm starts solve zero RHS without changing the null-space mode. */
  for(int i=0;i<n;++i) r.data[i]=rd.data[i]=0;
  CHECK(solve(precision,&r,&x,&rd,&xd,10,tol,&info)==TVDB_OK);
  CHECK(info.converged && info.iterations==0 && info.final_residual_norm==0);
  for(int i=0;i<n;++i) CHECK(x.data[i]==7 && xd.data[i]==7);
  /* Zero budget and invalid options do not mutate a nontrivial warm start. */
  if(n>1) { r.data[0]=rd.data[0]=1; r.data[1]=rd.data[1]=-1; }
  CHECK(solve(precision,&r,&x,&rd,&xd,0,tol,&info)==TVDB_OK);
  CHECK(info.iterations==0); CHECK(info.converged==(n==1));
  CHECK(solve(precision,&r,&x,&rd,&xd,-1,tol,&info)!=TVDB_OK);
  CHECK(solve(precision,&r,&x,&rd,&xd,10,NAN,&info)!=TVDB_OK);
  for(int i=0;i<n;++i) CHECK(x.data[i]==7 && xd.data[i]==7);
  free(exact); free(returned); free(r.data); free(x.data); free(rd.data); free(xd.data);
}
#ifdef TVDB_TEST_RESIDENT
static void resident_alias(int precision) {
  tvdb_gpu_grid_desc_t d={3,1,1,1,precision==2?TVDB_GPU_F64:TVDB_GPU_F32,0,0,0,1};
  tvdb_gpu_dense_grid_t* g=NULL;tvdb_error_t err={0};
  float f[3]={-1,0,1};double v[3]={-1,0,1};size_t bytes=precision==2?sizeof(v):sizeof(f);
  CHECK(tvdb_gpu_dense_grid_create(ctx,&d,&g,&err)==TVDB_OK);
  if(!g)return;
  CHECK(tvdb_gpu_dense_grid_upload(g,precision==2?(const void*)v:(const void*)f,bytes,&err)==TVDB_OK);
  tvdb_poisson_result_t result;
  CHECK(tvdb_gpu_poisson_resident(ctx,g,g,precision,10,1e-10,&result,&err)==TVDB_OK);
  CHECK(result.converged);
  CHECK(tvdb_gpu_dense_grid_download(g,precision==2?(void*)v:(void*)f,bytes,&err)==TVDB_OK);
  for(int i=0;i<3;++i)CHECK(fabs((precision==2?v[i]:(double)f[i])-(1-i))<1e-5);
  tvdb_gpu_dense_grid_destroy(g);
  tvdb_gpu_resident_metrics_t metrics;tvdb_gpu_resident_metrics(ctx,&metrics);CHECK(metrics.live_bytes==0);
}
#endif
int main(int argc,char** argv) {
  int has64=1;
#ifdef TVDB_TEST_GPU
  tvdb_error_t err; tvdb_gpu_backend_t backend=argc>1 && argv[1][0]=='c' ? TVDB_GPU_BACKEND_CUDA : TVDB_GPU_BACKEND_VULKAN;
  if(tvdb_gpu_context_create(backend,0,&ctx,&err)!=TVDB_OK) return 77;
  if(backend==TVDB_GPU_BACKEND_VULKAN && !tvdb_gpu_spirv_available()) { tvdb_gpu_context_destroy(ctx); return 77; }
  tvdb_gpu_context_info_t device; tvdb_gpu_context_info(ctx,&device,&err);
  printf("backend=%d device=%s\n",(int)device.backend,device.device_name);
  has64=tvdb_gpu_supports_fp64(ctx);
#else
  (void)argc; (void)argv;
#endif
#ifdef TVDB_TEST_RESIDENT
  if(!has64){tvdb_gpu_context_destroy(ctx);return 77;}
  for(int p=0;p<3;++p)run(p,17,9,3,500);
  /* Odd vector lengths and a partially occupied reduction group exercise the
   * float/double workspace boundaries without relying on allocation padding. */
  for(int p=0;p<3;++p)run(p,129,1,1,64);
  for(int p=0;p<3;++p)resident_alias(p);
#endif
  for(int p=0;p<3;++p) { if(p && !has64) continue; run(p,5,4,3,500); run(p,9,1,1,500); run(p,1,1,1,500); }
#ifdef TVDB_TEST_GPU
  tvdb_gpu_context_destroy(ctx);
#endif
  return failures ? 1 : 0;
}
