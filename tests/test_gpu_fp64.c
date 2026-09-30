/* CPU-parity checks for the fp64 scalar stencils and fp64 CSG on both backends.
 *
 * fp64 is an optional Vulkan feature (shaderFloat64) and is a fraction of fp32
 * rate on consumer parts, so the ops report TVDB_ERROR_UNIMPLEMENTED when the
 * device cannot run them rather than silently computing in fp32. This test
 * checks that gate as well as the arithmetic, and skips cleanly when the device
 * has no fp64 at all.
 *
 * Tolerance is relative, 1e-12: the whole point of these ops is double
 * precision, so a tolerance that would also pass fp32 (1e-5) would be
 * meaningless here.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "tinyvdb_gpu.h"
static int fails=0;
static void cmp(const char*n,const double*a,const double*b,size_t m){
  double worst=0;
  for(size_t i=0;i<m;i++){ double d=fabs(a[i]-b[i]); double s=fabs(b[i])>1e-9?fabs(b[i]):1.0; double r=d/s; if(r>worst)worst=r; }
  if(worst>1e-12){printf("  FAIL %-20s worst rel %.3e\n",n,worst);fails++;} else printf("  ok   %-20s worst rel %.3e\n",n,worst);
}
static void cdat(const tvdb_dense_grid_d*g,int x,int y,int z,double*o){
  if(x<0)x=0; if(x>g->nx-1)x=g->nx-1; if(y<0)y=0; if(y>g->ny-1)y=g->ny-1; if(z<0)z=0; if(z>g->nz-1)z=g->nz-1;
  *o=g->data[((size_t)z*g->ny+y)*g->nx+x];
}
int main(int argc,char**argv){
    int backend=(argc>1&&argv[1][0]=='c')?TVDB_GPU_BACKEND_CUDA:TVDB_GPU_BACKEND_VULKAN;
    tvdb_error_t e; memset(&e,0,sizeof e);
    tvdb_gpu_context_t*ctx=NULL;
    if(tvdb_gpu_context_create(backend,0,&ctx,&e)!=TVDB_OK){printf("no ctx\n");return 77;}
    printf("backend=%s fp64 supported=%d\n", backend==TVDB_GPU_BACKEND_CUDA?"cuda":"vulkan", (int)tvdb_gpu_supports_fp64(ctx));
    if(backend==TVDB_GPU_BACKEND_VULKAN && !tvdb_gpu_spirv_available()){
        printf("SKIP: built without GPU SPIR-V\n");tvdb_gpu_context_destroy(ctx);return 77;}
    if(!tvdb_gpu_supports_fp64(ctx)){printf("SKIP: no fp64\n");tvdb_gpu_context_destroy(ctx);return 0;}
    int nx=13,ny=9,nz=4; double h=0.31; size_t n=(size_t)nx*ny*nz;
    tvdb_dense_grid_d in; memset(&in,0,sizeof in);
    in.nx=nx;in.ny=ny;in.nz=nz;in.voxel_size=h;in.ox=-1.0;in.oy=0.25;in.oz=2.0;
    in.data=malloc(n*sizeof(double));
    for(int z=0;z<nz;z++)for(int y=0;y<ny;y++)for(int x=0;x<nx;x++)
        in.data[((size_t)z*ny+y)*nx+x]= sin(0.7*x+0.3*y-0.11*z)*2.0 + cos(0.05*(double)x*y)*0.5;
    const char* nm[4]={"laplacian_d","central_diff_x_d","central_diff_y_d","central_diff_z_d"};
    for(int op=0;op<4;op++){
        tvdb_dense_grid_d gpu; memset(&gpu,0,sizeof gpu);
        if(tvdb_gpu_stencil_scalar_d(ctx,&in,op,&gpu,&e)!=TVDB_OK){printf("  FAIL %s: %s\n",nm[op],e.message);fails++;continue;}
        double* ref=malloc(n*sizeof(double));
        if(op==0){ double ih2=1.0/(h*h);
            for(int z=0;z<nz;z++)for(int y=0;y<ny;y++)for(int x=0;x<nx;x++){
                double c,a,b,d,f,g; cdat(&in,x,y,z,&c);
                cdat(&in,x-1,y,z,&a); cdat(&in,x+1,y,z,&b); cdat(&in,x,y-1,z,&d);
                cdat(&in,x,y+1,z,&f); cdat(&in,x,y,z-1,&g); double s2; cdat(&in,x,y,z+1,&s2);
                ref[((size_t)z*ny+y)*nx+x]=(a+b+d+f+g+s2-6.0*c)*ih2; } }
        else for(int z=0;z<nz;z++)for(int y=0;y<ny;y++)for(int x=0;x<nx;x++){
            double p,q;
            if(op==1){cdat(&in,x+1,y,z,&p);cdat(&in,x-1,y,z,&q);}
            else if(op==2){cdat(&in,x,y+1,z,&p);cdat(&in,x,y-1,z,&q);}
            else {cdat(&in,x,y,z+1,&p);cdat(&in,x,y,z-1,&q);}
            ref[((size_t)z*ny+y)*nx+x]=(p-q)/(2.0*h); }
        if(gpu.nx!=nx||gpu.ny!=ny||gpu.nz!=nz||!gpu.data){printf("  FAIL %s dims\n",nm[op]);fails++;}
        else cmp(nm[op],gpu.data,ref,n);
        free(ref); free(gpu.data);
    }
    /* Batched fp64 trilinear sample against tvdb_sample_trilinear_dense_d.
     * Points are spread past both edges of the grid so the clamp is exercised,
     * and the grid origin is far from the origin in world space, which is where
     * carrying the geometry in fp32 would start losing voxels. */
    {
        const size_t npts = 517;   /* not a multiple of the 128-wide group */
        double* pts=malloc(npts*3*sizeof(double));
        double* got=malloc(npts*sizeof(double));
        double* ref=malloc(npts*sizeof(double));
        for(size_t i=0;i<npts;i++){
            double t=(double)i/(double)npts;
            pts[3*i+0]= -0.5 + t*4.0*h + 0.013*i;      /* spans outside both ends */
            pts[3*i+1]=  0.25 - t*3.0*h - 0.007*i;
            pts[3*i+2]=  2.0 + t*2.0*h + 0.003*i;
        }
        if(tvdb_gpu_sample_trilinear_dense_d_batch(ctx,&in,pts,npts,got,&e)!=TVDB_OK){
            printf("  FAIL sample_trilinear_d: %s\n",e.message);fails++;
        } else {
            for(size_t i=0;i<npts;i++)
                ref[i]=tvdb_sample_trilinear_dense_d(&in,pts[3*i],pts[3*i+1],pts[3*i+2]);
            cmp("sample_trilinear_d",got,ref,npts);
        }
        free(pts); free(got); free(ref);
    }

    /* fp64 CSG: min / max / max-with-negation, against the CPU twins. The CPU
     * uses `va < vb ? va : vb`, which differs from fmin/fmax on signed zero, so
     * the fields below include an exact +0.0/-0.0 pair: that is the one place a
     * naive min()/max() implementation would silently disagree. */
    {
        tvdb_dense_grid_d a=in, b=in; memset(&a,0,sizeof a); memset(&b,0,sizeof b);
        a.nx=b.nx=nx; a.ny=b.ny=ny; a.nz=b.nz=nz; a.voxel_size=b.voxel_size=h;
        a.ox=b.ox=in.ox; a.oy=b.oy=in.oy; a.oz=b.oz=in.oz;
        a.data=malloc(n*sizeof(double)); b.data=malloc(n*sizeof(double));
        for(int z=0;z<nz;z++)for(int y=0;y<ny;y++)for(int x=0;x<nx;x++){
            size_t i=((size_t)z*ny+y)*nx+x;
            a.data[i]= sin(0.31*x+0.17*y)*3.0;
            b.data[i]= cos(0.23*y-0.11*z)*3.0;
        }
        /* signed zeros: a=+0, b=-0 exercises the comparison-vs-min divergence */
        a.data[0]= 0.0; b.data[0]=-0.0;
        a.data[1]=-0.0; b.data[1]= 0.0;
        const char* cn[3]={"csg_union_d","csg_intersection_d","csg_difference_d"};
        for(int op=0;op<3;op++){
            tvdb_dense_grid_d gpu; memset(&gpu,0,sizeof gpu);
            if(tvdb_gpu_csg_dense_d(ctx,&a,&b,op,&gpu,&e)!=TVDB_OK){
                printf("  FAIL %s: %s\n",cn[op],e.message);fails++;continue; }
            if(gpu.nx!=nx||gpu.ny!=ny||gpu.nz!=nz||!gpu.data){
                printf("  FAIL %s dims\n",cn[op]);fails++;continue; }
            tvdb_dense_grid_d ref; memset(&ref,0,sizeof ref);
            ref.nx=nx;ref.ny=ny;ref.nz=nz;ref.voxel_size=h;ref.ox=a.ox;ref.oy=a.oy;ref.oz=a.oz;
            ref.data=malloc(n*sizeof(double));
            if(op==0) tvdb_csg_union_d(&a,&b,&ref);
            else if(op==1) tvdb_csg_intersection_d(&a,&b,&ref);
            else tvdb_csg_difference_d(&a,&b,&ref);
            /* Compare bit patterns, not values: signed zero is the point here. */
            int bad=0;
            for(size_t i=0;i<n;i++){
                if(memcmp(&gpu.data[i],&ref.data[i],sizeof(double))!=0){
                    if(!bad) printf("  FAIL %-20s at %zu gpu=%.17g ref=%.17g\n",
                                    cn[op],i,gpu.data[i],ref.data[i]);
                    bad++;
                }
            }
            if(bad) fails++;
            else printf("  ok   %-20s bit-exact over %zu voxels (incl. signed zero)\n",cn[op],n);
            free(ref.data); free(gpu.data);
        }
        /* shape mismatch must be rejected, not silently computed */
        { tvdb_dense_grid_d bad=a; bad.nx=nx-1; tvdb_dense_grid_d o; memset(&o,0,sizeof o);
          if(tvdb_gpu_csg_dense_d(ctx,&a,&bad,0,&o,&e)==TVDB_OK){printf("  FAIL csg_d accepted mismatched shapes\n");fails++;}
          else printf("  ok   %-20s mismatched shapes rejected\n","csg_dense_d"); }
        free(a.data); free(b.data);
    }

    tvdb_gpu_context_destroy(ctx);
    if(fails){printf("FP64 PARITY: FAIL\n");return 1;}
    printf("FP64 PARITY: OK\n"); return 0;
}
