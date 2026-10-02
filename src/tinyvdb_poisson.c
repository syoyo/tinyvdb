#include "tinyvdb_poisson_internal.h"
#include "tinyvdb_checked.h"
#include <float.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static tvdb_status_t poisson_error(tvdb_error_t* err,tvdb_status_t status,const char* message) {
  if (err) { memset(err,0,sizeof(*err)); err->status=status;
    snprintf(err->message,sizeof(err->message),"Poisson: %s",message); }
  return status;
}
static double poisson_read(const void* data,size_t i,bool fp64) {
  return fp64 ? ((const double*)data)[i] : ((const float*)data)[i];
}
/* Difference form avoids cancellation of the constant null-space component. */
static double poisson_positive_at(const void* data,bool fp64,size_t i,
 int ix,int iy,int iz,int nx,int ny,int nz,double inv_h2) {
  double c=poisson_read(data,i,fp64),sum=0;
  size_t plane=(size_t)nx*ny;
  if(ix>0) sum+=c-poisson_read(data,i-1,fp64);
  if(ix+1<nx) sum+=c-poisson_read(data,i+1,fp64);
  if(iy>0) sum+=c-poisson_read(data,i-nx,fp64);
  if(iy+1<ny) sum+=c-poisson_read(data,i+nx,fp64);
  if(iz>0) sum+=c-poisson_read(data,i-plane,fp64);
  if(iz+1<nz) sum+=c-poisson_read(data,i+plane,fp64);
  return sum*inv_h2;
}

/* Reports use the original projected RHS, without workspace rounding. */
/* How often the candidate residual stencil runs. It is a diagnostic: it supplies
 * info->final_residual_norm and picks which iterate is returned, and neither the
 * convergence test (which uses the cheap residual dot) nor the restart test reads
 * it. Sampling it every eighth iteration, plus on the last iteration and whenever
 * the cheap test says the solve has converged, keeps the reported number
 * meaningful while removing a second full stencil application from most
 * iterations. */
#define TVDB_POISSON_CANDIDATE_STRIDE 8

static double poisson_true_norm(const void* rhs,bool rhs_double,const void* x,bool x_double,
 int nx,int ny,int nz,double h,double rhs_mean) {
  double norm=0,inv_h2=1/(h*h);
  #pragma omp parallel for collapse(2) reduction(+:norm) schedule(static)
  for(int iz=0;iz<nz;++iz) for(int iy=0;iy<ny;++iy) for(int ix=0;ix<nx;++ix) {
    size_t i=((size_t)iz*ny+iy)*nx+ix;
    double r=-(poisson_read(rhs,i,rhs_double)-rhs_mean)-
      poisson_positive_at(x,x_double,i,ix,iy,iz,nx,ny,nz,inv_h2);
    norm+=r*r;
  }
  return sqrt(norm);
}

static double poisson_dot_f(const float* a,const float* b,size_t n) {
  double sum=0;
  #pragma omp parallel for reduction(+:sum) schedule(static)
  for(size_t i=0;i<n;++i) sum+=(double)a[i]*b[i];
  return sum;
}
static void poisson_project_f(float* a,size_t n) {
  double sum=0;
  #pragma omp parallel for reduction(+:sum) schedule(static)
  for(size_t i=0;i<n;++i) sum+=a[i];
  double mean=sum/(double)n;
  #pragma omp parallel for schedule(static)
  for(size_t i=0;i<n;++i) a[i]=(float)((double)a[i]-mean);
}
static tvdb_status_t poisson_apply_f(const float* src,float* dst,int nx,int ny,int nz,
 double h,tvdb_poisson_apply_fn apply,void* context,tvdb_error_t* err) {
  if(apply) return apply(context,src,dst,nx,ny,nz,h,false,err);
  double inv_h2=1/(h*h);
  #pragma omp parallel for collapse(2) schedule(static)
  for(int iz=0;iz<nz;++iz) for(int iy=0;iy<ny;++iy) for(int ix=0;ix<nx;++ix) {
    size_t i=((size_t)iz*ny+iy)*nx+ix;
    dst[i]=(float)poisson_positive_at(src,false,i,ix,iy,iz,nx,ny,nz,inv_h2);
  }
  return TVDB_OK;
}
static double poisson_residual_f(const float* b,const float* x,float* r,
 int nx,int ny,int nz,double h) {
  double sum=0,inv_h2=1/(h*h);
  #pragma omp parallel for collapse(2) reduction(+:sum) schedule(static)
  for(int iz=0;iz<nz;++iz) for(int iy=0;iy<ny;++iy) for(int ix=0;ix<nx;++ix) {
    size_t i=((size_t)iz*ny+iy)*nx+ix;
    double v=(double)b[i]-poisson_positive_at(x,false,i,ix,iy,iz,nx,ny,nz,inv_h2);
    r[i]=(float)v; sum+=v*v;
  }
  return sqrt(sum);
}
static void poisson_precondition_f(const float* r,float* z,int nx,int ny,int nz,double h) {
  #pragma omp parallel for collapse(2) schedule(static)
  for(int iz=0;iz<nz;++iz) for(int iy=0;iy<ny;++iy) for(int ix=0;ix<nx;++ix) {
    size_t i=((size_t)iz*ny+iy)*nx+ix;
    int degree=(ix>0)+(ix+1<nx)+(iy>0)+(iy+1<ny)+(iz>0)+(iz+1<nz);
    z[i]=degree ? (float)((double)r[i]*(h*h)/degree) : 0;
  }
  poisson_project_f(z,(size_t)nx*ny*nz);
}
static tvdb_status_t poisson_solve_f(const void* rhs,void* output,int nx,int ny,int nz,
 double h,bool input_double,int max_iters,double tolerance,bool absolute,
 double rhs_mean,double x_mean,tvdb_poisson_result_t* info,tvdb_error_t* err,
 tvdb_poisson_apply_fn apply,void* context) {
  size_t n=(size_t)nx*ny*nz,bytes;
  if(!tvdb_size_mul(n,7*sizeof(float),&bytes)) return poisson_error(err,TVDB_ERROR_INVALID_ARGUMENT,"workspace size overflow");
  float* storage=(float*)malloc(bytes);
  if(!storage) return poisson_error(err,TVDB_ERROR_OUT_OF_MEMORY,"workspace allocation failed");
  float *x=storage,*b=x+n,*r=b+n,*z=r+n,*p=z+n,*ap=p+n,*best=ap+n;
  for(size_t i=0;i<n;++i) {
    x[i]=(float)(poisson_read(output,i,input_double)-x_mean);
    b[i]=(float)(-(poisson_read(rhs,i,input_double)-rhs_mean));
  }
  poisson_residual_f(b,x,r,nx,ny,nz,h);
  double initial=poisson_true_norm(rhs,input_double,output,input_double,nx,ny,nz,h,rhs_mean);
  info->initial_residual_norm=info->final_residual_norm=initial;
  double best_norm=initial;
  for(size_t i=0;i<n;++i) best[i]=(float)poisson_read(output,i,input_double);
  double target=absolute ? tolerance : tolerance*initial;
  tvdb_status_t st=TVDB_OK;
  if(!isfinite(initial) || !isfinite(target)) { st=poisson_error(err,TVDB_ERROR_INVALID_DATA,"nonfinite residual"); goto done; }
  if(initial<=target) { info->converged=true; goto done; }
  if(max_iters==0) goto done;
  poisson_project_f(r,n);
  poisson_precondition_f(r,z,nx,ny,nz,h);
  memcpy(p,z,n*sizeof(float));
  double rz=poisson_dot_f(r,z,n);
  for(int it=0;it<max_iters;++it) {
    st=poisson_apply_f(p,ap,nx,ny,nz,h,apply,context,err);
    if(st!=TVDB_OK) goto done;
    poisson_project_f(ap,n);
    double pap=poisson_dot_f(p,ap,n),alpha=rz/pap;
    if(!(pap>0) || !isfinite(alpha) || !(rz>0)) {
      st=poisson_error(err,TVDB_ERROR_INVALID_DATA,"conjugate-gradient breakdown"); goto done;
    }
    #pragma omp parallel for schedule(static)
    for(size_t i=0;i<n;++i) { x[i]=(float)((double)x[i]+alpha*p[i]); r[i]=(float)((double)r[i]-alpha*ap[i]); }
    info->iterations=it+1;
    /* rr first: it is a plain vector dot, whereas the candidate below is a second
       full stencil application. Only a dot is needed to decide the restart, so
       computing it first also lets the candidate be skipped on most iterations. */
    double rr=poisson_dot_f(r,r,n);
    if(!isfinite(rr)) { st=poisson_error(err,TVDB_ERROR_INVALID_DATA,"nonfinite iterate"); goto done; }
    const bool converged_now=(sqrt(rr)<=target);

    /* Track the best iterate in the precision actually returned to the caller.
     * The conversion loop was serial and its isfinite check an early exit, so it
     * became one parallel pass with a reduction flag. The stencil is only a
     * sampled diagnostic -- it drives info->final_residual_norm and picks the
     * returned iterate, it does not steer the iteration -- so running it every
     * eighth iteration plus on the last one and on convergence keeps the reported
     * number honest for a fraction of the cost. Convergence decisions never used
     * it; they use rr and the restart residual below. */
    int bad_precision=0;
    #pragma omp parallel for reduction(|:bad_precision) schedule(static)
    for(long long ii=0;ii<(long long)n;++ii) {
      size_t i=(size_t)ii;
      double v=(double)x[i]+x_mean;
      float nv=input_double ? (float)v : (float)(float)v;
      ap[i]=nv;
      if(!isfinite((double)nv)) bad_precision=1;
    }
    if(bad_precision) { st=poisson_error(err,TVDB_ERROR_INVALID_DATA,"output precision overflow"); goto done; }

    const bool sample=(it%TVDB_POISSON_CANDIDATE_STRIDE==0) || (it+1==max_iters) || converged_now;
    if(sample) {
      double candidate=poisson_true_norm(rhs,input_double,ap,false,nx,ny,nz,h,rhs_mean);
      if(!isfinite(candidate)) { st=poisson_error(err,TVDB_ERROR_INVALID_DATA,"nonfinite output residual"); goto done; }
      if(candidate<best_norm) { best_norm=candidate; memcpy(best,ap,n*sizeof(float)); }
    }

    bool restart=(info->iterations%32==0 || converged_now);
    if(restart) {
      double actual=poisson_residual_f(b,x,r,nx,ny,nz,h);
      if(!isfinite(actual)) { st=poisson_error(err,TVDB_ERROR_INVALID_DATA,"nonfinite true residual"); goto done; }
      if(actual<=target) {
        /* The periodic restart (every 32 iterations) can detect convergence on
           an iteration the stride did not sample. Score this iterate before
           stopping, or a stale best (up to 7 iterations old) is returned and
           reported as not converged. */
        if(!sample) {
          double candidate=poisson_true_norm(rhs,input_double,ap,false,nx,ny,nz,h,rhs_mean);
          if(!isfinite(candidate)) { st=poisson_error(err,TVDB_ERROR_INVALID_DATA,"nonfinite output residual"); goto done; }
          if(candidate<best_norm) { best_norm=candidate; memcpy(best,ap,n*sizeof(float)); }
        }
        break;
      }
    }
    poisson_project_f(r,n);
    poisson_precondition_f(r,z,nx,ny,nz,h);
    double next=poisson_dot_f(r,z,n);
    double beta=restart ? 0 : next/rz;
    #pragma omp parallel for schedule(static)
    for(size_t i=0;i<n;++i) p[i]=(float)((double)z[i]+beta*p[i]);
    poisson_project_f(p,n); rz=next;
  }
  info->final_residual_norm=best_norm;
  info->converged=best_norm<=target;
  for(size_t i=0;i<n;++i) {
    if(input_double) ((double*)output)[i]=best[i]; else ((float*)output)[i]=(float)best[i];
  }

done:
  free(storage); return st;
}

static double poisson_dot_d(const double* a,const double* b,size_t n) {
  double sum=0;
  #pragma omp parallel for reduction(+:sum) schedule(static)
  for(size_t i=0;i<n;++i) sum+=(double)a[i]*b[i];
  return sum;
}
static void poisson_project_d(double* a,size_t n) {
  double sum=0;
  #pragma omp parallel for reduction(+:sum) schedule(static)
  for(size_t i=0;i<n;++i) sum+=a[i];
  double mean=sum/(double)n;
  #pragma omp parallel for schedule(static)
  for(size_t i=0;i<n;++i) a[i]=(double)((double)a[i]-mean);
}
static tvdb_status_t poisson_apply_d(const double* src,double* dst,int nx,int ny,int nz,
 double h,tvdb_poisson_apply_fn apply,void* context,tvdb_error_t* err) {
  if(apply) return apply(context,src,dst,nx,ny,nz,h,true,err);
  double inv_h2=1/(h*h);
  #pragma omp parallel for collapse(2) schedule(static)
  for(int iz=0;iz<nz;++iz) for(int iy=0;iy<ny;++iy) for(int ix=0;ix<nx;++ix) {
    size_t i=((size_t)iz*ny+iy)*nx+ix;
    dst[i]=(double)poisson_positive_at(src,true,i,ix,iy,iz,nx,ny,nz,inv_h2);
  }
  return TVDB_OK;
}
static double poisson_residual_d(const double* b,const double* x,double* r,
 int nx,int ny,int nz,double h) {
  double sum=0,inv_h2=1/(h*h);
  #pragma omp parallel for collapse(2) reduction(+:sum) schedule(static)
  for(int iz=0;iz<nz;++iz) for(int iy=0;iy<ny;++iy) for(int ix=0;ix<nx;++ix) {
    size_t i=((size_t)iz*ny+iy)*nx+ix;
    double v=(double)b[i]-poisson_positive_at(x,true,i,ix,iy,iz,nx,ny,nz,inv_h2);
    r[i]=(double)v; sum+=v*v;
  }
  return sqrt(sum);
}
static void poisson_precondition_d(const double* r,double* z,int nx,int ny,int nz,double h) {
  #pragma omp parallel for collapse(2) schedule(static)
  for(int iz=0;iz<nz;++iz) for(int iy=0;iy<ny;++iy) for(int ix=0;ix<nx;++ix) {
    size_t i=((size_t)iz*ny+iy)*nx+ix;
    int degree=(ix>0)+(ix+1<nx)+(iy>0)+(iy+1<ny)+(iz>0)+(iz+1<nz);
    z[i]=degree ? (double)((double)r[i]*(h*h)/degree) : 0;
  }
  poisson_project_d(z,(size_t)nx*ny*nz);
}
static tvdb_status_t poisson_solve_d(const void* rhs,void* output,int nx,int ny,int nz,
 double h,bool input_double,int max_iters,double tolerance,bool absolute,
 double rhs_mean,double x_mean,tvdb_poisson_result_t* info,tvdb_error_t* err,
 tvdb_poisson_apply_fn apply,void* context) {
  size_t n=(size_t)nx*ny*nz,bytes;
  if(!tvdb_size_mul(n,7*sizeof(double),&bytes)) return poisson_error(err,TVDB_ERROR_INVALID_ARGUMENT,"workspace size overflow");
  double* storage=(double*)malloc(bytes);
  if(!storage) return poisson_error(err,TVDB_ERROR_OUT_OF_MEMORY,"workspace allocation failed");
  double *x=storage,*b=x+n,*r=b+n,*z=r+n,*p=z+n,*ap=p+n,*best=ap+n;
  for(size_t i=0;i<n;++i) {
    x[i]=(double)(poisson_read(output,i,input_double)-x_mean);
    b[i]=(double)(-(poisson_read(rhs,i,input_double)-rhs_mean));
  }
  poisson_residual_d(b,x,r,nx,ny,nz,h);
  double initial=poisson_true_norm(rhs,input_double,output,input_double,nx,ny,nz,h,rhs_mean);
  info->initial_residual_norm=info->final_residual_norm=initial;
  double best_norm=initial;
  for(size_t i=0;i<n;++i) best[i]=(double)poisson_read(output,i,input_double);
  double target=absolute ? tolerance : tolerance*initial;
  tvdb_status_t st=TVDB_OK;
  if(!isfinite(initial) || !isfinite(target)) { st=poisson_error(err,TVDB_ERROR_INVALID_DATA,"nonfinite residual"); goto done; }
  if(initial<=target) { info->converged=true; goto done; }
  if(max_iters==0) goto done;
  poisson_project_d(r,n);
  poisson_precondition_d(r,z,nx,ny,nz,h);
  memcpy(p,z,n*sizeof(double));
  double rz=poisson_dot_d(r,z,n);
  for(int it=0;it<max_iters;++it) {
    st=poisson_apply_d(p,ap,nx,ny,nz,h,apply,context,err);
    if(st!=TVDB_OK) goto done;
    poisson_project_d(ap,n);
    double pap=poisson_dot_d(p,ap,n),alpha=rz/pap;
    if(!(pap>0) || !isfinite(alpha) || !(rz>0)) {
      st=poisson_error(err,TVDB_ERROR_INVALID_DATA,"conjugate-gradient breakdown"); goto done;
    }
    #pragma omp parallel for schedule(static)
    for(size_t i=0;i<n;++i) { x[i]=(double)((double)x[i]+alpha*p[i]); r[i]=(double)((double)r[i]-alpha*ap[i]); }
    info->iterations=it+1;
    /* Same restructuring as the fp32 solver above: cheap dot first, then a
       parallel conversion pass, then the diagnostic stencil only on sampled
       iterations. */
    double rr=poisson_dot_d(r,r,n);
    if(!isfinite(rr)) { st=poisson_error(err,TVDB_ERROR_INVALID_DATA,"nonfinite iterate"); goto done; }
    const bool converged_now=(sqrt(rr)<=target);

    int bad_precision=0;
    #pragma omp parallel for reduction(|:bad_precision) schedule(static)
    for(long long ii=0;ii<(long long)n;++ii) {
      size_t i=(size_t)ii;
      double v=(double)x[i]+x_mean;
      double nv=input_double ? (double)v : (double)(float)v;
      ap[i]=nv;
      if(!isfinite((double)nv)) bad_precision=1;
    }
    if(bad_precision) { st=poisson_error(err,TVDB_ERROR_INVALID_DATA,"output precision overflow"); goto done; }

    const bool sample=(it%TVDB_POISSON_CANDIDATE_STRIDE==0) || (it+1==max_iters) || converged_now;
    if(sample) {
      double candidate=poisson_true_norm(rhs,input_double,ap,true,nx,ny,nz,h,rhs_mean);
      if(!isfinite(candidate)) { st=poisson_error(err,TVDB_ERROR_INVALID_DATA,"nonfinite output residual"); goto done; }
      if(candidate<best_norm) { best_norm=candidate; memcpy(best,ap,n*sizeof(double)); }
    }

    bool restart=(info->iterations%32==0 || converged_now);
    if(restart) {
      double actual=poisson_residual_d(b,x,r,nx,ny,nz,h);
      if(!isfinite(actual)) { st=poisson_error(err,TVDB_ERROR_INVALID_DATA,"nonfinite true residual"); goto done; }
      if(actual<=target) {
        /* The periodic restart (every 32 iterations) can detect convergence on
           an iteration the stride did not sample. Score this iterate before
           stopping, or a stale best (up to 7 iterations old) is returned and
           reported as not converged. */
        if(!sample) {
          double candidate=poisson_true_norm(rhs,input_double,ap,true,nx,ny,nz,h,rhs_mean);
          if(!isfinite(candidate)) { st=poisson_error(err,TVDB_ERROR_INVALID_DATA,"nonfinite output residual"); goto done; }
          if(candidate<best_norm) { best_norm=candidate; memcpy(best,ap,n*sizeof(double)); }
        }
        break;
      }
    }
    poisson_project_d(r,n);
    poisson_precondition_d(r,z,nx,ny,nz,h);
    double next=poisson_dot_d(r,z,n);
    double beta=restart ? 0 : next/rz;
    #pragma omp parallel for schedule(static)
    for(size_t i=0;i<n;++i) p[i]=(double)((double)z[i]+beta*p[i]);
    poisson_project_d(p,n); rz=next;
  }
  info->final_residual_norm=best_norm;
  info->converged=best_norm<=target;
  for(size_t i=0;i<n;++i) {
    if(input_double) ((double*)output)[i]=best[i]; else ((float*)output)[i]=(float)best[i];
  }

done:
  free(storage); return st;
}

tvdb_status_t tvdb_poisson_solve_core(const void* rhs,void* x,int nx,int ny,int nz,
 double h,bool input_double,bool work_double,int max_iters,double tolerance,
 bool absolute,tvdb_poisson_result_t* result,tvdb_error_t* err,
 tvdb_poisson_apply_fn apply,void* context) {
  if(err) memset(err,0,sizeof(*err));
  if(result) memset(result,0,sizeof(*result));
  if(!result || !tvdb_grid_valid(nx,ny,nz,h,rhs,input_double?sizeof(double):sizeof(float)) ||
      !x || max_iters<0 || !isfinite(tolerance) || tolerance<0 ||
      !isfinite(h*h) || h*h==0 || !isfinite(1/(h*h)))
    return poisson_error(err,TVDB_ERROR_INVALID_ARGUMENT,"invalid shape, spacing, tolerance, or iteration limit");
  size_t n=(size_t)nx*ny*nz;
  double sum=0,comp=0,abs_sum=0,xsum=0,xcomp=0;
  for(size_t i=0;i<n;++i) {
    double b=poisson_read(rhs,i,input_double),v=poisson_read(x,i,input_double);
    if(!isfinite(b) || !isfinite(v)) return poisson_error(err,TVDB_ERROR_INVALID_ARGUMENT,"nonfinite input data");
    double y=b-comp,t=sum+y; comp=(t-sum)-y; sum=t; abs_sum+=fabs(b);
    y=v-xcomp; t=xsum+y; xcomp=(t-xsum)-y; xsum=t;
  }
  if(!isfinite(sum) || !isfinite(abs_sum) || !isfinite(xsum))
    return poisson_error(err,TVDB_ERROR_INVALID_ARGUMENT,"input reduction overflow");
  double eps=input_double?DBL_EPSILON:FLT_EPSILON;
  if(fabs(sum)>64*eps*abs_sum)
    return poisson_error(err,TVDB_ERROR_INVALID_ARGUMENT,"RHS has incompatible nonzero mean");
  return work_double ? poisson_solve_d(rhs,x,nx,ny,nz,h,input_double,max_iters,tolerance,absolute,
       sum/n,xsum/n,result,err,apply,context) :
    poisson_solve_f(rhs,x,nx,ny,nz,h,input_double,max_iters,tolerance,absolute,
       sum/n,xsum/n,result,err,apply,context);
}
