#pragma once
#include "tinyvdb_ops.h"
/* Positive edge-clamped -L apply; the GPU callback owns its device resources. */
typedef tvdb_status_t (*tvdb_poisson_apply_fn)(void* context, const void* src,
  void* dst, int nx,int ny,int nz,double h,bool fp64,tvdb_error_t* err);
tvdb_status_t tvdb_poisson_solve_core(const void* rhs, void* x, int nx,int ny,int nz,
  double h,bool input_double,bool work_double,int max_iters,double tolerance,
  bool absolute_tolerance,tvdb_poisson_result_t* result,tvdb_error_t* err,
  tvdb_poisson_apply_fn apply,void* context);
