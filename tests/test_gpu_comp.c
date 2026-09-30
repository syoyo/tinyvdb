/* CPU-parity checks for the elementwise binary grid ops (comp_max/min/sum/mult)
 * and the fp64-in/fp64-out Poisson solver, on both backends.
 *
 * comp_* is included here rather than in test_gpu_ops because the interesting part
 * is its *contract*, not its arithmetic: all four CPU ops return early and leave
 * `result` untouched unless all three grids share a shape, and they use the ternaries
 * `va > vb ? va : vb` rather than fmax. Both are places where a plausible GPU kernel
 * (clamping b's extent, or using fmax) would produce a field where the CPU produces
 * nothing, or a disagreement on NaN. The NaN and the shape-mismatch cases below are
 * the whole point of the test.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "tinyvdb_gpu.h"

static int fails = 0;
static const float kNaN = (float)(0.0 / 0.0);

static tvdb_dense_grid mk(int nx, int ny, int nz, float seed) {
  tvdb_dense_grid g; memset(&g, 0, sizeof g);
  g.nx = nx; g.ny = ny; g.nz = nz; g.voxel_size = 0.25f; g.ox = -1.0f; g.oy = 0.5f; g.oz = 2.0f;
  size_t n = (size_t)nx * ny * nz;
  g.data = (float*)malloc(n * sizeof(float));
  for (size_t i = 0; i < n; ++i) g.data[i] = sinf((float)i * 0.37f + seed) * 3.0f;
  return g;
}
static int same_bits(const float* a, const float* b, size_t n) {
  for (size_t i = 0; i < n; ++i) {
    unsigned int x, y; memcpy(&x, &a[i], 4); memcpy(&y, &b[i], 4);
    if (a[i] == 0.0f && b[i] == 0.0f) continue;
    if (x != y) return 0;
  }
  return 1;
}

static void comp_case(const char* name, tvdb_gpu_context_t* ctx, int op,
                      void (*cpu_fn)(const tvdb_dense_grid*, const tvdb_dense_grid*, tvdb_dense_grid*),
                      tvdb_status_t (*gpu_fn)(tvdb_gpu_context_t*, const tvdb_dense_grid*,
                                               const tvdb_dense_grid*, tvdb_dense_grid*, tvdb_error_t*)) {
  tvdb_dense_grid a = mk(9, 7, 5, 0.0f), b = mk(9, 7, 5, 1.7f);
  tvdb_dense_grid rc, rg;
  memset(&rc, 0, sizeof rc); memset(&rg, 0, sizeof rg);
  rc.nx = rg.nx = 9; rc.ny = rg.ny = 7; rc.nz = rg.nz = 5;
  size_t n = (size_t)9 * 7 * 5;
  rc.data = (float*)malloc(n * sizeof(float));
  rg.data = (float*)malloc(n * sizeof(float));
  for (size_t i = 0; i < n; ++i) rc.data[i] = rg.data[i] = -12345.0f;   /* sentinel */
  cpu_fn(&a, &b, &rc);
  tvdb_error_t e; memset(&e, 0, sizeof e);
  if (gpu_fn(ctx, &a, &b, &rg, &e) != TVDB_OK) {
    printf("  FAIL %-22s %s\n", name, e.message ? e.message : "?"); fails++;
  } else if (!same_bits(rc.data, rg.data, n)) {
    printf("  FAIL %-22s values differ from CPU\n", name); fails++;
  } else {
    printf("  ok   %-22s bit-identical to CPU\n", name);
  }
  free(a.data); free(b.data); free(rc.data); free(rg.data);
  (void)op;
}

int main(int argc, char** argv) {
  int backend = (argc > 1 && argv[1][0] == 'c') ? TVDB_GPU_BACKEND_CUDA : TVDB_GPU_BACKEND_VULKAN;
  tvdb_error_t e; memset(&e, 0, sizeof e);
  tvdb_gpu_context_t* ctx = NULL;
  if (tvdb_gpu_context_create(backend, 0, &ctx, &e) != TVDB_OK) { printf("no ctx\n"); return 77; }
  printf("backend=%s\n", backend == TVDB_GPU_BACKEND_CUDA ? "cuda" : "vulkan");
  if (backend == TVDB_GPU_BACKEND_VULKAN && !tvdb_gpu_spirv_available()) {
    printf("SKIP: built without GPU SPIR-V\n"); tvdb_gpu_context_destroy(ctx); return 77;
  }

  comp_case("comp_max", ctx, 0, tvdb_comp_max, tvdb_gpu_comp_max);
  comp_case("comp_min", ctx, 1, tvdb_comp_min, tvdb_gpu_comp_min);
  comp_case("comp_sum", ctx, 2, tvdb_comp_sum, tvdb_gpu_comp_sum);
  comp_case("comp_mult", ctx, 3, tvdb_comp_mult, tvdb_gpu_comp_mult);

  /* NaN: the CPU ternaries keep `va` when the comparison is false, fmax would not. */
  {
    tvdb_dense_grid a = mk(4, 4, 4, 0.0f), b = mk(4, 4, 4, 0.0f);
    size_t n = 64;
    a.data[0] = kNaN; b.data[0] = 1.0f;
    a.data[1] = 1.0f;  b.data[1] = kNaN;
    a.data[2] = kNaN;  b.data[2] = kNaN;
    tvdb_dense_grid rc, rg;
    memset(&rc, 0, sizeof rc); memset(&rg, 0, sizeof rg);
    rc.nx = rg.nx = rc.ny = rg.ny = rc.nz = rg.nz = 4;
    rc.data = (float*)malloc(n * sizeof(float));
    rg.data = (float*)malloc(n * sizeof(float));
    for (size_t i = 0; i < n; ++i) { rc.data[i] = -1.0f; rg.data[i] = -1.0f; }
    tvdb_comp_max(&a, &b, &rc);
    tvdb_gpu_comp_max(ctx, &a, &b, &rg, &e);
    if (!same_bits(rc.data, rg.data, n)) {
      printf("  FAIL %-22s NaN handling differs (fmax vs the CPU ternary)\n", "comp_max-nan"); fails++;
    } else {
      printf("  ok   %-22s matches the CPU ternaries on NaN\n", "comp_max-nan");
    }
    free(a.data); free(b.data); free(rc.data); free(rg.data);
  }

  /* Shape mismatch: the CPU leaves result untouched, and so must the GPU. A
     clamping kernel would write the whole field here. */
  {
    tvdb_dense_grid a = mk(6, 5, 4, 0.0f), b = mk(6, 5, 4, 2.0f);
    tvdb_dense_grid rc, rg;
    memset(&rc, 0, sizeof rc); memset(&rg, 0, sizeof rg);
    /* b is the right shape for a but not for the result */
    size_t n = (size_t)6 * 5 * 4, m = (size_t)5 * 5 * 4;
    rc.nx = 5; rc.ny = 5; rc.nz = 4; rc.voxel_size = 0.25f;
    rg.nx = 5; rg.ny = 5; rg.nz = 4; rg.voxel_size = 0.25f;
    rc.data = (float*)malloc(m * sizeof(float));
    rg.data = (float*)malloc(m * sizeof(float));
    for (size_t i = 0; i < m; ++i) { rc.data[i] = -777.0f; rg.data[i] = -777.0f; }
    tvdb_comp_sum(&a, &b, &rc);
    tvdb_gpu_comp_sum(ctx, &a, &b, &rg, &e);
    int untouched = 1;
    for (size_t i = 0; i < m; ++i) if (rg.data[i] != -777.0f) untouched = 0;
    if (!untouched || e.status != TVDB_ERROR_INVALID_ARGUMENT) {
      printf("  FAIL %-22s mismatch must leave result untouched and report INVALID_ARGUMENT\n", "comp_sum-shape-mismatch");

      fails++;
    } else {
      printf("  ok   %-22s result untouched, status INVALID_ARGUMENT\n", "comp_sum-shape-mismatch");
    }
    free(a.data); free(b.data); free(rc.data); free(rg.data);
  }

  /* fp64-in / fp64-out Poisson, distinct from the fp32-in / fp64-internals twin. */
  if (tvdb_gpu_supports_fp64(ctx)) {
    int nx = 10, ny = 10, nz = 10;
    size_t n = (size_t)nx * ny * nz;
    tvdb_dense_grid_d rhs; memset(&rhs, 0, sizeof rhs);
    rhs.nx = nx; rhs.ny = ny; rhs.nz = nz; rhs.voxel_size = 0.5;
    rhs.data = (double*)malloc(n * sizeof(double));
    double mean = 0;
    for (int z = 0; z < nz; ++z) for (int y = 0; y < ny; ++y) for (int x = 0; x < nx; ++x) {
      double v = sin(1.7 * x * 0.5) * cos(1.3 * y * 0.5) * sin(0.9 * z * 0.5);
      rhs.data[((size_t)z * ny + y) * nx + x] = v; mean += v;
    }
    mean /= (double)n;   /* the clamp-to-edge Laplacian is singular: mean must go */
    for (size_t i = 0; i < n; ++i) rhs.data[i] -= mean;
    tvdb_dense_grid_d a, b;
    memset(&a, 0, sizeof a); memset(&b, 0, sizeof b);
    a.nx = b.nx = nx; a.ny = b.ny = ny; a.nz = b.nz = nz; a.voxel_size = b.voxel_size = 0.5;
    a.data = (double*)calloc(n, sizeof(double));
    b.data = (double*)calloc(n, sizeof(double));
    int ia = tvdb_solve_poisson_dd(&rhs, &a, 400, 1e-5);
    memset(&e, 0, sizeof e);
    int ib = tvdb_gpu_solve_poisson_dd(ctx, &rhs, &b, 400, 1e-5, &e);
    if (e.status != TVDB_OK) { printf("  FAIL %-22s %s\n", "solve_poisson_dd", e.message ? e.message : "?"); fails++; }
    else {
      double worst = 0;
      for (size_t i = 0; i < n; ++i) { double d = fabs(a.data[i] - b.data[i]); if (d > worst) worst = d; }
      if (ia != ib || worst > 1e-9) {
        printf("  FAIL %-22s iters %d/%d worst %.3e\n", "solve_poisson_dd", ia, ib, worst); fails++;
      } else {
        printf("  ok   %-22s iters %d/%d, worst %.3e\n", "solve_poisson_dd", ia, ib, worst);
      }
    }
    free(rhs.data); free(a.data); free(b.data);
  } else {
    printf("  skip solve_poisson_dd: device lacks shaderFloat64\n");
  }

  tvdb_gpu_context_destroy(ctx);
  if (fails) { printf("elementwise/poisson_dd parity: %d FAILURE(S)\n", fails); return 1; }
  printf("elementwise/poisson_dd parity: OK\n");
  return 0;
}
