/* CPU-parity checks for fast sweeping (Eikonal / distance-to-surface) on both
 * backends.
 *
 * The contract is tvdb_fast_sweeping in tinyvdb_ops.c, which is Gauss-Seidel:
 * within a sweep direction it walks voxels in index order so each update reads
 * the already-updated value of the neighbour it has already passed. The GPU
 * reproduces that by decomposing each of the 8 directions into wavefront planes
 * ordered by L = dir.x*ix + dir.y*iy + dir.z*iz, and launching one dispatch per
 * plane. Every voxel on a plane therefore only ever reads levels strictly below
 * its own, which is exactly the set the serial sweep has already written, so
 * the two orders agree voxel for voxel.
 *
 * The comparison is absolute, scaled by the largest magnitude in the case. The
 * shader's godunov uses GLSL sqrt, which the spec allows to be up to 2 ULP away
 * from libm's sqrtf, so exact comparison is not available; the observed spread
 * is around 5e-7 relative.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "tinyvdb_gpu.h"

static int g_failures = 0;
#define EXPECT(cond) do { if (!(cond)) { \
  fprintf(stderr, "FAIL [%s:%d]: %s\n", __FILE__, __LINE__, #cond); ++g_failures; } } while (0)

typedef struct {
  int nx, ny, nz;
  float h;
  float band;
  int iters;
  float tol;
  int single_seed;   /* 1: seed only voxel (0,0,0), so the wavefront must cross
                      * the whole grid and a sweep that only advances one plane
                      * or one direction cannot pass. */
  const char* note;
} fs_case;

static void fill_src(float* dst, const fs_case* c) {
  for (int iz = 0; iz < c->nz; ++iz)
    for (int iy = 0; iy < c->ny; ++iy)
      for (int ix = 0; ix < c->nx; ++ix) {
        size_t i = ((size_t)iz * c->ny + iy) * c->nx + ix;
        if (c->single_seed) {
          /* Everything far outside the frozen band, so exactly one voxel seeds
           * the solve. Mixing signs here also covers the sign write-back, which
           * has to leave the seed and every other frozen voxel untouched. The
           * seed's magnitude is kept at 0.05 so it is frozen for every band
           * these cases use. */
          dst[i] = (i == 0) ? -0.05f : 9.0f;
        } else {
          float t = 0.7f * ix + 0.31f * iy - 0.17f * iz;
          dst[i] = sinf(t) * 1.8f + cosf(0.05f * ix * iy + 0.11f * iz) * 0.6f;
        }
      }
}


/* fp64 twin of run_case. Same tolerance reasoning, with one extra allowance: the
 * device-side change accumulator can only atomicMax the high 32 bits of the
 * pattern (GLSL has no uint64_t), so convergence can be detected up to 2^-20
 * relative later than the CPU's. That can cost an extra iteration, so the
 * iteration counts are allowed to differ by one -- but not the field, which must
 * still match to the same bound. */
static void run_case_d(tvdb_gpu_context_t* ctx, const fs_case* c) {
  size_t n = (size_t)c->nx * c->ny * c->nz;
  float* src = (float*)malloc(n * sizeof(float));
  if (!src) { ++g_failures; return; }
  fill_src(src, c);
  tvdb_dense_grid_d cpu, gpu;
  memset(&cpu, 0, sizeof cpu); memset(&gpu, 0, sizeof gpu);
  cpu.nx = gpu.nx = c->nx; cpu.ny = gpu.ny = c->ny; cpu.nz = gpu.nz = c->nz;
  cpu.voxel_size = gpu.voxel_size = (double)c->h;
  cpu.data = (double*)malloc(n * sizeof(double));
  gpu.data = (double*)malloc(n * sizeof(double));
  if (!cpu.data || !gpu.data) { ++g_failures; free(src); free(cpu.data); free(gpu.data); return; }
  for (size_t i = 0; i < n; ++i) cpu.data[i] = gpu.data[i] = (double)src[i];

  int it_cpu = tvdb_fast_sweeping_d(&cpu, (double)c->band, c->iters, (double)c->tol);
  int it_gpu = -1;
  tvdb_error_t e; memset(&e, 0, sizeof e);
  tvdb_status_t st = tvdb_gpu_fast_sweeping_d(ctx, &gpu, (double)c->band, c->iters,
                                              (double)c->tol, &it_gpu, &e);
  if (st != TVDB_OK) {
    printf("  FAIL %-32s d: %s\n", c->note, e.message);
    ++g_failures;
  } else {
    const double sentinel = 1.0e29;
    double maxabs = 0.0, scale = 1.0;
    int n_sentinel = 0;
    for (size_t i = 0; i < n; ++i) {
      if (fabs(cpu.data[i]) > sentinel) { ++n_sentinel; continue; }
      double d = fabs(cpu.data[i] - gpu.data[i]);
      if (d > maxabs) maxabs = d;
      if (fabs(cpu.data[i]) > scale) scale = fabs(cpu.data[i]);
    }
    double steps = scale / (c->h > 0.0f ? c->h : 1.0f);
    double tol = 1e-6 * scale * (steps > 1.0 ? steps : 1.0);
    double guard = 1e-3 * scale;
    int di = it_gpu - it_cpu;
    int ok = (maxabs <= tol) && (maxabs <= guard) && (di >= 0 && di <= 1);
    if (!ok) ++g_failures;
    printf("  %-4s %-32s d %2dx%2dx%2d h=%.2f band=%.2f it=%d/%d maxabs %.3e unsolved=%d\n",
           ok ? "ok" : "FAIL", c->note, c->nx, c->ny, c->nz, c->h, c->band,
           it_cpu, it_gpu, maxabs, n_sentinel);
  }
  free(cpu.data); free(gpu.data); free(src);
}

static void run_case(tvdb_gpu_context_t* ctx, const fs_case* c) {
  size_t n = (size_t)c->nx * c->ny * c->nz;
  float* src = (float*)malloc(n * sizeof(float));
  if (!src) { ++g_failures; return; }
  fill_src(src, c);

  tvdb_dense_grid cpu, gpu;
  memset(&cpu, 0, sizeof cpu); memset(&gpu, 0, sizeof gpu);
  cpu.nx = gpu.nx = c->nx; cpu.ny = gpu.ny = c->ny; cpu.nz = gpu.nz = c->nz;
  cpu.voxel_size = gpu.voxel_size = c->h;
  cpu.data = (float*)malloc(n * sizeof(float));
  gpu.data = (float*)malloc(n * sizeof(float));
  memcpy(cpu.data, src, n * sizeof(float));
  memcpy(gpu.data, src, n * sizeof(float));

  int it_cpu = tvdb_fast_sweeping(&cpu, c->band, c->iters, c->tol);
  int it_gpu = -1;
  tvdb_error_t e; memset(&e, 0, sizeof e);
  tvdb_status_t st = tvdb_gpu_fast_sweeping(ctx, &gpu, c->band, c->iters, c->tol, &it_gpu, &e);

  if (st != TVDB_OK) {
    printf("  FAIL %-32s %s\n", c->note, e.message);
    ++g_failures;
  } else {
    /* Scale on real values only. A field that is still at the 1e30 sentinel
     * would otherwise inflate the tolerance until any output passed. */
    const double sentinel = 1.0e29;
    double maxabs = 0.0, scale = 1.0;
    int n_sentinel = 0;
    for (size_t i = 0; i < n; ++i) {
      if (fabs((double)cpu.data[i]) > sentinel) { ++n_sentinel; continue; }
      double d = fabs((double)cpu.data[i] - (double)gpu.data[i]);
      if (d > maxabs) maxabs = d;
      if (fabs((double)cpu.data[i]) > scale) scale = fabs((double)cpu.data[i]);
    }
    /* Tolerance derived from where the residual actually comes from. The only
     * difference between the two implementations is GLSL sqrt being up to 2 ULP
     * from libm sqrtf, and a single-seed field is the sum of ~scale/h chained
     * updates, so the bound is per-step error times the number of steps. At 1
     * ULP relative per step this is ~1e-7 * steps, and the guard below caps the
     * tolerance at 1e-3 relative so the formula cannot quietly become lax enough
     * to hide a wrong plane order, which would be an O(scale) disagreement. */
    double steps = scale / (c->h > 0.0f ? c->h : 1.0f);
    double tol = 1e-6 * scale * (steps > 1.0 ? steps : 1.0);
    double guard = 1e-3 * scale;
    int ok = (maxabs <= tol) && (maxabs <= guard) && (it_cpu == it_gpu);
    if (!ok) ++g_failures;
    printf("  %-4s %-32s %2dx%2dx%2d h=%.2f band=%.2f it=%d/%d maxabs %.3e unsolved=%d\n",
           ok ? "ok" : "FAIL", c->note, c->nx, c->ny, c->nz, c->h, c->band,
           it_cpu, it_gpu, maxabs, n_sentinel);
  }
  free(cpu.data); free(gpu.data); free(src);
}

int main(int argc, char** argv) {
  setvbuf(stdout, NULL, _IONBF, 0);
  int want_cuda = (argc > 1 && argv[1][0] == 'c');
  tvdb_error_t e; memset(&e, 0, sizeof e);
  tvdb_gpu_context_t* ctx = NULL;
  tvdb_status_t st = tvdb_gpu_context_create(want_cuda ? TVDB_GPU_BACKEND_CUDA
                                                      : TVDB_GPU_BACKEND_VULKAN,
                                             0, &ctx, &e);
  if (st != TVDB_OK) {
    printf("no %s context: %s\n", want_cuda ? "cuda" : "vulkan", e.message);
    return 77;
  }
  printf("backend=%s\n", want_cuda ? "cuda" : "vulkan");
  if (!want_cuda && !tvdb_gpu_spirv_available()) {
    printf("SKIP: built without GPU SPIR-V\n");
    tvdb_gpu_context_destroy(ctx); return 77;
  }

  static const fs_case cases[] = {
    /* Mixed-sign fields with a real seed region. */
    {  8,  8,  8, 1.00f, 0.50f,  1, 0.0f,  0, "seeded-single-sweep" },
    {  8,  8,  8, 1.00f, 0.50f, 20, 1e-6f, 0, "seeded-converged" },
    /* Non-cubic dims, so an x/y/z mix-up in the plane decomposition shows up. */
    { 13,  7, 11, 1.00f, 0.40f, 40, 1e-6f, 0, "seeded-anisotropic-dims" },
    { 12,  9, 10, 0.50f, 0.20f,  5, 0.0f, 0, "seeded-anisotropic-h" },
    {  6,  5,  7, 1.00f, 0.30f,  3, 0.0f, 0, "seeded-few-iters" },
    {  6,  5,  7, 1.00f, 0.30f, 40, 1e-6f, 0, "seeded-tight-band" },
    /* One seed, far corner to seed: the wavefront has to traverse the grid in
     * every direction, so this is what pins down the plane ordering. */
    { 32, 24, 20, 0.10f, 0.05f, 100, 1e-6f, 1, "single-seed-far-corner" },
    { 24, 40, 16, 0.05f, 0.05f, 100, 1e-7f, 1, "single-seed-deep-propagation" },
    { 40, 40, 40, 0.20f, 0.05f, 100, 1e-6f, 1, "single-seed-cubic-deep" },
  };

  for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); ++i) run_case(ctx, &cases[i]);

  /* fp64. A subset: the shapes that exercise the plane ordering, not every case,
     because the fp32 loop above already covers the geometry and this adds width. */
  if (tvdb_gpu_supports_fp64(ctx)) {
    static const fs_case dcases[] = {
      {  8,  8,  8, 1.00f, 0.50f, 20, 1e-6f, 0, "seeded-converged" },
      { 13,  7, 11, 1.00f, 0.40f, 40, 1e-6f, 0, "seeded-anisotropic-dims" },
      {  6,  5,  7, 1.00f, 0.30f, 40, 1e-6f, 0, "seeded-tight-band" },
      { 32, 24, 20, 0.10f, 0.05f, 100, 1e-6f, 1, "single-seed-far-corner" },
      { 24, 40, 16, 0.05f, 0.05f, 100, 1e-7f, 1, "single-seed-deep-propagation" },
    };
    for (size_t i = 0; i < sizeof(dcases) / sizeof(dcases[0]); ++i) run_case_d(ctx, &dcases[i]);
  } else {
    printf("  skip fp64 cases: device lacks shaderFloat64\n");
  }

  /* Degenerate contract: with frozen_band 0 nothing is ever frozen unless a
   * voxel is exactly zero, so an all-nonzero input leaves the whole field at
   * the sentinel. Both backends have to agree on that exactly. */
  {
    static const fs_case zero = { 5, 4, 3, 1.0f, 0.0f, 5, 0.0f, 0, "band-zero-unsolved" };
    size_t n = (size_t)zero.nx * zero.ny * zero.nz;
    float* src = (float*)malloc(n * sizeof(float));
    if (src) {
      fill_src(src, &zero);
      tvdb_dense_grid cpu, gpu;
      memset(&cpu, 0, sizeof cpu); memset(&gpu, 0, sizeof gpu);
      cpu.nx = gpu.nx = zero.nx; cpu.ny = gpu.ny = zero.ny; cpu.nz = gpu.nz = zero.nz;
      cpu.voxel_size = gpu.voxel_size = zero.h;
      cpu.data = (float*)malloc(n * sizeof(float));
      gpu.data = (float*)malloc(n * sizeof(float));
      memcpy(cpu.data, src, n * sizeof(float));
      memcpy(gpu.data, src, n * sizeof(float));
      int it_cpu = tvdb_fast_sweeping(&cpu, zero.band, zero.iters, zero.tol);
      int it_gpu = -1;
      tvdb_error_t z; memset(&z, 0, sizeof z);
      tvdb_gpu_fast_sweeping(ctx, &gpu, zero.band, zero.iters, zero.tol, &it_gpu, &z);
      int identical = 1;
      for (size_t i = 0; i < n; ++i)
        if (memcmp(&cpu.data[i], &gpu.data[i], sizeof(float)) != 0) identical = 0;
      if (!identical || it_cpu != it_gpu) {
        printf("  FAIL %-32s band=0 must leave the field untouched (it %d/%d)\n",
               zero.note, it_cpu, it_gpu);
        ++g_failures;
      } else {
        printf("  ok   %-32s field untouched as required\n", zero.note);
      }
      free(cpu.data); free(gpu.data); free(src);
    }
  }

  /* Descriptor-pool ceiling regression. fast_sweeping used to allocate one
     descriptor set per wavefront plane from the shared pool (maxSets 1024), and
     total_planes = 8*(3N-2), so every grid above N=43 failed with
     VK_ERROR_OUT_OF_POOL_MEMORY. The cases above top out at 40^3 = 944 planes,
     92% of the limit, which is why it went unnoticed. One dynamic-offset set
     replaces all of them, so 64^3 (1520 planes) must now work -- and it has to
     produce the same answer as the CPU reference, not merely not fail. */
  {
    const int N = 64;
    const size_t n64 = (size_t)N * N * N;
    static const struct { int N; float band; int iters; const char* note; } big[] = {
      { 48, 0.40f, 3, "pool-ceiling-48" },
      { 64, 0.30f, 3, "pool-ceiling-64" },
    };
    for (unsigned b = 0; b < sizeof(big) / sizeof(big[0]); ++b) {
      const int M = big[b].N;
      const size_t nm = (size_t)M * M * M;
      tvdb_dense_grid cpu, gpu;
      memset(&cpu, 0, sizeof cpu); memset(&gpu, 0, sizeof gpu);
      cpu.nx = gpu.nx = cpu.ny = gpu.ny = cpu.nz = gpu.nz = M;
      cpu.voxel_size = gpu.voxel_size = 1.0f;
      cpu.data = (float*)malloc(nm * sizeof(float));
      gpu.data = (float*)malloc(nm * sizeof(float));
      /* A single seed in one corner, inside the frozen band, against a uniform
         positive far field: the wavefront has to traverse the whole grid in every
         direction, so a plane that never runs, or runs out of order, shows up as
         a large disagreement rather than a small one. (A seed outside the band
         would freeze nothing and the whole case would pass trivially.) */
      for (size_t i = 0; i < nm; ++i) cpu.data[i] = 1.0f;
      cpu.data[0] = -0.2f;
      /* Sanity: the seed must actually be inside this case's band, or the case
         measures nothing. */
      if (!(cpu.data[0] < 0.0f && -cpu.data[0] <= big[b].band)) {
        printf("  FAIL %-32s seed outside band %.2f\n", big[b].note, big[b].band);
        ++g_failures;
      }
      memcpy(gpu.data, cpu.data, nm * sizeof(float));
      int it_cpu = tvdb_fast_sweeping(&cpu, big[b].band, big[b].iters, 0.0f);
      int it_gpu = -1;
      tvdb_error_t pe; memset(&pe, 0, sizeof pe);
      tvdb_status_t rs = tvdb_gpu_fast_sweeping(ctx, &gpu, big[b].band, big[b].iters, 0.0f, &it_gpu, &pe);
      if (rs != TVDB_OK) {
        printf("  FAIL %-32s %d^3 (%ld planes): %s\n", big[b].note, M,
               8L * (3L * M - 2L), pe.message);
        ++g_failures;
      } else {
        double maxabs = 0.0, scale = 0.0;
        for (size_t i = 0; i < nm; ++i) {
          double d = (double)cpu.data[i] - (double)gpu.data[i];
          if (d < 0) d = -d;
          if (d > maxabs) maxabs = d;
          if (fabs(cpu.data[i]) > scale) scale = fabs(cpu.data[i]);
        }
        /* The same sqrt-tolerance derivation the cases above use, so a wrong
           plane order (an O(scale) disagreement) still cannot pass: the chain is
           ~scale/h updates and GLSL sqrtf may differ by 2 ULP per step, with the
           tolerance guarded at 1e-3 relative. */
        double steps = scale / (double)cpu.voxel_size;
        double tol = 1e-6 * scale * (steps > 1.0 ? steps : 1.0);
        double guard = 1e-3 * scale;
        if (maxabs > tol || maxabs > guard || it_gpu != it_cpu) {
          printf("  FAIL %-32s %d^3 maxabs %.3e (tol %.3e guard %.3e) it=%d/%d\n",
                 big[b].note, M, maxabs, tol, guard, it_gpu, it_cpu);
          ++g_failures;
        } else {
          printf("  ok   %-32s %d^3 (%ld planes) it=%d/%d maxabs %.3e\n",
                 big[b].note, M, 8L * (3L * M - 2L), it_gpu, it_cpu, maxabs);
        }
      }
      free(cpu.data); free(gpu.data);
    }
    (void)n64;
  }

  EXPECT(g_failures == 0);
  tvdb_gpu_context_destroy(ctx);
  printf("fast sweeping parity: %s\n", g_failures ? "FAIL" : "OK");
  return g_failures ? 1 : 0;
}
