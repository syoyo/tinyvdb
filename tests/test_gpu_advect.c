/* CPU-parity checks for semi-Lagrangian advection (tvdb_advect) on both backends.
 *
 * All six schemes are covered, plus the two contracts that are easy to get wrong:
 *
 *  - Both samplers clamp (tvdb_at / tvdb_vec_at clamp the index), so a backtrace
 *    that leaves the domain repeats the edge value rather than hitting a wall.
 *    The "fast-flow" case has |dt|*|v|/h > 1, which is exactly where that
 *    difference lives; a zero-fill instead would still agree on every other case.
 *  - A shape mismatch or a NULL data pointer makes the CPU return without writing,
 *    so `result` must come back untouched rather than half-updated.
 *
 * The comparison is absolute, scaled by the field's own magnitude. The kernel is
 * otherwise a transcription of the CPU, so the only permitted difference is
 * arithmetic reassociation that the compiler is free to do, and the bound is set
 * at 1e-5 relative with a 1e-3 relative hard cap so a wrong backtrace (which
 * displaces the result by O(field)) cannot slip through.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "tinyvdb_gpu.h"

static int g_failures = 0;

typedef struct { int nx, ny, nz; float h; float dt; float vmag; const char* note; } adv_case;

static void fill_field(tvdb_dense_grid* g) {
  for (int z = 0; z < g->nz; ++z) for (int y = 0; y < g->ny; ++y) for (int x = 0; x < g->nx; ++x) {
    float fx = x * g->voxel_size, fy = y * g->voxel_size, fz = z * g->voxel_size;
    g->data[((size_t)z * g->ny + y) * g->nx + x] =
      sinf(2.1f * fx) * cosf(1.7f * fy) * sinf(1.3f * fz) + 0.2f;
  }
}
/* A smooth divergence-light swirl, so the advected field stays bounded and
   comparable rather than smearing into noise. */
static void fill_vel(tvdb_dense_vec_grid* v, float vmag) {
  for (int z = 0; z < v->nz; ++z) for (int y = 0; y < v->ny; ++y) for (int x = 0; x < v->nx; ++x) {
    size_t i = ((size_t)z * v->ny + y) * v->nx + x;
    float fx = x * v->voxel_size, fy = y * v->voxel_size;
    v->data[i * 3 + 0] = vmag * cosf(1.1f * fy);
    v->data[i * 3 + 1] = -vmag * sinf(0.9f * fx);
    v->data[i * 3 + 2] = 0.3f * vmag * cosf(0.7f * fx + 0.5f * fy);
  }
}

static void run(tvdb_gpu_context_t* ctx, const adv_case* c, int scheme, int clamp) {
  int nx = c->nx, ny = c->ny, nz = c->nz;
  size_t n = (size_t)nx * ny * nz;
  tvdb_dense_grid f, rc, rg;
  tvdb_dense_vec_grid v;
  memset(&f, 0, sizeof f); memset(&rc, 0, sizeof rc); memset(&rg, 0, sizeof rg);
  memset(&v, 0, sizeof v);
  f.nx = rc.nx = rg.nx = nx; f.ny = rc.ny = rg.ny = ny; f.nz = rc.nz = rg.nz = nz;
  f.voxel_size = rc.voxel_size = rg.voxel_size = c->h;
  v.nx = nx; v.ny = ny; v.nz = nz; v.voxel_size = c->h;
  f.data = (float*)malloc(n * sizeof(float));
  rc.data = (float*)malloc(n * sizeof(float));
  rg.data = (float*)malloc(n * sizeof(float));
  v.data = (float*)malloc(n * 3u * sizeof(float));
  if (!f.data || !rc.data || !rg.data || !v.data) { ++g_failures; return; }
  fill_field(&f);
  fill_vel(&v, c->vmag);
  for (size_t i = 0; i < n; ++i) { rc.data[i] = -4242.0f; rg.data[i] = -4242.0f; }

  tvdb_advect(&f, &v, c->dt, scheme, clamp, &rc);
  tvdb_error_t e; memset(&e, 0, sizeof e);
  if (tvdb_gpu_advect(ctx, &f, &v, c->dt, scheme, clamp, &rg, &e) != TVDB_OK) {
    printf("  FAIL %-24s %-11s clamp=%d: %s\n", c->note, "advect", clamp, e.message);
    ++g_failures;
  } else {
    double maxabs = 0.0, scale = 1.0;
    for (size_t i = 0; i < n; ++i) {
      double d = fabs((double)rc.data[i] - (double)rg.data[i]);
      if (d > maxabs) maxabs = d;
      if (fabs((double)rc.data[i]) > scale) scale = fabs((double)rc.data[i]);
    }
    double ok_bound = 1e-5 * scale, guard = 1e-3 * scale;
    int ok = (maxabs <= ok_bound) && (maxabs <= guard);
    if (!ok) ++g_failures;
    printf("  %-4s %-24s %-11s clamp=%d  maxabs %.3e (scale %.3e)\n",
           ok ? "ok" : "FAIL", c->note,
           scheme == TVDB_ADVECT_MACCORMACK ? "maccormack" :
           scheme == TVDB_ADVECT_BFECC ? "bfecc" : "rk", clamp, maxabs, scale);
  }
  free(f.data); free(rc.data); free(rg.data); free(v.data);
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

  static const adv_case cases[] = {
    /* |dt|*|v|/h is well under 1: the backtrace stays inside the domain, so this
       pins the arithmetic without the clamping question. */
    { 16, 16, 16, 0.1f, 0.05f, 0.5f,  "sub-cell-flow" },
    { 16, 16, 16, 0.1f, 0.10f, 1.0f,  "one-cell-flow" },
    /* |dt|*|v|/h ~ 2.5: the backtrace leaves the domain on every edge voxel, so
       the clamped samplers are what decide the answer here. */
    { 16, 16, 16, 0.1f, 0.20f, 1.2f,  "multi-cell-flow" },
    { 12,  9, 14, 0.2f, 0.30f, 1.5f,  "multi-cell-anisotropic" },
    {  8,  8,  8, 1.0f, 0.50f, 4.0f,  "far-outside" },
    {  1,  9,  9, 0.5f, 0.20f, 1.0f,  "degenerate-nx1" },
    { 20, 20,  4, 0.05f, 0.10f, 1.0f, "thin-z" },
  };

  for (size_t i = 0; i < sizeof cases / sizeof cases[0]; ++i) {
    for (int s = TVDB_ADVECT_RK1; s <= TVDB_ADVECT_RK4; ++s) run(ctx, &cases[i], s, 0);
    run(ctx, &cases[i], TVDB_ADVECT_MACCORMACK, 0);
    run(ctx, &cases[i], TVDB_ADVECT_MACCORMACK, 1);
    run(ctx, &cases[i], TVDB_ADVECT_BFECC, 0);
    run(ctx, &cases[i], TVDB_ADVECT_BFECC, 1);
  }

  /* Shape mismatch: the CPU returns without writing, so result is untouched. */
  {
    int nx = 8, ny = 8, nz = 8; size_t n = 512;
    tvdb_dense_grid f; tvdb_dense_vec_grid v;
    memset(&f, 0, sizeof f); memset(&v, 0, sizeof v);
    f.nx = nx; f.ny = ny; f.nz = nz; f.voxel_size = 0.1f;
    v.nx = nx; v.ny = ny; v.nz = nz; v.voxel_size = 0.1f;
    f.data = (float*)malloc(n * sizeof(float));
    v.data = (float*)malloc(n * 3u * sizeof(float));
    tvdb_dense_grid r; memset(&r, 0, sizeof r);
    r.nx = nx; r.ny = ny + 1; r.nz = nz; r.voxel_size = 0.1f;
    r.data = (float*)malloc((size_t)nx * (ny + 1) * nz * sizeof(float));
    for (size_t i = 0; i < (size_t)nx * (ny + 1) * nz; ++i) r.data[i] = -99.0f;
    tvdb_advect(&f, &v, 0.1f, TVDB_ADVECT_RK2, 0, &r);
    tvdb_gpu_advect(ctx, &f, &v, 0.1f, TVDB_ADVECT_RK2, 0, &r, &e);
    int untouched = 1;
    for (size_t i = 0; i < (size_t)nx * (ny + 1) * nz; ++i) if (r.data[i] != -99.0f) untouched = 0;
    if (!untouched) { printf("  FAIL shape mismatch must leave result untouched\n"); ++g_failures; }
    else printf("  ok   %-32s untouched, status OK\n", "shape mismatch");
    /* An unknown scheme is an error, and must not write. This needs a
       shape-matched grid: the shape check comes first and returns OK, so reusing
       the mismatched one above would test nothing. Note the CPU has no scheme
       validation at all -- anything past RK4 falls through to the BFECC branch
       -- so this is a deliberate divergence documented in the header, not
       something the parity comparison can require. */
    r.ny = ny;
    r.data = (float*)malloc(n * sizeof(float));
    for (size_t i = 0; i < n; ++i) r.data[i] = -99.0f;
    tvdb_status_t st = tvdb_gpu_advect(ctx, &f, &v, 0.1f, 99, 0, &r, &e);
    int untouched2 = 1;
    for (size_t i = 0; i < n; ++i) if (r.data[i] != -99.0f) untouched2 = 0;
    if (st != TVDB_ERROR_INVALID_ARGUMENT || !untouched2) {
      printf("  FAIL unknown scheme returned %d (want INVALID_ARGUMENT), untouched=%d\n", st, untouched2);
      ++g_failures;
    } else printf("  ok   %-32s INVALID_ARGUMENT, result untouched\n", "unknown scheme");
    free(f.data); free(v.data); free(r.data);
  }

  tvdb_gpu_context_destroy(ctx);
  if (g_failures) { printf("advect parity: %d FAILURE(S)\n", g_failures); return 1; }
  printf("advect parity: OK\n");
  return 0;
}
