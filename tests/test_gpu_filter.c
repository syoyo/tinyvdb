/* CPU-parity checks for the dense filters and the single-node semi-Lagrangian
 * advect, on both backends.
 *
 * The interesting part of the filters is not the tap loop, it is the two
 * orderings the CPU uses and a fused kernel would silently change:
 *
 *   - the separable filters run one axis at a time through ping/pong buffers, so
 *     a fused 3-D pass gives a different (not merely a differently-rounded)
 *     result. The test includes width values where a 3-D box filter would visibly
 *     differ from three 1-D passes.
 *   - the Laplacian filter is Jacobi: every voxel reads the previous generation
 *     from a scratch buffer, and the buffers are swapped between iterations. An
 *     in-place update is Gauss-Seidel, which is order dependent.
 *
 * Edge handling clamps the *index*, so a tap overhanging the domain is evaluated
 * at the boundary voxel rather than renormalising the kernel. The field is not
 * locally constant, so those differ, and the corners are where they differ most.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "tinyvdb_gpu.h"

static int fails = 0;

static void fill(tvdb_dense_grid* g) {
  for (int z = 0; z < g->nz; ++z) for (int y = 0; y < g->ny; ++y) for (int x = 0; x < g->nx; ++x) {
    float fx = x * g->voxel_size, fy = y * g->voxel_size, fz = z * g->voxel_size;
    g->data[((size_t)z * g->ny + y) * g->nx + x] =
      sinf(2.3f * fx) * cosf(1.1f * fy) * sinf(0.7f * fz) + 0.1f;
  }
}
static void fillv(tvdb_dense_vec_grid* v, float m) {
  for (int z = 0; z < v->nz; ++z) for (int y = 0; y < v->ny; ++y) for (int x = 0; x < v->nx; ++x) {
    size_t i = ((size_t)z * v->ny + y) * v->nx + x;
    v->data[i*3+0] = m * cosf(0.9f * y);
    v->data[i*3+1] = -m * sinf(1.3f * x);
    v->data[i*3+2] = 0.2f * m;
  }
}

static void cmp(const char* name, const float* a, const float* b, size_t n, double scale) {
  double worst = 0.0;
  for (size_t i = 0; i < n; ++i) { double d = fabs((double)a[i] - (double)b[i]); if (d > worst) worst = d; }
  double tol = 1e-5 * (scale > 1.0 ? scale : 1.0), guard = 1e-3 * (scale > 1.0 ? scale : 1.0);
  if (!(worst <= tol) || !(worst <= guard)) {
    printf("  FAIL %-28s worst %.3e (scale %.3e)\n", name, worst, scale); fails++;
  } else {
    printf("  ok   %-28s worst %.3e\n", name, worst);
  }
}

typedef struct { int nx, ny, nz; float h; } shape;

static void run_filters(tvdb_gpu_context_t* ctx, const shape* s,
                        int width, int iters) {
  size_t n = (size_t)s->nx * s->ny * s->nz;
  tvdb_dense_grid a, b;
  memset(&a, 0, sizeof a); memset(&b, 0, sizeof b);
  a.nx = b.nx = s->nx; a.ny = b.ny = s->ny; a.nz = b.nz = s->nz;
  a.voxel_size = b.voxel_size = s->h;
  a.data = (float*)malloc(n * sizeof(float));
  b.data = (float*)malloc(n * sizeof(float));
  if (!a.data || !b.data) { fails++; return; }
  char lbl[80];
  /* fill() first: the scale has to come from the actual field, or the tolerance
     is derived from whatever was in the freshly malloc'd buffer and a wrong
     result can slip through on a huge "scale". */
  fill(&a);
  double scale = 1.0;
  for (size_t i = 0; i < n; ++i) if (fabs(a.data[i]) > scale) scale = fabs(a.data[i]);
  memcpy(b.data, a.data, n * sizeof(float));

  tvdb_mean_filter(&a, width, iters);
  tvdb_gpu_mean_filter(ctx, &b, width, iters, NULL);
  snprintf(lbl, sizeof lbl, "mean w=%d it=%d", width, iters); cmp(lbl, a.data, b.data, n, scale);

  fill(&a); memcpy(b.data, a.data, n * sizeof(float));
  tvdb_gaussian_filter(&a, width, iters);
  tvdb_gpu_gaussian_filter(ctx, &b, width, iters, NULL);
  snprintf(lbl, sizeof lbl, "gauss w=%d it=%d", width, iters); cmp(lbl, a.data, b.data, n, scale);

  fill(&a); memcpy(b.data, a.data, n * sizeof(float));
  tvdb_laplacian_filter(&a, iters);
  tvdb_gpu_laplacian_filter(ctx, &b, iters, NULL);
  snprintf(lbl, sizeof lbl, "lap it=%d", iters); cmp(lbl, a.data, b.data, n, scale);

  /* Median only up to the shader's radius bound; the parity assertion is exact
     (bit patterns), not a tolerance, because the selected value is order
     independent and the CPU's quickselect and the rank count must agree exactly.
     A salt-and-pepper field is used instead of the smooth one: a smooth field's
     median is a no-op, so every error in the window gather would be invisible. */
  if (width <= 2) {
    for (size_t i = 0; i < n; ++i) {
      unsigned int h = (unsigned int)(i * 2654435761u);
      a.data[i] = (h & 7u) == 0u ? 5.0f : ((h & 3u) == 0u ? -4.0f : sinf(0.9f * (float)i));
      if (fabs(a.data[i]) > scale) scale = fabs(a.data[i]);
    }
    memcpy(b.data, a.data, n * sizeof(float));
    tvdb_median_filter(&a, width, iters);
    if (tvdb_gpu_median_filter(ctx, &b, width, iters, NULL) != TVDB_OK) {
      printf("  FAIL median r=%d it=%d\n", width, iters); fails++;
    } else {
      int exact = 1;
      for (size_t i = 0; i < n; ++i) {
        unsigned int x, y; memcpy(&x, &a.data[i], 4); memcpy(&y, &b.data[i], 4);
        if (a.data[i] == 0.0f && b.data[i] == 0.0f) continue;
        if (x != y) { exact = 0; break; }
      }
      snprintf(lbl, sizeof lbl, "median r=%d it=%d", width, iters);
      if (!exact) { printf("  FAIL %-28s not bit-identical to the CPU\n", lbl); fails++; }
      else printf("  ok   %-28s bit-identical\n", lbl);
    }
  }

  free(a.data); free(b.data);
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

  static const shape shapes[] = {
    { 16, 16, 16, 0.1f },
    { 12,  9, 14, 0.2f },
    { 20, 20,  4, 0.05f },   /* thin: the z axis has 4 voxels, so a wide kernel overhangs it */
    {  8,  8,  8, 1.0f },
    {  1,  8,  8, 0.5f },   /* nx == 1: every x tap clamps */
  };
  for (size_t i = 0; i < sizeof shapes / sizeof shapes[0]; ++i) {
    printf(" shape %dx%dx%d h=%.2f\n", shapes[i].nx, shapes[i].ny, shapes[i].nz, shapes[i].h);
    run_filters(ctx, &shapes[i], 1, 1);
    run_filters(ctx, &shapes[i], 2, 2);
    run_filters(ctx, &shapes[i], 3, 3);
    run_filters(ctx, &shapes[i], 4, 2);
  }

  /* Single-node semi-Lagrangian advect, sub-cell and multi-cell. */
  {
    struct { int nx, ny, nz; float h, dt, v; const char* note; } cs[] = {
      { 16, 16, 16, 0.1f, 0.05f, 0.5f, "sub-cell" },
      { 16, 16, 16, 0.1f, 0.25f, 1.5f, "multi-cell" },
      { 12,  9, 14, 0.2f, 0.40f, 2.0f, "anisotropic" },
    };
    for (size_t c = 0; c < sizeof cs / sizeof cs[0]; ++c) {
      int nx = cs[c].nx, ny = cs[c].ny, nz = cs[c].nz;
      size_t n = (size_t)nx * ny * nz;
      tvdb_dense_grid f, rc, rg; tvdb_dense_vec_grid v;
      memset(&f, 0, sizeof f); memset(&rc, 0, sizeof rc); memset(&rg, 0, sizeof rg);
      memset(&v, 0, sizeof v);
      f.nx = rc.nx = rg.nx = nx; f.ny = rc.ny = rg.ny = ny; f.nz = rc.nz = rg.nz = nz;
      f.voxel_size = rc.voxel_size = rg.voxel_size = cs[c].h;
      v.nx = nx; v.ny = ny; v.nz = nz; v.voxel_size = cs[c].h;
      f.data = (float*)malloc(n * sizeof(float));
      rc.data = (float*)malloc(n * sizeof(float));
      rg.data = (float*)malloc(n * sizeof(float));
      v.data = (float*)malloc(n * 3u * sizeof(float));
      if (!f.data || !rc.data || !rg.data || !v.data) { fails++; break; }
      fill(&f); fillv(&v, cs[c].v);
      for (size_t i = 0; i < n; ++i) { rc.data[i] = -777.0f; rg.data[i] = -777.0f; }
      tvdb_advect_semi_lagrangian(&f, &v, cs[c].dt, &rc);
      if (tvdb_gpu_advect_semi_lagrangian(ctx, &f, &v, cs[c].dt, &rg, &e) != TVDB_OK) {
        printf("  FAIL advect_sl %-20s %s\n", cs[c].note, e.message); fails++;
      } else {
        double worst = 0.0;
        for (size_t i = 0; i < n; ++i) { double d = fabs((double)rc.data[i] - (double)rg.data[i]); if (d > worst) worst = d; }
        if (worst > 1e-5) { printf("  FAIL advect_sl %-20s worst %.3e\n", cs[c].note, worst); fails++; }
        else printf("  ok   %-28s worst %.3e\n", cs[c].note, worst);
      }
      free(f.data); free(rc.data); free(rg.data); free(v.data);
    }
  }

  /* radius above the shader's window bound must report UNIMPLEMENTED rather than
     silently filtering a smaller window, and must leave the grid untouched. */
  {
    tvdb_dense_grid g; memset(&g, 0, sizeof g);
    g.nx = g.ny = g.nz = 8; g.voxel_size = 1.0f;
    g.data = (float*)calloc(512, sizeof(float));
    for (int i = 0; i < 512; ++i) g.data[i] = (float)(i % 7);
    tvdb_error_t me; memset(&me, 0, sizeof me);
    tvdb_status_t st = tvdb_gpu_median_filter(ctx, &g, 3, 1, &me);
    int untouched = 1;
    for (int i = 0; i < 512; ++i) if (g.data[i] != (float)(i % 7)) untouched = 0;
    if (st != TVDB_ERROR_UNIMPLEMENTED || !untouched) {
      printf("  FAIL median radius 3 returned %d (want UNIMPLEMENTED), untouched=%d\n", st, untouched);
      fails++;
    } else printf("  ok   %-32s UNIMPLEMENTED, grid untouched\n", "median radius above bound");
    /* radius < 1 is a CPU no-op, not an error. */
    st = tvdb_gpu_median_filter(ctx, &g, 0, 1, &me);
    untouched = 1;
    for (int i = 0; i < 512; ++i) if (g.data[i] != (float)(i % 7)) untouched = 0;
    if (st != TVDB_OK || !untouched) { printf("  FAIL median radius 0 must be a no-op\n"); fails++; }
    else printf("  ok   %-32s no-op, grid untouched\n", "median radius 0");
    free(g.data);
  }

  /* width <= 0 and iterations <= 0 are CPU no-ops, not errors. */
  {
    tvdb_dense_grid g; memset(&g, 0, sizeof g);
    g.nx = g.ny = g.nz = 4; g.voxel_size = 1.0f;
    g.data = (float*)calloc(64, sizeof(float));
    for (int i = 0; i < 64; ++i) g.data[i] = (float)i;
    tvdb_status_t s1 = tvdb_gpu_mean_filter(ctx, &g, 0, 3, &e);
    tvdb_status_t s2 = tvdb_gpu_gaussian_filter(ctx, &g, 2, 0, &e);
    tvdb_status_t s3 = tvdb_gpu_laplacian_filter(ctx, &g, 0, &e);
    int unchanged = 1;
    for (int i = 0; i < 64; ++i) if (g.data[i] != (float)i) unchanged = 0;
    if (s1 != TVDB_OK || s2 != TVDB_OK || s3 != TVDB_OK || !unchanged) {
      printf("  FAIL degenerate filter args must be no-ops (%d/%d/%d, unchanged=%d)\n", s1, s2, s3, unchanged);
      fails++;
    } else printf("  ok   %-28s no-ops, grid untouched\n", "degenerate args");
    free(g.data);
  }

  tvdb_gpu_context_destroy(ctx);
  if (fails) { printf("filter parity: %d FAILURE(S)\n", fails); return 1; }
  printf("filter parity: OK\n");
  return 0;
}
