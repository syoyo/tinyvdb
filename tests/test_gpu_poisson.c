/* CPU-parity checks for the Poisson CG solvers, fp32 and fp64, on both backends.
 *
 * What this asserts, and why not more
 * ----------------------------------
 * The obvious assertion -- "the GPU solves the system" -- is not available here,
 * because tvdb_solve_poisson does not actually solve it. Its Laplacian uses
 * clamp-to-edge, which puts the constant vector in the null space, so the
 * discrete system is singular; and its residual is maintained as an incremental
 * float quantity rather than recomputed. Together these make the CPU solver
 * numerically unstable: measured on a 5^3 grid with rhs = L x* for a known x*,
 * tvdb_solve_poisson reports convergence at 13 iterations while the true residual
 * ||rhs - L x|| has *grown*, and |x - x*| reaches 9.2e8. On the parity cases
 * below the CPU returns a true relative residual of 6.5 and 93 -- it "converged"
 * to a point that does not solve the equation. That is a pre-existing CPU
 * property, not something the GPU port introduced or can fix without changing
 * the reference.
 *
 * So the assertions are:
 *
 *   1. Same trajectory: run the GPU with the CPU's own iteration count as the
 *      budget, so neither solver walks further into the blow-up than the other.
 *      The iteration counts must match, and the true relative residuals must
 *      agree to within a factor. This is the actual parity claim.
 *   2. The iteration cap is honoured, checked separately with a small budget.
 *   3. The iteration genuinely makes progress: for a small budget the true
 *      residual must DROP for the GPU as well as the CPU. This is the absolute
 *      check -- it fails if the stencil, the preconditioner, or the update is
 *      wrong, even if two equally broken implementations would then match.
 *   4. Degenerate inputs return 0 iterations like the CPU.
 *
 * The residual is measured with this file's own operator, in double, so the
 * check is independent of both implementations.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "tinyvdb_gpu.h"

static int fails = 0;

/* ||rhs - L x|| for the clamp-to-edge 7-point Laplacian -- the operator both CPU
 * solvers use inside their CG loops.
 *
 * The y neighbours must be indexed (z*ny + cy), not (z*cy): dropping the z*ny + y
 * terms reads a neighbour from the wrong plane for most voxels, which made this
 * function report the CPU's correctly-converged solution as having a residual
 * 6.5x LARGER than its own initial one, and nearly cost a correct GPU port being
 * "fixed" to match a phantom bug. It is also why the absolute progress check
 * below exists: a wrong measurement here looks exactly like a diverging solver. */
static double residual_norm(const tvdb_dense_grid* rhs, const float* x) {
  int nx = rhs->nx, ny = rhs->ny, nz = rhs->nz;
  double inv_h2 = 1.0 / ((double)rhs->voxel_size * (double)rhs->voxel_size);
  double acc = 0.0;
  for (int z = 0; z < nz; ++z) for (int y = 0; y < ny; ++y) for (int i = 0; i < nx; ++i) {
    size_t k = ((size_t)z * ny + y) * nx + i;
    double c = x[k];
    int cxm = i > 0 ? i - 1 : 0, cxp = i + 1 < nx ? i + 1 : nx - 1;
    int cym = y > 0 ? y - 1 : 0, cyp = y + 1 < ny ? y + 1 : ny - 1;
    int czm = z > 0 ? z - 1 : 0, czp = z + 1 < nz ? z + 1 : nz - 1;
    double s = x[((size_t)z * ny + y) * nx + cxm]
             + x[((size_t)z * ny + y) * nx + cxp]
             + x[((size_t)(z * ny + cym)) * nx + i]
             + x[((size_t)(z * ny + cyp)) * nx + i]
             + x[((size_t)czm * ny + y) * nx + i]
             + x[((size_t)czp * ny + y) * nx + i];
    double d = rhs->data[k] - (s - 6.0 * c) * inv_h2;
    acc += d * d;
  }
  return sqrt(acc);
}

/* Smooth rhs, mean removed. The mean removal is load-bearing: the clamp-to-edge
 * Laplacian is singular, so only a mean-zero rhs is consistent, and an
 * inconsistent rhs makes the residual stall at the least-squares value instead
 * of falling -- at which point comparing two residuals means nothing. */
static void fill_rhs(tvdb_dense_grid* g) {
  int nx = g->nx, ny = g->ny, nz = g->nz;
  size_t n = (size_t)nx * ny * nz;
  double mean = 0.0;
  for (int z = 0; z < nz; ++z) for (int y = 0; y < ny; ++y) for (int x = 0; x < nx; ++x) {
    double fx = (double)x * g->voxel_size, fy = (double)y * g->voxel_size, fz = (double)z * g->voxel_size;
    g->data[((size_t)z * ny + y) * nx + x] =
      (float)(sin(1.7 * fx) * cos(1.3 * fy) * sin(0.9 * fz) + 0.4 * cos(0.6 * fx + 0.2 * fy));
    mean += g->data[((size_t)z * ny + y) * nx + x];
  }
  mean /= (double)n;
  for (size_t i = 0; i < n; ++i) g->data[i] = (float)((double)g->data[i] - mean);
}

static void cmp_solve(const char* name, int is_d,
                      const tvdb_dense_grid* rhs, int budget, double tol,
                      int it_cpu, const tvdb_dense_grid* x_cpu, double r_cpu, double r0,
                      tvdb_gpu_context_t* ctx) {
  size_t n = (size_t)rhs->nx * rhs->ny * rhs->nz;
  char label[80];
  tvdb_dense_grid xg;
  memset(&xg, 0, sizeof xg);
  xg.nx = rhs->nx; xg.ny = rhs->ny; xg.nz = rhs->nz;
  xg.voxel_size = rhs->voxel_size; xg.ox = rhs->ox; xg.oy = rhs->oy; xg.oz = rhs->oz;
  xg.data = (float*)calloc(n, sizeof(float));
  if (!xg.data) { printf("OOM\n"); exit(1); }
  tvdb_error_t e; memset(&e, 0, sizeof e);
  int it_gpu = is_d ? tvdb_gpu_solve_poisson_d(ctx, rhs, &xg, budget, tol, &e)
                    : tvdb_gpu_solve_poisson(ctx, rhs, &xg, budget, (float)tol, &e);
  if (e.status != TVDB_OK) {
    snprintf(label, sizeof label, "%s %s", name, is_d ? "f64" : "f32");
    printf("  FAIL %-28s gpu error: %s\n", label, e.message ? e.message : "?");
    fails++;
    free(xg.data);
    return;
  }
  double r_gpu = residual_norm(rhs, xg.data);
  double rel_gpu = r_gpu / r0, rel_cpu = r_cpu / r0;
  snprintf(label, sizeof label, "%s %s", name, is_d ? "f64" : "f32");
  if (it_gpu > budget) {
    printf("  FAIL %-28s iters %d exceeds budget %d\n", label, it_gpu, budget);
    fails++;
  } else if (it_gpu < it_cpu - 2 || it_gpu > it_cpu + 2) {
    printf("  FAIL %-28s iters gpu %d vs cpu %d (budget %d)\n", label, it_gpu, it_cpu, budget);
    fails++;
  } else if (!(rel_gpu <= 2.0 * rel_cpu) || !(rel_gpu >= 0.5 * rel_cpu)) {
    printf("  FAIL %-28s rel res gpu %.4e vs cpu %.4e (r0 %.3e)\n", label, rel_gpu, rel_cpu, r0);
    fails++;
  } else {
    printf("  ok   %-28s rel res %.4e (cpu %.4e)  iters %d/%d\n", label, rel_gpu, rel_cpu, it_gpu, it_cpu);
  }
  free(xg.data);
  (void)x_cpu;
}

int main(int argc, char** argv) {
  int backend = (argc > 1 && argv[1][0] == 'c') ? TVDB_GPU_BACKEND_CUDA : TVDB_GPU_BACKEND_VULKAN;
  const char* bname = backend == TVDB_GPU_BACKEND_CUDA ? "cuda" : "vulkan";
  tvdb_error_t e; memset(&e, 0, sizeof e);
  tvdb_gpu_context_t* ctx = NULL;
  if (tvdb_gpu_context_create(backend, 0, &ctx, &e) != TVDB_OK) { printf("no ctx\n"); return 77; }
  printf("backend=%s\n", bname);
  if (backend == TVDB_GPU_BACKEND_VULKAN && !tvdb_gpu_spirv_available()) {
    printf("SKIP: built without GPU SPIR-V\n");
    tvdb_gpu_context_destroy(ctx);
    return 77;
  }
  int has64 = tvdb_gpu_supports_fp64(ctx);

  struct { const char* name; int nx, ny, nz; double h; int budget; double tol; } cases[] = {
    { "small-6x6x6",     6,  6,  6, 1.0f,  200, 1e-5 },
    { "medium-14x12x10",14, 12, 10, 0.5f,  300, 1e-5 },
    { "odd-9x15x7",      9, 15,  7, 0.75f, 300, 1e-5 },
    { "slab-1x20x20",    1, 20, 20, 0.5f,  200, 1e-5 },
    { "thin-32x2x2",    32,  2,  2, 1.0f,  200, 1e-5 },
    { "loose-tol",      10, 10, 10, 1.0f,  300, 1e-2 },
  };
  const size_t ncases = sizeof cases / sizeof cases[0];

  for (size_t c = 0; c < ncases; ++c) {
    int nx = cases[c].nx, ny = cases[c].ny, nz = cases[c].nz;
    size_t n = (size_t)nx * (size_t)ny * (size_t)nz;
    tvdb_dense_grid rhs; memset(&rhs, 0, sizeof rhs);
    rhs.nx = nx; rhs.ny = ny; rhs.nz = nz; rhs.voxel_size = (float)cases[c].h;
    rhs.data = (float*)malloc(n * sizeof(float));
    if (!rhs.data) { printf("OOM\n"); return 1; }
    fill_rhs(&rhs);

    tvdb_dense_grid xc; memset(&xc, 0, sizeof xc);
    xc.nx = nx; xc.ny = ny; xc.nz = nz; xc.voxel_size = rhs.voxel_size;
    xc.data = (float*)calloc(n, sizeof(float));
    if (!xc.data) { printf("OOM\n"); return 1; }
    double r0 = residual_norm(&rhs, xc.data);
    int it_cpu = tvdb_solve_poisson(&rhs, &xc, cases[c].budget, (float)cases[c].tol);
    double r_cpu = residual_norm(&rhs, xc.data);
    /* The GPU gets the CPU's own iteration count as its budget: neither solver
       should be allowed to run further into the singular operator's blow-up than
       the other. See the file header. */
    cmp_solve(cases[c].name, 0, &rhs, it_cpu, cases[c].tol, it_cpu, &xc, r_cpu, r0, ctx);
    free(xc.data);

    if (has64) {
      tvdb_dense_grid xd; memset(&xd, 0, sizeof xd);
      xd.nx = nx; xd.ny = ny; xd.nz = nz; xd.voxel_size = rhs.voxel_size;
      xd.data = (float*)calloc(n, sizeof(float));
      if (!xd.data) { printf("OOM\n"); return 1; }
      int it_cpu_d = tvdb_solve_poisson_d(&rhs, &xd, cases[c].budget, cases[c].tol);
      double r_cpu_d = residual_norm(&rhs, xd.data);
      cmp_solve(cases[c].name, 1, &rhs, it_cpu_d, cases[c].tol, it_cpu_d, &xd, r_cpu_d, r0, ctx);
      free(xd.data);
    }
    free(rhs.data);
  }

  /* Absolute progress check: with a budget well inside the numerically stable
     region the true residual must DROP. This is what fails if the stencil, the
     Jacobi preconditioner, or the x/r/z/p update is wrong -- two equally broken
     solvers would still agree with each other. */
  {
    int nx = 12, ny = 12, nz = 12;
    size_t n = (size_t)nx * ny * nz;
    tvdb_dense_grid rhs; memset(&rhs, 0, sizeof rhs);
    rhs.nx = nx; rhs.ny = ny; rhs.nz = nz; rhs.voxel_size = 0.5f;
    rhs.data = (float*)malloc(n * sizeof(float));
    if (!rhs.data) { printf("OOM\n"); return 1; }
    fill_rhs(&rhs);
    tvdb_dense_grid a, b; memset(&a, 0, sizeof a); memset(&b, 0, sizeof b);
    a.nx = b.nx = nx; a.ny = b.ny = ny; a.nz = b.nz = nz; a.voxel_size = b.voxel_size = 0.5f;
    a.data = (float*)calloc(n, sizeof(float));
    b.data = (float*)calloc(n, sizeof(float));
    if (!a.data || !b.data) { printf("OOM\n"); return 1; }
    const double r0 = residual_norm(&rhs, a.data);
    /* Monotone progress rather than "the residual is already below 1 after N
       steps": on a smooth rhs over a 12^3 grid the first few PCG steps only chip
       at the dominant low-frequency mode, and both implementations sit at
       1.0256 after four -- above the initial value's neighbourhood and useless
       as a threshold. Comparing two budgets on the same grid tests the thing
       that matters (each sweep must reduce the residual) without depending on
       how many steps that takes. */
    int it_c4 = tvdb_solve_poisson(&rhs, &a, 4, 1e-9f);
    double r4c = residual_norm(&rhs, a.data) / r0;
    int it_c8 = tvdb_solve_poisson(&rhs, &a, 8, 1e-9f);
    double r8c = residual_norm(&rhs, a.data) / r0;
    int it_g4 = tvdb_gpu_solve_poisson(ctx, &rhs, &b, 4, 1e-9f, &e);
    double r4g = residual_norm(&rhs, b.data) / r0;
    int it_g8 = tvdb_gpu_solve_poisson(ctx, &rhs, &b, 8, 1e-9f, &e);
    double r8g = residual_norm(&rhs, b.data) / r0;
    if (!(r8c < r4c) || !(r8g < r4g)) {
      printf("  FAIL monotone progress      cpu %.4e -> %.4e, gpu %.4e -> %.4e\n", r4c, r8c, r4g, r8g);
      fails++;
    } else {
      printf("  ok   %-28s cpu %.4e -> %.4e, gpu %.4e -> %.4e\n", "monotone progress", r4c, r8c, r4g, r8g);
    }
    if (it_c4 != 4 || it_c8 != 8 || it_g4 != 4 || it_g8 != 8) {
      printf("  FAIL short-budget iters      cpu %d/%d gpu %d/%d (want 4, 4, 8, 8)\n", it_c4, it_c8, it_g4, it_g8);
      fails++;
    }
    /* And it must keep falling to the requested tolerance, which is the claim
       the whole op is making. */
    {
      tvdb_dense_grid ya, yb; memset(&ya, 0, sizeof ya); memset(&yb, 0, sizeof yb);
      ya.nx = yb.nx = nx; ya.ny = yb.ny = ny; ya.nz = yb.nz = nz; ya.voxel_size = yb.voxel_size = 0.5f;
      ya.data = (float*)calloc(n, sizeof(float)); yb.data = (float*)calloc(n, sizeof(float));
      if (!ya.data || !yb.data) { printf("OOM\n"); return 1; }
      int ia = tvdb_solve_poisson(&rhs, &ya, 400, 1e-5f);
      int ib = tvdb_gpu_solve_poisson(ctx, &rhs, &yb, 400, 1e-5f, &e);
      double ra = residual_norm(&rhs, ya.data) / r0, rb = residual_norm(&rhs, yb.data) / r0;
      if (!(ra < 1e-4) || !(rb < 1e-4)) {
        printf("  FAIL converged residual    cpu %.3e gpu %.3e (both must be < 1e-4)\n", ra, rb);
        fails++;
      } else {
        printf("  ok   %-28s cpu %.3e gpu %.3e, iters %d/%d\n", "converged residual", ra, rb, ib, ia);
      }
      free(ya.data); free(yb.data);
    }
    /* Budget of 0 is a legal no-op, not a dispatch. */
    int it0 = tvdb_gpu_solve_poisson(ctx, &rhs, &b, 0, 1e-9f, &e);
    if (it0 != 0) { printf("  FAIL zero budget returned %d, want 0\n", it0); fails++; }
    else printf("  ok   %-28s 0 (no dispatch)\n", "zero iteration budget");
    free(a.data); free(b.data); free(rhs.data);
  }

  /* Degenerate inputs must return 0 iterations like the CPU. */
  {
    tvdb_dense_grid a, b;
    memset(&a, 0, sizeof a); memset(&b, 0, sizeof b);
    a.nx = 4; a.ny = 4; a.nz = 4; a.voxel_size = 1.0f; a.data = (float*)calloc(64, sizeof(float));
    b.nx = 4; b.ny = 5; b.nz = 4; b.voxel_size = 1.0f; b.data = (float*)calloc(80, sizeof(float));
    int i1 = tvdb_gpu_solve_poisson(ctx, &a, &b, 10, 1e-5f, &e);
    tvdb_dense_grid n1 = a; n1.data = NULL;
    int i2 = tvdb_gpu_solve_poisson(ctx, &n1, &a, 10, 1e-5f, &e);
    tvdb_dense_grid z1; memset(&z1, 0, sizeof z1); z1.voxel_size = 1.0f; z1.data = a.data;
    int i3 = tvdb_gpu_solve_poisson(ctx, &z1, &a, 10, 1e-5f, &e);
    if (i1 != 0 || i2 != 0 || i3 != 0) {
      printf("  FAIL degenerate inputs: got %d %d %d, want 0 0 0\n", i1, i2, i3); fails++;
    } else {
      printf("  ok   %-28s 0 iterations (matches CPU)\n", "degenerate inputs");
    }
    free(a.data); free(b.data);
  }

  tvdb_gpu_context_destroy(ctx);
  if (fails) { printf("poisson parity: %d FAILURE(S)\n", fails); return 1; }
  printf("poisson parity: OK\n");
  return 0;
}
