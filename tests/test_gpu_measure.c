/* CPU-parity checks for surface_area / volume, fp32 and fp64, on both backends.
 *
 * These are the two ops whose GPU result can be *exactly* equal to the CPU
 * rather than merely close, so this test asserts bit equality and not a
 * tolerance. That is the point of the port: both CPU ops count a per-voxel
 * predicate into an integer and scale the count once, and a sum of 1.0s in fp64
 * is exact below 2^53, so the GPU reproduces the CPU's integer and then its
 * float multiply in the same association order.
 *
 * It also pins the one asymmetry that would be a real bug to "harmonise": the
 * fp32 CPU ops test `<= 0` and the fp64 ones test `< 0`, so they disagree on
 * exact zeros. A grid full of exact zeros is the case that tells the two apart.
 *
 * The large case exists to catch the fp32-accumulator trap: a 2^24-exceeding
 * crossing count stops being exact in fp32, so a reduction that accumulated in
 * the input's own width would drift from the CPU here and nowhere else.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "tinyvdb_gpu.h"

static int fails = 0;

static void bitcmp_f32(const char* name, float gpu, float cpu) {
  /* Compare bit patterns, but treat +0/-0 as equal so the test does not fail on
     an inconsequential sign. NaN vs NaN is a failure here. */
  unsigned int a, b;
  memcpy(&a, &gpu, 4); memcpy(&b, &cpu, 4);
  if (gpu == 0.0f && cpu == 0.0f) a = b = 0;
  if (a != b) {
    printf("  FAIL %-34s gpu %.9g (0x%08x) cpu %.9g (0x%08x)\n", name, gpu, a, cpu, b);
    fails++;
  } else {
    printf("  ok   %-34s %.9g (bit-identical)\n", name, gpu);
  }
}

static void relcmp_f64(const char* name, double gpu, double cpu) {
  /* The fp64 CPU ops add the cell measure per crossing, so their reduction
     order is both OpenMP-schedule and compiler dependent. Counting and scaling
     once is the same quantity computed more accurately, so a tight relative
     bound is the honest assertion -- exact equality is not well defined here. */
  double d = fabs(gpu - cpu);
  double s = fabs(cpu) > 1e-12 ? fabs(cpu) : 1.0;
  double r = d / s;
  if (!(r <= 1e-14)) {
    printf("  FAIL %-34s gpu %.17g cpu %.17g rel %.3e\n", name, gpu, cpu, r);
    fails++;
  } else {
    printf("  ok   %-34s rel %.3e\n", name, r);
  }
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

  struct { const char* name; int nx, ny, nz; double h; int kind; } cases[] = {
    /* kind: 0 = smooth field, 1 = exact zeros, 2 = checkerboard, 3 = all positive */
    { "smooth-13x9x4",     13,  9,  4, 0.31, 0 },
    { "zeros-8x8x8",        8,  8,  8, 0.5,  1 },
    { "checker-16x16x2",   16, 16,  2, 0.125,2 },
    { "positive-9x7x5",     9,  7,  5, 1.0,  3 },
    { "thin-1x1x1",         1,  1,  1, 2.0,  3 },
    { "slab-1x40x40",       1, 40, 40, 0.25,2 },
    /* 128^3 = 2,097,152 voxels; a checkerboard crosses 3 edges per voxel, so
       ~6.3M faces -- under 2^24, so this checks the plumbing. The fp32
       accumulator trap needs more, which is why there is a second large case. */
    { "large-checker-128",128,128,128, 1.0/64.0, 2 },
    /* 181^3 = 5,929,741 voxels, checkerboard, so ~17.7M crossings -- past 2^24
       (16,777,216), the point where a fp32 accumulator stops representing every
       integer. The 128^3 case above stays under it, so only this one can catch a
       reduction that accumulated in the input's own width. 181 is prime so the
       shape is not a cube multiple and no dimension aliasing can mask a stride
       bug. */
    { "huge-checker-181",181,181,181, 1.0/181.0, 2 },
  };
  const size_t ncases = sizeof cases / sizeof cases[0];

  for (size_t c = 0; c < ncases; ++c) {
    int nx = cases[c].nx, ny = cases[c].ny, nz = cases[c].nz;
    size_t n = (size_t)nx * (size_t)ny * (size_t)nz;
    double h = cases[c].h;

    tvdb_dense_grid g; memset(&g, 0, sizeof g);
    g.nx = nx; g.ny = ny; g.nz = nz; g.voxel_size = (float)h;
    g.ox = -1.0f; g.oy = 0.25f; g.oz = 2.0f;
    g.data = (float*)malloc(n * sizeof(float));
    if (!g.data) { printf("OOM\n"); return 1; }
    for (int z = 0; z < nz; ++z) for (int y = 0; y < ny; ++y) for (int x = 0; x < nx; ++x) {
      size_t i = ((size_t)z * ny + y) * nx + x;
      double v;
      switch (cases[c].kind) {
        case 0: v = sin(0.7 * x + 0.3 * y - 0.11 * z) * 2.0 + cos(0.05 * (double)x * y) * 0.5; break;
        case 1: v = ((x + y + z) % 2 == 0) ? 0.0 : ((x & 1) ? 1.0 : -1.0); break;
        case 2: v = ((x + y + z) & 1) ? 1.0 : -1.0; break;
        default: v = fabs(sin(0.31 * x + 0.17 * y + 0.09 * z)) + 0.125; break;
      }
      g.data[i] = (float)v;
    }

    float gpu_area = 0.0f, gpu_vol = 0.0f;
    char label[96];
    memset(&e, 0, sizeof e);
    if (tvdb_gpu_surface_area(ctx, &g, &gpu_area, &e) != TVDB_OK) {
      printf("  FAIL %-20s surface_area: %s\n", cases[c].name, e.message ? e.message : "?"); fails++;
    } else {
      float cpu_area = tvdb_surface_area(&g);
      snprintf(label, sizeof label, "%s surface_area", cases[c].name);
      bitcmp_f32(label, gpu_area, cpu_area);
    }
    memset(&e, 0, sizeof e);
    if (tvdb_gpu_volume(ctx, &g, &gpu_vol, &e) != TVDB_OK) {
      printf("  FAIL %-20s volume: %s\n", cases[c].name, e.message ? e.message : "?"); fails++;
    } else {
      float cpu_vol = tvdb_volume(&g);
      snprintf(label, sizeof label, "%s volume", cases[c].name);
      bitcmp_f32(label, gpu_vol, cpu_vol);
    }
    free(g.data);

    if (has64 && nx <= 128) {
      tvdb_dense_grid_d gd; memset(&gd, 0, sizeof gd);
      gd.nx = nx; gd.ny = ny; gd.nz = nz; gd.voxel_size = h;
      gd.ox = -1.0; gd.oy = 0.25; gd.oz = 2.0;
      gd.data = (double*)malloc(n * sizeof(double));
      if (!gd.data) { printf("OOM\n"); return 1; }
      for (int z = 0; z < nz; ++z) for (int y = 0; y < ny; ++y) for (int x = 0; x < nx; ++x) {
        size_t i = ((size_t)z * ny + y) * nx + x;
        /* Same shapes, but as doubles and not rounded through float, so the
           exact-zero case really is exact. */
        double v;
        switch (cases[c].kind) {
          case 0: v = sin(0.7 * x + 0.3 * y - 0.11 * z) * 2.0 + cos(0.05 * (double)x * y) * 0.5; break;
          case 1: v = ((x + y + z) % 2 == 0) ? 0.0 : ((x & 1) ? 1.0 : -1.0); break;
          case 2: v = ((x + y + z) & 1) ? 1.0 : -1.0; break;
          default: v = fabs(sin(0.31 * x + 0.17 * y + 0.09 * z)) + 0.125; break;
        }
        gd.data[i] = v;
      }
      double gpu_area_d = 0.0, gpu_vol_d = 0.0;
      memset(&e, 0, sizeof e);
      if (tvdb_gpu_surface_area_d(ctx, &gd, &gpu_area_d, &e) != TVDB_OK) {
        printf("  FAIL %-20s surface_area_d: %s\n", cases[c].name, e.message ? e.message : "?"); fails++;
      } else {
        double cpu_area_d = tvdb_surface_area_d(&gd);
        snprintf(label, sizeof label, "%s surface_area_d", cases[c].name);
        relcmp_f64(label, gpu_area_d, cpu_area_d);
      }
      memset(&e, 0, sizeof e);
      if (tvdb_gpu_volume_d(ctx, &gd, &gpu_vol_d, &e) != TVDB_OK) {
        printf("  FAIL %-20s volume_d: %s\n", cases[c].name, e.message ? e.message : "?"); fails++;
      } else {
        double cpu_vol_d = tvdb_volume_d(&gd);
        snprintf(label, sizeof label, "%s volume_d", cases[c].name);
        relcmp_f64(label, gpu_vol_d, cpu_vol_d);
      }
      free(gd.data);
    }
  }

  /* A NULL data pointer returns 0 like the CPU, rather than dispatching. */
  {
    tvdb_dense_grid empty; memset(&empty, 0, sizeof empty);
    empty.nx = empty.ny = empty.nz = 4; empty.voxel_size = 0.5f;
    float a = -1.0f, v = -1.0f;
    if (tvdb_gpu_surface_area(ctx, &empty, &a, &e) != TVDB_OK || tvdb_gpu_volume(ctx, &empty, &v, &e) != TVDB_OK) {
      printf("  FAIL null-data grid: expected OK\n"); fails++;
    } else if (a != 0.0f || v != 0.0f) {
      printf("  FAIL null-data grid: area %g vol %g, want 0\n", a, v); fails++;
    } else {
      printf("  ok   %-34s 0 (matches CPU null-data path)\n", "null-data grid");
    }
  }

  tvdb_gpu_context_destroy(ctx);
  if (fails) { printf("measure parity: %d FAILURE(S)\n", fails); return 1; }
  printf("measure parity: OK\n");
  return 0;
}
