#include "tinyvdb_gpu.h"
#include "tinyvdb_grid_index.h"
#include "tinyvdb_jagged.h"
#include "tinyvdb_levelset.h"
#include "tinyvdb_ops.h"
#include "tinyvdb_ray.h"
#include "tinyvdb_render.h"
#include "tinyvdb_sample.h"
#include "tinyvdb_sparse.h"
#include "tinyvdb_stats.h"
#include "tinyvdb_topology.h"
#include "tinyvdb_tsdf.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int g_failures = 0;

#define EXPECT(cond) do { \
  if (!(cond)) { \
    fprintf(stderr, "FAIL [%s:%d]: %s\n", __FILE__, __LINE__, #cond); \
    ++g_failures; \
  } \
} while (0)

#define EXPECT_NEAR(a, b, tol) do { \
  double _a = (double)(a), _b = (double)(b); \
  if (fabs(_a - _b) > (double)(tol)) { \
    fprintf(stderr, "FAIL [%s:%d]: %s=%g %s=%g diff=%g tol=%g\n", \
            __FILE__, __LINE__, #a, _a, #b, _b, fabs(_a - _b), (double)(tol)); \
    ++g_failures; \
  } \
} while (0)

static void fill_grid(tvdb_dense_grid* g, int n, float bias) {
  tvdb_dense_grid_init(g, n, n, n);
  g->voxel_size = 0.25f;
  g->ox = -0.5f;
  g->oy = -0.25f;
  g->oz = 0.125f;
  for (int z = 0; z < n; ++z) {
    for (int y = 0; y < n; ++y) {
      for (int x = 0; x < n; ++x) {
        size_t i = (size_t)((z * n + y) * n + x);
        g->data[i] = 0.17f * (float)x - 0.11f * (float)y + 0.07f * (float)z + bias;
      }
    }
  }
}

static void test_dense_csg(tvdb_gpu_context_t* ctx) {
  tvdb_dense_grid a, b, cpu, gpu;
  fill_grid(&a, 8, -0.4f);
  fill_grid(&b, 8, 0.2f);
  tvdb_dense_grid_init(&cpu, 8, 8, 8);
  tvdb_dense_grid_init(&gpu, 8, 8, 8);
  cpu.voxel_size = gpu.voxel_size = a.voxel_size;
  cpu.ox = gpu.ox = a.ox; cpu.oy = gpu.oy = a.oy; cpu.oz = gpu.oz = a.oz;

  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  tvdb_csg_union(&a, &b, &cpu);
  if (tvdb_gpu_csg_dense(ctx, &a, &b, 0, &gpu, &err) != TVDB_OK) {
    fprintf(stderr, "dense csg union failed: %s\n", err.message);
    EXPECT(0);
    goto done;
  }
  for (size_t i = 0; i < 512; ++i) EXPECT_NEAR(gpu.data[i], cpu.data[i], 1e-6f);

  tvdb_csg_difference(&a, &b, &cpu);
  if (tvdb_gpu_csg_dense(ctx, &a, &b, 2, &gpu, &err) != TVDB_OK) {
    fprintf(stderr, "dense csg difference failed: %s\n", err.message);
    EXPECT(0);
    goto done;
  }
  for (size_t i = 0; i < 512; ++i) EXPECT_NEAR(gpu.data[i], cpu.data[i], 1e-6f);

done:
  tvdb_dense_grid_free(&a);
  tvdb_dense_grid_free(&b);
  tvdb_dense_grid_free(&cpu);
  tvdb_dense_grid_free(&gpu);
}

static void test_gpu_sdf_sphere(tvdb_gpu_context_t* ctx, const char* label) {
  const float center[3] = {0.3f, -0.2f, 0.5f};
  tvdb_dense_grid cpu, gpu;
  memset(&cpu, 0, sizeof(cpu));
  memset(&gpu, 0, sizeof(gpu));
  EXPECT(tvdb_level_set_sphere(1.25f, center, 0.05f, 3.0f, &cpu));
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  clock_t t0 = clock();
  tvdb_status_t st = tvdb_gpu_level_set_sphere(ctx, 1.25f, center, 0.05f, 3.0f, &gpu, &err);
  double gpu_ms = (double)(clock() - t0) * 1000.0 / (double)CLOCKS_PER_SEC;
  if (st != TVDB_OK) {
    fprintf(stderr, "gpu sphere SDF failed: %s\n", err.message);
    EXPECT(0);
    goto done;
  }
  EXPECT(cpu.nx == gpu.nx && cpu.ny == gpu.ny && cpu.nz == gpu.nz);
  EXPECT_NEAR(cpu.ox, gpu.ox, 1e-7f);
  EXPECT_NEAR(cpu.oy, gpu.oy, 1e-7f);
  EXPECT_NEAR(cpu.oz, gpu.oz, 1e-7f);
  EXPECT_NEAR(cpu.voxel_size, gpu.voxel_size, 1e-7f);
  size_t n = (size_t)cpu.nx * (size_t)cpu.ny * (size_t)cpu.nz;
  float max_err = 0.0f;
  for (size_t i = 0; i < n; ++i) {
    float e = fabsf(cpu.data[i] - gpu.data[i]);
    if (e > max_err) max_err = e;
  }
  EXPECT(max_err <= 2.0e-5f);
  printf("[gpu:%s:bench] sdf sphere %dx%dx%d voxels: gpu %.3f ms, max_err %.3g\n",
         label, gpu.nx, gpu.ny, gpu.nz, gpu_ms, max_err);
done:
  tvdb_dense_grid_free(&cpu);
  tvdb_dense_grid_free(&gpu);
}

static void test_gpu_sdf_box(tvdb_gpu_context_t* ctx, const char* label) {
  const float half_extents[3] = {0.65f, 1.10f, 0.45f};
  const float center[3] = {-0.15f, 0.25f, 0.40f};
  tvdb_dense_grid cpu, gpu;
  memset(&cpu, 0, sizeof(cpu));
  memset(&gpu, 0, sizeof(gpu));
  EXPECT(tvdb_level_set_box(half_extents, center, 0.05f, 3.0f, &cpu));
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  clock_t t0 = clock();
  tvdb_status_t st = tvdb_gpu_level_set_box(ctx, half_extents, center, 0.05f, 3.0f, &gpu, &err);
  double gpu_ms = (double)(clock() - t0) * 1000.0 / (double)CLOCKS_PER_SEC;
  if (st != TVDB_OK) {
    fprintf(stderr, "gpu box SDF failed: %s\n", err.message);
    EXPECT(0);
    goto done;
  }
  EXPECT(cpu.nx == gpu.nx && cpu.ny == gpu.ny && cpu.nz == gpu.nz);
  EXPECT_NEAR(cpu.ox, gpu.ox, 1e-7f);
  EXPECT_NEAR(cpu.oy, gpu.oy, 1e-7f);
  EXPECT_NEAR(cpu.oz, gpu.oz, 1e-7f);
  EXPECT_NEAR(cpu.voxel_size, gpu.voxel_size, 1e-7f);
  size_t n = (size_t)cpu.nx * (size_t)cpu.ny * (size_t)cpu.nz;
  float max_err = 0.0f;
  for (size_t i = 0; i < n; ++i) {
    float e = fabsf(cpu.data[i] - gpu.data[i]);
    if (e > max_err) max_err = e;
  }
  EXPECT(max_err <= 2.0e-5f);
  printf("[gpu:%s:bench] sdf box %dx%dx%d voxels: gpu %.3f ms, max_err %.3g\n",
         label, gpu.nx, gpu.ny, gpu.nz, gpu_ms, max_err);
done:
  tvdb_dense_grid_free(&cpu);
  tvdb_dense_grid_free(&gpu);
}

static void test_gpu_sdf_torus(tvdb_gpu_context_t* ctx, const char* label) {
  const float center[3] = {0.10f, -0.25f, 0.35f};
  tvdb_dense_grid cpu, gpu;
  memset(&cpu, 0, sizeof(cpu));
  memset(&gpu, 0, sizeof(gpu));
  EXPECT(tvdb_level_set_torus(0.80f, 0.22f, center, 0.04f, 3.0f, &cpu));
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  clock_t t0 = clock();
  tvdb_status_t st = tvdb_gpu_level_set_torus(ctx, 0.80f, 0.22f, center, 0.04f, 3.0f, &gpu, &err);
  double gpu_ms = (double)(clock() - t0) * 1000.0 / (double)CLOCKS_PER_SEC;
  if (st != TVDB_OK) {
    fprintf(stderr, "gpu torus SDF failed: %s\n", err.message);
    EXPECT(0);
    goto done;
  }
  EXPECT(cpu.nx == gpu.nx && cpu.ny == gpu.ny && cpu.nz == gpu.nz);
  EXPECT_NEAR(cpu.ox, gpu.ox, 1e-7f);
  EXPECT_NEAR(cpu.oy, gpu.oy, 1e-7f);
  EXPECT_NEAR(cpu.oz, gpu.oz, 1e-7f);
  EXPECT_NEAR(cpu.voxel_size, gpu.voxel_size, 1e-7f);
  size_t n = (size_t)cpu.nx * (size_t)cpu.ny * (size_t)cpu.nz;
  float max_err = 0.0f;
  for (size_t i = 0; i < n; ++i) {
    float e = fabsf(cpu.data[i] - gpu.data[i]);
    if (e > max_err) max_err = e;
  }
  EXPECT(max_err <= 2.0e-5f);
  printf("[gpu:%s:bench] sdf torus %dx%dx%d voxels: gpu %.3f ms, max_err %.3g\n",
         label, gpu.nx, gpu.ny, gpu.nz, gpu_ms, max_err);
done:
  tvdb_dense_grid_free(&cpu);
  tvdb_dense_grid_free(&gpu);
}

static void test_sample(tvdb_gpu_context_t* ctx) {
  tvdb_dense_grid g;
  fill_grid(&g, 8, 0.0f);
  tvdb_vec3f pts[5] = {
      {-0.30f, -0.05f, 0.40f},
      { 0.20f,  0.30f, 0.70f},
      {-0.45f, -0.20f, 0.15f},
      { 1.00f,  0.10f, 1.10f},
      {-1.00f, -1.00f, 0.00f},
  };
  float cpu[5], gpu[5];
  tvdb_sample_trilinear_dense_batch(&g, pts, 5, cpu);
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_sample_trilinear_dense_batch(ctx, &g, pts, 5, gpu, &err) != TVDB_OK) {
    fprintf(stderr, "sample failed: %s\n", err.message);
    EXPECT(0);
    tvdb_dense_grid_free(&g);
    return;
  }
  for (int i = 0; i < 5; ++i) EXPECT_NEAR(gpu[i], cpu[i], 2e-5f);
  tvdb_dense_grid_free(&g);
}

static void test_sample_quadratic(tvdb_gpu_context_t* ctx) {
  tvdb_dense_grid g;
  fill_grid(&g, 8, 0.0f);
  tvdb_vec3f pts[6] = {
      {-0.30f, -0.05f, 0.40f},
      { 0.20f,  0.30f, 0.70f},
      {-0.45f, -0.20f, 0.15f},
      { 1.00f,  0.10f, 1.10f},
      {-1.00f, -1.00f, 0.00f},   // far out-of-range -> edge clamp
      { 0.55f,  0.45f, 0.95f},
  };
  float cpu[6], gpu[6];
  tvdb_sample_quadratic_dense_batch(&g, pts, 6, cpu);
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_sample_quadratic_dense_batch(ctx, &g, pts, 6, gpu, &err) != TVDB_OK) {
    fprintf(stderr, "quadratic sample failed: %s\n", err.message);
    EXPECT(0);
    tvdb_dense_grid_free(&g);
    return;
  }
  for (int i = 0; i < 6; ++i) EXPECT_NEAR(gpu[i], cpu[i], 2e-5f);
  tvdb_dense_grid_free(&g);
}

static double now_seconds(void) {
  struct timespec ts;
  timespec_get(&ts, TIME_UTC);
  return (double)ts.tv_sec + (double)ts.tv_nsec * 1.0e-9;
}

static size_t parse_vram_budget_mib(void) {
  const char* env = getenv("TVDB_GPU_TEST_VRAM_MB");
  if (!env || !env[0]) return 0;
  char* end = NULL;
  unsigned long long v = strtoull(env, &end, 10);
  if (end == env || v == 0) return 0;
  if (v < 128ull) v = 128ull;
  if (v > 2048ull) v = 2048ull;
  return (size_t)v;
}

static int floor_cuberoot_size(size_t v) {
  size_t lo = 1, hi = 2048;
  while (lo < hi) {
    size_t mid = (lo + hi + 1u) / 2u;
    if (mid <= v / mid / mid) lo = mid;
    else hi = mid - 1u;
  }
  return (int)lo;
}

static int planned_sparse_test_dim(size_t budget_mib) {
  if (budget_mib == 0) return 192;
  size_t budget_bytes = budget_mib * 1024ull * 1024ull;
  size_t dense_bytes = budget_bytes / 16ull; // hard ceiling: leave room for driver heaps, staging, sparse pages, and other processes.
  int n = floor_cuberoot_size(dense_bytes / sizeof(float));
  n = (n / 64) * 64;
  if (n < 192) n = 192;
  if (n > 320) n = 320;
  return n;
}

static void test_vulkan_image3d_sample_and_bench(tvdb_gpu_context_t* ctx,
                                                 const tvdb_gpu_context_info_t* info) {
  if (info->backend != TVDB_GPU_BACKEND_VULKAN) return;
  enum { N = 48, SAMPLES = 65536, ITERS = 8 };
  tvdb_dense_grid g;
  fill_grid(&g, N, 0.05f);
  tvdb_vec3f* pts = (tvdb_vec3f*)calloc(SAMPLES, sizeof(tvdb_vec3f));
  float* ssbo = (float*)calloc(SAMPLES, sizeof(float));
  float* image = (float*)calloc(SAMPLES, sizeof(float));
  float* sparse_image = (float*)calloc(SAMPLES, sizeof(float));
  if (!pts || !ssbo || !image || !sparse_image) {
    EXPECT(0);
    goto done;
  }
  for (int i = 0; i < SAMPLES; ++i) {
    int ix = i % N;
    int iy = (i / N) % N;
    int iz = (i / (N * N)) % N;
    pts[i].x = g.ox + ((float)ix + 0.37f) * g.voxel_size;
    pts[i].y = g.oy + ((float)iy + 0.49f) * g.voxel_size;
    pts[i].z = g.oz + ((float)iz + 0.61f) * g.voxel_size;
  }
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_sample_trilinear_dense_batch(ctx, &g, pts, SAMPLES, ssbo, &err) != TVDB_OK) {
    fprintf(stderr, "sample bench ssbo failed: %s\n", err.message);
    EXPECT(0);
    goto done;
  }
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_sample_trilinear_dense_batch_vulkan_image3d(ctx, &g, pts, SAMPLES, image, &err) != TVDB_OK) {
    fprintf(stderr, "sample image3D unavailable: %s\n", err.message);
    goto done;
  }
  for (int i = 0; i < SAMPLES; i += 997) EXPECT_NEAR(image[i], ssbo[i], 3e-4f);
  int sparse_ok = 0;
  if (info->supports_sparse_3d_images) {
    memset(&err, 0, sizeof(err));
    if (tvdb_gpu_sample_trilinear_dense_batch_vulkan_sparse_image3d(ctx, &g, pts, SAMPLES, sparse_image, &err) == TVDB_OK) {
      sparse_ok = 1;
      for (int i = 0; i < SAMPLES; i += 997) EXPECT_NEAR(sparse_image[i], ssbo[i], 3e-4f);
    } else {
      fprintf(stderr, "sample sparse image3D unavailable: %s\n", err.message);
    }
  }

  double t0 = now_seconds();
  for (int it = 0; it < ITERS; ++it) {
    EXPECT(tvdb_gpu_sample_trilinear_dense_batch(ctx, &g, pts, SAMPLES, ssbo, &err) == TVDB_OK);
  }
  double t1 = now_seconds();
  for (int it = 0; it < ITERS; ++it) {
    EXPECT(tvdb_gpu_sample_trilinear_dense_batch_vulkan_image3d(ctx, &g, pts, SAMPLES, image, &err) == TVDB_OK);
  }
  double t2 = now_seconds();
  double t3 = t2;
  if (sparse_ok) {
    for (int it = 0; it < ITERS; ++it) {
      EXPECT(tvdb_gpu_sample_trilinear_dense_batch_vulkan_sparse_image3d(ctx, &g, pts, SAMPLES, sparse_image, &err) == TVDB_OK);
    }
    t3 = now_seconds();
  }
  double ssbo_ms = (t1 - t0) * 1000.0 / (double)ITERS;
  double image_ms = (t2 - t1) * 1000.0 / (double)ITERS;
  if (sparse_ok) {
    double sparse_ms = (t3 - t2) * 1000.0 / (double)ITERS;
    printf("[gpu:vulkan:bench] sample %d^3 grid, %d pts: ssbo %.3f ms, image3D %.3f ms, sparseImage3D %.3f ms, image/ssbo %.3fx, sparse/ssbo %.3fx\n",
           N, SAMPLES, ssbo_ms, image_ms, sparse_ms, image_ms / ssbo_ms, sparse_ms / ssbo_ms);
  } else {
    printf("[gpu:vulkan:bench] sample %d^3 grid, %d pts: ssbo %.3f ms, image3D %.3f ms, ratio %.3fx, sparse3d_feature=%d sparseImage3D=unavailable\n",
           N, SAMPLES, ssbo_ms, image_ms, image_ms / ssbo_ms, info->supports_sparse_3d_images);
  }

done:
  free(sparse_image);
  free(image);
  free(ssbo);
  free(pts);
  tvdb_dense_grid_free(&g);
}

static void test_vulkan_partial_sparse_image3d(tvdb_gpu_context_t* ctx,
                                               const tvdb_gpu_context_info_t* info) {
  if (info->backend != TVDB_GPU_BACKEND_VULKAN || !info->supports_sparse_3d_images) return;
  enum { ACTIVE = 4096, ITERS = 4 };
  size_t budget_mib = parse_vram_budget_mib();
  int N = planned_sparse_test_dim(budget_mib);
  size_t dense_bytes = (size_t)N * (size_t)N * (size_t)N * sizeof(float);
  size_t estimated_peak_mib = (dense_bytes + (ACTIVE * 16u) + (ACTIVE * sizeof(float)) + (1u << 20) - 1u) >> 20;
  printf("[gpu:vulkan:bench] partial sparseImage3D plan: budget=%zu MiB, dim=%d^3, est_peak<=%zu MiB\n",
         budget_mib, N, estimated_peak_mib);
  tvdb_sparse_grid sg;
  tvdb_sparse_grid_init(&sg);
  if (!tvdb_sparse_grid_reserve(&sg, ACTIVE)) {
    EXPECT(0);
    return;
  }
  sg.voxel_size = 0.125f;
  sg.ox = -2.0f; sg.oy = -1.0f; sg.oz = 0.5f;
  int k = 0;
  int z0 = N / 24;
  int y0 = N / 12;
  int x0 = N / 8;
  for (int z = z0; z < z0 + 16; ++z) {
    for (int y = y0; y < y0 + 16; ++y) {
      for (int x = x0; x < x0 + 16; ++x) {
        sg.coords[k].x = x;
        sg.coords[k].y = y;
        sg.coords[k].z = z;
        sg.values[k] = 0.01f * (float)x - 0.02f * (float)y + 0.03f * (float)z;
        ++k;
      }
    }
  }
  sg.count = (size_t)k;
  tvdb_vec3f* pts = (tvdb_vec3f*)calloc(sg.count, sizeof(tvdb_vec3f));
  float* out = (float*)calloc(sg.count, sizeof(float));
  float* ssbo = (float*)calloc(sg.count, sizeof(float));
  float* persistent = (float*)calloc(sg.count, sizeof(float));
  float* batch_out = (float*)calloc(sg.count, sizeof(float));
  tvdb_gpu_vulkan_sparse_image3d_t* persistent_image = NULL;
  tvdb_gpu_vulkan_sample_batch_t* batch = NULL;
  tvdb_gpu_vulkan_sample_batch_t* batch2 = NULL;
  tvdb_dense_grid dense;
  tvdb_dense_grid_init(&dense, N, N, N);
  dense.voxel_size = sg.voxel_size;
  dense.ox = sg.ox; dense.oy = sg.oy; dense.oz = sg.oz;
  for (size_t i = 0; i < (size_t)N * (size_t)N * (size_t)N; ++i) dense.data[i] = -7.0f;
  for (size_t i = 0; i < sg.count; ++i) {
    dense.data[(size_t)sg.coords[i].x + (size_t)N * ((size_t)sg.coords[i].y + (size_t)N * (size_t)sg.coords[i].z)] = sg.values[i];
  }
  if (!pts || !out || !ssbo || !persistent || !batch_out) {
    EXPECT(0);
    goto done;
  }
  for (size_t i = 0; i < sg.count; ++i) {
    pts[i].x = sg.ox + ((float)sg.coords[i].x + 0.5f) * sg.voxel_size;
    pts[i].y = sg.oy + ((float)sg.coords[i].y + 0.5f) * sg.voxel_size;
    pts[i].z = sg.oz + ((float)sg.coords[i].z + 0.5f) * sg.voxel_size;
  }
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_sample_trilinear_sparse_vulkan_sparse_image3d(ctx, &sg, -7.0f, N, N, N, pts, sg.count, out, &err) != TVDB_OK) {
    fprintf(stderr, "partial sparse image3D unavailable: %s\n", err.message);
    goto done;
  }
  if (tvdb_gpu_sample_trilinear_dense_batch(ctx, &dense, pts, sg.count, ssbo, &err) != TVDB_OK) {
    fprintf(stderr, "partial sparse ssbo comparison failed: %s\n", err.message);
    EXPECT(0);
    goto done;
  }
  if (tvdb_gpu_vulkan_sparse_image3d_create(ctx, &sg, -7.0f, N, N, N, &persistent_image, &err) != TVDB_OK) {
    fprintf(stderr, "persistent sparse image3D create unavailable: %s\n", err.message);
    goto done;
  }
  if (tvdb_gpu_vulkan_sparse_image3d_sample(persistent_image, pts, sg.count, persistent, &err) != TVDB_OK) {
    fprintf(stderr, "persistent sparse image3D sample unavailable: %s\n", err.message);
    goto done;
  }
  if (tvdb_gpu_vulkan_sample_batch_create(ctx, pts, sg.count, &batch, &err) != TVDB_OK) {
    fprintf(stderr, "persistent sample batch create unavailable: %s\n", err.message);
    goto done;
  }
  if (tvdb_gpu_vulkan_sample_batch_create(ctx, pts, sg.count, &batch2, &err) != TVDB_OK) {
    fprintf(stderr, "second sample batch create unavailable: %s\n", err.message);
    goto done;
  }
  if (tvdb_gpu_vulkan_sparse_image3d_sample_batch(persistent_image, batch, &err) != TVDB_OK) {
    fprintf(stderr, "persistent sample batch dispatch unavailable: %s\n", err.message);
    goto done;
  }
  if (tvdb_gpu_vulkan_sample_batch_readback(batch, batch_out, sg.count, &err) != TVDB_OK) {
    fprintf(stderr, "persistent sample batch readback unavailable: %s\n", err.message);
    goto done;
  }
  if (tvdb_gpu_vulkan_sparse_image3d_sample_batch_submit(persistent_image, batch, &err) != TVDB_OK) {
    fprintf(stderr, "async sample batch submit unavailable: %s\n", err.message);
    goto done;
  }
  int async_done = 0;
  for (int spin = 0; spin < 100000 && !async_done; ++spin) {
    EXPECT(tvdb_gpu_vulkan_sample_batch_poll(batch, &async_done, &err) == TVDB_OK);
  }
  if (!async_done) EXPECT(tvdb_gpu_vulkan_sample_batch_wait(batch, &err) == TVDB_OK);
  if (tvdb_gpu_vulkan_sparse_image3d_sample_batch_submit(persistent_image, batch, &err) != TVDB_OK) {
    fprintf(stderr, "first multi-inflight sample submit unavailable: %s\n", err.message);
    goto done;
  }
  if (tvdb_gpu_vulkan_sparse_image3d_sample_batch_submit(persistent_image, batch2, &err) != TVDB_OK) {
    fprintf(stderr, "second multi-inflight sample submit unavailable: %s\n", err.message);
    goto done;
  }
  EXPECT(tvdb_gpu_vulkan_sample_batch_wait(batch, &err) == TVDB_OK);
  EXPECT(tvdb_gpu_vulkan_sample_batch_wait(batch2, &err) == TVDB_OK);
  if (tvdb_gpu_vulkan_sample_batch_readback(batch, batch_out, sg.count, &err) != TVDB_OK) {
    fprintf(stderr, "async sample batch readback unavailable: %s\n", err.message);
    goto done;
  }
  for (size_t i = 0; i < sg.count; i += 251) EXPECT_NEAR(out[i], sg.values[i], 2e-4f);
  for (size_t i = 0; i < sg.count; i += 251) EXPECT_NEAR(persistent[i], sg.values[i], 2e-4f);
  for (size_t i = 0; i < sg.count; i += 251) EXPECT_NEAR(batch_out[i], sg.values[i], 2e-4f);

  double t0 = now_seconds();
  for (int it = 0; it < ITERS; ++it) {
    EXPECT(tvdb_gpu_sample_trilinear_dense_batch(ctx, &dense, pts, sg.count, ssbo, &err) == TVDB_OK);
  }
  double t1 = now_seconds();
  for (int it = 0; it < ITERS; ++it) {
    EXPECT(tvdb_gpu_sample_trilinear_sparse_vulkan_sparse_image3d(ctx, &sg, -7.0f, N, N, N, pts, sg.count, out, &err) == TVDB_OK);
  }
  double t2 = now_seconds();
  for (int it = 0; it < ITERS; ++it) {
    EXPECT(tvdb_gpu_vulkan_sparse_image3d_sample(persistent_image, pts, sg.count, persistent, &err) == TVDB_OK);
  }
  double t3 = now_seconds();
  for (int it = 0; it < ITERS; ++it) {
    EXPECT(tvdb_gpu_vulkan_sparse_image3d_sample_batch(persistent_image, batch, &err) == TVDB_OK);
  }
  double t4 = now_seconds();
  for (int it = 0; it < ITERS; ++it) {
    EXPECT(tvdb_gpu_vulkan_sparse_image3d_sample_batch_submit(persistent_image, batch, &err) == TVDB_OK);
    EXPECT(tvdb_gpu_vulkan_sample_batch_wait(batch, &err) == TVDB_OK);
  }
  double t_async = now_seconds();
  EXPECT(tvdb_gpu_vulkan_sample_batch_readback(batch, batch_out, sg.count, &err) == TVDB_OK);
  double t5 = now_seconds();
  double ssbo_ms = (t1 - t0) * 1000.0 / (double)ITERS;
  double sparse_ms = (t2 - t1) * 1000.0 / (double)ITERS;
  double persistent_ms = (t3 - t2) * 1000.0 / (double)ITERS;
  double batch_ms = (t4 - t3) * 1000.0 / (double)ITERS;
  double async_ms = (t_async - t4) * 1000.0 / (double)ITERS;
  double readback_ms = (t5 - t_async) * 1000.0;
  printf("[gpu:vulkan:bench] partial sparseImage3D %d^3 grid, %zu active/sample pts, budget=%zu MiB, est_peak<=%zu MiB: denseSSBO %.3f ms, oneShotPartialSparse %.3f ms, persistentSparse %.3f ms, deviceBatch %.3f ms, asyncSubmitWait %.3f ms, batchReadback %.3f ms, persistent/ssbo %.3fx, batch/ssbo %.3fx\n",
         N, sg.count, budget_mib, estimated_peak_mib, ssbo_ms, sparse_ms, persistent_ms, batch_ms, async_ms, readback_ms, persistent_ms / ssbo_ms, batch_ms / ssbo_ms);

done:
  tvdb_gpu_vulkan_sample_batch_destroy(batch2);
  tvdb_gpu_vulkan_sample_batch_destroy(batch);
  tvdb_gpu_vulkan_sparse_image3d_destroy(persistent_image);
  tvdb_dense_grid_free(&dense);
  free(batch_out);
  free(persistent);
  free(ssbo);
  free(out);
  free(pts);
  tvdb_sparse_grid_free(&sg);
}

// Sampling a partial sparse image in UNBOUND regions must return the background
// value (the shared-background-page fallback), not undefined memory. Without the
// fallback the unbound samples would be garbage and mismatch the dense path.
static void test_sparse_image_background(tvdb_gpu_context_t* ctx, const tvdb_gpu_context_info_t* info) {
  if (info->backend != TVDB_GPU_BACKEND_VULKAN || !info->supports_sparse_3d_images) return;
  const int N = 64;
  const float bg = -7.0f;
  tvdb_sparse_grid sg;
  tvdb_sparse_grid_init(&sg);
  if (!tvdb_sparse_grid_reserve(&sg, 64)) { EXPECT(0); return; }
  sg.voxel_size = 0.1f; sg.ox = -0.5f; sg.oy = 0.25f; sg.oz = 1.0f;
  size_t k = 0;
  for (int z = 2; z < 6; ++z) for (int y = 2; y < 6; ++y) for (int x = 2; x < 6; ++x) {  // small corner block
    sg.coords[k].x = x; sg.coords[k].y = y; sg.coords[k].z = z;
    sg.values[k] = 0.1f * (float)x + 0.2f * (float)y - 0.05f * (float)z;
    ++k;
  }
  sg.count = k;

  // Dense reference grid (background everywhere, active voxels overwritten).
  tvdb_dense_grid dense;
  tvdb_dense_grid_init(&dense, N, N, N);
  dense.voxel_size = sg.voxel_size; dense.ox = sg.ox; dense.oy = sg.oy; dense.oz = sg.oz;
  for (size_t i = 0; i < (size_t)N*N*N; ++i) dense.data[i] = bg;
  for (size_t i = 0; i < sg.count; ++i)
    dense.data[(size_t)sg.coords[i].x + (size_t)N*((size_t)sg.coords[i].y + (size_t)N*(size_t)sg.coords[i].z)] = sg.values[i];

  // Sample a coarse grid spanning the whole volume -> most points are unbound.
  const int S = 7;
  size_t np = (size_t)S*S*S;
  tvdb_vec3f* pts = (tvdb_vec3f*)calloc(np, sizeof(tvdb_vec3f));
  float* gpu_sparse = (float*)calloc(np, sizeof(float));
  float* gpu_ssbo = (float*)calloc(np, sizeof(float));
  size_t p = 0, far_unbound = 0;
  for (int iz = 0; iz < S; ++iz) for (int iy = 0; iy < S; ++iy) for (int ix = 0; ix < S; ++ix) {
    int vx = ix * (N / S), vy = iy * (N / S), vz = iz * (N / S);
    pts[p].x = sg.ox + ((float)vx + 0.5f) * sg.voxel_size;
    pts[p].y = sg.oy + ((float)vy + 0.5f) * sg.voxel_size;
    pts[p].z = sg.oz + ((float)vz + 0.5f) * sg.voxel_size;
    if (vx >= 8 || vy >= 8 || vz >= 8) ++far_unbound;  // clearly outside the active block + its pages
    ++p;
  }
  EXPECT(far_unbound > 0);

  tvdb_error_t err; memset(&err, 0, sizeof(err));
  if (tvdb_gpu_sample_trilinear_sparse_vulkan_sparse_image3d(ctx, &sg, bg, N, N, N, pts, np, gpu_sparse, &err) != TVDB_OK) {
    fprintf(stderr, "sparse-image background sample unavailable: %s\n", err.message);
    goto done;
  }
  EXPECT(tvdb_gpu_sample_trilinear_dense_batch(ctx, &dense, pts, np, gpu_ssbo, &err) == TVDB_OK);
  // The sparse image (with the background-page fallback) must match the dense
  // path everywhere, including unbound regions which must read exactly bg.
  for (size_t i = 0; i < np; ++i) {
    EXPECT_NEAR(gpu_sparse[i], gpu_ssbo[i], 2e-4f);
    int vx = (int)(((double)pts[i].x - sg.ox) / sg.voxel_size + 0.5);
    int vy = (int)(((double)pts[i].y - sg.oy) / sg.voxel_size + 0.5);
    int vz = (int)(((double)pts[i].z - sg.oz) / sg.voxel_size + 0.5);
    if (vx >= 8 || vy >= 8 || vz >= 8) EXPECT_NEAR(gpu_sparse[i], bg, 2e-4f);  // unbound -> background
  }
done:
  free(pts); free(gpu_sparse); free(gpu_ssbo);
  tvdb_dense_grid_free(&dense);
  tvdb_sparse_grid_free(&sg);
}

static void test_sparse_conv(tvdb_gpu_context_t* ctx) {
  tvdb_sparse_grid sg, cpu, gpu;
  tvdb_sparse_grid_init(&sg);
  tvdb_sparse_grid_init(&cpu);
  tvdb_sparse_grid_init(&gpu);
  EXPECT(tvdb_sparse_grid_reserve(&sg, 27));
  size_t k = 0;
  for (int z = 0; z < 3; ++z) {
    for (int y = 0; y < 3; ++y) {
      for (int x = 0; x < 3; ++x) {
        sg.coords[k].x = x;
        sg.coords[k].y = y;
        sg.coords[k].z = z;
        sg.values[k] = (float)(k % 7) * 0.125f - 0.3f;
        ++k;
      }
    }
  }
  sg.count = 27;
  float kernel[27];
  for (int i = 0; i < 27; ++i) kernel[i] = (float)(i % 5) * 0.05f - 0.08f;
  EXPECT(tvdb_sparse_conv3d(&sg, kernel, 3, 3, 3, 0.25f, &cpu));
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_sparse_conv3d(ctx, &sg, kernel, 3, 3, 3, 0.25f, &gpu, &err) != TVDB_OK) {
    fprintf(stderr, "sparse conv failed: %s\n", err.message);
    EXPECT(0);
    goto done;
  }
  EXPECT(gpu.count == cpu.count);
  for (size_t i = 0; i < cpu.count; ++i) {
    EXPECT(gpu.coords[i].x == cpu.coords[i].x);
    EXPECT(gpu.coords[i].y == cpu.coords[i].y);
    EXPECT(gpu.coords[i].z == cpu.coords[i].z);
    EXPECT_NEAR(gpu.values[i], cpu.values[i], 2e-5f);
  }
done:
  tvdb_sparse_grid_free(&sg);
  tvdb_sparse_grid_free(&cpu);
  tvdb_sparse_grid_free(&gpu);
}

// Force the brute-force fallback: voxels spread over a >400M-voxel bbox so the
// dense index grid would not fit, exercising the scan path (must match CPU).
static void test_sparse_conv_brute(tvdb_gpu_context_t* ctx) {
  tvdb_sparse_grid sg, cpu, gpu;
  tvdb_sparse_grid_init(&sg); tvdb_sparse_grid_init(&cpu); tvdb_sparse_grid_init(&gpu);
  const int32_t pts[6][3] = {{0,0,0},{800,1,2},{1,800,3},{2,3,800},{800,800,800},{400,400,400}};
  EXPECT(tvdb_sparse_grid_reserve(&sg, 6));
  for (int i = 0; i < 6; ++i) {
    sg.coords[i].x = pts[i][0]; sg.coords[i].y = pts[i][1]; sg.coords[i].z = pts[i][2];
    sg.values[i] = (float)(i + 1) * 0.3f - 0.5f;
  }
  sg.count = 6;
  float kernel[27];
  for (int i = 0; i < 27; ++i) kernel[i] = (float)(i % 4) * 0.07f - 0.1f;
  EXPECT(tvdb_sparse_conv3d(&sg, kernel, 3, 3, 3, 0.2f, &cpu));
  tvdb_error_t err; memset(&err, 0, sizeof(err));
  if (tvdb_gpu_sparse_conv3d(ctx, &sg, kernel, 3, 3, 3, 0.2f, &gpu, &err) != TVDB_OK) {
    fprintf(stderr, "sparse conv (brute) failed: %s\n", err.message); EXPECT(0);
  } else {
    EXPECT(gpu.count == cpu.count);
    for (size_t i = 0; i < cpu.count && gpu.count == cpu.count; ++i) {
      EXPECT(gpu.coords[i].x == cpu.coords[i].x && gpu.coords[i].y == cpu.coords[i].y && gpu.coords[i].z == cpu.coords[i].z);
      EXPECT_NEAR(gpu.values[i], cpu.values[i], 2e-5f);
    }
  }
  tvdb_sparse_grid_free(&sg); tvdb_sparse_grid_free(&cpu); tvdb_sparse_grid_free(&gpu);
}

static void test_spatial_queries(tvdb_gpu_context_t* ctx) {
  // Active set: a 4x4x4 block based at a negative-inclusive origin to exercise
  // the signed-coordinate path.
  const int bx = -1, by = 2, bz = 5;
  enum { NA = 64 };
  int32_t active[NA * 3];
  size_t na = 0;
  for (int z = 0; z < 4; ++z)
    for (int y = 0; y < 4; ++y)
      for (int x = 0; x < 4; ++x) {
        active[3 * na + 0] = bx + x;
        active[3 * na + 1] = by + y;
        active[3 * na + 2] = bz + z;
        ++na;
      }

  // Queries: all active coords (in first-seen order) plus a handful outside.
  enum { NEXTRA = 6 };
  const int outside[NEXTRA][3] = {
    {bx - 1, by, bz}, {bx, by + 4, bz}, {bx, by, bz + 4},
    {100, 100, 100}, {bx + 2, by + 2, bz - 1}, {-50, -50, -50}};
  const size_t nq = na + NEXTRA;
  int32_t* query = (int32_t*)malloc(nq * 3 * sizeof(int32_t));
  memcpy(query, active, na * 3 * sizeof(int32_t));
  for (size_t i = 0; i < NEXTRA; ++i) {
    query[3 * (na + i) + 0] = outside[i][0];
    query[3 * (na + i) + 1] = outside[i][1];
    query[3 * (na + i) + 2] = outside[i][2];
  }

  const float vs[3] = {0.25f, 0.25f, 0.25f};
  const float origin[3] = {0.1f, -0.2f, 0.3f};

  // World points: voxel centers of every active voxel (inside) plus the
  // outside coords' centers (absent).
  float* points = (float*)malloc(nq * 3 * sizeof(float));
  tvdb_ijk_to_world(query, nq, vs, origin, points);

  tvdb_error_t err;
  memset(&err, 0, sizeof(err));

  // --- coords_in_grid -------------------------------------------------------
  uint8_t* cpu_mask = (uint8_t*)malloc(nq);
  uint8_t* gpu_mask = (uint8_t*)malloc(nq);
  EXPECT(tvdb_coords_in_set(active, na, query, nq, cpu_mask));
  if (tvdb_gpu_coords_in_grid(ctx, active, na, query, nq, gpu_mask, &err) != TVDB_OK) {
    fprintf(stderr, "coords_in_grid failed: %s\n", err.message);
    EXPECT(0);
  } else {
    for (size_t i = 0; i < nq; ++i) EXPECT(gpu_mask[i] == cpu_mask[i]);
  }

  // --- ijk_to_index ---------------------------------------------------------
  int64_t* cpu_idx = (int64_t*)malloc(nq * sizeof(int64_t));
  int64_t* gpu_idx = (int64_t*)malloc(nq * sizeof(int64_t));
  EXPECT(tvdb_ijk_to_index(active, na, query, nq, cpu_idx));
  if (tvdb_gpu_ijk_to_index(ctx, active, na, query, nq, gpu_idx, &err) != TVDB_OK) {
    fprintf(stderr, "ijk_to_index failed: %s\n", err.message);
    EXPECT(0);
  } else {
    for (size_t i = 0; i < nq; ++i) EXPECT(gpu_idx[i] == cpu_idx[i]);
  }

  // --- points_in_grid -------------------------------------------------------
  uint8_t* cpu_pmask = (uint8_t*)malloc(nq);
  uint8_t* gpu_pmask = (uint8_t*)malloc(nq);
  EXPECT(tvdb_points_in_set(points, nq, vs, origin, active, na, cpu_pmask));
  if (tvdb_gpu_points_in_grid(ctx, points, nq, vs, origin, active, na, gpu_pmask, &err) != TVDB_OK) {
    fprintf(stderr, "points_in_grid failed: %s\n", err.message);
    EXPECT(0);
  } else {
    for (size_t i = 0; i < nq; ++i) EXPECT(gpu_pmask[i] == cpu_pmask[i]);
  }

  // --- neighbor_counts (6- and 26-connectivity) -----------------------------
  int32_t* cpu_cnt = (int32_t*)malloc(na * sizeof(int32_t));
  int32_t* gpu_cnt = (int32_t*)malloc(na * sizeof(int32_t));
  for (int conn = 6; conn <= 26; conn += 20) {
    EXPECT(tvdb_neighbor_counts(active, na, conn, cpu_cnt));
    if (tvdb_gpu_neighbor_counts(ctx, active, na, conn, gpu_cnt, &err) != TVDB_OK) {
      fprintf(stderr, "neighbor_counts(conn=%d) failed: %s\n", conn, err.message);
      EXPECT(0);
    } else {
      for (size_t i = 0; i < na; ++i) EXPECT(gpu_cnt[i] == cpu_cnt[i]);
    }
  }

  free(query); free(points);
  free(cpu_mask); free(gpu_mask);
  free(cpu_idx); free(gpu_idx);
  free(cpu_pmask); free(gpu_pmask);
  free(cpu_cnt); free(gpu_cnt);
}

static void make_sphere(tvdb_dense_grid* g) {
  const float center[3] = {0.1f, -0.1f, 0.2f};
  memset(g, 0, sizeof(*g));
  EXPECT(tvdb_level_set_sphere(1.0f, center, 0.1f, 3.0f, g));
}

static void test_topology(tvdb_gpu_context_t* ctx) {
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));

  // dilate / erode parity vs CPU (3 iterations on a sphere SDF).
  for (int mode = 0; mode < 2; ++mode) {
    tvdb_dense_grid cpu, gpu;
    make_sphere(&cpu); make_sphere(&gpu);
    const int iters = 3;
    tvdb_status_t st;
    if (mode == 0) { tvdb_dilate(&cpu, iters); st = tvdb_gpu_dilate(ctx, &gpu, iters, &err); }
    else           { tvdb_erode(&cpu, iters);  st = tvdb_gpu_erode(ctx, &gpu, iters, &err); }
    if (st != TVDB_OK) {
      fprintf(stderr, "gpu %s failed: %s\n", mode == 0 ? "dilate" : "erode", err.message);
      EXPECT(0);
    } else {
      size_t n = (size_t)cpu.nx * (size_t)cpu.ny * (size_t)cpu.nz;
      for (size_t i = 0; i < n; ++i) EXPECT_NEAR(gpu.data[i], cpu.data[i], 2e-5f);
    }
    tvdb_dense_grid_free(&cpu);
    tvdb_dense_grid_free(&gpu);
  }

  // prune parity: the narrow-band background is +/-3; snap voxels within tol of +3.
  {
    tvdb_dense_grid cpu, gpu;
    make_sphere(&cpu); make_sphere(&gpu);
    const float bg = 3.0f, tol = 0.6f;
    tvdb_prune_grid(&cpu, bg, tol);
    tvdb_status_t st = tvdb_gpu_prune(ctx, &gpu, bg, tol, &err);
    if (st != TVDB_OK) {
      fprintf(stderr, "gpu prune failed: %s\n", err.message);
      EXPECT(0);
    } else {
      size_t n = (size_t)cpu.nx * (size_t)cpu.ny * (size_t)cpu.nz;
      for (size_t i = 0; i < n; ++i) EXPECT_NEAR(gpu.data[i], cpu.data[i], 1e-6f);
    }
    tvdb_dense_grid_free(&cpu);
    tvdb_dense_grid_free(&gpu);
  }

  // coarsen / refine parity vs CPU (integer factor 2).
  for (int mode = 0; mode < 2; ++mode) {
    tvdb_dense_grid src, cpu, gpu;
    make_sphere(&src);
    memset(&cpu, 0, sizeof(cpu));
    memset(&gpu, 0, sizeof(gpu));
    tvdb_status_t st;
    if (mode == 0) { EXPECT(tvdb_coarsen_grid(&src, 2, &cpu, NULL)); st = tvdb_gpu_coarsen(ctx, &src, 2, &gpu, &err); }
    else           { EXPECT(tvdb_refine_grid(&src, 2, &cpu, NULL));  st = tvdb_gpu_refine(ctx, &src, 2, &gpu, &err); }
    if (st != TVDB_OK) {
      fprintf(stderr, "gpu %s failed: %s\n", mode == 0 ? "coarsen" : "refine", err.message);
      EXPECT(0);
    } else {
      EXPECT(gpu.nx == cpu.nx && gpu.ny == cpu.ny && gpu.nz == cpu.nz);
      EXPECT_NEAR(gpu.voxel_size, cpu.voxel_size, 1e-7f);
      size_t n = (size_t)cpu.nx * (size_t)cpu.ny * (size_t)cpu.nz;
      for (size_t i = 0; i < n; ++i) EXPECT_NEAR(gpu.data[i], cpu.data[i], 1e-4f);
    }
    tvdb_dense_grid_free(&src);
    tvdb_dense_grid_free(&cpu);
    tvdb_dense_grid_free(&gpu);
  }
}

static void test_volume_render(tvdb_gpu_context_t* ctx) {
  // Radial fog blob centred at world origin.
  tvdb_dense_grid dens;
  tvdb_dense_grid_init(&dens, 32, 32, 32);
  dens.voxel_size = 0.1f;
  dens.ox = dens.oy = dens.oz = -1.6f;
  for (int z = 0; z < 32; ++z)
    for (int y = 0; y < 32; ++y)
      for (int x = 0; x < 32; ++x) {
        float wx = dens.ox + ((float)x + 0.5f) * dens.voxel_size;
        float wy = dens.oy + ((float)y + 0.5f) * dens.voxel_size;
        float wz = dens.oz + ((float)z + 0.5f) * dens.voxel_size;
        float r = sqrtf(wx*wx + wy*wy + wz*wz);
        dens.data[(size_t)(z*32 + y)*32 + x] = r < 1.0f ? (1.0f - r) * 5.0f : 0.0f;
      }

  const float eye[3] = {0.0f, 0.0f, -5.0f};
  const float center[3] = {0.0f, 0.0f, 0.0f};
  const float up[3] = {0.0f, 1.0f, 0.0f};
  const int W = 64, H = 64;
  float* cpu = (float*)malloc((size_t)W * H * sizeof(float));
  float* gpu = (float*)malloc((size_t)W * H * sizeof(float));
  EXPECT(tvdb_volume_render(&dens, eye, center, up, 0.6f, W, H, 1.0f, 0.05f, 0.0f, cpu));
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  tvdb_status_t st = tvdb_gpu_volume_render(ctx, &dens, eye, center, up, 0.6f, W, H, 1.0f, 0.05f, 0.0f, gpu, &err);
  if (st != TVDB_OK) {
    fprintf(stderr, "gpu volume_render failed: %s\n", err.message);
    EXPECT(0);
  } else {
    float max_err = 0.0f, center_val = gpu[(H/2)*W + W/2], corner_val = gpu[0];
    for (int i = 0; i < W*H; ++i) { float e = fabsf(cpu[i] - gpu[i]); if (e > max_err) max_err = e; }
    EXPECT(max_err <= 2e-3f);
    EXPECT(center_val > corner_val);  // blob brighter at image centre
  }
  free(cpu); free(gpu);
  tvdb_dense_grid_free(&dens);
}

static void test_ray_queries(tvdb_gpu_context_t* ctx) {
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));

  // A handful of rays with non-grid-aligned directions to avoid voxel-corner
  // ties in the DDA. Grid world AABB = [0, 1.6]^3.
  enum { NR = 4 };
  tvdb_ray rays[NR] = {
    {{-0.5f, 0.37f, 0.81f}, {1.0f, 0.05f, -0.03f}, 0.0f, 4.0f},
    {{ 0.83f, -0.5f, 0.41f}, {0.02f, 1.0f, 0.04f}, 0.0f, 4.0f},
    {{ 0.21f, 0.95f, -0.5f}, {0.07f, -0.06f, 1.0f}, 0.0f, 4.0f},
    {{-0.4f, -0.4f, -0.4f}, {1.0f, 1.02f, 0.98f}, 0.0f, 4.0f},
  };
  float flat[NR * 8];
  for (int i = 0; i < NR; ++i) {
    flat[8*i+0] = rays[i].origin.x; flat[8*i+1] = rays[i].origin.y; flat[8*i+2] = rays[i].origin.z;
    flat[8*i+3] = rays[i].tmin;
    flat[8*i+4] = rays[i].dir.x; flat[8*i+5] = rays[i].dir.y; flat[8*i+6] = rays[i].dir.z;
    flat[8*i+7] = rays[i].tmax;
  }

  // --- uniform_ray_samples --------------------------------------------------
  const size_t M = 8;
  float* gpu_pts = (float*)malloc(NR * M * 3 * sizeof(float));
  float* gpu_t = (float*)malloc(NR * M * sizeof(float));
  if (tvdb_gpu_uniform_ray_samples(ctx, flat, NR, M, gpu_pts, gpu_t, &err) != TVDB_OK) {
    fprintf(stderr, "uniform_ray_samples failed: %s\n", err.message);
    EXPECT(0);
  } else {
    for (int r = 0; r < NR; ++r) {
      tvdb_vec3f cpu_pts[8]; float cpu_t[8];
      tvdb_uniform_ray_samples(&rays[r], M, cpu_pts, cpu_t);
      for (size_t s = 0; s < M; ++s) {
        size_t g = (size_t)r * M + s;
        EXPECT_NEAR(gpu_t[g], cpu_t[s], 1e-5f);
        EXPECT_NEAR(gpu_pts[3*g+0], cpu_pts[s].x, 1e-5f);
        EXPECT_NEAR(gpu_pts[3*g+1], cpu_pts[s].y, 1e-5f);
        EXPECT_NEAR(gpu_pts[3*g+2], cpu_pts[s].z, 1e-5f);
      }
    }
  }
  free(gpu_pts); free(gpu_t);

  // --- voxels_along_ray (DDA) -----------------------------------------------
  tvdb_dense_grid grid;
  tvdb_dense_grid_init(&grid, 16, 16, 16);
  grid.voxel_size = 0.1f; grid.ox = grid.oy = grid.oz = 0.0f;
  const size_t cap = 64;
  int32_t* gpu_vox = (int32_t*)malloc(NR * cap * 3 * sizeof(int32_t));
  int32_t* gpu_cnt = (int32_t*)malloc(NR * sizeof(int32_t));
  if (tvdb_gpu_voxels_along_ray(ctx, &grid, flat, NR, cap, gpu_vox, gpu_cnt, &err) != TVDB_OK) {
    fprintf(stderr, "voxels_along_ray failed: %s\n", err.message);
    EXPECT(0);
  } else {
    for (int r = 0; r < NR; ++r) {
      tvdb_vec3i cpu_vox[64];
      size_t cpu_n = tvdb_voxels_along_ray_dense(&grid, &rays[r], cpu_vox, cap);
      // Amanatides-Woo termination at the exit boundary is float-sensitive, so
      // the CPU and GPU may differ by one trailing voxel; require the common
      // prefix to match exactly and the counts to be within one.
      size_t gn = (size_t)gpu_cnt[r];
      EXPECT(gn + 1 >= cpu_n && cpu_n + 1 >= gn);
      size_t common = gn < cpu_n ? gn : cpu_n;
      for (size_t k = 0; k < common; ++k) {
        size_t b = ((size_t)r * cap + k) * 3;
        EXPECT(gpu_vox[b+0] == cpu_vox[k].x);
        EXPECT(gpu_vox[b+1] == cpu_vox[k].y);
        EXPECT(gpu_vox[b+2] == cpu_vox[k].z);
      }
    }
  }
  free(gpu_vox); free(gpu_cnt);
  tvdb_dense_grid_free(&grid);

  // --- segments_along_ray: rays through a sphere SDF -> one inside run each --
  tvdb_dense_grid sdf;
  make_sphere(&sdf);  // sphere radius 1, centre ~(0.1,-0.1,0.2)
  enum { NSR = 3 };
  tvdb_ray srays[NSR] = {
    {{-3.0f, -0.1f, 0.2f}, {1.0f, 0.0f, 0.0f}, 0.0f, 6.0f},
    {{0.1f, -3.0f, 0.2f},  {0.0f, 1.0f, 0.0f}, 0.0f, 6.0f},
    {{-2.0f, -2.0f, 0.2f}, {1.0f, 1.0f, 0.0f}, 0.0f, 6.0f},
  };
  float sflat[NSR * 8];
  for (int i = 0; i < NSR; ++i) {
    sflat[8*i+0] = srays[i].origin.x; sflat[8*i+1] = srays[i].origin.y; sflat[8*i+2] = srays[i].origin.z;
    sflat[8*i+3] = srays[i].tmin;
    sflat[8*i+4] = srays[i].dir.x; sflat[8*i+5] = srays[i].dir.y; sflat[8*i+6] = srays[i].dir.z;
    sflat[8*i+7] = srays[i].tmax;
  }
  const size_t scap = 8, sc = 256;
  float* gpu_pairs = (float*)malloc(NSR * scap * 2 * sizeof(float));
  int32_t* gpu_pc = (int32_t*)malloc(NSR * sizeof(int32_t));
  if (tvdb_gpu_segments_along_ray(ctx, &sdf, sflat, NSR, 0.0f, sc, scap, gpu_pairs, gpu_pc, &err) != TVDB_OK) {
    fprintf(stderr, "segments_along_ray failed: %s\n", err.message);
    EXPECT(0);
  } else {
    for (int r = 0; r < NSR; ++r) {
      float cpu_pairs[16];
      size_t cpu_np = tvdb_segments_along_ray(&sdf, &srays[r], 0.0f, sc, cpu_pairs, scap);
      EXPECT((size_t)gpu_pc[r] == cpu_np);
      EXPECT(cpu_np == 1);  // each ray crosses the sphere once
      size_t m = (size_t)gpu_pc[r] < cpu_np ? (size_t)gpu_pc[r] : cpu_np;
      for (size_t p = 0; p < m && p < scap; ++p) {
        EXPECT_NEAR(gpu_pairs[((size_t)r*scap + p)*2 + 0], cpu_pairs[2*p+0], 1e-3f);
        EXPECT_NEAR(gpu_pairs[((size_t)r*scap + p)*2 + 1], cpu_pairs[2*p+1], 1e-3f);
      }
    }
  }
  free(gpu_pairs); free(gpu_pc);
  tvdb_dense_grid_free(&sdf);
}

static void init_tsdf_pair(tvdb_dense_grid* tsdf, tvdb_dense_grid* w, float trunc) {
  tvdb_dense_grid_init(tsdf, 24, 24, 24);
  tvdb_dense_grid_init(w, 24, 24, 24);
  tsdf->voxel_size = w->voxel_size = 0.05f;
  tsdf->ox = w->ox = -0.6f; tsdf->oy = w->oy = -0.6f; tsdf->oz = w->oz = 0.5f;
  size_t n = 24*24*24;
  for (size_t i = 0; i < n; ++i) { tsdf->data[i] = trunc; w->data[i] = 0.0f; }
}

static void test_tsdf(tvdb_gpu_context_t* ctx) {
  const float trunc = 0.1f;
  const int W = 64, H = 64;
  float* depth = (float*)malloc((size_t)W * H * sizeof(float));
  for (int i = 0; i < W*H; ++i) depth[i] = 1.0f;  // fronto-parallel plane at z=1

  tvdb_depth_frame frame;
  memset(&frame, 0, sizeof(frame));
  frame.width = W; frame.height = H; frame.depth = depth;
  frame.fx = 128.0f; frame.fy = 128.0f; frame.cx = 32.0f; frame.cy = 32.0f;
  // world<-camera identity (camera at origin looking +z).
  frame.pose[0] = 1.0f; frame.pose[5] = 1.0f; frame.pose[10] = 1.0f;
  frame.trunc_distance = trunc; frame.depth_min = 0.1f; frame.depth_max = 3.0f;

  tvdb_dense_grid tc, wc, tg, wg;
  init_tsdf_pair(&tc, &wc, trunc);
  init_tsdf_pair(&tg, &wg, trunc);
  EXPECT(tvdb_integrate_tsdf(&tc, &wc, &frame));
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  tvdb_status_t st = tvdb_gpu_integrate_tsdf(ctx, &tg, &wg, &frame, &err);
  if (st != TVDB_OK) {
    fprintf(stderr, "gpu integrate_tsdf failed: %s\n", err.message);
    EXPECT(0);
  } else {
    size_t n = 24*24*24, updated = 0;
    for (size_t i = 0; i < n; ++i) {
      EXPECT_NEAR(tg.data[i], tc.data[i], 1e-5f);
      EXPECT_NEAR(wg.data[i], wc.data[i], 1e-5f);
      if (wc.data[i] > 0.5f) ++updated;
    }
    EXPECT(updated > 0);  // some voxels integrated the frame
  }
  tvdb_dense_grid_free(&tc); tvdb_dense_grid_free(&wc);
  tvdb_dense_grid_free(&tg); tvdb_dense_grid_free(&wg);
  free(depth);
}

static void test_stats(tvdb_gpu_context_t* ctx) {
  tvdb_dense_grid g;
  make_sphere(&g);
  tvdb_grid_stats_t cpu, gpu;
  EXPECT(tvdb_grid_statistics(&g, &cpu));
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_grid_statistics(ctx, &g, &gpu, &err) != TVDB_OK) {
    fprintf(stderr, "gpu grid_statistics failed: %s\n", err.message);
    EXPECT(0);
  } else {
    EXPECT(gpu.count == cpu.count);
    EXPECT_NEAR(gpu.min, cpu.min, 1e-5);
    EXPECT_NEAR(gpu.max, cpu.max, 1e-5);
    double srel = fabs(cpu.sum) * 1e-4 + 1e-2;
    EXPECT_NEAR(gpu.sum, cpu.sum, srel);
    EXPECT_NEAR(gpu.mean, cpu.mean, 1e-4);
    EXPECT_NEAR(gpu.stddev, cpu.stddev, 1e-3);
  }

  // --- check_level_set: sphere SDF should report |grad| ~ 1 -----------------
  {
    tvdb_level_set_check_t cc, gc;
    EXPECT(tvdb_check_level_set(&g, 0.0, 0.5, &cc));
    if (tvdb_gpu_check_level_set(ctx, &g, 0.0, 0.5, &gc, &err) != TVDB_OK) {
      fprintf(stderr, "gpu check_level_set failed: %s\n", err.message);
      EXPECT(0);
    } else {
      EXPECT(gc.band_count == cc.band_count);
      EXPECT_NEAR(gc.mean_grad_mag, cc.mean_grad_mag, 1e-3);
      EXPECT_NEAR(gc.max_grad_error, cc.max_grad_error, 1e-3);
      EXPECT_NEAR(gc.bad_fraction, cc.bad_fraction, 0.02);
    }
  }

  // --- check_fog_volume: raw SDF invalid, clamped [0,1] copy valid ----------
  {
    int cv, gv; double cmn, cmx, gmn, gmx;
    EXPECT(tvdb_check_fog_volume(&g, 0.01, &cv, &cmn, &cmx));
    EXPECT(tvdb_gpu_check_fog_volume(ctx, &g, 0.01, &gv, &gmn, &gmx, &err) == TVDB_OK);
    EXPECT(gv == cv);  // both invalid (SDF has negatives)
    EXPECT_NEAR(gmn, cmn, 1e-5);
    EXPECT_NEAR(gmx, cmx, 1e-5);

    tvdb_dense_grid fog;
    tvdb_dense_grid_init(&fog, g.nx, g.ny, g.nz);
    fog.voxel_size = g.voxel_size; fog.ox = g.ox; fog.oy = g.oy; fog.oz = g.oz;
    size_t n = (size_t)g.nx * g.ny * g.nz;
    for (size_t i = 0; i < n; ++i) { float v = g.data[i]; fog.data[i] = v < 0 ? 0.0f : (v > 1 ? 1.0f : v); }
    EXPECT(tvdb_check_fog_volume(&fog, 0.01, &cv, &cmn, &cmx));
    EXPECT(tvdb_gpu_check_fog_volume(ctx, &fog, 0.01, &gv, &gmn, &gmx, &err) == TVDB_OK);
    EXPECT(gv == cv && gv == 1);  // both valid
    tvdb_dense_grid_free(&fog);
  }
  tvdb_dense_grid_free(&g);
}

static void test_flood(tvdb_gpu_context_t* ctx) {
  // Sphere SDF: the narrow band clamps values to +/-0.3. Flood with band=0.2:
  // deep-interior far voxels (v <= -0.2) are enclosed -> set to -band; exterior
  // far voxels (v >= 0.2) -> +band. The reachability flood is deterministic, so
  // GPU and CPU agree exactly.
  const float band = 0.2f;
  tvdb_dense_grid cpu, gpu;
  make_sphere(&cpu); make_sphere(&gpu);
  tvdb_signed_flood_fill(&cpu, band);
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_signed_flood_fill(ctx, &gpu, band, &err) != TVDB_OK) {
    fprintf(stderr, "gpu signed_flood_fill failed: %s\n", err.message);
    EXPECT(0);
  } else {
    size_t n = (size_t)cpu.nx * cpu.ny * cpu.nz, interior = 0;
    for (size_t i = 0; i < n; ++i) {
      EXPECT_NEAR(gpu.data[i], cpu.data[i], 1e-6f);
      if (cpu.data[i] < -(band - 0.01f)) ++interior;
    }
    EXPECT(interior > 0);  // the enclosed interior was filled to -band
  }
  tvdb_dense_grid_free(&cpu);
  tvdb_dense_grid_free(&gpu);
}

static void test_splat(tvdb_gpu_context_t* ctx) {
  const int N = 16;
  tvdb_dense_grid cpu, gpu;
  tvdb_dense_grid_init(&cpu, N, N, N);
  tvdb_dense_grid_init(&gpu, N, N, N);
  cpu.voxel_size = gpu.voxel_size = 0.1f;
  cpu.ox = gpu.ox = -0.8f; cpu.oy = gpu.oy = -0.8f; cpu.oz = gpu.oz = -0.8f;

  const size_t NP = 300;
  tvdb_vec3f* pts = (tvdb_vec3f*)malloc(NP * sizeof(tvdb_vec3f));
  float* flat = (float*)malloc(NP * 3 * sizeof(float));
  float* vals = (float*)malloc(NP * sizeof(float));
  unsigned int s = 12345u;
  for (size_t i = 0; i < NP; ++i) {
    s = s * 1664525u + 1013904223u; float a = (float)(s >> 8) / 16777216.0f;
    s = s * 1664525u + 1013904223u; float b = (float)(s >> 8) / 16777216.0f;
    s = s * 1664525u + 1013904223u; float c = (float)(s >> 8) / 16777216.0f;
    s = s * 1664525u + 1013904223u; float d = (float)(s >> 8) / 16777216.0f;
    pts[i].x = -0.7f + a * 1.4f; pts[i].y = -0.7f + b * 1.4f; pts[i].z = -0.7f + c * 1.4f;
    flat[3*i+0] = pts[i].x; flat[3*i+1] = pts[i].y; flat[3*i+2] = pts[i].z;
    vals[i] = d * 2.0f - 1.0f;
  }
  size_t nvox = (size_t)N * N * N;
  float* wc = (float*)calloc(nvox, sizeof(float));
  float* wg = (float*)calloc(nvox, sizeof(float));

  tvdb_splat_trilinear_dense(&cpu, pts, vals, NP, wc);
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_splat_trilinear_dense(ctx, &gpu, flat, vals, NP, wg, &err) != TVDB_OK) {
    fprintf(stderr, "gpu splat failed: %s\n", err.message);
    EXPECT(0);
  } else {
    for (size_t i = 0; i < nvox; ++i) {
      EXPECT_NEAR(gpu.data[i], cpu.data[i], 1e-4f);  // atomic-add order differs
      EXPECT_NEAR(wg[i], wc[i], 1e-4f);
    }
  }
  free(pts); free(flat); free(vals); free(wc); free(wg);
  tvdb_dense_grid_free(&cpu); tvdb_dense_grid_free(&gpu);
}

static void test_gaussian_sh(tvdb_gpu_context_t* ctx) {
  // View-dependent SH color eval at degree 3 (K=16), parity vs CPU reference.
  const uint32_t N = 200, degree = 3, K = 16;
  float* sh = (float*)malloc((size_t)N * K * 3 * sizeof(float));
  float* dirs = (float*)malloc((size_t)N * 3 * sizeof(float));
  float* cpu = (float*)malloc((size_t)N * 3 * sizeof(float));
  float* gpu = (float*)malloc((size_t)N * 3 * sizeof(float));
  unsigned int s = 24601u;
  for (size_t i = 0; i < (size_t)N * K * 3; ++i) {
    s = s * 1664525u + 1013904223u; sh[i] = (float)(s >> 8) / 16777216.0f * 2.0f - 1.0f;
  }
  for (uint32_t g = 0; g < N; ++g) {
    s = s * 1664525u + 1013904223u; float a = (float)(s >> 8) / 16777216.0f * 2.0f - 1.0f;
    s = s * 1664525u + 1013904223u; float b = (float)(s >> 8) / 16777216.0f * 2.0f - 1.0f;
    s = s * 1664525u + 1013904223u; float c = (float)(s >> 8) / 16777216.0f * 2.0f - 1.0f;
    dirs[3*g+0] = a; dirs[3*g+1] = b; dirs[3*g+2] = c;  // unnormalized; normalized internally
  }
  if (N > 4) { dirs[3*4+0] = dirs[3*4+1] = dirs[3*4+2] = 0.0f; }  // degenerate dir -> DC only
  tvdb_error_t cerr, err;
  memset(&cerr, 0, sizeof(cerr)); memset(&err, 0, sizeof(err));
  EXPECT(tvdb_gaussian_sh_eval(N, degree, sh, dirs, cpu, &cerr) == TVDB_OK);
  if (tvdb_gpu_gaussian_sh_eval(ctx, N, degree, sh, dirs, gpu, &err) != TVDB_OK) {
    fprintf(stderr, "gpu gaussian sh failed: %s\n", err.message);
    EXPECT(0);
  } else {
    for (size_t i = 0; i < (size_t)N * 3; ++i) EXPECT_NEAR(gpu[i], cpu[i], 2e-5f);
  }
  free(sh); free(dirs); free(cpu); free(gpu);
}

static void pack_sort(const int32_t* coords, size_t n, long long* keys);  // defined below

static void test_voxelize_unbounded(tvdb_gpu_context_t* ctx) {
  // Points spread over a ~10^18-voxel ijk bbox (tiny voxels, huge range): the
  // dense-occupancy path can't fit that in VRAM, so this exercises the O(n)
  // hash-set path. Duplicate voxels (jittered points sharing a cell) test dedup.
  const size_t NU = 400, NP = 800;
  const float vs[3] = {0.01f, 0.01f, 0.01f};
  const float origin[3] = {0.0f, 0.0f, 0.0f};
  int32_t* centers = (int32_t*)malloc(NU * 3 * sizeof(int32_t));
  float* flat = (float*)malloc(NP * 3 * sizeof(float));
  unsigned int s = 4242u;
  #define RND01 ( (s = s*1664525u + 1013904223u), (float)(s >> 8) / 16777216.0f )
  for (size_t u = 0; u < NU; ++u)
    for (int a = 0; a < 3; ++a)
      centers[3*u+a] = (int32_t)(RND01 * 1000000.0f) - 500000;  // within +-2^20 for pack_sort
  for (size_t i = 0; i < NP; ++i) {
    size_t u = i % NU;
    for (int a = 0; a < 3; ++a) {
      float jitter = (RND01 - 0.5f) * 0.6f * vs[a];  // stays inside the voxel
      flat[3*i+a] = origin[a] + ((float)centers[3*u+a] + 0.5f) * vs[a] + jitter;
    }
  }
  #undef RND01

  int32_t* cpu_coords = NULL; size_t cpu_n = 0;
  EXPECT(tvdb_voxelize_points(flat, NP, vs, origin, &cpu_coords, &cpu_n));
  EXPECT(cpu_n > 0 && cpu_n <= NU);
  tvdb_error_t err; memset(&err, 0, sizeof(err));

  // Explicit unbounded entry point and the auto-fallback wrapper must agree.
  for (int which = 0; which < 2; ++which) {
    int32_t* gpu_coords = NULL; size_t gpu_n = 0;
    tvdb_status_t st = which == 0
      ? tvdb_gpu_voxelize_points_unbounded(ctx, flat, NP, vs, origin, &gpu_coords, &gpu_n, &err)
      : tvdb_gpu_voxelize_points(ctx, flat, NP, vs, origin, &gpu_coords, &gpu_n, &err);
    if (st != TVDB_OK) {
      fprintf(stderr, "gpu voxelize unbounded (%d) failed: %s\n", which, err.message);
      EXPECT(0);
    } else {
      EXPECT(gpu_n == cpu_n);
      if (gpu_n == cpu_n && cpu_n > 0) {
        long long* kc = (long long*)malloc(cpu_n * sizeof(long long));
        long long* kg = (long long*)malloc(gpu_n * sizeof(long long));
        pack_sort(cpu_coords, cpu_n, kc);
        pack_sort(gpu_coords, gpu_n, kg);
        for (size_t i = 0; i < cpu_n; ++i) EXPECT(kc[i] == kg[i]);  // same voxel set
        free(kc); free(kg);
      }
    }
    free(gpu_coords);
  }
  free(cpu_coords); free(centers); free(flat);
}

static void test_gaussian_project(tvdb_gpu_context_t* ctx) {
  // Project 3D Gaussians to 2D conics, parity vs CPU tvdb_gaussian_project.
  const uint32_t N = 100;
  float* means = (float*)malloc(N * 3 * sizeof(float));
  float* quats = (float*)malloc(N * 4 * sizeof(float));
  float* log_scales = (float*)malloc(N * 3 * sizeof(float));
  float* opac = (float*)malloc(N * sizeof(float));
  float* sh_dc = (float*)malloc(N * 3 * sizeof(float));
  unsigned int s = 99173u;
  #define RND01 ( (s = s*1664525u + 1013904223u), (float)(s >> 8) / 16777216.0f )
  for (uint32_t i = 0; i < N; ++i) {
    means[3*i+0] = RND01 * 2.0f - 1.0f;
    means[3*i+1] = RND01 * 2.0f - 1.0f;
    means[3*i+2] = RND01 * 2.0f - 1.0f;       // depth = z + 5 (extrinsics below) -> visible
    float qx = RND01*2-1, qy = RND01*2-1, qz = RND01*2-1, qw = RND01*2-1;
    float ql = sqrtf(qx*qx+qy*qy+qz*qz+qw*qw); if (ql < 1e-6f) { qw = 1; ql = 1; }
    quats[4*i+0]=qx/ql; quats[4*i+1]=qy/ql; quats[4*i+2]=qz/ql; quats[4*i+3]=qw/ql;
    log_scales[3*i+0] = RND01 - 2.0f; log_scales[3*i+1] = RND01 - 2.0f; log_scales[3*i+2] = RND01 - 2.0f;
    opac[i] = RND01 * 4.0f - 2.0f;
    sh_dc[3*i+0] = RND01; sh_dc[3*i+1] = RND01; sh_dc[3*i+2] = RND01;
  }
  #undef RND01
  // Column-major extrinsics: identity rotation + translation (0,0,5).
  float extr[16] = {1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,5,1};
  tvdb_camera_t* cam = tvdb_camera_create_perspective(500.0f, 500.0f, 256.0f, 256.0f,
                                                      512.0f, 512.0f, 0.1f, 100.0f, extr);
  if (!cam) { EXPECT(0); free(means); free(quats); free(log_scales); free(opac); free(sh_dc); return; }

  tvdb_gaussian_splat_t splat;
  memset(&splat, 0, sizeof(splat));
  splat.num_gaussians = N;
  splat.means = means; splat.quats = quats; splat.log_scales = log_scales;
  splat.logit_opacities = opac; splat.sh_coeffs = sh_dc; splat.owns_data = 0;

  tvdb_error_t cerr, err;
  memset(&cerr, 0, sizeof(cerr)); memset(&err, 0, sizeof(err));
  uint32_t cpu_count = 0;
  tvdb_projected_gaussian_t* cpu = tvdb_gaussian_project(&splat, cam, &cpu_count, &cerr);
  tvdb_projected_gaussian_t* gpu = (tvdb_projected_gaussian_t*)malloc(N * sizeof(tvdb_projected_gaussian_t));
  EXPECT(cpu != NULL && cpu_count == N);
  if (cpu && tvdb_gpu_gaussian_project(ctx, N, means, quats, log_scales, opac, sh_dc,
                                       cam->extrinsics, cam->intrinsics, cam->near, cam->far, gpu, &err) != TVDB_OK) {
    fprintf(stderr, "gpu gaussian project failed: %s\n", err.message);
    EXPECT(0);
  } else if (cpu) {
    for (uint32_t i = 0; i < N; ++i) {
      const float* c = (const float*)&cpu[i];
      const float* g = (const float*)&gpu[i];
      for (int k = 0; k < 11; ++k) {
        float tol = 1e-3f * (1.0f + fabsf(c[k]));  // GPU reorders FP; fast-sqrt bit trick matches
        EXPECT(fabsf(g[k] - c[k]) <= tol);
      }
    }
  }
  tvdb_projected_gaussian_destroy(cpu);
  free(gpu);
  tvdb_camera_destroy(cam);
  free(means); free(quats); free(log_scales); free(opac); free(sh_dc);
}

// Generic dispatch engine, exercised through tvdb_gpu_axpy (which builds a
// dispatch spec with storage-in, storage-out, and uniform bindings).
static void test_dispatch(tvdb_gpu_context_t* ctx) {
  const size_t N = 1000;
  float* x = (float*)malloc(N * sizeof(float));
  float* y = (float*)malloc(N * sizeof(float));
  float* gpu = (float*)malloc(N * sizeof(float));
  const float alpha = 2.5f;
  unsigned int s = 271828u;
  for (size_t i = 0; i < N; ++i) {
    s = s * 1664525u + 1013904223u; x[i] = (float)(s >> 8) / 16777216.0f * 4.0f - 2.0f;
    s = s * 1664525u + 1013904223u; y[i] = (float)(s >> 8) / 16777216.0f * 4.0f - 2.0f;
  }
  tvdb_error_t err; memset(&err, 0, sizeof(err));
  if (tvdb_gpu_axpy(ctx, x, y, alpha, N, gpu, &err) != TVDB_OK) {
    fprintf(stderr, "gpu axpy (dispatch) failed: %s\n", err.message); EXPECT(0);
  } else {
    for (size_t i = 0; i < N; ++i) EXPECT_NEAR(gpu[i], alpha * x[i] + y[i], 2e-5f);
  }
  free(x); free(y); free(gpu);
}

static void test_gaussian_mcmc(tvdb_gpu_context_t* ctx) {
  const uint32_t N = 150;
  float* opac = (float*)malloc(N * sizeof(float));
  float* scales = (float*)malloc(N * 3 * sizeof(float));
  int32_t* ratios = (int32_t*)malloc(N * sizeof(int32_t));
  float* cpu_op = (float*)malloc(N * sizeof(float));
  float* gpu_op = (float*)malloc(N * sizeof(float));
  float* cpu_sc = (float*)malloc(N * 3 * sizeof(float));
  float* gpu_sc = (float*)malloc(N * 3 * sizeof(float));
  unsigned int s = 8675309u;
  #define RND01 ( (s = s*1664525u + 1013904223u), (float)(s >> 8) / 16777216.0f )
  for (uint32_t i = 0; i < N; ++i) {
    opac[i] = 0.02f + RND01 * 0.95f;               // (0,1)
    scales[3*i+0] = 0.05f + RND01; scales[3*i+1] = 0.05f + RND01; scales[3*i+2] = 0.05f + RND01;
    ratios[i] = 1 + (int)(RND01 * 8.0f);           // [1,8]
  }
  tvdb_error_t cerr, err; memset(&cerr, 0, sizeof(cerr)); memset(&err, 0, sizeof(err));
  EXPECT(tvdb_gaussian_mcmc_relocation(N, opac, scales, ratios, cpu_op, cpu_sc, &cerr) == TVDB_OK);
  if (tvdb_gpu_gaussian_mcmc_relocation(ctx, N, opac, scales, ratios, gpu_op, gpu_sc, &err) != TVDB_OK) {
    fprintf(stderr, "gpu mcmc relocation failed: %s\n", err.message); EXPECT(0);
  } else {
    for (uint32_t i = 0; i < N; ++i) {
      EXPECT_NEAR(gpu_op[i], cpu_op[i], 2e-5f);
      for (int d = 0; d < 3; ++d) {
        float tol = 1e-3f * (1.0f + fabsf(cpu_sc[3*i+d]));
        EXPECT(fabsf(gpu_sc[3*i+d] - cpu_sc[3*i+d]) <= tol);
      }
    }
    // Sanity: ratio==1 is identity (opacity & scale unchanged).
    int found_r1 = 0;
    for (uint32_t i = 0; i < N && !found_r1; ++i) if (ratios[i] == 1) {
      found_r1 = 1;
      EXPECT_NEAR(cpu_op[i], opac[i], 2e-5f);
      EXPECT_NEAR(cpu_sc[3*i+0], scales[3*i+0], 1e-4f);
    }
  }

  // ---- add_noise ----
  float* means = (float*)malloc(N * 3 * sizeof(float));
  float* quats = (float*)malloc(N * 4 * sizeof(float));
  float* lsc = (float*)malloc(N * 3 * sizeof(float));
  float* opl = (float*)malloc(N * sizeof(float));
  float* rnd = (float*)malloc(N * 3 * sizeof(float));
  float* cpu_m = (float*)malloc(N * 3 * sizeof(float));
  float* gpu_m = (float*)malloc(N * 3 * sizeof(float));
  for (uint32_t i = 0; i < N; ++i) {
    means[3*i+0]=RND01*2-1; means[3*i+1]=RND01*2-1; means[3*i+2]=RND01*2-1;
    float qx=RND01*2-1, qy=RND01*2-1, qz=RND01*2-1, qw=RND01*2-1;
    float ql=sqrtf(qx*qx+qy*qy+qz*qz+qw*qw); if (ql<1e-6f){qw=1;ql=1;}
    quats[4*i+0]=qx/ql; quats[4*i+1]=qy/ql; quats[4*i+2]=qz/ql; quats[4*i+3]=qw/ql;
    lsc[3*i+0]=RND01-2; lsc[3*i+1]=RND01-2; lsc[3*i+2]=RND01-2;
    opl[i]=RND01*8-4;  // logit; mostly op >> 0.005 (gate ~1)
    rnd[3*i+0]=RND01*2-1; rnd[3*i+1]=RND01*2-1; rnd[3*i+2]=RND01*2-1;
  }
  #undef RND01
  opl[0] = -8.0f;  // op ~ 0.0003 < 0.005: drives the steep gate toward 0 (exercises the suppression branch)
  opl[1] = -5.3f;  // op ~ 0.005: right at the gate midpoint, so a wrong gate constant would diverge
  const float lr = 0.01f;
  EXPECT(tvdb_gaussian_mcmc_add_noise(N, means, quats, lsc, opl, rnd, lr, cpu_m, &cerr) == TVDB_OK);
  if (tvdb_gpu_gaussian_mcmc_add_noise(ctx, N, means, quats, lsc, opl, rnd, lr, gpu_m, &err) != TVDB_OK) {
    fprintf(stderr, "gpu mcmc add_noise failed: %s\n", err.message); EXPECT(0);
  } else {
    for (uint32_t i = 0; i < N * 3; ++i) {
      float tol = 2e-4f * (1.0f + fabsf(cpu_m[i]));
      EXPECT(fabsf(gpu_m[i] - cpu_m[i]) <= tol);
    }
  }
  free(opac); free(scales); free(ratios); free(cpu_op); free(gpu_op); free(cpu_sc); free(gpu_sc);
  free(means); free(quats); free(lsc); free(opl); free(rnd); free(cpu_m); free(gpu_m);
}

static void test_splat_quadratic(tvdb_gpu_context_t* ctx) {
  const int N = 16;
  tvdb_dense_grid cpu, gpu;
  tvdb_dense_grid_init(&cpu, N, N, N);
  tvdb_dense_grid_init(&gpu, N, N, N);
  cpu.voxel_size = gpu.voxel_size = 0.1f;
  cpu.ox = gpu.ox = -0.8f; cpu.oy = gpu.oy = -0.8f; cpu.oz = gpu.oz = -0.8f;

  const size_t NP = 300;
  tvdb_vec3f* pts = (tvdb_vec3f*)malloc(NP * sizeof(tvdb_vec3f));
  float* flat = (float*)malloc(NP * 3 * sizeof(float));
  float* vals = (float*)malloc(NP * sizeof(float));
  unsigned int s = 777u;
  for (size_t i = 0; i < NP; ++i) {
    s = s * 1664525u + 1013904223u; float a = (float)(s >> 8) / 16777216.0f;
    s = s * 1664525u + 1013904223u; float b = (float)(s >> 8) / 16777216.0f;
    s = s * 1664525u + 1013904223u; float c = (float)(s >> 8) / 16777216.0f;
    s = s * 1664525u + 1013904223u; float d = (float)(s >> 8) / 16777216.0f;
    pts[i].x = -0.7f + a * 1.4f; pts[i].y = -0.7f + b * 1.4f; pts[i].z = -0.7f + c * 1.4f;
    flat[3*i+0] = pts[i].x; flat[3*i+1] = pts[i].y; flat[3*i+2] = pts[i].z;
    vals[i] = d * 2.0f - 1.0f;
  }
  size_t nvox = (size_t)N * N * N;
  float* wc = (float*)calloc(nvox, sizeof(float));
  float* wg = (float*)calloc(nvox, sizeof(float));

  tvdb_splat_quadratic_dense(&cpu, pts, vals, NP, wc);
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_splat_quadratic_dense(ctx, &gpu, flat, vals, NP, wg, &err) != TVDB_OK) {
    fprintf(stderr, "gpu quadratic splat failed: %s\n", err.message);
    EXPECT(0);
  } else {
    for (size_t i = 0; i < nvox; ++i) {
      EXPECT_NEAR(gpu.data[i], cpu.data[i], 1e-4f);  // atomic-add order differs
      EXPECT_NEAR(wg[i], wc[i], 1e-4f);
    }
  }
  free(pts); free(flat); free(vals); free(wc); free(wg);
  tvdb_dense_grid_free(&cpu); tvdb_dense_grid_free(&gpu);
}

static void test_points_to_mask(tvdb_gpu_context_t* ctx) {
  const int N = 16;
  tvdb_dense_grid mask;
  tvdb_dense_grid_init(&mask, N, N, N);
  mask.voxel_size = 0.1f; mask.ox = mask.oy = mask.oz = -0.8f;
  size_t nvox = (size_t)N * N * N;

  const size_t NP = 300;
  float* flat = (float*)malloc(NP * 3 * sizeof(float));
  unsigned int s = 777u;
  for (size_t i = 0; i < NP; ++i) {
    s = s * 1664525u + 1013904223u; float a = (float)(s >> 8) / 16777216.0f;
    s = s * 1664525u + 1013904223u; float b = (float)(s >> 8) / 16777216.0f;
    s = s * 1664525u + 1013904223u; float c = (float)(s >> 8) / 16777216.0f;
    flat[3*i+0] = -0.7f + a * 1.4f; flat[3*i+1] = -0.7f + b * 1.4f; flat[3*i+2] = -0.7f + c * 1.4f;
  }
  // CPU reference occupancy.
  float* ref = (float*)calloc(nvox, sizeof(float));
  for (size_t i = 0; i < NP; ++i) {
    int ix = (int)floorf((flat[3*i+0] - mask.ox) / mask.voxel_size);
    int iy = (int)floorf((flat[3*i+1] - mask.oy) / mask.voxel_size);
    int iz = (int)floorf((flat[3*i+2] - mask.oz) / mask.voxel_size);
    if (ix>=0&&ix<N&&iy>=0&&iy<N&&iz>=0&&iz<N) ref[(size_t)(iz*N+iy)*N+ix] = 1.0f;
  }

  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_points_to_mask(ctx, &mask, flat, NP, &err) != TVDB_OK) {
    fprintf(stderr, "gpu points_to_mask failed: %s\n", err.message);
    EXPECT(0);
  } else {
    size_t occ = 0;
    for (size_t i = 0; i < nvox; ++i) { EXPECT(mask.data[i] == ref[i]); if (ref[i] > 0.5f) ++occ; }
    EXPECT(occ > 0);
  }
  free(flat); free(ref);
  tvdb_dense_grid_free(&mask);
}

static int cmp_i64(const void* a, const void* b) {
  long long x = *(const long long*)a, y = *(const long long*)b;
  return (x > y) - (x < y);
}
static void pack_sort(const int32_t* coords, size_t n, long long* keys) {
  for (size_t i = 0; i < n; ++i)
    keys[i] = (((long long)coords[3*i+0] + (1<<20)) << 42) |
              (((long long)coords[3*i+1] + (1<<20)) << 21) |
              ((long long)coords[3*i+2] + (1<<20));
  qsort(keys, n, sizeof(long long), cmp_i64);
}

static void test_voxelize(tvdb_gpu_context_t* ctx) {
  const size_t NP = 300;
  float* flat = (float*)malloc(NP * 3 * sizeof(float));
  unsigned int s = 9001u;
  for (size_t i = 0; i < NP; ++i) {
    s = s * 1664525u + 1013904223u; float a = (float)(s >> 8) / 16777216.0f;
    s = s * 1664525u + 1013904223u; float b = (float)(s >> 8) / 16777216.0f;
    s = s * 1664525u + 1013904223u; float c = (float)(s >> 8) / 16777216.0f;
    flat[3*i+0] = -0.7f + a * 1.4f; flat[3*i+1] = -0.7f + b * 1.4f; flat[3*i+2] = -0.7f + c * 1.4f;
  }
  const float vs[3] = {0.1f, 0.1f, 0.1f};
  const float origin[3] = {-0.8f, -0.8f, -0.8f};

  int32_t* cpu_coords = NULL; size_t cpu_n = 0;
  EXPECT(tvdb_voxelize_points(flat, NP, vs, origin, &cpu_coords, &cpu_n));
  int32_t* gpu_coords = NULL; size_t gpu_n = 0;
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_voxelize_points(ctx, flat, NP, vs, origin, &gpu_coords, &gpu_n, &err) != TVDB_OK) {
    fprintf(stderr, "gpu voxelize_points failed: %s\n", err.message);
    EXPECT(0);
  } else {
    EXPECT(gpu_n == cpu_n);
    EXPECT(gpu_n > 0);
    if (gpu_n == cpu_n && cpu_n > 0) {
      long long* kc = (long long*)malloc(cpu_n * sizeof(long long));
      long long* kg = (long long*)malloc(gpu_n * sizeof(long long));
      pack_sort(cpu_coords, cpu_n, kc);
      pack_sort(gpu_coords, gpu_n, kg);
      for (size_t i = 0; i < cpu_n; ++i) EXPECT(kc[i] == kg[i]);  // same set of voxels
      free(kc); free(kg);
    }
  }
  free(cpu_coords); free(gpu_coords); free(flat);
}

typedef struct { long long key; float val; } kv_t;
static int cmp_kv(const void* a, const void* b) {
  long long x = ((const kv_t*)a)->key, y = ((const kv_t*)b)->key;
  return (x > y) - (x < y);
}
static void build_kv(const tvdb_sparse_grid* g, kv_t* kv) {
  for (size_t i = 0; i < g->count; ++i) {
    kv[i].key = (((long long)g->coords[i].x + (1<<20)) << 42) |
                (((long long)g->coords[i].y + (1<<20)) << 21) |
                ((long long)g->coords[i].z + (1<<20));
    kv[i].val = g->values[i];
  }
  qsort(kv, g->count, sizeof(kv_t), cmp_kv);
}

static void test_sparse_erode(tvdb_gpu_context_t* ctx) {
  // Solid 5x5x5 block; erode (1 iter) keeps the interior 3x3x3 with max-pooled
  // values. Compare GPU vs CPU as sets.
  tvdb_sparse_grid in, cpu, gpu;
  tvdb_sparse_grid_init(&in); tvdb_sparse_grid_init(&cpu); tvdb_sparse_grid_init(&gpu);
  EXPECT(tvdb_sparse_grid_reserve(&in, 125));
  size_t k = 0;
  for (int z = 0; z < 5; ++z) for (int y = 0; y < 5; ++y) for (int x = 0; x < 5; ++x) {
    in.coords[k].x = x; in.coords[k].y = y; in.coords[k].z = z;
    in.values[k] = 0.1f * (float)(x + y + z) - 0.5f; ++k;
  }
  in.count = 125;

  EXPECT(tvdb_erode_sparse(&in, 1, &cpu));
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_erode_sparse(ctx, &in, 1, &gpu, &err) != TVDB_OK) {
    fprintf(stderr, "gpu erode_sparse failed: %s\n", err.message);
    EXPECT(0);
  } else {
    EXPECT(gpu.count == cpu.count);
    EXPECT(cpu.count == 27);  // 3x3x3 interior
    if (gpu.count == cpu.count && cpu.count > 0) {
      kv_t* kc = (kv_t*)malloc(cpu.count * sizeof(kv_t));
      kv_t* kg = (kv_t*)malloc(gpu.count * sizeof(kv_t));
      build_kv(&cpu, kc); build_kv(&gpu, kg);
      for (size_t i = 0; i < cpu.count; ++i) { EXPECT(kc[i].key == kg[i].key); EXPECT_NEAR(kc[i].val, kg[i].val, 1e-6f); }
      free(kc); free(kg);
    }
  }
  tvdb_sparse_grid_free(&in); tvdb_sparse_grid_free(&cpu); tvdb_sparse_grid_free(&gpu);
}

static void test_sparse_dilate(tvdb_gpu_context_t* ctx) {
  // A 3x3x3 block with varied values; dilate 1 iter grows by the 6-neighborhood
  // with min-pooled values (inactive neighbors fall back to background).
  tvdb_sparse_grid in, cpu, gpu;
  tvdb_sparse_grid_init(&in); tvdb_sparse_grid_init(&cpu); tvdb_sparse_grid_init(&gpu);
  EXPECT(tvdb_sparse_grid_reserve(&in, 27));
  size_t k = 0;
  for (int z = 0; z < 3; ++z) for (int y = 0; y < 3; ++y) for (int x = 0; x < 3; ++x) {
    in.coords[k].x = x; in.coords[k].y = y; in.coords[k].z = z;
    in.values[k] = -0.1f * (float)(x + y + z) - 0.2f; ++k;
  }
  in.count = 27;
  const float background = 1.0f;

  EXPECT(tvdb_dilate_sparse(&in, background, 1, &cpu));
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_dilate_sparse(ctx, &in, background, 1, &gpu, &err) != TVDB_OK) {
    fprintf(stderr, "gpu dilate_sparse failed: %s\n", err.message);
    EXPECT(0);
  } else {
    EXPECT(gpu.count == cpu.count);
    EXPECT(cpu.count > 27);  // grew
    if (gpu.count == cpu.count && cpu.count > 0) {
      kv_t* kc = (kv_t*)malloc(cpu.count * sizeof(kv_t));
      kv_t* kg = (kv_t*)malloc(gpu.count * sizeof(kv_t));
      build_kv(&cpu, kc); build_kv(&gpu, kg);
      for (size_t i = 0; i < cpu.count; ++i) { EXPECT(kc[i].key == kg[i].key); EXPECT_NEAR(kc[i].val, kg[i].val, 1e-6f); }
      free(kc); free(kg);
    }
  }
  tvdb_sparse_grid_free(&in); tvdb_sparse_grid_free(&cpu); tvdb_sparse_grid_free(&gpu);
}

static void test_merge(tvdb_gpu_context_t* ctx) {
  // Two sphere SDFs at different centres -> different grid origins; merge covers
  // the union AABB with SDF-union (min) semantics.
  tvdb_dense_grid a, b, cpu, gpu;
  memset(&a, 0, sizeof(a)); memset(&b, 0, sizeof(b)); memset(&cpu, 0, sizeof(cpu)); memset(&gpu, 0, sizeof(gpu));
  const float ca[3] = {0.0f, 0.0f, 0.0f}, cb[3] = {0.8f, 0.1f, -0.1f};
  EXPECT(tvdb_level_set_sphere(0.5f, ca, 0.1f, 3.0f, &a));
  EXPECT(tvdb_level_set_sphere(0.5f, cb, 0.1f, 3.0f, &b));
  const float bg = 3.0f;
  EXPECT(tvdb_merge_grids(&a, &b, bg, &cpu, NULL));
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_merge_grids(ctx, &a, &b, bg, &gpu, &err) != TVDB_OK) {
    fprintf(stderr, "gpu merge_grids failed: %s\n", err.message);
    EXPECT(0);
  } else {
    EXPECT(gpu.nx == cpu.nx && gpu.ny == cpu.ny && gpu.nz == cpu.nz);
    EXPECT_NEAR(gpu.ox, cpu.ox, 1e-6f); EXPECT_NEAR(gpu.oy, cpu.oy, 1e-6f); EXPECT_NEAR(gpu.oz, cpu.oz, 1e-6f);
    if (gpu.nx == cpu.nx && gpu.ny == cpu.ny && gpu.nz == cpu.nz) {
      size_t n = (size_t)cpu.nx * cpu.ny * cpu.nz;
      for (size_t i = 0; i < n; ++i) EXPECT_NEAR(gpu.data[i], cpu.data[i], 1e-6f);
    }
  }
  tvdb_dense_grid_free(&a); tvdb_dense_grid_free(&b);
  tvdb_dense_grid_free(&cpu); tvdb_dense_grid_free(&gpu);
}

static void test_active_coords(tvdb_gpu_context_t* ctx) {
  // Sphere SDF: exterior clamps to +0.3. Extract voxels != 0.3 -> band/interior.
  tvdb_dense_grid g;
  make_sphere(&g);
  tvdb_sparse_grid cpu, gpu;
  tvdb_sparse_grid_init(&cpu); tvdb_sparse_grid_init(&gpu);
  EXPECT(tvdb_active_grid_coords(&g, 0.3f, &cpu));
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_active_grid_coords(ctx, &g, 0.3f, 0.0f, &gpu, &err) != TVDB_OK) {
    fprintf(stderr, "gpu active_grid_coords failed: %s\n", err.message);
    EXPECT(0);
  } else {
    EXPECT(gpu.count == cpu.count);
    EXPECT(cpu.count > 0 && cpu.count < (size_t)g.nx * g.ny * g.nz);
    if (gpu.count == cpu.count && cpu.count > 0) {
      kv_t* kc = (kv_t*)malloc(cpu.count * sizeof(kv_t));
      kv_t* kg = (kv_t*)malloc(gpu.count * sizeof(kv_t));
      build_kv(&cpu, kc); build_kv(&gpu, kg);
      for (size_t i = 0; i < cpu.count; ++i) { EXPECT(kc[i].key == kg[i].key); EXPECT_NEAR(kc[i].val, kg[i].val, 1e-6f); }
      free(kc); free(kg);
    }
  }
  tvdb_dense_grid_free(&g);
  tvdb_sparse_grid_free(&cpu); tvdb_sparse_grid_free(&gpu);
}

static void test_checksum(tvdb_gpu_context_t* ctx) {
  tvdb_dense_grid g;
  make_sphere(&g);
  size_t n = (size_t)g.nx * g.ny * g.nz;
  // CPU reference: the same order-independent additive mix (commutative, so the
  // total is partition-independent).
  uint32_t cpu = 0;
  for (size_t i = 0; i < n; ++i) {
    uint32_t bits; memcpy(&bits, &g.data[i], sizeof(uint32_t));
    uint32_t h = bits ^ ((uint32_t)i * 2654435761u);
    h *= 2654435761u; h ^= h >> 15; cpu += h;
  }
  uint32_t gpu = 0;
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_grid_checksum(ctx, &g, &gpu, &err) != TVDB_OK) {
    fprintf(stderr, "gpu grid_checksum failed: %s\n", err.message);
    EXPECT(0);
  } else {
    EXPECT(gpu == cpu);
    EXPECT(gpu != 0u);
  }
  tvdb_dense_grid_free(&g);
}

static void test_mesh_to_sdf(tvdb_gpu_context_t* ctx) {
  // A unit tetrahedron.
  // Irregular tetrahedron (asymmetric, to avoid the many exact equidistant
  // ties a symmetric mesh produces, which make the nearest-normal sign FP-fragile).
  tvdb_vec3f verts[4] = {{0.03f,0.02f,-0.01f},{1.13f,0.07f,0.04f},{0.11f,0.91f,0.13f},{-0.06f,0.15f,1.07f}};
  tvdb_triangle faces[4] = {{0,1,2},{0,2,3},{0,3,1},{1,3,2}};
  tvdb_triangle_mesh mesh;
  memset(&mesh, 0, sizeof(mesh));
  mesh.vertices = verts; mesh.vertex_count = 4;
  mesh.faces = faces; mesh.face_count = 4;

  tvdb_dense_grid cpu, gpu;
  memset(&cpu, 0, sizeof(cpu)); memset(&gpu, 0, sizeof(gpu));
  EXPECT(tvdb_mesh_to_sdf(&mesh, 0.2f, 0.3f, &cpu, NULL));
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_mesh_to_sdf(ctx, &mesh, 0.2f, 0.3f, &gpu, &err) != TVDB_OK) {
    fprintf(stderr, "gpu mesh_to_sdf failed: %s\n", err.message);
    EXPECT(0);
  } else {
    EXPECT(gpu.nx == cpu.nx && gpu.ny == cpu.ny && gpu.nz == cpu.nz);
    EXPECT_NEAR(gpu.ox, cpu.ox, 1e-6f); EXPECT_NEAR(gpu.oy, cpu.oy, 1e-6f); EXPECT_NEAR(gpu.oz, cpu.oz, 1e-6f);
    if (gpu.nx == cpu.nx && gpu.ny == cpu.ny && gpu.nz == cpu.nz) {
      // The (unsigned) distance field is the substantive computation and is
      // deterministic, so |value| matches exactly. The closest-triangle-normal
      // sign is only well-defined near the surface and is FP-fragile at voxels
      // (near-)equidistant to multiple triangles, so allow a small fraction of
      // sign flips while requiring the magnitudes to match.
      size_t n = (size_t)cpu.nx * cpu.ny * cpu.nz, neg = 0, sign_flips = 0;
      for (size_t i = 0; i < n; ++i) {
        EXPECT_NEAR(fabsf(gpu.data[i]), fabsf(cpu.data[i]), 2e-5f);
        if ((gpu.data[i] < 0) != (cpu.data[i] < 0)) ++sign_flips;
        if (cpu.data[i] < 0) ++neg;
      }
      EXPECT(neg > 0);                 // some interior voxels
      EXPECT(sign_flips * 10 <= n);    // < 10% sign disagreement (far-field ties)
    }
  }
  tvdb_dense_grid_free(&cpu); tvdb_dense_grid_free(&gpu);
}

static void test_marching_cubes(tvdb_gpu_context_t* ctx) {
  tvdb_dense_grid g;
  make_sphere(&g);
  tvdb_triangle_mesh mesh;
  memset(&mesh, 0, sizeof(mesh));
  EXPECT(tvdb_sdf_to_mesh(&g, 0.0f, &mesh, NULL));
  float* verts = NULL; size_t tcount = 0;
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_marching_cubes(ctx, &g, 0.0f, &verts, &tcount, &err) != TVDB_OK) {
    fprintf(stderr, "gpu marching_cubes failed: %s\n", err.message);
    EXPECT(0);
  } else {
    EXPECT(tcount == mesh.face_count);
    EXPECT(tcount > 0);
    if (tcount == mesh.face_count) {
      // Same cell/table order -> triangle T's vertex positions must match.
      for (size_t t = 0; t < tcount; ++t) {
        tvdb_triangle f = mesh.faces[t];
        tvdb_vec3f cv[3] = { mesh.vertices[f.v0], mesh.vertices[f.v1], mesh.vertices[f.v2] };
        for (int k = 0; k < 3; ++k) {
          EXPECT_NEAR(verts[t*9 + k*3 + 0], cv[k].x, 1e-5f);
          EXPECT_NEAR(verts[t*9 + k*3 + 1], cv[k].y, 1e-5f);
          EXPECT_NEAR(verts[t*9 + k*3 + 2], cv[k].z, 1e-5f);
        }
      }
    }
  }
  free(verts);
  free(mesh.vertices); free(mesh.faces);
  tvdb_dense_grid_free(&g);
}

static void test_sparse_conv_strided(tvdb_gpu_context_t* ctx) {
  // 4x4x4 block; 3x3x3 kernel; stride 2 -> 2x2x2 output coords (floor(c/2)).
  tvdb_sparse_grid in, gpu;
  tvdb_sparse_grid_init(&in); tvdb_sparse_grid_init(&gpu);
  EXPECT(tvdb_sparse_grid_reserve(&in, 64));
  size_t k = 0;
  for (int z = 0; z < 4; ++z) for (int y = 0; y < 4; ++y) for (int x = 0; x < 4; ++x) {
    in.coords[k].x = x; in.coords[k].y = y; in.coords[k].z = z;
    in.values[k] = 0.1f * (float)(x*16 + y*4 + z) - 1.0f; ++k;
  }
  in.count = 64;
  float kernel[27];
  for (int i = 0; i < 27; ++i) kernel[i] = (float)(i % 5) * 0.05f - 0.08f;
  const int stride = 2; const float pad = 0.5f;

  // CPU reference: output coords = unique floor(c/2); value = conv at oc*2.
  int ocoord[8][3]; float oval[8]; size_t no = 0;
  for (int oz = 0; oz < 2; ++oz) for (int oy = 0; oy < 2; ++oy) for (int ox = 0; ox < 2; ++ox) {
    float acc = 0.0f;
    for (int dk = 0; dk < 3; ++dk) for (int dj = 0; dj < 3; ++dj) for (int di = 0; di < 3; ++di) {
      int qx = ox*stride + di-1, qy = oy*stride + dj-1, qz = oz*stride + dk-1;
      float v = pad;
      for (size_t i = 0; i < 64; ++i) if (in.coords[i].x==qx && in.coords[i].y==qy && in.coords[i].z==qz) { v = in.values[i]; break; }
      acc += kernel[(dk*3+dj)*3+di] * v;
    }
    ocoord[no][0]=ox; ocoord[no][1]=oy; ocoord[no][2]=oz; oval[no]=acc; ++no;
  }

  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_sparse_conv3d_strided(ctx, &in, kernel, 3, 3, 3, stride, pad, &gpu, &err) != TVDB_OK) {
    fprintf(stderr, "gpu sparse_conv_strided failed: %s\n", err.message);
    EXPECT(0);
  } else {
    EXPECT(gpu.count == no);
    if (gpu.count == no) {
      kv_t* kc = (kv_t*)malloc(no * sizeof(kv_t));
      kv_t* kg = (kv_t*)malloc(no * sizeof(kv_t));
      for (size_t i = 0; i < no; ++i) {
        kc[i].key = (((long long)ocoord[i][0]+(1<<20))<<42)|(((long long)ocoord[i][1]+(1<<20))<<21)|((long long)ocoord[i][2]+(1<<20));
        kc[i].val = oval[i];
      }
      qsort(kc, no, sizeof(kv_t), cmp_kv);
      build_kv(&gpu, kg);
      for (size_t i = 0; i < no; ++i) { EXPECT(kc[i].key == kg[i].key); EXPECT_NEAR(kc[i].val, kg[i].val, 2e-5f); }
      free(kc); free(kg);
    }
  }
  tvdb_sparse_grid_free(&in); tvdb_sparse_grid_free(&gpu);
}

static void test_conv_transpose(tvdb_gpu_context_t* ctx) {
  // 2x2x2 input; 3x3x3 kernel; stride 2 (upsampling adjoint).
  tvdb_sparse_grid in, gpu;
  tvdb_sparse_grid_init(&in); tvdb_sparse_grid_init(&gpu);
  EXPECT(tvdb_sparse_grid_reserve(&in, 8));
  size_t k = 0;
  for (int z = 0; z < 2; ++z) for (int y = 0; y < 2; ++y) for (int x = 0; x < 2; ++x) {
    in.coords[k].x = x; in.coords[k].y = y; in.coords[k].z = z;
    in.values[k] = 0.2f * (float)(x*4 + y*2 + z) + 0.1f; ++k;
  }
  in.count = 8;
  float kernel[27];
  for (int i = 0; i < 27; ++i) kernel[i] = (float)(i % 4) * 0.1f - 0.1f;
  const int stride = 2;

  // CPU reference: scatter-accumulate into a dense bbox accumulator.
  const int BM = -1, D = 5;  // bbmin=-1, dims=5 per axis
  float acc[125]; char occ[125];
  memset(acc, 0, sizeof(acc)); memset(occ, 0, sizeof(occ));
  for (size_t i = 0; i < 8; ++i) {
    int cx = in.coords[i].x*stride, cy = in.coords[i].y*stride, cz = in.coords[i].z*stride;
    float v = in.values[i];
    for (int dk = 0; dk < 3; ++dk) for (int dj = 0; dj < 3; ++dj) for (int di = 0; di < 3; ++di) {
      int ox = cx+di-1-BM, oy = cy+dj-1-BM, oz = cz+dk-1-BM;
      int lin = (oz*D+oy)*D+ox; acc[lin] += kernel[(dk*3+dj)*3+di]*v; occ[lin] = 1;
    }
  }
  size_t no = 0; for (int i = 0; i < 125; ++i) if (occ[i]) ++no;

  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  if (tvdb_gpu_sparse_conv3d_transpose(ctx, &in, kernel, 3, 3, 3, stride, &gpu, &err) != TVDB_OK) {
    fprintf(stderr, "gpu conv_transpose failed: %s\n", err.message);
    EXPECT(0);
  } else {
    EXPECT(gpu.count == no);
    if (gpu.count == no) {
      kv_t* kc = (kv_t*)malloc(no * sizeof(kv_t));
      kv_t* kg = (kv_t*)malloc(no * sizeof(kv_t));
      size_t w = 0;
      for (int lin = 0; lin < 125; ++lin) if (occ[lin]) {
        int oz = lin/(D*D), rem = lin-oz*D*D, oy = rem/D, ox = rem-oy*D;
        int cx = ox+BM, cy = oy+BM, cz = oz+BM;
        kc[w].key = (((long long)cx+(1<<20))<<42)|(((long long)cy+(1<<20))<<21)|((long long)cz+(1<<20));
        kc[w].val = acc[lin]; ++w;
      }
      qsort(kc, no, sizeof(kv_t), cmp_kv);
      build_kv(&gpu, kg);
      for (size_t i = 0; i < no; ++i) { EXPECT(kc[i].key == kg[i].key); EXPECT_NEAR(kc[i].val, kg[i].val, 2e-5f); }
      free(kc); free(kg);
    }
  }
  tvdb_sparse_grid_free(&in); tvdb_sparse_grid_free(&gpu);
}

static void test_buffer_interop(tvdb_gpu_context_t* ctx) {
  // Device-resident buffer: upload -> download round-trip + native handle.
  const size_t N = 256;
  float src[256], dst[256];
  for (size_t i = 0; i < N; ++i) { src[i] = 0.137f * (float)i - 3.0f; dst[i] = 0.0f; }
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  tvdb_gpu_buffer_t* buf = NULL;
  if (tvdb_gpu_buffer_create(ctx, N * sizeof(float), &buf, &err) != TVDB_OK) {
    fprintf(stderr, "buffer_create failed: %s\n", err.message);
    EXPECT(0); return;
  }
  EXPECT(tvdb_gpu_buffer_size(buf) == N * sizeof(float));
  EXPECT(tvdb_gpu_buffer_native_handle(buf) != 0);
  EXPECT(tvdb_gpu_buffer_upload(buf, src, N * sizeof(float), &err) == TVDB_OK);
  EXPECT(tvdb_gpu_buffer_download(buf, dst, N * sizeof(float), &err) == TVDB_OK);
  for (size_t i = 0; i < N; ++i) EXPECT(dst[i] == src[i]);  // bit-exact device round-trip
  tvdb_gpu_buffer_destroy(buf);
}

static void test_gaussian_forward(tvdb_gpu_context_t* ctx) {
  tvdb_projected_gaussian_t gs[4] = {
    { 4.0f, 4.0f, 0.20f, 0.02f, 0.18f, 0.85f, 1.0f, 6.0f, {1.0f, 0.2f, 0.1f} },
    { 8.0f, 6.0f, 0.30f,-0.05f, 0.25f, 0.75f, 1.5f, 5.0f, {0.1f, 0.9f, 0.2f} },
    {10.0f,10.0f, 0.15f, 0.00f, 0.15f, 0.65f, 2.0f, 7.0f, {0.2f, 0.3f, 0.95f} },
    { 6.0f,11.0f, 0.40f, 0.10f, 0.30f, 0.55f, 2.5f, 4.0f, {0.5f, 0.5f, 0.5f} },
  };
  const uint32_t W = 16, H = 16, F = 3;
  float bg[3] = {0.0f, 0.0f, 0.0f};
  tvdb_raster_output_t cpu, gpu;
  tvdb_error_t cerr, err;
  memset(&cerr, 0, sizeof(cerr)); memset(&err, 0, sizeof(err));
  EXPECT(tvdb_gaussian_rasterize_forward(gs, 4, W, H, F, bg, 0.005f, &cpu, &cerr) == TVDB_OK);
  if (tvdb_gpu_gaussian_rasterize_forward(ctx, gs, 4, W, H, F, bg, 0.005f, &gpu, &err) != TVDB_OK) {
    fprintf(stderr, "gpu gaussian forward failed: %s\n", err.message);
    EXPECT(0);
  } else {
    EXPECT(gpu.width == cpu.width && gpu.height == cpu.height && gpu.num_features == cpu.num_features);
    size_t npix = (size_t)W * H, nonzero = 0;
    for (size_t i = 0; i < npix * F; ++i) EXPECT_NEAR(gpu.image[i], cpu.image[i], 2e-5f);
    for (size_t p = 0; p < npix; ++p) {
      EXPECT_NEAR(gpu.alpha[p], cpu.alpha[p], 2e-5f);
      if (cpu.alpha[p] > 0.0f) { EXPECT(gpu.last_ids[p] == cpu.last_ids[p]); ++nonzero; }
    }
    EXPECT(nonzero > 0);  // gaussians actually rendered
  }
  tvdb_raster_output_destroy(&cpu); tvdb_raster_output_destroy(&gpu);
}

static void test_gaussian_backward_gpu(tvdb_gpu_context_t* ctx) {
  tvdb_projected_gaussian_t gs[4] = {
    { 4.0f, 4.0f, 0.20f, 0.02f, 0.18f, 0.85f, 1.0f, 6.0f, {1.0f, 0.2f, 0.1f} },
    { 8.0f, 6.0f, 0.30f,-0.05f, 0.25f, 0.75f, 1.5f, 5.0f, {0.1f, 0.9f, 0.2f} },
    {10.0f,10.0f, 0.15f, 0.00f, 0.15f, 0.65f, 2.0f, 7.0f, {0.2f, 0.3f, 0.95f} },
    { 6.0f,11.0f, 0.40f, 0.10f, 0.30f, 0.55f, 2.5f, 4.0f, {0.5f, 0.5f, 0.5f} },
  };
  const uint32_t W = 16, H = 16, F = 3, N = 4;
  float bg[3] = {0.0f, 0.0f, 0.0f};
  tvdb_raster_output_t fwd;
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  EXPECT(tvdb_gaussian_rasterize_forward(gs, N, W, H, F, bg, 0.005f, &fwd, &err) == TVDB_OK);
  // Loss L = Σ||C||² + ΣA²  ->  dL/dC = 2C, dL/dA = 2A.
  size_t npix = (size_t)W * H;
  float* dC = (float*)malloc(npix * F * sizeof(float));
  float* dA = (float*)malloc(npix * sizeof(float));
  for (size_t i = 0; i < npix * F; ++i) dC[i] = 2.0f * fwd.image[i];
  for (size_t p = 0; p < npix; ++p) dA[p] = 2.0f * fwd.alpha[p];

  tvdb_gaussian_grad_t gc, gg;
  EXPECT(tvdb_gaussian_grad_init(&gc, N, F) == TVDB_OK);
  EXPECT(tvdb_gaussian_grad_init(&gg, N, F) == TVDB_OK);
  EXPECT(tvdb_gaussian_rasterize_backward(gs, N, &fwd, dC, dA, bg, 0.005f, &gc, &err) == TVDB_OK);
  if (tvdb_gpu_gaussian_rasterize_backward(ctx, gs, N, &fwd, dC, dA, bg, 0.005f, &gg, &err) != TVDB_OK) {
    fprintf(stderr, "gpu gaussian backward failed: %s\n", err.message);
    EXPECT(0);
  } else {
    #define GCMP(a, b) EXPECT_NEAR((a), (b), fabsf(b) * 2e-3f + 2e-4f)
    for (uint32_t i = 0; i < N; ++i) {
      GCMP(gg.grad_x[i], gc.grad_x[i]); GCMP(gg.grad_y[i], gc.grad_y[i]);
      GCMP(gg.grad_conic_a[i], gc.grad_conic_a[i]); GCMP(gg.grad_conic_b[i], gc.grad_conic_b[i]); GCMP(gg.grad_conic_c[i], gc.grad_conic_c[i]);
      GCMP(gg.grad_opacity[i], gc.grad_opacity[i]);
      for (uint32_t f = 0; f < F; ++f) GCMP(gg.grad_feature[i*F+f], gc.grad_feature[i*F+f]);
    }
    #undef GCMP
  }
  tvdb_gaussian_grad_destroy(&gc); tvdb_gaussian_grad_destroy(&gg);
  tvdb_raster_output_destroy(&fwd);
  free(dC); free(dA);
}

static float ref_ssim_mean(const float* a, const float* b, int W, int H, int C, float dr) {
  const int R = 5, wn = 11; float win[121], sum = 0.0f, sigma = 1.5f;
  for (int dy=-R; dy<=R; ++dy) for (int dx=-R; dx<=R; ++dx) { float v = expf(-(float)(dx*dx+dy*dy)/(2.0f*sigma*sigma)); win[(dy+R)*wn+(dx+R)]=v; sum+=v; }
  for (int i=0;i<121;++i) win[i]/=sum;
  float c1=(0.01f*dr)*(0.01f*dr), c2=(0.03f*dr)*(0.03f*dr);
  double acc = 0.0;
  for (int py=0; py<H; ++py) for (int px=0; px<W; ++px) {
    float ssim_sum = 0.0f;
    for (int c=0;c<C;++c){ float ma=0,mb=0,maa=0,mbb=0,mab=0;
      for (int dy=-R;dy<=R;++dy) for (int dx=-R;dx<=R;++dx){
        int qx=px+dx; if(qx<0)qx=0; if(qx>=W)qx=W-1; int qy=py+dy; if(qy<0)qy=0; if(qy>=H)qy=H-1;
        float wgt=win[(dy+R)*wn+(dx+R)]; float va=a[(qy*W+qx)*C+c], vb=b[(qy*W+qx)*C+c];
        ma+=wgt*va; mb+=wgt*vb; maa+=wgt*va*va; mbb+=wgt*vb*vb; mab+=wgt*va*vb;
      }
      float va2=maa-ma*ma, vb2=mbb-mb*mb, vab=mab-ma*mb;
      ssim_sum += ((2.0f*ma*mb+c1)*(2.0f*vab+c2))/((ma*ma+mb*mb+c1)*(va2+vb2+c2));
    }
    acc += ssim_sum/(float)C;
  }
  return (float)(acc/((double)W*H));
}

static void test_ssim(tvdb_gpu_context_t* ctx) {
  const int W = 16, H = 16, C = 3;
  float* a = (float*)malloc((size_t)W*H*C*sizeof(float));
  float* b = (float*)malloc((size_t)W*H*C*sizeof(float));
  unsigned int s = 4242u;
  for (int i = 0; i < W*H*C; ++i) {
    s = s*1664525u + 1013904223u; float r = (float)(s>>8)/16777216.0f;
    a[i] = r; b[i] = r*0.8f + 0.1f;  // a degraded copy
  }
  tvdb_error_t err; memset(&err, 0, sizeof(err));
  float gpu_mean = 0.0f, self = 0.0f;
  if (tvdb_gpu_ssim(ctx, a, b, W, H, C, 1.0f, &gpu_mean, NULL, &err) != TVDB_OK) {
    fprintf(stderr, "gpu ssim failed: %s\n", err.message); EXPECT(0);
  } else {
    float cpu_mean = ref_ssim_mean(a, b, W, H, C, 1.0f);
    EXPECT_NEAR(gpu_mean, cpu_mean, 2e-5f);
    EXPECT(gpu_mean > 0.0f && gpu_mean < 1.0f);  // degraded -> SSIM in (0,1)
    EXPECT(tvdb_gpu_ssim(ctx, a, a, W, H, C, 1.0f, &self, NULL, &err) == TVDB_OK);
    EXPECT_NEAR(self, 1.0f, 1e-4f);  // identical images -> SSIM 1
  }
  free(a); free(b);
}

static void fill_block(tvdb_sparse_grid* g, int n, float bias) {
  tvdb_sparse_grid_init(g);
  tvdb_sparse_grid_reserve(g, (size_t)n*n*n);
  size_t k = 0;
  for (int z = 0; z < n; ++z) for (int y = 0; y < n; ++y) for (int x = 0; x < n; ++x) {
    g->coords[k].x = x; g->coords[k].y = y; g->coords[k].z = z;
    g->values[k] = 0.1f*(float)(x+2*y+3*z) + bias; ++k;
  }
  g->count = (size_t)n*n*n;
}

static void test_batched_conv(tvdb_gpu_context_t* ctx) {
  // A GridBatch of 3 different-sized grids; one batched dispatch must equal
  // running the same-topology conv on each grid individually.
  tvdb_sparse_grid in[3], out[3], ref;
  fill_block(&in[0], 2, -0.5f); fill_block(&in[1], 3, 0.2f); fill_block(&in[2], 1, 1.0f);
  for (int g = 0; g < 3; ++g) tvdb_sparse_grid_init(&out[g]);
  tvdb_sparse_grid_init(&ref);
  float kernel[27];
  for (int i = 0; i < 27; ++i) kernel[i] = (float)(i % 5) * 0.05f - 0.08f;
  const float pad = 0.25f;

  tvdb_error_t err; memset(&err, 0, sizeof(err));
  if (tvdb_gpu_sparse_conv3d_batched(ctx, in, 3, kernel, 3, 3, 3, pad, out, &err) != TVDB_OK) {
    fprintf(stderr, "gpu batched conv failed: %s\n", err.message); EXPECT(0);
  } else {
    for (int g = 0; g < 3; ++g) {
      EXPECT(tvdb_sparse_conv3d(&in[g], kernel, 3, 3, 3, pad, &ref));
      EXPECT(out[g].count == ref.count);
      for (size_t i = 0; i < ref.count && out[g].count == ref.count; ++i) {
        EXPECT(out[g].coords[i].x == ref.coords[i].x && out[g].coords[i].y == ref.coords[i].y && out[g].coords[i].z == ref.coords[i].z);
        EXPECT_NEAR(out[g].values[i], ref.values[i], 2e-5f);
      }
    }
  }
  for (int g = 0; g < 3; ++g) { tvdb_sparse_grid_free(&in[g]); tvdb_sparse_grid_free(&out[g]); }
  tvdb_sparse_grid_free(&ref);
}

// Drive the batched GPU conv through the GridBatch container: build a batch from
// N grids, feed its read-only views to the batched op, and check the result
// equals per-grid CPU conv. Also validate the JaggedTensor value bridge.
static void test_grid_batch_gpu(tvdb_gpu_context_t* ctx) {
  tvdb_sparse_grid in[3], out[3], ref;
  fill_block(&in[0], 2, -0.3f); fill_block(&in[1], 3, 0.4f); fill_block(&in[2], 2, 0.9f);
  for (int g = 0; g < 3; ++g) tvdb_sparse_grid_init(&out[g]);
  tvdb_sparse_grid_init(&ref);
  float kernel[27];
  for (int i = 0; i < 27; ++i) kernel[i] = (float)(i % 6) * 0.04f - 0.07f;
  const float pad = 0.15f;

  tvdb_grid_batch_t gb;
  EXPECT(tvdb_grid_batch_from_grids(&gb, in, 3));
  EXPECT(tvdb_grid_batch_size(&gb) == 3);
  // JaggedTensor bridge over the batch values must match each grid's values.
  tvdb_jagged_t vj;
  EXPECT(tvdb_grid_batch_values_jagged(&gb, &vj));
  EXPECT(tvdb_jagged_total(&vj) == (int64_t)(in[0].count + in[1].count + in[2].count));
  for (int g = 0; g < 3; ++g) {
    int64_t s = 0; float* gv = tvdb_jagged_list_ptr(&vj, g, &s);
    EXPECT(s == (int64_t)in[g].count);
    for (size_t i = 0; i < in[g].count; ++i) EXPECT_NEAR(gv[i], in[g].values[i], 0.0f);
  }
  tvdb_jagged_free(&vj);

  // Feed the batch's read-only views to the batched GPU op.
  tvdb_sparse_grid views[3];
  EXPECT(tvdb_grid_batch_views(&gb, views));
  tvdb_error_t err; memset(&err, 0, sizeof(err));
  if (tvdb_gpu_sparse_conv3d_batched(ctx, views, 3, kernel, 3, 3, 3, pad, out, &err) != TVDB_OK) {
    fprintf(stderr, "grid-batch gpu conv failed: %s\n", err.message); EXPECT(0);
  } else {
    for (int g = 0; g < 3; ++g) {
      EXPECT(tvdb_sparse_conv3d(&in[g], kernel, 3, 3, 3, pad, &ref));
      EXPECT(out[g].count == ref.count);
      for (size_t i = 0; i < ref.count && out[g].count == ref.count; ++i)
        EXPECT_NEAR(out[g].values[i], ref.values[i], 2e-5f);
    }
  }
  tvdb_grid_batch_free(&gb);  // frees batch storage; views must not be freed
  for (int g = 0; g < 3; ++g) { tvdb_sparse_grid_free(&in[g]); tvdb_sparse_grid_free(&out[g]); }
  tvdb_sparse_grid_free(&ref);
}

static void test_multi_gpu(tvdb_gpu_context_t* ctx) {
  // Partition a 4-grid batch across multiple GPU contexts. If the other backend
  // is available we use two distinct contexts (a real multi-device-style split);
  // otherwise the same context twice. Either way the merged result must equal
  // the single-context batched conv.
  tvdb_sparse_grid in[4], single[4], multi[4];
  fill_block(&in[0], 2, -0.4f); fill_block(&in[1], 3, 0.1f); fill_block(&in[2], 2, 0.7f); fill_block(&in[3], 1, -0.2f);
  for (int g = 0; g < 4; ++g) { tvdb_sparse_grid_init(&single[g]); tvdb_sparse_grid_init(&multi[g]); }
  float kernel[27];
  for (int i = 0; i < 27; ++i) kernel[i] = (float)(i % 6) * 0.04f - 0.1f;
  const float pad = 0.3f;

  tvdb_error_t err; memset(&err, 0, sizeof(err));
  EXPECT(tvdb_gpu_sparse_conv3d_batched(ctx, in, 4, kernel, 3, 3, 3, pad, single, &err) == TVDB_OK);

  // Try a second, distinct context on the other backend.
  tvdb_gpu_context_info_t info; memset(&info, 0, sizeof(info));
  tvdb_gpu_context_info(ctx, &info, &err);
  tvdb_gpu_backend_t other = (info.backend == TVDB_GPU_BACKEND_CUDA) ? TVDB_GPU_BACKEND_VULKAN : TVDB_GPU_BACKEND_CUDA;
  tvdb_gpu_context_t* ctx2 = NULL;
  tvdb_error_t e2; memset(&e2, 0, sizeof(e2));
  int two = (tvdb_gpu_context_create(other, 0, &ctx2, &e2) == TVDB_OK);
  tvdb_gpu_context_t* ctxs[2] = { ctx, two ? ctx2 : ctx };

  if (tvdb_gpu_multi_sparse_conv3d_batched(ctxs, 2, in, 4, kernel, 3, 3, 3, pad, multi, &err) != TVDB_OK) {
    fprintf(stderr, "gpu multi batched conv failed: %s\n", err.message); EXPECT(0);
  } else {
    for (int g = 0; g < 4; ++g) {
      EXPECT(multi[g].count == single[g].count);
      for (size_t i = 0; i < single[g].count && multi[g].count == single[g].count; ++i)
        EXPECT_NEAR(multi[g].values[i], single[g].values[i], 2e-5f);
    }
  }
  if (two) tvdb_gpu_context_destroy(ctx2);
  for (int g = 0; g < 4; ++g) { tvdb_sparse_grid_free(&in[g]); tvdb_sparse_grid_free(&single[g]); tvdb_sparse_grid_free(&multi[g]); }
}

// Cross-API external-memory interop: fill a Vulkan exportable buffer, export its
// memory as an opaque fd, import into CUDA, and read it back. Needs a Vulkan
// exporter and a CUDA importer on the same GPU; skips gracefully otherwise.
static void test_external_memory_interop(void) {
  tvdb_error_t verr, cerr, err;
  memset(&verr, 0, sizeof(verr)); memset(&cerr, 0, sizeof(cerr)); memset(&err, 0, sizeof(err));
  tvdb_gpu_context_t* vk = NULL;
  tvdb_gpu_context_t* cu = NULL;
  if (tvdb_gpu_context_create(TVDB_GPU_BACKEND_VULKAN, 0, &vk, &verr) != TVDB_OK) {
    printf("external-memory: SKIP (no Vulkan exporter)\n"); return;
  }
  if (tvdb_gpu_context_create(TVDB_GPU_BACKEND_CUDA, 0, &cu, &cerr) != TVDB_OK) {
    printf("external-memory: SKIP (no CUDA importer)\n"); tvdb_gpu_context_destroy(vk); return;
  }
  if (!tvdb_gpu_context_supports_external_memory(vk) || !tvdb_gpu_context_supports_external_memory(cu)) {
    printf("external-memory: SKIP (unsupported: vk=%d cu=%d)\n",
           tvdb_gpu_context_supports_external_memory(vk), tvdb_gpu_context_supports_external_memory(cu));
    tvdb_gpu_context_destroy(cu); tvdb_gpu_context_destroy(vk); return;
  }

  const size_t N = 1024;  // 4 KiB, far under the VRAM budget
  float src[1024], dst[1024];
  for (size_t i = 0; i < N; ++i) { src[i] = 0.091f * (float)i - 7.5f; dst[i] = 0.0f; }

  tvdb_gpu_buffer_t* xbuf = NULL;
  if (tvdb_gpu_buffer_create_exportable(vk, N * sizeof(float), &xbuf, &err) != TVDB_OK) {
    fprintf(stderr, "buffer_create_exportable failed: %s\n", err.message); EXPECT(0);
    tvdb_gpu_context_destroy(cu); tvdb_gpu_context_destroy(vk); return;
  }
  EXPECT(tvdb_gpu_buffer_upload(xbuf, src, N * sizeof(float), &err) == TVDB_OK);

  uint64_t handle = 0;
  if (tvdb_gpu_buffer_export(xbuf, &handle, &err) != TVDB_OK) {
    fprintf(stderr, "buffer_export failed: %s\n", err.message); EXPECT(0);
  }

  tvdb_gpu_buffer_t* ibuf = NULL;
  if (tvdb_gpu_buffer_import(cu, handle, N * sizeof(float), &ibuf, &err) != TVDB_OK) {
    fprintf(stderr, "buffer_import failed: %s\n", err.message); EXPECT(0);
  } else {
    // The CUDA buffer aliases the Vulkan memory; read it back through CUDA.
    EXPECT(tvdb_gpu_buffer_download(ibuf, dst, N * sizeof(float), &err) == TVDB_OK);
    for (size_t i = 0; i < N; ++i) EXPECT(dst[i] == src[i]);  // bit-exact cross-API share
    printf("external-memory: OK (Vulkan->CUDA shared %zu bytes)\n", N * sizeof(float));
    tvdb_gpu_buffer_destroy(ibuf);
  }
  tvdb_gpu_buffer_destroy(xbuf);
  tvdb_gpu_context_destroy(cu);
  tvdb_gpu_context_destroy(vk);
}

static int run_backend(tvdb_gpu_backend_t backend, const char* label, int required) {
  tvdb_error_t err;
  memset(&err, 0, sizeof(err));
  tvdb_gpu_context_t* ctx = NULL;
  tvdb_status_t st = tvdb_gpu_context_create(backend, 0, &ctx, &err);
  if (st != TVDB_OK) {
    printf("%s: unavailable: %s\n", label, err.message);
    if (required) ++g_failures;
    return 0;
  }
  tvdb_gpu_context_info_t info;
  memset(&info, 0, sizeof(info));
  EXPECT(tvdb_gpu_context_info(ctx, &info, &err) == TVDB_OK);
  printf("[gpu:%s] backend=%d device='%s' sparse3d=%d\n",
         label, (int)info.backend, info.device_name, info.supports_sparse_3d_images);

  test_dense_csg(ctx);
  test_gpu_sdf_sphere(ctx, label);
  test_gpu_sdf_box(ctx, label);
  test_gpu_sdf_torus(ctx, label);
  test_sample(ctx);
  test_sample_quadratic(ctx);
  test_vulkan_image3d_sample_and_bench(ctx, &info);
  test_vulkan_partial_sparse_image3d(ctx, &info);
  test_sparse_image_background(ctx, &info);
  test_sparse_conv(ctx);
  test_sparse_conv_brute(ctx);
  test_spatial_queries(ctx);
  test_topology(ctx);
  test_volume_render(ctx);
  test_ray_queries(ctx);
  test_tsdf(ctx);
  test_stats(ctx);
  test_flood(ctx);
  test_splat(ctx);
  test_splat_quadratic(ctx);
  test_gaussian_sh(ctx);
  test_gaussian_project(ctx);
  test_gaussian_mcmc(ctx);
  test_dispatch(ctx);
  test_points_to_mask(ctx);
  test_voxelize(ctx);
  test_voxelize_unbounded(ctx);
  test_sparse_erode(ctx);
  test_sparse_dilate(ctx);
  test_merge(ctx);
  test_active_coords(ctx);
  test_checksum(ctx);
  test_mesh_to_sdf(ctx);
  test_marching_cubes(ctx);
  test_sparse_conv_strided(ctx);
  test_conv_transpose(ctx);
  test_buffer_interop(ctx);
  test_gaussian_forward(ctx);
  test_gaussian_backward_gpu(ctx);
  test_ssim(ctx);
  test_batched_conv(ctx);
  test_grid_batch_gpu(ctx);
  test_multi_gpu(ctx);
  tvdb_gpu_context_destroy(ctx);
  return 1;
}

int main(void) {
  tvdb_gpu_device_info_t devices[8];
  size_t ndev = tvdb_gpu_enumerate_devices(TVDB_GPU_BACKEND_AUTO, devices, 8);
  if (ndev == 0) {
    printf("SKIP: no Vulkan or CUDA runtime available\n");
    return 77;
  }
  int ran = 0;
  ran += run_backend(TVDB_GPU_BACKEND_VULKAN, "vulkan", 0);
  ran += run_backend(TVDB_GPU_BACKEND_CUDA, "cuda", 0);
  test_external_memory_interop();
  if (ran == 0) {
    printf("SKIP: no GPU context could be created\n");
    return 77;
  }

  if (g_failures == 0) {
    printf("All GPU backend parity tests passed.\n");
    return 0;
  }
  printf("%d GPU backend failure(s).\n", g_failures);
  return 1;
}
