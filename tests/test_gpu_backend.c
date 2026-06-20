#include "tinyvdb_gpu.h"
#include "tinyvdb_grid_index.h"
#include "tinyvdb_levelset.h"
#include "tinyvdb_ops.h"
#include "tinyvdb_render.h"
#include "tinyvdb_sample.h"
#include "tinyvdb_sparse.h"
#include "tinyvdb_topology.h"

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
  test_vulkan_image3d_sample_and_bench(ctx, &info);
  test_vulkan_partial_sparse_image3d(ctx, &info);
  test_sparse_conv(ctx);
  test_spatial_queries(ctx);
  test_topology(ctx);
  test_volume_render(ctx);
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
