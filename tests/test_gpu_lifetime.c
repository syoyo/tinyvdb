/* Resource-lifetime harness for the GPU backend.
 *
 * The 44-case parity suite calls each op a handful of times, so it is
 * structurally unable to catch a descriptor-pool exhaustion or a per-dispatch
 * device-object leak. This runs the four map-backed paths in rotation inside a
 * single context and reports RSS growth, which is how both real bugs were
 * found. Fast sweeping is in the rotation for its up-front per-plane descriptor
 * sets: 128 sets per call against a shared pool with a fixed maxSets.
 *
 * Run:  test_gpu_lifetime [iterations]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "tinyvdb_gpu.h"
#include "tinyvdb_sparse.h"

static long rss_mb(void)
{
    FILE *f = fopen("/proc/self/status", "r");
    char l[256]; long v = 0;
    while (f && fgets(l, sizeof l, f)) {
        if (!strncmp(l, "VmRSS:", 6)) { sscanf(l + 6, "%ld", &v); break; }
    }
    if (f) fclose(f);
    return v / 1024;
}

int main(int argc, char **argv)
{
    int iter = (argc > 1) ? atoi(argv[1]) : 200;
    tvdb_error_t e; memset(&e, 0, sizeof e);
    tvdb_gpu_context_t *ctx = NULL;
    if (tvdb_gpu_context_create(TVDB_GPU_BACKEND_VULKAN, 0, &ctx, &e) != TVDB_OK) {
        printf("no vulkan context\n"); return 77;   /* skip */
    }

    if (!tvdb_gpu_spirv_available()) { printf("SKIP: built without GPU SPIR-V\n"); return 77; }

    /* Above TVDB_INDEX_MAP_MIN_ACTIVE (2048) so the map paths are taken. */
    const int L = 16, N = L * L * L;
    int32_t *act = malloc((size_t)N * 3 * 4);
    int k = 0;
    for (int i = 0; i < L; i++) for (int j = 0; j < L; j++) for (int z = 0; z < L; z++) {
        act[k*3+0] = i; act[k*3+1] = j; act[k*3+2] = z; k++;
    }
    const size_t nq = 4096;
    int32_t *q = malloc(nq * 3 * 4);
    int64_t *oi = malloc(nq * 8);
    int32_t *nc = malloc((size_t)N * 4);
    float *pts = malloc(nq * 3 * 4);
    uint8_t *mask = malloc(nq);
    float vs[3] = { 1, 1, 1 }, og[3] = { 0, 0, 0 };
    srand(5);
    for (size_t i = 0; i < nq; i++) {
        pts[3*i+0] = (float)(rand() % L);
        pts[3*i+1] = (float)(rand() % L);
        pts[3*i+2] = (float)(rand() % L);
        q[3*i+0] = (int)pts[3*i+0]; q[3*i+1] = (int)pts[3*i+1]; q[3*i+2] = (int)pts[3*i+2];
    }
    /* sparse_conv needs coords spread so the dense fast path declines. */
    float kern[27];
    for (int i = 0; i < 27; i++) kern[i] = 0.1f * (float)(i % 5);
    tvdb_sparse_grid gin; memset(&gin, 0, sizeof gin);
    gin.coords = malloc((size_t)N * sizeof(tvdb_vec3i));
    gin.values = malloc((size_t)N * sizeof(float));
    gin.capacity = (size_t)N; gin.count = (size_t)N; gin.voxel_size = 1.0f;
    for (int i = 0; i < L; i++) for (int j = 0; j < L; j++) for (int z = 0; z < L; z++) {
        int t = (i * L + j) * L + z;
        gin.coords[t].x = i * 400; gin.coords[t].y = j * 400; gin.coords[t].z = z * 400;
        gin.values[t] = 1.0f + (float)(t % 5);
    }

    /* warm up so one-time driver initialisation is not counted */
    tvdb_sparse_grid w; memset(&w, 0, sizeof w);
    tvdb_gpu_sparse_conv3d(ctx, &gin, kern, 3, 3, 3, -1.0f, &w, &e);
    free(w.coords); free(w.values);

    tvdb_dense_grid mscalar; memset(&mscalar, 0, sizeof mscalar);
    mscalar.nx = 16; mscalar.ny = 16; mscalar.nz = 16; mscalar.voxel_size = 0.05f;
    mscalar.data = malloc(16*16*16 * sizeof(float));
    for (int i = 0; i < 16*16*16; i++) mscalar.data[i] = (float)((i % 17) - 8);

    /* Fast sweeping allocates one descriptor set per wavefront plane up front
     * (128 for an 8x8x8 grid: 16 planes x 8 directions) and frees them again,
     * so it is the path most likely to exhaust the shared descriptor pool or
     * leak a set per call. */
    const int F = 8, FN = F * F * F;
    tvdb_dense_grid fs; memset(&fs, 0, sizeof fs);
    fs.nx = F; fs.ny = F; fs.nz = F; fs.voxel_size = 1.0f;
    fs.data = malloc((size_t)FN * sizeof(float));
    for (int i = 0; i < FN; i++) fs.data[i] = (float)((i % 13) - 6);
    { tvdb_dense_grid w2 = fs; int it2 = 0;
      if (tvdb_gpu_fast_sweeping(ctx, &w2, 0.5f, 2, 0.0f, &it2, &e) != TVDB_OK) {
          printf("FAIL fast_sweeping warmup: %s\n", e.message); return 1; } }

    /* Dense dilate is a ping-pong that allocates a fresh descriptor set per
     * iteration, and those sets are now parked with their fences rather than
     * returned to the pool at submit. It is the path that would leak a set per
     * iteration, or exhaust the pool, if that lifetime moved. */
    tvdb_dense_grid mg; memset(&mg, 0, sizeof mg);
    mg.nx = 24; mg.ny = 24; mg.nz = 24; mg.voxel_size = 0.04f;
    mg.data = malloc(24*24*24 * sizeof(float));
    { float* pristine = malloc(24*24*24 * sizeof(float));
      for (int iz = 0; iz < 24; iz++) for (int iy = 0; iy < 24; iy++) for (int ix = 0; ix < 24; ix++) {
          double dx = ix-12, dy = iy-12, dz = iz-12;
          pristine[(iz*24+iy)*24+ix] = (float)(dx*dx+dy*dy+dz*dz - 36.0); }
      tvdb_dense_grid w3; memset(&w3, 0, sizeof w3);
      w3.nx=w3.ny=w3.nz=24; w3.voxel_size=0.04f; w3.data=malloc(24*24*24*sizeof(float));
      memcpy(w3.data, pristine, 24*24*24*sizeof(float));
      if (tvdb_gpu_dilate(ctx, &w3, 6, &e) != TVDB_OK) {
          printf("FAIL dilate warmup: %s\n", e.message); return 1; }
      free(w3.data); memcpy(mg.data, pristine, 24*24*24*sizeof(float)); free(pristine); }

    /* The reusable index map is the heaviest device-object path: three compute
     * pipelines, two descriptor sets, a descriptor-set layout, and six buffers
     * (three device-local plus three host-visible) per map. Built and queried
     * inside the loop so a leak in its create/destroy shows up as a rate rather
     * than as a single high-water mark. */
    tvdb_gpu_index_map_t* rmap = NULL;
    if (tvdb_gpu_index_map_create(ctx, act, N, &rmap, &e) != TVDB_OK) {
        printf("FAIL index_map_create warmup: %s\n", e.message); return 1; }
    for (int i = 0; i < 2; ++i) {
        if (tvdb_gpu_ijk_to_index_mapped(ctx, rmap, q, nq, (int32_t*)oi, &e) != TVDB_OK) {
            printf("FAIL ijk_to_index_mapped warmup: %s\n", e.message); return 1; }
    }
    { int32_t* rcounts = malloc((size_t)N * sizeof(int32_t));
      if (tvdb_gpu_neighbor_counts_mapped(ctx, rmap, 6, rcounts, &e) != TVDB_OK) {
          printf("FAIL neighbor_counts_mapped warmup: %s\n", e.message); return 1; }
      free(rcounts); }
    tvdb_gpu_index_map_destroy(ctx, rmap);

    long base = rss_mb();
    for (int it = 0; it < iter; it++) {
        if (tvdb_gpu_ijk_to_index(ctx, act, N, q, nq, oi, &e) != TVDB_OK) {
            printf("FAIL ijk_to_index it=%d: %s\n", it, e.message); return 1;
        }
        if (tvdb_gpu_neighbor_counts(ctx, act, N, 26, nc, &e) != TVDB_OK) {
            printf("FAIL neighbor_counts it=%d: %s\n", it, e.message); return 1;
        }
        if (tvdb_gpu_points_in_grid(ctx, pts, nq, vs, og, act, N, mask, &e) != TVDB_OK) {
            printf("FAIL points_in_grid it=%d: %s\n", it, e.message); return 1;
        }
        tvdb_sparse_grid out; memset(&out, 0, sizeof out);
        if (tvdb_gpu_sparse_conv3d(ctx, &gin, kern, 3, 3, 3, -1.0f, &out, &e) != TVDB_OK) {
            printf("FAIL sparse_conv3d it=%d: %s\n", it, e.message); return 1;
        }
        free(out.coords); free(out.values);
        /* mean_curvature_flow stages DEVICE_LOCAL buffers, so it is the path
         * that would leak a VkBuffer/VkDeviceMemory per iteration if the new
         * device-local path or its cleanup regressed. */
        tvdb_dense_grid mf; memset(&mf, 0, sizeof mf);
        if (tvdb_gpu_mean_curvature_flow(ctx, &mscalar, 0.01f, 4, &mf, &e) != TVDB_OK) {
            printf("FAIL mean_curvature_flow it=%d: %s\n", it, e.message); return 1;
        }
        free(mf.data);
        tvdb_dense_grid fsw = fs; int fit = 0;
        if (tvdb_gpu_fast_sweeping(ctx, &fsw, 0.5f, 2, 0.0f, &fit, &e) != TVDB_OK) {
            printf("FAIL fast_sweeping it=%d: %s\n", it, e.message); return 1;
        }
        /* 6 dispatches, 6 freshly allocated descriptor sets parked per call. */
        tvdb_dense_grid mw = mg;
        if (tvdb_gpu_dilate(ctx, &mw, 6, &e) != TVDB_OK) {
            printf("FAIL dilate it=%d: %s\n", it, e.message); return 1;
        }
        /* Create, query all three kinds twice, destroy -- per iteration. */
        tvdb_gpu_index_map_t* im = NULL;
        if (tvdb_gpu_index_map_create(ctx, act, N, &im, &e) != TVDB_OK) {
            printf("FAIL index_map_create it=%d: %s\n", it, e.message); return 1; }
        for (int i = 0; i < 2; ++i) {
            if (tvdb_gpu_ijk_to_index_mapped(ctx, im, q, nq, (int32_t*)oi, &e) != TVDB_OK) {
                printf("FAIL ijk_to_index_mapped it=%d: %s\n", it, e.message); return 1; }
            if (tvdb_gpu_points_in_grid_mapped(ctx, im, pts, nq, vs, og, (int32_t*)oi, &e) != TVDB_OK) {
                printf("FAIL points_in_grid_mapped it=%d: %s\n", it, e.message); return 1; }
        }
        if (tvdb_gpu_neighbor_counts_mapped(ctx, im, 26, nc, &e) != TVDB_OK) {
            printf("FAIL neighbor_counts_mapped it=%d: %s\n", it, e.message); return 1; }
        tvdb_gpu_index_map_destroy(ctx, im);
    }
    long end = rss_mb();
    printf("%d iterations x 8 paths: OK. RSS %ld -> %ld MB (delta %+ld MB, %.2f MB/iter)\n",
           iter, base, end, end - base, (double)(end - base) / iter);
    /* A leak shows up as a rate that holds steady as iter doubles; a driver
     * cache plateaus. Measured: clean 0.00 MB/iter, with the command buffer
     * return removed 0.58 MB/iter. 0.20 sits between the two with margin. */
    double rate = (double)(end - base) / iter;
    if (iter >= 200 && rate > 0.20) {
        printf("FAIL: %.2f MB/iter suggests a leak\n", rate);
        return 1;
    }
    free(act); free(q); free(oi); free(nc); free(pts); free(mask);
    free(gin.coords); free(gin.values); free(mscalar.data); free(fs.data); free(mg.data);
    tvdb_gpu_context_destroy(ctx);
    return 0;
}
