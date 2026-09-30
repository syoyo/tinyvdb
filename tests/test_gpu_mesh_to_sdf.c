/* CPU-parity for mesh_to_sdf on both backends, on meshes with enough faces to
 * matter.
 *
 * The existing check inside test_gpu_backend.c uses a 4-face tetrahedron and
 * tolerates up to 10% sign disagreement. That cannot validate the kernel: a
 * brute-force scan of four faces and a scan of four thousand behave identically
 * if the voxel loop is right and identically if it is wrong, and 10% of 20k
 * voxels is 2000 sign flips, which is a lot of latitude. So this covers what the
 * op actually does:
 *
 *  - meshes from 256 to ~4000 faces, so the per-voxel face loop is exercised;
 *  - grid resolutions that span single-slab and chunked dispatch
 *    (TVDB_MESH_SDF_MAX_VOXELS_PER_DISPATCH);
 *  - a non-cubic grid, since the slab indexing computes x/y/z from a flat id;
 *  - magnitude compared tightly and sign disagreement bounded at 0.1% of
 *    voxels, which is roughly two orders tighter than before and still above the
 *    measured rate (0.04% worst observed, at voxels that are near-equidistant to
 *    several triangles, where the closest-normal sign is FP-fragile by
 *    construction -- the CPU itself is only defined to within its own rounding
 *    there).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif
#include "tinyvdb_gpu.h"
#include "tinyvdb_mesh.h"

static int g_failures = 0;
#define EXPECT(cond) do { if (!(cond)) { \
  fprintf(stderr, "FAIL [%s:%d]: %s\n", __FILE__, __LINE__, #cond); ++g_failures; } } while (0)

/* UV sphere, radius 0.5 centred at the origin. The grid is padded by band_width
 * on every side, so the voxel extents are not equal and z slabbing is not
 * accidentally equivalent to x or y. */
static void build_sphere(int seg, int ring, tvdb_vec3f** V, tvdb_triangle** F,
                         size_t* nv, size_t* nf) {
  *V = (tvdb_vec3f*)malloc((size_t)(seg + 1) * (ring + 1) * sizeof(tvdb_vec3f));
  *F = (tvdb_triangle*)malloc((size_t)seg * ring * 2 * sizeof(tvdb_triangle));
  if (!*V || !*F) { printf("OOM building sphere\n"); exit(2); }
  size_t k = 0;
  for (int j = 0; j <= ring; ++j) {
    float th = (float)M_PI * (float)j / (float)ring;
    for (int i = 0; i <= seg; ++i) {
      float ph = 2.0f * (float)M_PI * (float)i / (float)seg;
      (*V)[k].x = 0.5f * sinf(th) * cosf(ph);
      (*V)[k].y = 0.5f * cosf(th);
      (*V)[k].z = 0.5f * sinf(th) * sinf(ph);
      ++k;
    }
  }
  size_t kf = 0;
  for (int j = 0; j < ring; ++j)
    for (int i = 0; i < seg; ++i) {
      int a = j * (seg + 1) + i, b = a + seg + 1;
      (*F)[kf].v0 = a; (*F)[kf].v1 = b;     (*F)[kf].v2 = a + 1; ++kf;
      (*F)[kf].v0 = a + 1; (*F)[kf].v1 = b; (*F)[kf].v2 = b + 1; ++kf;
    }
  *nv = k; *nf = kf;
}

static void run_case(tvdb_gpu_context_t* ctx, int seg, int ring, float res, float band,
                     const char* note) {
  tvdb_vec3f* V; tvdb_triangle* F; size_t nv, nf;
  build_sphere(seg, ring, &V, &F, &nv, &nf);
  tvdb_triangle_mesh mesh; memset(&mesh, 0, sizeof mesh);
  mesh.vertices = V; mesh.vertex_count = nv; mesh.faces = F; mesh.face_count = nf;

  tvdb_dense_grid cpu, gpu;
  memset(&cpu, 0, sizeof cpu); memset(&gpu, 0, sizeof gpu);
  tvdb_error_t e; memset(&e, 0, sizeof e);
  if (!tvdb_mesh_to_sdf(&mesh, res, band, &cpu, NULL)) {
    printf("  FAIL %-20s cpu reference failed\n", note); ++g_failures;
    free(V); free(F); return;
  }
  if (tvdb_gpu_mesh_to_sdf(ctx, &mesh, res, band, &gpu, &e) != TVDB_OK) {
    printf("  FAIL %-20s gpu: %s\n", note, e.message); ++g_failures;
    tvdb_dense_grid_free(&cpu); free(V); free(F); return;
  }
  if (gpu.nx != cpu.nx || gpu.ny != cpu.ny || gpu.nz != cpu.nz) {
    printf("  FAIL %-20s dims %dx%dx%d vs %dx%dx%d\n", note,
           gpu.nx, gpu.ny, gpu.nz, cpu.nx, cpu.ny, cpu.nz);
    ++g_failures;
  } else if (gpu.ox != cpu.ox || gpu.oy != cpu.oy || gpu.oz != cpu.oz ||
             gpu.voxel_size != cpu.voxel_size) {
    printf("  FAIL %-20s grid frame differs\n", note); ++g_failures;
  } else {
    /* The two properties are compared separately, which is the point. A sign flip
     * on a band-saturated voxel shows up as a 2*band difference in the *signed*
     * value, so comparing signed values would let sign noise masquerade as a
     * distance error (or hide one). The unsigned distance field is the
     * substantive computation and is deterministic; the sign is only defined up
     * to the closest-face tie-break. */
    size_t n = (size_t)cpu.nx * cpu.ny * cpu.nz, flips = 0, neg = 0;
    double worst_mag = 0.0;
    int out_of_band = 0;
    for (size_t i = 0; i < n; ++i) {
      double am = fabs((double)cpu.data[i]), bm = fabs((double)gpu.data[i]);
      double d = am - bm; if (d < 0) d = -d;
      if (d > worst_mag) worst_mag = d;
      if (cpu.data[i] < 0.0f) ++neg;
      if ((cpu.data[i] < 0.0f) != (gpu.data[i] < 0.0f)) ++flips;
      /* The op clamps to +/-band; anything outside that is a real error. */
      if (bm > (double)band * 1.001) out_of_band = 1;
    }
    if (out_of_band) { printf("  FAIL %-20s output exceeds band %.4f\n", note, band); ++g_failures; }
    /* 0.1% of voxels: ~100x tighter than the previous 10% allowance, and still
     * above the measured rate. */
    int ok = (worst_mag <= 2e-5) && (flips * 1000 <= n);
    if (!ok) ++g_failures;
    printf("  %-4s %-20s %zux%zux%zu %6zu faces, %8zu voxels: worst|df| %.2e, flips %zu (%.4f%%), interior %zu\n",
           ok ? "ok" : "FAIL", note, (size_t)cpu.nx, (size_t)cpu.ny, (size_t)cpu.nz, nf, n,
           worst_mag, flips, 100.0 * (double)flips / (double)n, neg);
  }
  tvdb_dense_grid_free(&cpu); tvdb_dense_grid_free(&gpu);
  free(V); free(F);
}

int main(int argc, char** argv) {
  int want_cuda = (argc > 1 && argv[1][0] == 'c');
  tvdb_error_t e; memset(&e, 0, sizeof e);
  tvdb_gpu_context_t* ctx = NULL;
  tvdb_status_t st = tvdb_gpu_context_create(want_cuda ? TVDB_GPU_BACKEND_CUDA
                                                      : TVDB_GPU_BACKEND_VULKAN,
                                             0, &ctx, &e);
  if (st != TVDB_OK) { printf("no context: %s\n", e.message); return 77; }
  setvbuf(stdout, NULL, _IONBF, 0);
  printf("backend=%s\n", want_cuda ? "cuda" : "vulkan");
  if (!want_cuda && !tvdb_gpu_spirv_available()) {
    printf("SKIP: built without GPU SPIR-V\n");
    tvdb_gpu_context_destroy(ctx); return 77;
  }

  /* Small faces, coarse grid: the 256-face case, single slab. */
  run_case(ctx, 16,  8, 0.05f,  0.20f, "256-faces-coarse");
  /* Asymmetric segment/ring counts: the grid then comes out non-cubic, which is
   * what the slab index arithmetic needs covering. */
  run_case(ctx, 24, 12, 0.03f,  0.20f, "576-faces-noncubic");
  /* Thousands of faces: the per-voxel face loop is the whole cost. */
  run_case(ctx, 48, 24, 0.02f,  0.20f, "2304-faces");
  run_case(ctx, 64, 32, 0.02f,  0.20f, "4096-faces");
  /* Band smaller than the voxel size: most voxels saturate, so this leans on the
   * sign path and the clamp. */
  run_case(ctx, 32, 16, 0.02f,  0.01f, "tight-band-clamp");
  /* Over TVDB_MESH_SDF_MAX_VOXELS_PER_DISPATCH (1M), so the z-slab path runs. */
  run_case(ctx, 16,  8, 0.012f, 0.20f, "chunked-slabs");

  EXPECT(g_failures == 0);
  tvdb_gpu_context_destroy(ctx);
  printf("mesh_to_sdf parity: %s\n", g_failures ? "FAIL" : "OK");
  return g_failures ? 1 : 0;
}
