/* Mesh -> narrow-band level set -> isosurface-stuffed tetrahedra, timed.
 *
 *   bench_volumetric MESH.obj [--res N] [--tets DIV] [--threads N]
 *                    [--gpu cuda|hip] [--compare]
 *
 * --res sets the voxel size to extent / N (default 128), --tets the lattice
 * spacing to extent / DIV (default 48, 0 skips stuffing). --gpu runs the
 * per-voxel and per-lattice-vertex passes on a CUDA or HIP device; --compare
 * also runs the CPU and reports the differences. --host-only replaces the
 * per-voxel pass with a trivial one, timing the host's sparse bookkeeping.
 * --write FILE saves the level set (uncompressed VDB) and --write-tets FILE
 * the raw tet mesh (positions, tets, boundary) for byte comparisons. */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "tinyvdb_sparse_tools.h"
#include "tinyvdb_tetmesh.h"
#include "tinyvdb_thread.h"
#if defined(TVDB_BENCH_GPU)
#include "tinyvdb_gpu.h"
#endif

static double now(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

/* Minimal OBJ: "v x y z" and "f a b c ..." (fan-triangulated; a/b/c forms). */
static int load_obj(const char *path, tvdb_triangle_mesh *m) {
  FILE *f = fopen(path, "r");
  if (!f) return 0;
  char line[4096];
  size_t vcap = 0, fcap = 0;
  memset(m, 0, sizeof(*m));
  while (fgets(line, sizeof(line), f)) {
    if (line[0] == 'v' && line[1] == ' ') {
      if (m->vertex_count == vcap) {
        vcap = vcap ? 2 * vcap : 1024;
        m->vertices = (tvdb_vec3f *)realloc(m->vertices, vcap * sizeof(tvdb_vec3f));
      }
      tvdb_vec3f *v = m->vertices + m->vertex_count++;
      if (sscanf(line + 2, "%f %f %f", &v->x, &v->y, &v->z) != 3) return 0;
    } else if (line[0] == 'f' && line[1] == ' ') {
      long idx[64];
      int n = 0;
      char *s = line + 2;
      while (n < 64) {
        char *end;
        long i = strtol(s, &end, 10);
        if (end == s) break;
        idx[n++] = i < 0 ? (long)m->vertex_count + i : i - 1;
        s = end;
        while (*s && *s != ' ' && *s != '\t') ++s;
      }
      for (int k = 2; k < n; ++k) {
        if (m->face_count == fcap) {
          fcap = fcap ? 2 * fcap : 1024;
          m->faces = (tvdb_triangle *)realloc(m->faces, fcap * sizeof(tvdb_triangle));
        }
        tvdb_triangle *t = m->faces + m->face_count++;
        t->v0 = (uint32_t)idx[0];
        t->v1 = (uint32_t)idx[k - 1];
        t->v2 = (uint32_t)idx[k];
      }
    }
  }
  fclose(f);
  m->vertex_capacity = vcap;
  m->face_capacity = fcap;
  return m->face_count > 0;
}

/* Distances that keep about half the candidates, signs from parity. */
static tvdb_status_t trivial_eval(void *user, const int32_t *ijk, size_t count, double h,
                                  float *distance, double *winding, tvdb_error_t *err) {
  (void)user;
  (void)err;
  for (size_t i = 0; i < count; ++i) {
    distance[i] = (float)(h * (double)(ijk[3 * i] & 7));
    winding[i] = (double)(ijk[3 * i + 1] & 1);
  }
  return TVDB_OK;
}

int main(int argc, char **argv) {
  const char *path = NULL, *gpu = NULL, *write = NULL, *write_tets = NULL;
  double res = 128, div = 48;
  int threads = 0, compare = 0, host_only = 0;
  for (int i = 1; i < argc; ++i) {
    if (!strcmp(argv[i], "--res") && i + 1 < argc) res = atof(argv[++i]);
    else if (!strcmp(argv[i], "--tets") && i + 1 < argc) div = atof(argv[++i]);
    else if (!strcmp(argv[i], "--threads") && i + 1 < argc) threads = atoi(argv[++i]);
    else if (!strcmp(argv[i], "--gpu") && i + 1 < argc) gpu = argv[++i];
    else if (!strcmp(argv[i], "--compare")) compare = 1;
    else if (!strcmp(argv[i], "--host-only")) host_only = 1;
    else if (!strcmp(argv[i], "--write") && i + 1 < argc) write = argv[++i];
    else if (!strcmp(argv[i], "--write-tets") && i + 1 < argc) write_tets = argv[++i];
    else path = argv[i];
  }
  tvdb_triangle_mesh mesh;
  if (!path || !load_obj(path, &mesh)) {
    fprintf(stderr, "usage: bench_volumetric MESH.obj [--res N] [--tets DIV] "
                    "[--threads N] [--gpu cuda|hip] [--compare]\n");
    return 2;
  }
  float lo[3] = {INFINITY, INFINITY, INFINITY}, hi[3] = {-INFINITY, -INFINITY, -INFINITY};
  for (size_t i = 0; i < mesh.vertex_count; ++i) {
    const float *p = &mesh.vertices[i].x;
    for (int a = 0; a < 3; ++a) {
      if (p[a] < lo[a]) lo[a] = p[a];
      if (p[a] > hi[a]) hi[a] = p[a];
    }
  }
  double extent = 0;
  for (int a = 0; a < 3; ++a) extent = fmax(extent, (double)hi[a] - lo[a]);
  const double h = extent / res;
  printf("%s: %zu vertices, %zu faces, extent %.4g, voxel %.4g\n", path,
         mesh.vertex_count, mesh.face_count, extent, h);

  tvdb_error_t err;
  tvdb_thread_pool_t *pool = NULL;
  if (threads > 0 && tvdb_thread_pool_create((size_t)threads, &pool, &err) != TVDB_OK) return 1;
#if defined(TVDB_BENCH_GPU)
  tvdb_gpu_context_t *ctx = NULL;
  if (gpu) {
    const tvdb_gpu_backend_t b =
        gpu[0] == 'h' ? TVDB_GPU_BACKEND_HIP : TVDB_GPU_BACKEND_CUDA;
    if (tvdb_gpu_context_create(b, 0, &ctx, &err) != TVDB_OK) {
      fprintf(stderr, "gpu: %s\n", err.message);
      return 77;
    }
    tvdb_gpu_context_info_t info;
    tvdb_gpu_context_info(ctx, &info, NULL);
    /* Compile the kernels (first use) outside the timings. */
    const tvdb_vec3f tv[3] = {{0, 0, 0}, {1, 0, 0}, {0, 1, 0}};
    const tvdb_triangle tf = {0, 1, 2};
    const tvdb_triangle_mesh tri = {.vertices = (tvdb_vec3f *)tv, .vertex_count = 3,
                                    .faces = (tvdb_triangle *)&tf, .face_count = 1};
    tvdb_mesh_level_set_options_t wo;
    memset(&wo, 0, sizeof(wo));
    wo.voxel_size = 0.25f;
    wo.exterior_width = wo.interior_width = 0.75f;
    tvdb_grid_t warm;
    memset(&warm, 0, sizeof(warm));
    const double t0 = now();
    if (tvdb_gpu_mesh_to_level_set(ctx, &tri, &wo, NULL, &warm, NULL, &err) != TVDB_OK) {
      fprintf(stderr, "gpu warm-up: %s\n", err.message);
      return 1;
    }
    tvdb_grid_destroy_owned(&warm);
    printf("device: %s (kernel compile %.3f s)\n", info.device_name, now() - t0);
  }
#else
  if (gpu) {
    fprintf(stderr, "built without the GPU backend\n");
    return 77;
  }
#endif
  tvdb_mesh_level_set_options_t opt;
  memset(&opt, 0, sizeof(opt));
  opt.voxel_size = (float)h;
  opt.exterior_width = opt.interior_width = (float)(3 * h);
  opt.max_voxels = 200000000;
  if (host_only) opt.evaluate = trivial_eval;
  tvdb_grid_t grid, cpu_grid;
  memset(&grid, 0, sizeof(grid));
  memset(&cpu_grid, 0, sizeof(cpu_grid));
  tvdb_mesh_level_set_result_t r;
  double t = now();
  tvdb_status_t st;
#if defined(TVDB_BENCH_GPU)
  if (ctx) st = tvdb_gpu_mesh_to_level_set(ctx, &mesh, &opt, pool, &grid, &r, &err);
  else
#endif
    st = tvdb_mesh_to_level_set(&mesh, &opt, pool, &grid, &r, &err);
  if (st != TVDB_OK) {
    fprintf(stderr, "level set: %s\n", err.message);
    return 1;
  }
  printf("level set (%s): %.3f s, %zu candidates, %zu active\n",
         host_only ? "host only" : gpu ? gpu : "cpu",
         now() - t, r.candidate_voxels, r.active_voxels);
  if (write) {
    tvdb_file_t file;
    tvdb_file_init_for_write(&file, NULL);
    file.grids = &grid;
    file.num_grids = 1;
    uint8_t *data = NULL;
    size_t size = 0;
    FILE *f = NULL;
    if (tvdb_write_to_memory(&file, 0, 0, &data, &size, &err) != TVDB_OK ||
        !(f = fopen(write, "wb")) || fwrite(data, 1, size, f) != size) {
      fprintf(stderr, "write failed\n");
      return 1;
    }
    fclose(f);
    free(data);
  }
  if (gpu && compare) {
    tvdb_mesh_level_set_result_t rc;
    t = now();
    if (tvdb_mesh_to_level_set(&mesh, &opt, pool, &cpu_grid, &rc, &err) != TVDB_OK) return 1;
    printf("level set (cpu): %.3f s, %zu active\n", now() - t, rc.active_voxels);
  }

  if (div > 0) {
    tvdb_stuffing_options_t so;
    memset(&so, 0, sizeof(so));
    so.spacing = extent / div;
    so.max_lattice_vertices = 200000000;
    so.max_tets = 200000000;
    tvdb_tet_mesh tm;
    memset(&tm, 0, sizeof(tm));
    t = now();
#if defined(TVDB_BENCH_GPU)
    if (ctx) st = tvdb_gpu_level_set_to_tet_mesh(ctx, &grid, &so, pool, &tm, &err);
    else
#endif
      st = tvdb_level_set_to_tet_mesh(&grid, &so, pool, &tm, &err);
    if (st != TVDB_OK) {
      fprintf(stderr, "stuffing: %s\n", err.message);
      return 1;
    }
    const double ts = now() - t;
    tvdb_tet_mesh_quality_t q;
    tvdb_tet_mesh_quality(&tm, &q, NULL);
    printf("stuffing (%s): %.3f s, %zu vertices, %zu tets, volume %.6g, "
           "dihedral %.1f-%.1f, inverted %zu\n",
           gpu ? gpu : "cpu", ts, tm.vertex_count, tm.tet_count, q.volume,
           q.min_dihedral, q.max_dihedral, q.inverted);
    if (write_tets) {
      FILE *f = fopen(write_tets, "wb");
      if (!f || fwrite(tm.positions, sizeof(float), 3 * tm.vertex_count, f) != 3 * tm.vertex_count ||
          fwrite(tm.tets, sizeof(int32_t), 4 * tm.tet_count, f) != 4 * tm.tet_count ||
          fwrite(tm.boundary, sizeof(int32_t), 3 * tm.boundary_count, f) != 3 * tm.boundary_count) {
        fprintf(stderr, "tet write failed\n");
        return 1;
      }
      fclose(f);
    }
    if (gpu && compare) {
      tvdb_tet_mesh tc;
      memset(&tc, 0, sizeof(tc));
      t = now();
      if (tvdb_level_set_to_tet_mesh(cpu_grid.tree.nodes ? &cpu_grid : &grid, &so, pool,
                                     &tc, &err) != TVDB_OK)
        return 1;
      printf("stuffing (cpu): %.3f s, %zu tets\n", now() - t, tc.tet_count);
      tvdb_tet_mesh_free(&tc);
    }
    tvdb_tet_mesh_free(&tm);
  }
  tvdb_grid_destroy_owned(&grid);
  tvdb_grid_destroy_owned(&cpu_grid);
#if defined(TVDB_BENCH_GPU)
  tvdb_gpu_context_destroy(ctx);
#endif
  tvdb_thread_pool_destroy(pool);
  tvdb_triangle_mesh_free(&mesh);
  return 0;
}
