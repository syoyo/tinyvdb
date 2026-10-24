/* GPU (CUDA or HIP) mesh level sets, level-set sampling and isosurface
 * stuffing against the CPU functions, on a tinyvdb_gpu_compute device and
 * through a tvdb_gpu_context_t.
 *
 *   test_gpu_volumetric [cuda|hip]   (default hip, then cuda)
 *
 * Level sets: same active voxels, magnitudes within 1e-6 voxel and the same
 * sign wherever |value| exceeds 1e-5 voxel; at voxels on the surface itself
 * the winding number is 1/2 and float (GPU) and double (CPU) may round it to
 * either side. Identical bytes are reported, not required: CPU builds may
 * contract floating-point expressions. Stuffing: same mesh. Closed, inside-out, open
 * and self-intersecting meshes, fast and exact winding. Exits 77 without a
 * CUDA/HIP device. */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tinyvdb_gpu.h"
#include "tinyvdb_tree_internal.h"

static int g_failures;
#define EXPECT(x)                                                   \
  do {                                                              \
    if (!(x)) {                                                     \
      fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #x);       \
      ++g_failures;                                                 \
    }                                                               \
  } while (0)

static void mesh_reserve(tvdb_triangle_mesh *m, size_t v, size_t f) {
  m->vertices = (tvdb_vec3f *)realloc(m->vertices, v * sizeof(tvdb_vec3f));
  m->faces = (tvdb_triangle *)realloc(m->faces, f * sizeof(tvdb_triangle));
  m->vertex_capacity = v;
  m->face_capacity = f;
}
/* Latitude-longitude sphere; `rows_kept` < rows leaves the bottom open. */
static void add_sphere(tvdb_triangle_mesh *m, float r, const float c[3], int rows,
                       int cols, int rows_kept, int flip) {
  const size_t base = m->vertex_count;
  mesh_reserve(m, base + (size_t)(rows + 1) * cols,
               m->face_count + 2 * (size_t)rows * cols);
  for (int i = 0; i <= rows; ++i)
    for (int j = 0; j < cols; ++j) {
      const double th = 3.14159265358979 * i / rows, ph = 2 * 3.14159265358979 * j / cols;
      m->vertices[m->vertex_count++] =
          (tvdb_vec3f){c[0] + r * (float)(sin(th) * cos(ph)), c[1] + r * (float)(sin(th) * sin(ph)),
                       c[2] + r * (float)cos(th)};
    }
  for (int i = 0; i < rows_kept; ++i)
    for (int j = 0; j < cols; ++j) {
      const uint32_t a = (uint32_t)(base + i * cols + j), b = (uint32_t)(base + i * cols + (j + 1) % cols),
                     d = (uint32_t)(base + (i + 1) * cols + j),
                     e = (uint32_t)(base + (i + 1) * cols + (j + 1) % cols);
      tvdb_triangle t0 = {a, d, b}, t1 = {b, d, e};
      if (flip) {
        t0 = (tvdb_triangle){a, b, d};
        t1 = (tvdb_triangle){b, e, d};
      }
      m->faces[m->face_count++] = t0;
      m->faces[m->face_count++] = t1;
    }
}
static void add_torus(tvdb_triangle_mesh *m, float R, float r, int nu, int nv) {
  const size_t base = m->vertex_count;
  mesh_reserve(m, base + (size_t)nu * nv, m->face_count + 2 * (size_t)nu * nv);
  for (int i = 0; i < nu; ++i)
    for (int j = 0; j < nv; ++j) {
      const double u = 2 * 3.14159265358979 * i / nu, v = 2 * 3.14159265358979 * j / nv;
      m->vertices[m->vertex_count++] = (tvdb_vec3f){(float)((R + r * cos(v)) * cos(u)),
                                                    (float)((R + r * cos(v)) * sin(u)),
                                                    (float)(r * sin(v))};
    }
  for (int i = 0; i < nu; ++i)
    for (int j = 0; j < nv; ++j) {
      const uint32_t a = (uint32_t)(base + i * nv + j), b = (uint32_t)(base + ((i + 1) % nu) * nv + j),
                     c = (uint32_t)(base + ((i + 1) % nu) * nv + (j + 1) % nv),
                     d = (uint32_t)(base + i * nv + (j + 1) % nv);
      m->faces[m->face_count++] = (tvdb_triangle){a, b, c};
      m->faces[m->face_count++] = (tvdb_triangle){a, c, d};
    }
}

/* Every active voxel of either grid: same activity, same sign, close value. */
static void compare_level_sets(const char *label, const tvdb_grid_t *a, const tvdb_grid_t *b,
                               double h) {
  tvdb_tree_index ia, ib;
  memset(&ia, 0, sizeof(ia));
  memset(&ib, 0, sizeof(ib));
  if (tvdb_tree_index_create(a, 1, &ia, NULL) != TVDB_OK ||
      tvdb_tree_index_create(b, 1, &ib, NULL) != TVDB_OK) {
    EXPECT(!"tree index");
    tvdb_tree_index_destroy(&ia);
    return;
  }
  EXPECT(ia.active_voxels == ib.active_voxels);
  EXPECT(ia.has_bbox == ib.has_bbox);
  size_t checked = 0, mismatched = 0, sign = 0, surface = 0;
  double worst = 0;
  for (int64_t z = ia.bbox_min[2] - 1; ia.has_bbox && z <= ia.bbox_max[2] + 1; ++z)
    for (int64_t y = ia.bbox_min[1] - 1; y <= ia.bbox_max[1] + 1; ++y)
      for (int64_t x = ia.bbox_min[0] - 1; x <= ia.bbox_max[0] + 1; ++x) {
        const int32_t c[3] = {(int32_t)x, (int32_t)y, (int32_t)z};
        int on_a = 0, on_b = 0;
        const float va = tvdb_tree_get(&ia, c, &on_a), vb = tvdb_tree_get(&ib, c, &on_b);
        if (!on_a && !on_b && va == vb) continue;
        ++checked;
        if (on_a != on_b) ++mismatched;
        if ((va < 0) != (vb < 0)) {
          if (fmin(fabs(va), fabs(vb)) > 1e-5 * h) ++sign;
          else ++surface;
        }
        const double d = fabs(fabs((double)va) - fabs((double)vb));
        if (d > worst) worst = d;
      }
  printf("%s: %zu active, %zu compared, activity mismatches %zu, sign mismatches %zu "
         "(+%zu on the surface), max |diff| %.3g voxel\n",
         label, ia.active_voxels, checked, mismatched, sign, surface, worst / h);
  EXPECT(mismatched == 0);
  EXPECT(sign == 0);
  EXPECT(worst <= 1e-6 * h);
  tvdb_tree_index_destroy(&ia);
  tvdb_tree_index_destroy(&ib);
}

static int same_bytes(const tvdb_grid_t *a, const tvdb_grid_t *b) {
  tvdb_file_t fa, fb;
  tvdb_file_init_for_write(&fa, NULL);
  tvdb_file_init_for_write(&fb, NULL);
  fa.grids = (tvdb_grid_t *)a;
  fb.grids = (tvdb_grid_t *)b;
  fa.num_grids = fb.num_grids = 1;
  uint8_t *da = NULL, *db = NULL;
  size_t na = 0, nb = 0;
  int same = tvdb_write_to_memory(&fa, 0, 0, &da, &na, NULL) == TVDB_OK &&
             tvdb_write_to_memory(&fb, 0, 0, &db, &nb, NULL) == TVDB_OK && na == nb &&
             !memcmp(da, db, na);
  free(da);
  free(db);
  return same;
}

/* CPU reference for tvdb_gpu_level_set_sample (tet_grid_sample's arithmetic). */
static float cpu_sample(const tvdb_tree_index *ix, const double inv[3][4], const double p[3]) {
  double q[3];
  for (int a = 0; a < 3; ++a)
    q[a] = inv[a][3] + inv[a][0] * p[0] + inv[a][1] * p[1] + inv[a][2] * p[2];
  int32_t base[3];
  double f[3];
  for (int a = 0; a < 3; ++a) {
    const double fl = floor(q[a]);
    base[a] = (int32_t)fl;
    f[a] = q[a] - fl;
  }
  double sum = 0;
  for (int c = 0; c < 8; ++c) {
    const int32_t at[3] = {base[0] + (c & 1), base[1] + ((c >> 1) & 1), base[2] + ((c >> 2) & 1)};
    const double w = ((c & 1) ? f[0] : 1 - f[0]) * (((c >> 1) & 1) ? f[1] : 1 - f[1]) *
                     (((c >> 2) & 1) ? f[2] : 1 - f[2]);
    sum += w * (double)tvdb_tree_get(ix, at, NULL);
  }
  return (float)sum;
}

static void check_sampling(tvdb_gpu_compute_t *ctx, const tvdb_grid_t *g) {
  tvdb_tree_index ix;
  memset(&ix, 0, sizeof(ix));
  EXPECT(tvdb_tree_index_create(g, 1, &ix, NULL) == TVDB_OK);
  double m[4][4];
  EXPECT(tvdb_tree_matrix(&g->transform, m));
  const double h = m[0][0];
  double inv[3][4] = {{1 / h, 0, 0, 0}, {0, 1 / h, 0, 0}, {0, 0, 1 / h, 0}};
  const size_t n = 200000;
  double *p = (double *)malloc(n * 3 * sizeof(double));
  float *gpu = (float *)malloc(n * sizeof(float));
  uint64_t s = 12345;
  for (size_t i = 0; i < 3 * n; ++i) {
    s = s * 6364136223846793005u + 1442695040888963407u;
    p[i] = ((double)(s >> 11) / 9007199254740992.0 * 4.0 - 2.0); /* inside and outside */
  }
  EXPECT(tvdb_gpu_compute_level_set_sample(ctx, g, p, n, gpu, NULL) == TVDB_OK);
  size_t differ = 0;
  for (size_t i = 0; i < n; ++i) differ += cpu_sample(&ix, inv, p + 3 * i) != gpu[i];
  printf("level set sampling: %zu points, %zu differ from the CPU\n", n, differ);
  EXPECT(differ == 0);
  free(p);
  free(gpu);
  tvdb_tree_index_destroy(&ix);
}

static void check_stuffing(tvdb_gpu_compute_t *ctx, const char *label, const tvdb_grid_t *g,
                           double spacing) {
  tvdb_stuffing_options_t so;
  memset(&so, 0, sizeof(so));
  so.spacing = spacing;
  tvdb_tet_mesh cpu, gpu;
  memset(&cpu, 0, sizeof(cpu));
  memset(&gpu, 0, sizeof(gpu));
  EXPECT(tvdb_level_set_to_tet_mesh(g, &so, NULL, &cpu, NULL) == TVDB_OK);
  EXPECT(tvdb_gpu_compute_level_set_to_tet_mesh(ctx, g, &so, NULL, &gpu, NULL) == TVDB_OK);
  EXPECT(cpu.vertex_count == gpu.vertex_count && cpu.tet_count == gpu.tet_count &&
         cpu.boundary_count == gpu.boundary_count);
  if (cpu.vertex_count == gpu.vertex_count && cpu.tet_count == gpu.tet_count &&
      cpu.boundary_count == gpu.boundary_count) {
    EXPECT(!memcmp(cpu.positions, gpu.positions, 3 * cpu.vertex_count * sizeof(float)));
    EXPECT(!memcmp(cpu.tets, gpu.tets, 4 * cpu.tet_count * sizeof(int32_t)));
    EXPECT(!memcmp(cpu.boundary, gpu.boundary, 3 * cpu.boundary_count * sizeof(int32_t)));
  }
  printf("%s stuffing: %zu tets (cpu %zu)\n", label, gpu.tet_count, cpu.tet_count);
  EXPECT(gpu.tet_count > 0);
  tvdb_tet_mesh_free(&cpu);
  tvdb_tet_mesh_free(&gpu);
}

static void run_case(tvdb_gpu_compute_t *ctx, const char *label, const tvdb_triangle_mesh *m,
                     float h, tvdb_level_set_sign_t sign, int stuff) {
  tvdb_mesh_level_set_options_t o;
  memset(&o, 0, sizeof(o));
  o.voxel_size = h;
  o.exterior_width = o.interior_width = 3 * h;
  o.sign = sign;
  o.max_voxels = 20000000;
  tvdb_grid_t cpu, gpu;
  memset(&cpu, 0, sizeof(cpu));
  memset(&gpu, 0, sizeof(gpu));
  tvdb_mesh_level_set_result_t rc, rg;
  tvdb_error_t e;
  memset(&e, 0, sizeof(e));
  EXPECT(tvdb_mesh_to_level_set(m, &o, NULL, &cpu, &rc, NULL) == TVDB_OK);
  const tvdb_status_t st = tvdb_gpu_compute_mesh_to_level_set(ctx, m, &o, NULL, &gpu, &rg, &e);
  if (st != TVDB_OK) fprintf(stderr, "%s: %s\n", label, e.message);
  EXPECT(st == TVDB_OK);
  if (st == TVDB_OK) {
    EXPECT(rc.candidate_voxels == rg.candidate_voxels);
    EXPECT(rc.active_voxels == rg.active_voxels);
    char name[128];
    snprintf(name, sizeof(name), "%s (%s)%s", label,
             sign == TVDB_LEVEL_SET_SIGN_WINDING_EXACT ? "exact" : "fast",
             same_bytes(&cpu, &gpu) ? " [identical bytes]" : "");
    compare_level_sets(name, &cpu, &gpu, h);
    if (stuff) check_stuffing(ctx, label, &gpu, 4.0 * h);
  }
  tvdb_grid_destroy_owned(&cpu);
  tvdb_grid_destroy_owned(&gpu);
}

/* The same level set and tets through a full GPU context (forwarding and its
 * module cache). */
static void check_context(tvdb_gpu_backend_t backend, const tvdb_triangle_mesh *m) {
  tvdb_gpu_context_t *ctx = NULL;
  EXPECT(tvdb_gpu_context_create(backend, 0, &ctx, NULL) == TVDB_OK);
  if (!ctx) return;
  tvdb_gpu_context_info_t info;
  tvdb_gpu_context_info(ctx, &info, NULL);
  EXPECT(info.backend == backend);
  tvdb_mesh_level_set_options_t o;
  memset(&o, 0, sizeof(o));
  o.voxel_size = 0.05f;
  o.exterior_width = o.interior_width = 0.15f;
  tvdb_grid_t cpu = {0}, gpu = {0};
  EXPECT(tvdb_mesh_to_level_set(m, &o, NULL, &cpu, NULL, NULL) == TVDB_OK);
  for (int pass = 0; pass < 2; ++pass) { /* the second reuses the module */
    tvdb_error_t e;
    memset(&e, 0, sizeof(e));
    const tvdb_status_t st = tvdb_gpu_mesh_to_level_set(ctx, m, &o, NULL, &gpu, NULL, &e);
    if (st != TVDB_OK) fprintf(stderr, "context pass %d: %s\n", pass, e.message);
    EXPECT(st == TVDB_OK);
    if (st == TVDB_OK) compare_level_sets("context level set", &cpu, &gpu, o.voxel_size);
  }
  tvdb_stuffing_options_t so;
  memset(&so, 0, sizeof(so));
  so.spacing = 0.2;
  tvdb_tet_mesh a, b;
  memset(&a, 0, sizeof(a));
  memset(&b, 0, sizeof(b));
  float v = 0;
  EXPECT(tvdb_level_set_to_tet_mesh(&cpu, &so, NULL, &a, NULL) == TVDB_OK);
  EXPECT(tvdb_gpu_level_set_to_tet_mesh(ctx, &cpu, &so, NULL, &b, NULL) == TVDB_OK);
  EXPECT(a.tet_count == b.tet_count && a.tet_count > 0);
  EXPECT(tvdb_gpu_level_set_sample(ctx, &cpu, (const double[3]){0, 0, 0}, 1, &v, NULL) == TVDB_OK);
  EXPECT(v < 0);
  tvdb_tet_mesh_free(&a);
  tvdb_tet_mesh_free(&b);
  tvdb_grid_destroy_owned(&cpu);
  tvdb_grid_destroy_owned(&gpu);
  tvdb_gpu_context_destroy(ctx);
}

int main(int argc, char **argv) {
  tvdb_gpu_compute_t *ctx = NULL;
  tvdb_error_t e;
  memset(&e, 0, sizeof(e));
  const char *want = argc > 1 ? argv[1] : NULL;
  if (!want || want[0] == 'h') tvdb_gpu_compute_create(TVDB_GPU_BACKEND_HIP, 0, &ctx, &e);
  if (!ctx && (!want || want[0] == 'c')) tvdb_gpu_compute_create(TVDB_GPU_BACKEND_CUDA, 0, &ctx, &e);
  if (!ctx) {
    printf("SKIP: no CUDA or HIP device (%s)\n", e.message);
    return 77;
  }
  const tvdb_gpu_backend_t backend = tvdb_gpu_compute_backend(ctx);
  printf("backend=%s device='%s'\n", backend == TVDB_GPU_BACKEND_HIP ? "hip" : "cuda",
         tvdb_gpu_compute_device_name(ctx));
  EXPECT(tvdb_gpu_compute_create(TVDB_GPU_BACKEND_VULKAN, 0, &(tvdb_gpu_compute_t *){NULL}, NULL) ==
         TVDB_ERROR_INVALID_ARGUMENT);

  const float o[3] = {0, 0, 0}, o2[3] = {0.45f, 0.1f, -0.05f};
  tvdb_triangle_mesh sphere = {0}, inside_out = {0}, open = {0}, torus = {0}, blobs = {0},
                     coarse = {0}, coarse_open = {0};
  add_sphere(&sphere, 1.0f, o, 48, 96, 48, 0);
  add_sphere(&coarse, 1.0f, o, 16, 32, 16, 0);        /* exact winding is O(faces) */
  add_sphere(&coarse_open, 1.0f, o, 16, 32, 12, 0);
  add_sphere(&inside_out, 1.0f, o, 48, 96, 48, 1);
  add_sphere(&open, 1.0f, o, 48, 96, 36, 0);          /* bottom cap removed */
  add_torus(&torus, 1.0f, 0.35f, 96, 48);
  add_sphere(&blobs, 0.8f, o, 32, 64, 32, 0);         /* two overlapping shells */
  add_sphere(&blobs, 0.7f, o2, 32, 64, 32, 0);

  run_case(ctx, "sphere", &sphere, 0.025f, TVDB_LEVEL_SET_SIGN_WINDING_FAST, 1);
  run_case(ctx, "coarse sphere", &coarse, 0.04f, TVDB_LEVEL_SET_SIGN_WINDING_EXACT, 0);
  run_case(ctx, "inside-out sphere", &inside_out, 0.04f, TVDB_LEVEL_SET_SIGN_WINDING_FAST, 0);
  run_case(ctx, "open sphere", &open, 0.04f, TVDB_LEVEL_SET_SIGN_WINDING_FAST, 0);
  run_case(ctx, "coarse open sphere", &coarse_open, 0.05f, TVDB_LEVEL_SET_SIGN_WINDING_EXACT, 0);
  run_case(ctx, "torus", &torus, 0.03f, TVDB_LEVEL_SET_SIGN_WINDING_FAST, 1);
  run_case(ctx, "overlapping shells", &blobs, 0.03f, TVDB_LEVEL_SET_SIGN_WINDING_FAST, 1);

  {
    /* Sampling, including flood-filled interior tiles and the background. */
    tvdb_mesh_level_set_options_t lo;
    memset(&lo, 0, sizeof(lo));
    lo.voxel_size = 0.04f;
    lo.exterior_width = lo.interior_width = 0.12f;
    tvdb_grid_t g = {0};
    EXPECT(tvdb_gpu_compute_mesh_to_level_set(ctx, &torus, &lo, NULL, &g, NULL, NULL) == TVDB_OK);
    check_sampling(ctx, &g);
    float v = 0;
    EXPECT(tvdb_gpu_compute_level_set_sample(NULL, &g, (const double[3]){0, 0, 0}, 1, &v, NULL) ==
           TVDB_ERROR_INVALID_ARGUMENT);
    EXPECT(tvdb_gpu_level_set_sample(NULL, &g, (const double[3]){0, 0, 0}, 1, &v, NULL) ==
           TVDB_ERROR_INVALID_ARGUMENT);
    tvdb_grid_destroy_owned(&g);
  }
  {
    /* Vulkan contexts do not run these. */
    tvdb_gpu_context_t *vk = NULL;
    if (tvdb_gpu_context_create(TVDB_GPU_BACKEND_VULKAN, 0, &vk, NULL) == TVDB_OK) {
      tvdb_mesh_level_set_options_t lo;
      memset(&lo, 0, sizeof(lo));
      lo.voxel_size = 0.1f;
      lo.exterior_width = lo.interior_width = 0.3f;
      tvdb_grid_t g = {0};
      EXPECT(tvdb_gpu_mesh_to_level_set(vk, &sphere, &lo, NULL, &g, NULL, NULL) ==
             TVDB_ERROR_UNIMPLEMENTED);
      tvdb_gpu_context_destroy(vk);
    }
  }
  check_context(backend, &coarse);
  tvdb_triangle_mesh *meshes[] = {&sphere, &inside_out, &open, &torus, &blobs, &coarse,
                                  &coarse_open};
  for (int i = 0; i < 7; ++i) {
    free(meshes[i]->vertices);
    free(meshes[i]->faces);
  }
  tvdb_gpu_compute_destroy(ctx);
  if (g_failures) {
    printf("%d failure(s)\n", g_failures);
    return 1;
  }
  printf("GPU volumetric parity: OK\n");
  return 0;
}
