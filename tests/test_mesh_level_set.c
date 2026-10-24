/* tvdb_mesh_to_level_set against analytic distances (box, sphere), sign
 * robustness (inside-out, open meshes), determinism across worker counts,
 * VDB round trip and argument failures. */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tinyvdb_sparse_tools.h"
#include "tinyvdb_sparse_tree.h"
#include "tinyvdb_tree_internal.h"
#include "tinyvdb_winding.h"

#define CHECK(x)                                                    \
  do {                                                              \
    if (!(x)) {                                                     \
      fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #x);      \
      return 1;                                                     \
    }                                                               \
  } while (0)

static int mesh_reserve(tvdb_triangle_mesh *m, size_t v, size_t f) {
  m->vertices = (tvdb_vec3f *)realloc(m->vertices, v * sizeof(tvdb_vec3f));
  m->faces = (tvdb_triangle *)realloc(m->faces, f * sizeof(tvdb_triangle));
  m->vertex_capacity = v;
  m->face_capacity = f;
  return m->vertices && m->faces;
}
static void mesh_free(tvdb_triangle_mesh *m) {
  free(m->vertices);
  free(m->faces);
  memset(m, 0, sizeof(*m));
}
/* Axis-aligned box [-1,1]^3, outward winding; `skip` omits one face pair. */
static int make_box(tvdb_triangle_mesh *m, int skip) {
  static const float c[8][3] = {{-1, -1, -1}, {1, -1, -1}, {1, 1, -1}, {-1, 1, -1},
                                {-1, -1, 1},  {1, -1, 1},  {1, 1, 1},  {-1, 1, 1}};
  static const uint32_t f[12][3] = {{0, 2, 1}, {0, 3, 2}, {4, 5, 6}, {4, 6, 7},
                                    {0, 1, 5}, {0, 5, 4}, {1, 2, 6}, {1, 6, 5},
                                    {2, 3, 7}, {2, 7, 6}, {3, 0, 4}, {3, 4, 7}};
  if (!mesh_reserve(m, 8, 12)) return 0;
  for (int i = 0; i < 8; ++i) m->vertices[i] = (tvdb_vec3f){c[i][0], c[i][1], c[i][2]};
  m->vertex_count = 8;
  m->face_count = 0;
  for (int i = 0; i < 12; ++i) {
    if (skip >= 0 && i / 2 == skip) continue;
    m->faces[m->face_count++] = (tvdb_triangle){f[i][0], f[i][1], f[i][2]};
  }
  return 1;
}
/* Icosphere of radius 1 after `levels` midpoint subdivisions. */
static int make_sphere(tvdb_triangle_mesh *m, int levels) {
  const float t = 1.61803398875f;
  const float iv[12][3] = {{-1, t, 0}, {1, t, 0},  {-1, -t, 0}, {1, -t, 0},
                           {0, -1, t}, {0, 1, t},  {0, -1, -t}, {0, 1, -t},
                           {t, 0, -1}, {t, 0, 1},  {-t, 0, -1}, {-t, 0, 1}};
  const uint32_t ifc[20][3] = {{0, 11, 5}, {0, 5, 1},  {0, 1, 7},   {0, 7, 10}, {0, 10, 11},
                               {1, 5, 9},  {5, 11, 4}, {11, 10, 2}, {10, 7, 6}, {7, 1, 8},
                               {3, 9, 4},  {3, 4, 2},  {3, 2, 6},   {3, 6, 8},  {3, 8, 9},
                               {4, 9, 5},  {2, 4, 11}, {6, 2, 10},  {8, 6, 7},  {9, 8, 1}};
  size_t nv = 12, nf = 20;
  for (int l = 0; l < levels; ++l) {
    nv += nf * 3 / 2;
    nf *= 4;
  }
  if (!mesh_reserve(m, nv + nf * 3, nf)) return 0; /* generous: no edge dedup */
  for (int i = 0; i < 12; ++i) {
    const float n = sqrtf(iv[i][0] * iv[i][0] + iv[i][1] * iv[i][1] + iv[i][2] * iv[i][2]);
    m->vertices[i] = (tvdb_vec3f){iv[i][0] / n, iv[i][1] / n, iv[i][2] / n};
  }
  m->vertex_count = 12;
  for (int i = 0; i < 20; ++i) m->faces[i] = (tvdb_triangle){ifc[i][0], ifc[i][1], ifc[i][2]};
  m->face_count = 20;
  tvdb_triangle *scratch = (tvdb_triangle *)malloc(nf * sizeof(tvdb_triangle));
  if (!scratch) return 0;
  for (int l = 0; l < levels; ++l) {
    size_t out = 0;
    for (size_t f = 0; f < m->face_count; ++f) {
      const uint32_t v[3] = {m->faces[f].v0, m->faces[f].v1, m->faces[f].v2};
      uint32_t mid[3];
      for (int e = 0; e < 3; ++e) {
        const tvdb_vec3f a = m->vertices[v[e]], b = m->vertices[v[(e + 1) % 3]];
        tvdb_vec3f p = {(a.x + b.x) / 2, (a.y + b.y) / 2, (a.z + b.z) / 2};
        const float n = sqrtf(p.x * p.x + p.y * p.y + p.z * p.z);
        p.x /= n; p.y /= n; p.z /= n;
        mid[e] = (uint32_t)m->vertex_count;
        m->vertices[m->vertex_count++] = p; /* duplicates are harmless here */
      }
      scratch[out++] = (tvdb_triangle){v[0], mid[0], mid[2]};
      scratch[out++] = (tvdb_triangle){v[1], mid[1], mid[0]};
      scratch[out++] = (tvdb_triangle){v[2], mid[2], mid[1]};
      scratch[out++] = (tvdb_triangle){mid[0], mid[1], mid[2]};
    }
    memcpy(m->faces, scratch, out * sizeof(tvdb_triangle));
    m->face_count = out;
  }
  free(scratch);
  return 1;
}
static double box_sdf(const double p[3]) {
  double q[3], outside = 0, inside = -1e300;
  for (int a = 0; a < 3; ++a) {
    q[a] = fabs(p[a]) - 1;
    outside += q[a] > 0 ? q[a] * q[a] : 0;
    if (q[a] > inside) inside = q[a];
  }
  return outside > 0 ? sqrt(outside) : inside;
}
static const char *grid_class(const tvdb_grid_t *g) {
  for (size_t i = 0; i < g->metadata.count; ++i)
    if (g->metadata.entries[i].name && !strcmp(g->metadata.entries[i].name, "class") &&
        g->metadata.entries[i].value.type == TVDB_VALUE_STRING)
      return g->metadata.entries[i].value.u.s.str;
  return "";
}
typedef double (*analytic_fn)(const double p[3]);
/* Every active voxel matches the analytic field within tol, and the band
 * limits hold. Returns the active count via *active (0 on failure). */
static int check_against(const tvdb_grid_t *g, double h, float ext, float in,
                         analytic_fn f, double tol, size_t *active) {
  tvdb_sparse_grid sg = {0};
  if (!tvdb_grid_to_sparse(g, &sg)) return 0;
  int ok = 1;
  for (size_t i = 0; i < sg.count && ok; ++i) {
    const double p[3] = {sg.coords[i].x * h, sg.coords[i].y * h, sg.coords[i].z * h};
    const double ref = f(p);
    const float v = sg.values[i];
    if (!(v > -in && v < ext) || fabs(v - ref) > tol) {
      fprintf(stderr, "voxel (%d %d %d): %g vs %g\n", sg.coords[i].x, sg.coords[i].y,
              sg.coords[i].z, v, ref);
      ok = 0;
    }
  }
  *active = sg.count;
  tvdb_sparse_grid_free(&sg);
  return ok;
}
static double sphere_sdf(const double p[3]) {
  return sqrt(p[0] * p[0] + p[1] * p[1] + p[2] * p[2]) - 1;
}
static float value_at(const tvdb_grid_t *g, int x, int y, int z) {
  tvdb_tree_index p = {0};
  if (tvdb_tree_index_create(g, 1, &p, NULL) != TVDB_OK) return NAN;
  const int32_t c[3] = {x, y, z};
  const float v = tvdb_tree_get(&p, c, NULL);
  tvdb_tree_index_destroy(&p);
  return v;
}
static int same_grid(const tvdb_grid_t *a, const tvdb_grid_t *b) {
  tvdb_sparse_grid sa = {0}, sb = {0};
  int ok = tvdb_grid_to_sparse(a, &sa) && tvdb_grid_to_sparse(b, &sb) &&
           sa.count == sb.count &&
           !memcmp(sa.coords, sb.coords, sa.count * sizeof(*sa.coords)) &&
           !memcmp(sa.values, sb.values, sa.count * sizeof(*sa.values));
  tvdb_sparse_grid_free(&sa);
  tvdb_sparse_grid_free(&sb);
  return ok;
}

/* Same active voxels with values within tol (face vertex order changes the
 * float rounding of closest-point distances, not their sign). */
static int close_grid(const tvdb_grid_t *a, const tvdb_grid_t *b, float tol) {
  tvdb_sparse_grid sa = {0}, sb = {0};
  int ok = tvdb_grid_to_sparse(a, &sa) && tvdb_grid_to_sparse(b, &sb) &&
           sa.count == sb.count &&
           !memcmp(sa.coords, sb.coords, sa.count * sizeof(*sa.coords));
  for (size_t i = 0; ok && i < sa.count; ++i) ok = fabsf(sa.values[i] - sb.values[i]) <= tol;
  tvdb_sparse_grid_free(&sa);
  tvdb_sparse_grid_free(&sb);
  return ok;
}

int main(void) {
  tvdb_error_t err;
  tvdb_triangle_mesh box = {0}, sphere = {0}, open = {0};
  CHECK(make_box(&box, -1) && make_box(&open, 1) && make_sphere(&sphere, 4));
  const double h = 0.1;
  tvdb_mesh_level_set_options_t o = {0};
  o.voxel_size = (float)h;
  o.exterior_width = o.interior_width = 0.3f;
  tvdb_mesh_level_set_result_t r;
  size_t active = 0;

  /* Winding numbers: inside a closed box 1, outside 0, inside-out -1. */
  {
    tvdb_winding_t *fast = NULL, *exact = NULL;
    CHECK(tvdb_winding_create(&box, TVDB_WINDING_FAST, &fast, &err) == TVDB_OK);
    CHECK(tvdb_winding_create(&box, TVDB_WINDING_EXACT, &exact, &err) == TVDB_OK);
    const double in[3] = {0.1, -0.2, 0.3}, out[3] = {2.5, 0, 0};
    CHECK(fabs(tvdb_winding_eval(exact, in) - 1) < 1e-9);
    CHECK(fabs(tvdb_winding_eval(exact, out)) < 1e-9);
    CHECK(fabs(tvdb_winding_eval(fast, in) - 1) < 1e-6);
    CHECK(fabs(tvdb_winding_eval(fast, out)) < 1e-2);
    tvdb_winding_destroy(fast);
    tvdb_winding_destroy(exact);
    tvdb_winding_t *big = NULL;
    CHECK(tvdb_winding_create(&sphere, TVDB_WINDING_FAST, &big, &err) == TVDB_OK);
    const double far[3] = {5, 4, 3}, centre[3] = {0, 0, 0}, near_in[3] = {0.95, 0, 0};
    CHECK(fabs(tvdb_winding_eval(big, far)) < 1e-2);
    CHECK(fabs(tvdb_winding_eval(big, centre) - 1) < 1e-2);
    CHECK(fabs(tvdb_winding_eval(big, near_in) - 1) < 1e-2);
    tvdb_winding_destroy(big);
  }

  /* Box: exact distances (the closest-face distance is the box SDF). */
  tvdb_grid_t grid = {0};
  CHECK(tvdb_mesh_to_level_set(&box, &o, NULL, &grid, &r, &err) == TVDB_OK);
  CHECK(!strcmp(grid_class(&grid), "level set"));
  CHECK(check_against(&grid, h, o.exterior_width, o.interior_width, box_sdf, 1e-5, &active));
  CHECK(active == r.active_voxels && active > 1000 && r.max_distance < 0.3 + 1e-6);
  CHECK(value_at(&grid, 0, 0, 0) == -0.3f);  /* flood-filled interior tile */
  CHECK(value_at(&grid, 40, 0, 0) == 0.3f);  /* background */

  /* Inside-out and open boxes keep the sign (|winding| > 1/2). */
  {
    tvdb_triangle_mesh flipped = {0};
    CHECK(make_box(&flipped, -1));
    for (size_t i = 0; i < flipped.face_count; ++i) {
      const uint32_t t = flipped.faces[i].v1;
      flipped.faces[i].v1 = flipped.faces[i].v2;
      flipped.faces[i].v2 = t;
    }
    tvdb_grid_t g2 = {0};
    CHECK(tvdb_mesh_to_level_set(&flipped, &o, NULL, &g2, NULL, &err) == TVDB_OK);
    CHECK(close_grid(&grid, &g2, 1e-6f));
    tvdb_grid_destroy_owned(&g2);
    mesh_free(&flipped);
    CHECK(tvdb_mesh_to_level_set(&open, &o, NULL, &g2, NULL, &err) == TVDB_OK);
    CHECK(value_at(&g2, 0, 0, 0) < 0);
    tvdb_grid_destroy_owned(&g2);
  }

  /* Sphere: mesh chordal error of a level-4 icosphere is below 0.002. */
  {
    tvdb_grid_t g3 = {0};
    o.sign = TVDB_LEVEL_SET_SIGN_WINDING_FAST;
    CHECK(tvdb_mesh_to_level_set(&sphere, &o, NULL, &g3, &r, &err) == TVDB_OK);
    CHECK(check_against(&g3, h, o.exterior_width, o.interior_width, sphere_sdf, 0.003,
                        &active));
    CHECK(value_at(&g3, 0, 0, 0) == -0.3f);
    /* Same grid with any worker count and with exact winding signs. */
    for (size_t threads = 1; threads <= 4; threads += 3) {
      tvdb_thread_pool_t *pool = NULL;
      tvdb_grid_t g4 = {0};
      CHECK(tvdb_thread_pool_create(threads, &pool, &err) == TVDB_OK);
      CHECK(tvdb_mesh_to_level_set(&sphere, &o, pool, &g4, NULL, &err) == TVDB_OK);
      CHECK(same_grid(&g3, &g4));
      tvdb_grid_destroy_owned(&g4);
      tvdb_thread_pool_destroy(pool);
    }
    tvdb_mesh_level_set_options_t ox = o;
    ox.sign = TVDB_LEVEL_SET_SIGN_WINDING_EXACT;
    tvdb_grid_t g5 = {0};
    CHECK(tvdb_mesh_to_level_set(&sphere, &ox, NULL, &g5, NULL, &err) == TVDB_OK);
    CHECK(same_grid(&g3, &g5));
    tvdb_grid_destroy_owned(&g5);

    /* VDB round trip keeps values, class and transform. */
    tvdb_file_t file, reloaded = {0};
    tvdb_file_init_for_write(&file, NULL);
    file.grids = &g3;
    file.num_grids = 1;
    uint8_t *bytes = NULL;
    size_t size = 0;
    CHECK(tvdb_write_to_memory(&file, TVDB_COMPRESS_ZIP | TVDB_COMPRESS_ACTIVE_MASK, 0,
                               &bytes, &size, &err) == TVDB_OK);
    CHECK(tvdb_file_open_memory(&reloaded, bytes, size, NULL, &err) == TVDB_OK);
    CHECK(tvdb_read_all_grids(&reloaded, &err) == TVDB_OK && reloaded.num_grids == 1);
    CHECK(same_grid(&g3, reloaded.grids));
    CHECK(!strcmp(grid_class(reloaded.grids), "level set"));
    CHECK(reloaded.grids[0].transform.voxel_size[0] == (double)o.voxel_size);
    tvdb_file_close(&reloaded);
    free(bytes);
    tvdb_grid_destroy_owned(&g3);
  }

  /* Failures preserve out. */
  {
    tvdb_mesh_level_set_options_t bad = o;
    bad.voxel_size = 0;
    CHECK(tvdb_mesh_to_level_set(&box, &bad, NULL, &grid, NULL, &err) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    bad = o;
    bad.max_voxels = 100;
    CHECK(tvdb_mesh_to_level_set(&box, &bad, NULL, &grid, NULL, &err) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    box.faces[0].v1 = 99;
    CHECK(tvdb_mesh_to_level_set(&box, &o, NULL, &grid, NULL, &err) ==
          TVDB_ERROR_INVALID_DATA);
    box.faces[0].v1 = 2;
    CHECK(check_against(&grid, h, o.exterior_width, o.interior_width, box_sdf, 1e-5,
                        &active));
  }
  tvdb_grid_destroy_owned(&grid);
  mesh_free(&box);
  mesh_free(&open);
  mesh_free(&sphere);
  printf("test_mesh_level_set: ok\n");
  return 0;
}
