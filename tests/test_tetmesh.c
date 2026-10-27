/* Isosurface stuffing: analytic sphere and box fields, the mesh -> level set
 * -> tets path, watertight outward boundaries, orientation, volume, dihedral
 * bounds, determinism across worker counts and failure handling. */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tinyvdb_sparse_tools.h"
#include "tinyvdb_tetmesh.h"

#define TEST_PI 3.14159265358979323846

#define CHECK(x)                                                    \
  do {                                                              \
    if (!(x)) {                                                     \
      fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #x);      \
      return 1;                                                     \
    }                                                               \
  } while (0)

static int sphere(const double p[3], float *v, void *user) {
  (void)user;
  *v = (float)(sqrt(p[0] * p[0] + p[1] * p[1] + p[2] * p[2]) - 1.0);
  return 1;
}
/* Lattice samples are zero; fail or return NaN at the extra center probe. */
static int failing_center(const double p[3], float *v, void *user) {
  for (int i = 0; i < 3; ++i) {
    if (2 * p[i] != floor(2 * p[i])) {
      *v = NAN;
      return *(const int *)user;
    }
  }
  *v = 0;
  return 1;
}
static int box(const double p[3], float *v, void *user) {
  (void)user;
  double out = 0, in = -1e300;
  for (int a = 0; a < 3; ++a) {
    const double q = fabs(p[a]) - (a == 0 ? 1.0 : 0.5);
    out += q > 0 ? q * q : 0;
    if (q > in) in = q;
  }
  *v = (float)(out > 0 ? sqrt(out) : in);
  return 1;
}

/* Every undirected boundary edge is used by exactly two boundary triangles in
 * opposite directions (closed, consistently oriented). Returns the Euler
 * characteristic V - E + F of the boundary, or -1000 on failure. */
static int boundary_euler(const tvdb_tet_mesh *m) {
  const size_t ne = 3 * m->boundary_count;
  int64_t *e = (int64_t *)malloc(ne * sizeof(int64_t));
  char *used = (char *)calloc(m->vertex_count ? m->vertex_count : 1, 1);
  if (!e || !used) return -1000;
  for (size_t f = 0; f < m->boundary_count; ++f)
    for (int k = 0; k < 3; ++k) {
      const int64_t a = m->boundary[3 * f + k], b = m->boundary[3 * f + (k + 1) % 3];
      e[3 * f + k] = a * (int64_t)m->vertex_count + b;
      used[a] = 1;
    }
  /* Each directed edge must appear once and its reverse once. */
  int ok = 1;
  size_t directed = 0;
  for (size_t i = 0; i < ne && ok; ++i) {
    const int64_t a = e[i] / (int64_t)m->vertex_count, b = e[i] % (int64_t)m->vertex_count;
    const int64_t rev = b * (int64_t)m->vertex_count + a;
    size_t same = 0, back = 0;
    for (size_t j = 0; j < ne; ++j) {
      same += e[j] == e[i];
      back += e[j] == rev;
    }
    if (same != 1 || back != 1) ok = 0;
    ++directed;
  }
  size_t v = 0;
  for (size_t i = 0; i < m->vertex_count; ++i) v += used[i];
  free(e);
  free(used);
  if (!ok) return -1000;
  return (int)v - (int)(directed / 2) + (int)m->boundary_count;
}
static int same_mesh(const tvdb_tet_mesh *a, const tvdb_tet_mesh *b) {
  return a->vertex_count == b->vertex_count && a->tet_count == b->tet_count &&
         a->boundary_count == b->boundary_count &&
         !memcmp(a->positions, b->positions, 3 * a->vertex_count * sizeof(float)) &&
         !memcmp(a->tets, b->tets, 4 * a->tet_count * sizeof(int32_t)) &&
         !memcmp(a->boundary, b->boundary, 3 * a->boundary_count * sizeof(int32_t));
}

int main(void) {
  tvdb_error_t err;
  tvdb_stuffing_options_t o = {0};
  o.spacing = 0.1;
  const double lo[3] = {-1, -1, -1}, hi[3] = {1, 1, 1};
  tvdb_tet_mesh m = {0};
  tvdb_tet_mesh_quality_t q;

  /* Sphere. */
  CHECK(tvdb_sdf_to_tet_mesh(sphere, NULL, lo, hi, &o, NULL, &m, &err) == TVDB_OK);
  CHECK(tvdb_tet_mesh_quality(&m, &q, &err) == TVDB_OK);
  printf("sphere: %zu verts %zu tets %zu boundary, dihedral %.2f..%.2f, volume %.5f\n",
         m.vertex_count, m.tet_count, m.boundary_count, q.min_dihedral, q.max_dihedral,
         q.volume);
  CHECK(m.tet_count > 1000 && q.inverted == 0);
  CHECK(fabs(q.volume - 4.0 / 3.0 * TEST_PI) < 0.02 * 4.0 / 3.0 * TEST_PI);
  CHECK(boundary_euler(&m) == 2);
  for (size_t f = 0; f < 3 * m.boundary_count; ++f) {
    const float *p = m.positions + 3 * (size_t)m.boundary[f];
    CHECK(fabs(sqrt(p[0] * p[0] + p[1] * p[1] + p[2] * p[2]) - 1) < 0.01);
  }
  const double sphere_min = q.min_dihedral, sphere_max = q.max_dihedral;
  CHECK(sphere_min > 5 && sphere_max < 175);

  /* Deterministic with any worker count. */
  for (size_t threads = 1; threads <= 4; threads += 3) {
    tvdb_thread_pool_t *pool = NULL;
    tvdb_tet_mesh m2 = {0};
    CHECK(tvdb_thread_pool_create(threads, &pool, &err) == TVDB_OK);
    CHECK(tvdb_sdf_to_tet_mesh(sphere, NULL, lo, hi, &o, pool, &m2, &err) == TVDB_OK);
    CHECK(same_mesh(&m, &m2));
    tvdb_tet_mesh_free(&m2);
    tvdb_thread_pool_destroy(pool);
  }

  /* Box with sharp edges (2 x 1 x 1). */
  {
    tvdb_tet_mesh b = {0};
    const double blo[3] = {-1, -0.5, -0.5}, bhi[3] = {1, 0.5, 0.5};
    CHECK(tvdb_sdf_to_tet_mesh(box, NULL, blo, bhi, &o, NULL, &b, &err) == TVDB_OK);
    CHECK(tvdb_tet_mesh_quality(&b, &q, &err) == TVDB_OK);
    printf("box: %zu tets, dihedral %.2f..%.2f, volume %.5f\n", b.tet_count, q.min_dihedral,
           q.max_dihedral, q.volume);
    CHECK(q.inverted == 0 && fabs(q.volume - 2.0) < 0.05 && boundary_euler(&b) == 2);
    tvdb_tet_mesh_free(&b);
  }

  /* Mesh -> level set -> tets. */
  {
    /* Octahedron-free path: a level set of the analytic sphere via a coarse
     * icosahedral mesh is enough to exercise tree sampling and tiles. */
    tvdb_triangle_mesh mesh = {0};
    const int nlat = 24, nlon = 48;
    mesh.vertex_count = (size_t)(nlat - 1) * nlon + 2;
    mesh.vertices = (tvdb_vec3f *)malloc(mesh.vertex_count * sizeof(tvdb_vec3f));
    mesh.faces = (tvdb_triangle *)malloc((size_t)2 * nlat * nlon * sizeof(tvdb_triangle));
    CHECK(mesh.vertices && mesh.faces);
    mesh.vertices[0] = (tvdb_vec3f){0, 0, 1};
    mesh.vertices[1] = (tvdb_vec3f){0, 0, -1};
    for (int i = 1; i < nlat; ++i)
      for (int j = 0; j < nlon; ++j) {
        const double th = TEST_PI * i / nlat, ph = 2 * TEST_PI * j / nlon;
        mesh.vertices[2 + (size_t)(i - 1) * nlon + j] =
            (tvdb_vec3f){(float)(sin(th) * cos(ph)), (float)(sin(th) * sin(ph)), (float)cos(th)};
      }
#define RING(i, j) (uint32_t)(2 + (size_t)((i) - 1) * nlon + (size_t)(((j) % nlon + nlon) % nlon))
    size_t nf = 0;
    for (int j = 0; j < nlon; ++j) {
      mesh.faces[nf++] = (tvdb_triangle){0, RING(1, j), RING(1, j + 1)};
      mesh.faces[nf++] = (tvdb_triangle){1, RING(nlat - 1, j + 1), RING(nlat - 1, j)};
    }
    for (int i = 1; i + 1 < nlat; ++i)
      for (int j = 0; j < nlon; ++j) {
        mesh.faces[nf++] = (tvdb_triangle){RING(i, j), RING(i + 1, j), RING(i + 1, j + 1)};
        mesh.faces[nf++] = (tvdb_triangle){RING(i, j), RING(i + 1, j + 1), RING(i, j + 1)};
      }
#undef RING
    mesh.face_count = nf;
    tvdb_mesh_level_set_options_t lo2 = {0};
    lo2.voxel_size = 0.05f;
    lo2.exterior_width = lo2.interior_width = 0.25f;
    tvdb_grid_t g = {0};
    CHECK(tvdb_mesh_to_level_set(&mesh, &lo2, NULL, &g, NULL, &err) == TVDB_OK);
    tvdb_stuffing_options_t so = {0};
    so.spacing = 0.15;
    tvdb_tet_mesh t = {0};
    CHECK(tvdb_level_set_to_tet_mesh(&g, &so, NULL, &t, &err) == TVDB_OK);
    CHECK(tvdb_tet_mesh_quality(&t, &q, &err) == TVDB_OK);
    printf("level set: %zu tets, dihedral %.2f..%.2f, volume %.5f\n", t.tet_count,
           q.min_dihedral, q.max_dihedral, q.volume);
    CHECK(q.inverted == 0 && boundary_euler(&t) == 2);
    CHECK(fabs(q.volume - 4.0 / 3.0 * TEST_PI) < 0.05 * 4.0 / 3.0 * TEST_PI);
    /* The level-set sampler caches tree lookups per range; the mesh must not
     * depend on how many ranges run at once. */
    for (size_t threads = 2; threads <= 4; threads += 2) {
      tvdb_thread_pool_t *pool = NULL;
      tvdb_tet_mesh t2 = {0};
      CHECK(tvdb_thread_pool_create(threads, &pool, &err) == TVDB_OK);
      CHECK(tvdb_level_set_to_tet_mesh(&g, &so, pool, &t2, &err) == TVDB_OK);
      printf("level set, %zu threads: %zu tets\n", threads, t2.tet_count);
      CHECK(same_mesh(&t, &t2));
      tvdb_tet_mesh_free(&t2);
      tvdb_thread_pool_destroy(pool);
    }
    tvdb_tet_mesh_free(&t);
    tvdb_grid_destroy_owned(&g);
    free(mesh.vertices);
    free(mesh.faces);
  }

  /* A failed or non-finite center probe must preserve the existing mesh. */
  {
    tvdb_stuffing_options_t probe = {0};
    const double pmin[3] = {0, 0, 0}, pmax[3] = {1, 1, 1};
    float *original = m.positions;
    size_t vertices = m.vertex_count, tets = m.tet_count;
    probe.spacing = 1;
    for (int mode = 0; mode < 2; ++mode) {
      CHECK(tvdb_sdf_to_tet_mesh(failing_center, &mode, pmin, pmax, &probe,
                                 NULL, &m, &err) == TVDB_ERROR_INVALID_DATA);
      CHECK(err.status == TVDB_ERROR_INVALID_DATA);
      CHECK(m.positions == original && m.vertex_count == vertices && m.tet_count == tets);
    }
  }

  /* Failures preserve out. */
  {
    tvdb_stuffing_options_t bad = o;
    bad.spacing = 0;
    CHECK(tvdb_sdf_to_tet_mesh(sphere, NULL, lo, hi, &bad, NULL, &m, &err) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    bad = o;
    bad.max_tets = 10;
    CHECK(tvdb_sdf_to_tet_mesh(sphere, NULL, lo, hi, &bad, NULL, &m, &err) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    bad = o;
    bad.max_lattice_vertices = 100;
    CHECK(tvdb_sdf_to_tet_mesh(sphere, NULL, lo, hi, &bad, NULL, &m, &err) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(tvdb_tet_mesh_quality(&m, &q, &err) == TVDB_OK && q.inverted == 0 &&
          boundary_euler(&m) == 2);
  }
  tvdb_tet_mesh_free(&m);
  printf("test_tetmesh: ok\n");
  return 0;
}
