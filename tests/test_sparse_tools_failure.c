#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static size_t calls, fail_at;
static void* fault_malloc(size_t n) {
  return ++calls == fail_at ? NULL : malloc(n);
}
static void* fault_calloc(size_t n, size_t s) {
  return ++calls == fail_at ? NULL : calloc(n, s);
}
static void* fault_realloc(void* p, size_t n) {
  return ++calls == fail_at ? NULL : realloc(p, n);
}
#define malloc fault_malloc
#define calloc fault_calloc
#define realloc fault_realloc
#include "../src/tinyvdb_sparse_tools.c"
#undef malloc
#undef calloc
#undef realloc
#include "sdf_tree_fixture.h"
#define CHECK(x)                                                            \
  do {                                                                      \
    if (!(x)) {                                                             \
      fprintf(stderr, "line %d fail=%zu: %s (%s)\n", __LINE__, fail_at, #x, \
              err.message);                                                 \
      return 1;                                                             \
    }                                                                       \
  } while (0)
static tvdb_status_t run(int op, const tvdb_grid_t* g, tvdb_grid_t* out,
                         tvdb_triangle_mesh* mesh,
                         tvdb_level_set_rebuild_result_t* rebuild,
                         tvdb_poisson_result_t* solve, tvdb_error_t* err) {
  tvdb_sparse_poisson_options_t opts = {100, 1e-6, 10000, NULL, NULL, NULL};
  if (op == 0)
    return tvdb_grid_resample(g, &g->transform, TVDB_SAMPLE_LINEAR, 10000, out,
                              err);
  if (op == 1) return tvdb_grid_volume_to_mesh(g, 0, .8, 10000, mesh, err);
  if (op == 2)
    return tvdb_grid_level_set_track(g, 2, 2, 10000, out, rebuild, err);
  return tvdb_grid_solve_poisson(g, &opts, out, solve, err);
}
int main(void) {
  tvdb_error_t err = {0};
  tvdb_grid_t tmpl, g = {0};
  sdf_fixture_template(&tmpl);
  tvdb_vec3i coords[27];
  float values[27];
  size_t n = 0;
  for (int x = 0; x < 3; ++x)
    for (int y = 0; y < 3; ++y)
      for (int z = 0; z < 3; ++z) {
        coords[n] = (tvdb_vec3i){x, y, z};
        values[n++] = -1;
      }
  tvdb_sparse_grid sg = {coords, values, 27, 0, 1, 0, 0, 0};
  CHECK(tvdb_grid_from_sparse_using_template(&tmpl, &sg, "fault", 1, &g));
  for (int op = 0; op < 4; ++op) {
    tvdb_grid_t out = {0};
    tvdb_triangle_mesh mesh = {0};
    tvdb_level_set_rebuild_result_t report = {0};
    tvdb_poisson_result_t solve = {0};
    calls = fail_at = 0;
    CHECK(run(op, &g, &out, &mesh, &report, &solve, &err) == TVDB_OK);
    size_t total = calls;
    tvdb_grid_destroy_owned(&out);
    tvdb_triangle_mesh_free(&mesh);
    for (size_t f = 1; f <= total; ++f) {
      tvdb_sparse_grid keep = {coords, values, 1, 0, 1, 0, 0, 0};
      CHECK(
          tvdb_grid_from_sparse_using_template(&tmpl, &keep, "keep", 9, &out));
      mesh.vertices = malloc(3 * sizeof(tvdb_vec3f));
      mesh.faces = malloc(sizeof(tvdb_triangle));
      CHECK(mesh.vertices && mesh.faces);
      mesh.vertex_count = mesh.vertex_capacity = 3;
      mesh.face_count = mesh.face_capacity = 1;
      memset(mesh.vertices, 0, 3 * sizeof(tvdb_vec3f));
      mesh.faces[0] = (tvdb_triangle){0, 1, 2};
      tvdb_grid_t old = out;
      tvdb_triangle_mesh old_mesh = mesh;
      memset(&report, 0x3a, sizeof(report));
      memset(&solve, 0x2b, sizeof(solve));
      tvdb_level_set_rebuild_result_t old_report = report;
      tvdb_poisson_result_t old_solve = solve;
      calls = 0;
      fail_at = f;
      CHECK(run(op, &g, &out, &mesh, &report, &solve, &err) ==
            TVDB_ERROR_OUT_OF_MEMORY);
      CHECK(!memcmp(&old, &out, sizeof(out)) &&
            !memcmp(&old_mesh, &mesh, sizeof(mesh)));
      CHECK(!memcmp(&report, &old_report, sizeof(report)) &&
            !memcmp(&solve, &old_solve, sizeof(solve)));
      fail_at = 0;
      tvdb_grid_destroy_owned(&out);
      tvdb_triangle_mesh_free(&mesh);
    }
    printf("sparse operation %d: %zu allocation failures checked\n", op, total);
  }
  tvdb_grid_destroy_owned(&g);
  return 0;
}
