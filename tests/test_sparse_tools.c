#include <stdio.h>

#include "sdf_tree_fixture.h"
#include "tinyvdb_mesh_conversion.h"
#include "tinyvdb_sparse_tools.h"
#include "tinyvdb_tree_internal.h"
#define CHECK(x)                                                        \
  do {                                                                  \
    if (!(x)) {                                                         \
      fprintf(stderr, "line %d: %s (%s)\n", __LINE__, #x, err.message); \
      return 1;                                                         \
    }                                                                   \
  } while (0)
static int make_sphere(tvdb_grid_t* out, int radius, float band) {
  tvdb_grid_t tmpl;
  sdf_fixture_template(&tmpl);
  tvdb_sparse_grid sg = {0};
  if (!tvdb_sparse_grid_reserve(&sg, 20000)) return 0;
  for (int x = -radius - 3; x <= radius + 3; ++x)
    for (int y = -radius - 3; y <= radius + 3; ++y)
      for (int z = -radius - 3; z <= radius + 3; ++z) {
        float phi = 2 * (sqrtf((float)(x * x + y * y + z * z)) - radius);
        if (fabsf(phi) < band) {
          sg.coords[sg.count] = (tvdb_vec3i){x, y, z};
          sg.values[sg.count++] = phi;
        }
      }
  tvdb_grid_t g = {0};
  int ok = tvdb_grid_from_sparse_using_template(&tmpl, &sg, "sphere", band, &g);
  if (ok)
    ok = tvdb_grid_signed_flood_fill(&g, band, -band, out, NULL) == TVDB_OK;
  tvdb_grid_destroy_owned(&g);
  tvdb_sparse_grid_free(&sg);
  return ok;
}
static double volume(const tvdb_triangle_mesh* m) {
  double s = 0;
  for (size_t i = 0; i < m->face_count; ++i) {
    tvdb_triangle f = m->faces[i];
    tvdb_vec3f a = m->vertices[f.v0], b = m->vertices[f.v1],
               c = m->vertices[f.v2];
    s += (double)a.x * (b.y * c.z - b.z * c.y) +
         (double)a.y * (b.z * c.x - b.x * c.z) +
         (double)a.z * (b.x * c.y - b.y * c.x);
  }
  return s / 6;
}
static int face_boundary(const int32_t c[3], const int64_t n[3],
                         tvdb_boundary_kind_t* kind, double* value,
                         void* user) {
  int mode = *(int*)user;
  *kind = TVDB_BOUNDARY_DIRICHLET;
  *value = n[0] + 2 * n[1] - .5 * n[2] + 3;
  if (mode == 1) {
    *kind = n[0] != c[0] ? TVDB_BOUNDARY_DIRICHLET : TVDB_BOUNDARY_NEUMANN;
    *value = *kind == TVDB_BOUNDARY_DIRICHLET ? (double)n[0] : 0;
  }
  if (mode == 2 || mode == 3) {
    *kind = TVDB_BOUNDARY_NEUMANN;
    *value = 0;
  }
  if (mode == 4) *value = NAN;
  return mode != 5;
}
static double coefficient(const int32_t c[3], const int64_t n[3], void* user) {
  return *(int*)user == 6 ? NAN : 1 + .03 * ((double)c[0] + n[0]);
}
int main(void) {
  tvdb_error_t err = {0};
  tvdb_grid_t sphere = {0}, rebuilt = {0}, sampled = {0}, empty = {0};
  CHECK(make_sphere(&sphere, 5, 4));
  tvdb_grid_t before = sphere;
  tvdb_level_set_rebuild_result_t info = {0};
  CHECK(tvdb_grid_level_set_track(&sphere, 3, 3, 200000, &rebuilt, &info,
                                  &err) == TVDB_OK);
  CHECK(info.active_voxels > tvdb_grid_active_voxel_count(&sphere));
  CHECK(info.surface_cells && info.candidate_voxels >= info.active_voxels);
  CHECK(!memcmp(&before, &sphere, sizeof(before)));
  tvdb_tree_index pi = {0}, ri = {0};
  CHECK(tvdb_tree_index_create(&sphere, 1, &pi, &err) == TVDB_OK);
  CHECK(tvdb_tree_index_create(&rebuilt, 1, &ri, &err) == TVDB_OK);
  double maxerr = 0;
  size_t visited = 0;
  for (int x = -8; x <= 8; ++x)
    for (int y = -8; y <= 8; ++y)
      for (int z = -8; z <= 8; ++z) {
        int32_t c[3] = {x, y, z};
        int active;
        float v = tvdb_tree_get(&ri, c, &active);
        double d = sqrt((double)x * x + (double)y * y + (double)z * z) - 5;
        if (active) {
          CHECK(v > -3 && v < 3);
          maxerr = fmax(maxerr, fabs(v - d));
          ++visited;
        }
        if (d > 3.5) CHECK(v == 3 && !active);
        if (d < -3.5) CHECK(v == -3 && !active);
      }
  CHECK(visited == info.active_voxels);
  CHECK(maxerr < .3);
  tvdb_tree_diagnostics_t diag;
  CHECK(tvdb_grid_diagnose(&rebuilt, TVDB_TREE_DIAG_LEVEL_SET, 0, 0, &diag,
                           &err) == TVDB_OK &&
        diag.valid);
  tvdb_grid_t preserved = rebuilt;
  tvdb_level_set_rebuild_result_t preserved_report = info;
  CHECK(tvdb_grid_level_set_track(&sphere, 3, 3, 10, &rebuilt, &info, &err) !=
        TVDB_OK);
  CHECK(!memcmp(&preserved, &rebuilt, sizeof(rebuilt)) &&
        !memcmp(&preserved_report, &info, sizeof(info)));
  CHECK(tvdb_grid_level_set_track(&sphere, 3, 3, 0, &sphere, &info, &err) ==
        TVDB_ERROR_INVALID_ARGUMENT);

  tvdb_grid_t asymmetric = {0};
  tvdb_tree_index ai = {0};
  CHECK(tvdb_grid_level_set_rebuild(&sphere, .5f, 2, 3, 200000, &asymmetric,
                                    NULL, &err) == TVDB_OK);
  CHECK(tvdb_tree_index_create(&asymmetric, 1, &ai, &err) == TVDB_OK);
  int32_t center_coord[3] = {0, 0, 0}, near_coord[3] = {7, 0, 0},
          far_coord[3] = {8, 0, 0};
  int activity;
  CHECK(tvdb_tree_get(&ai, center_coord, &activity) == -3 && !activity);
  CHECK(fabs(tvdb_tree_get(&ai, near_coord, &activity) - 1.75) < 1e-4 &&
        activity);
  CHECK(tvdb_tree_get(&ai, far_coord, &activity) == 2 && !activity);
  tvdb_tree_index_destroy(&ai);
  tvdb_grid_destroy_owned(&asymmetric);
  tvdb_triangle_mesh mesh = {0}, adaptive = {0}, dense_mesh = {0};
  CHECK(tvdb_grid_volume_to_mesh(&sphere, 0, 0, 100000, &mesh, &err) ==
        TVDB_OK);
  CHECK(mesh.vertex_count && mesh.face_count && volume(&mesh) > 0);
  tvdb_dense_grid dense = {0};
  tvdb_dense_grid_init(&dense, 17, 17, 17);
  CHECK(dense.data);
  dense.ox = dense.oy = dense.oz = -8.5f;
  dense.voxel_size = 1;
  for (int z = 0; z < 17; ++z)
    for (int y = 0; y < 17; ++y)
      for (int x = 0; x < 17; ++x) {
        int32_t c[3] = {x - 8, y - 8, z - 8};
        dense.data[((size_t)z * 17 + y) * 17 + x] = tvdb_tree_get(&pi, c, NULL);
      }
  CHECK(tvdb_sdf_to_mesh_ex(&dense, 0, TVDB_MESH_WINDING_OUTWARD, NULL,
                            &dense_mesh, NULL, &err) == TVDB_OK);
  CHECK(dense_mesh.vertex_count == mesh.vertex_count &&
        dense_mesh.face_count == mesh.face_count);
  CHECK(fabs(volume(&mesh) - volume(&dense_mesh)) < 1e-4);
  CHECK(tvdb_grid_volume_to_mesh(&sphere, 0, 1, 100000, &adaptive, &err) ==
        TVDB_OK);
  CHECK(adaptive.vertex_count < mesh.vertex_count &&
        adaptive.face_count < mesh.face_count);
  for (size_t i = 0; i < adaptive.vertex_count; ++i) {
    double best = INFINITY;
    tvdb_vec3f a = adaptive.vertices[i];
    for (size_t j = 0; j < mesh.vertex_count; ++j) {
      tvdb_vec3f b = mesh.vertices[j];
      best = fmin(best, hypot(hypot((double)a.x - b.x, (double)a.y - b.y),
                              (double)a.z - b.z));
    }
    CHECK(best <= 1);
  }
  tvdb_triangle_mesh keep = mesh;
  CHECK(tvdb_grid_volume_to_mesh(&sphere, 0, 0, 1, &mesh, &err) != TVDB_OK);
  CHECK(!memcmp(&keep, &mesh, sizeof(mesh)));
  tvdb_transform_t transform = sphere.transform;
  CHECK(tvdb_grid_resample(&sphere, &transform, TVDB_SAMPLE_NEAREST, 200000,
                           &sampled, &err) == TVDB_OK);
  tvdb_tree_index si = {0};
  CHECK(tvdb_tree_index_create(&sampled, 1, &si, &err) == TVDB_OK);
  for (int x = -8; x <= 8; ++x)
    for (int y = -8; y <= 8; ++y)
      for (int z = -8; z <= 8; ++z) {
        int32_t c[3] = {x, y, z};
        int a, b;
        CHECK(tvdb_tree_get(&pi, c, &a) == tvdb_tree_get(&si, c, &b) && a == b);
      }
  tvdb_tree_index_destroy(&si);
  tvdb_grid_destroy_owned(&sampled);
  /* Analytic affine field, separate source/target maps, eight-tap activity. */
  tvdb_grid_t tmpl, field = {0};
  sdf_fixture_template(&tmpl);
  tvdb_sparse_grid sg = {0};
  CHECK(tvdb_sparse_grid_reserve(&sg, 125));
  for (int x = -2; x <= 2; ++x)
    for (int y = -2; y <= 2; ++y)
      for (int z = -2; z <= 2; ++z) {
        sg.coords[sg.count] = (tvdb_vec3i){x, y, z};
        sg.values[sg.count++] = x + 2 * y - .5f * z;
      }
  CHECK(tvdb_grid_from_sparse_using_template(&tmpl, &sg, "field", 0, &field));
  transform.type = TVDB_TRANSFORM_AFFINE;
  memset(transform.matrix, 0, sizeof(transform.matrix));
  transform.matrix[0][1] = -.5;
  transform.matrix[1][0] = .5;
  transform.matrix[0][2] = .2;
  transform.matrix[2][2] = .75;
  transform.matrix[3][3] = 1;
  transform.matrix[0][3] = .25;
  CHECK(tvdb_grid_resample(&field, &transform, TVDB_SAMPLE_LINEAR, 100000,
                           &sampled, &err) == TVDB_OK);
  CHECK(tvdb_tree_index_create(&sampled, 1, &si, &err) == TVDB_OK);
  for (int x = -1; x <= 1; ++x)
    for (int y = -1; y <= 1; ++y)
      for (int z = -1; z <= 1; ++z) {
        int32_t c[3] = {x, y, z};
        int active;
        double expected = (-.5 * y + .2 * z + .25) + x - .375 * z;
        CHECK(fabs(tvdb_tree_get(&si, c, &active) - expected) < 1e-6 && active);
      }
  CHECK(!memcmp(&sampled.transform, &transform, sizeof(transform)));
  tvdb_tree_index_destroy(&si);
  tvdb_grid_destroy_owned(&sampled);
  /* Reflection flips winding in index space so world outward volume stays
   * positive. */
  tvdb_transform_t saved = sphere.transform;
  sphere.transform.type = TVDB_TRANSFORM_SCALE;
  sphere.transform.voxel_size[0] = -1;
  sphere.transform.voxel_size[1] = 2;
  sphere.transform.voxel_size[2] = 1;
  tvdb_triangle_mesh reflected = {0};
  CHECK(tvdb_grid_volume_to_mesh(&sphere, 0, 0, 100000, &reflected, &err) ==
        TVDB_OK);
  CHECK(volume(&reflected) > 0);
  tvdb_triangle_mesh_free(&reflected);
  CHECK(tvdb_grid_level_set_track(&sphere, 3, 3, 100000, &sampled, &info,
                                  &err) == TVDB_ERROR_UNSUPPORTED_TRANSFORM);
  sphere.transform = saved;
  /* Active tiles and fully inactive stored regions must both produce surfaces.
   */
  tvdb_grid_t tile = {0}, pruned = {0};
  sg.count = 0;
  CHECK(tvdb_sparse_grid_reserve(&sg, 512));
  for (int x = 0; x < 8; ++x)
    for (int y = 0; y < 8; ++y)
      for (int z = 0; z < 8; ++z) {
        sg.coords[sg.count] = (tvdb_vec3i){x, y, z};
        sg.values[sg.count++] = -1;
      }
  CHECK(tvdb_grid_from_sparse_using_template(&tmpl, &sg, "tile", 1, &tile));
  CHECK(tvdb_grid_prune(&tile, &pruned, &err) == TVDB_OK);
  CHECK(tvdb_grid_volume_to_mesh(&pruned, 0, 0, 100000, &reflected, &err) ==
            TVDB_OK &&
        reflected.face_count > 0);
  tvdb_triangle_mesh_free(&reflected);
  for (size_t i = 0; i < pruned.tree.num_nodes; ++i)
    if (pruned.tree.nodes[i].type == TVDB_NODE_INTERNAL)
      memset(pruned.tree.nodes[i].u.internal.value_mask.bits.data, 0,
             pruned.tree.nodes[i].u.internal.value_mask.bits.num_bytes);
  CHECK(tvdb_grid_volume_to_mesh(&pruned, 0, 0, 100000, &reflected, &err) ==
            TVDB_OK &&
        reflected.face_count > 0);
  tvdb_triangle_mesh_free(&reflected);
  CHECK(tvdb_grid_resample(&pruned, &saved, TVDB_SAMPLE_NEAREST, 100000,
                           &sampled, &err) == TVDB_OK);
  CHECK(tvdb_tree_index_create(&sampled, 1, &si, &err) == TVDB_OK);
  int32_t inside[3] = {3, 3, 3};
  int on;
  CHECK(tvdb_tree_get(&si, inside, &on) == -1 && !on);
  tvdb_tree_index_destroy(&si);
  tvdb_grid_destroy_owned(&sampled);
  /* Sparse manufactured variable-coefficient solution on an anisotropic grid.
   */
  tvdb_grid_t rhs = {0}, solution = {0};
  sg.count = 0;
  for (int x = 0; x < 4; ++x)
    for (int y = 0; y < 4; ++y)
      for (int z = 0; z < 4; ++z) {
        sg.coords[sg.count] = (tvdb_vec3i){x, y, z};
        sg.values[sg.count++] = -.24f;
      }
  CHECK(tvdb_grid_from_sparse_using_template(&tmpl, &sg, "rhs", 0, &rhs));
  rhs.transform.type = TVDB_TRANSFORM_SCALE;
  rhs.transform.voxel_size[0] = .5;
  rhs.transform.voxel_size[1] = 1;
  rhs.transform.voxel_size[2] = 2;
  int mode = 0;
  tvdb_sparse_poisson_options_t options = {300,           1e-6,        100000,
                                           face_boundary, coefficient, &mode};
  tvdb_poisson_result_t solved;
  CHECK(tvdb_grid_solve_poisson(&rhs, &options, &solution, &solved, &err) ==
            TVDB_OK &&
        solved.converged && solved.iterations > 0);
  CHECK(tvdb_tree_index_create(&solution, 1, &si, &err) == TVDB_OK);
  for (size_t i = 0; i < sg.count; ++i) {
    int32_t c[3] = {sg.coords[i].x, sg.coords[i].y, sg.coords[i].z};
    CHECK(fabs(tvdb_tree_get(&si, c, NULL) -
               (c[0] + 2 * c[1] - .5 * c[2] + 3)) < 2e-5);
  }
  tvdb_tree_index_destroy(&si);
  tvdb_grid_destroy_owned(&solution);
  mode = 1;
  options.coefficient = NULL;
  rhs.transform = tmpl.transform;
  for (size_t i = 0; i < rhs.tree.num_nodes; ++i)
    if (rhs.tree.nodes[i].type == TVDB_NODE_LEAF)
      memset(rhs.tree.nodes[i].u.leaf.data, 0,
             rhs.tree.nodes[i].u.leaf.data_size);
  CHECK(tvdb_grid_solve_poisson(&rhs, &options, &solution, &solved, &err) ==
            TVDB_OK &&
        solved.converged);
  CHECK(tvdb_tree_index_create(&solution, 1, &si, &err) == TVDB_OK);
  for (size_t i = 0; i < sg.count; ++i) {
    int32_t c[3] = {sg.coords[i].x, sg.coords[i].y, sg.coords[i].z};
    CHECK(fabs(tvdb_tree_get(&si, c, NULL) - c[0]) < 1e-5);
  }
  tvdb_tree_index_destroy(&si);
  tvdb_grid_destroy_owned(&rhs);
  /* Two disconnected pure-Neumann components, each requiring its own mean. */
  sg.count = 0;
  for (int group = 0; group < 2; ++group)
    for (int x = 0; x < 5; ++x) {
      sg.coords[sg.count] = (tvdb_vec3i){x, group * 100, 0};
      sg.values[sg.count++] = x == 0 ? -1 : x == 4 ? 1 : 0;
    }
  CHECK(tvdb_grid_from_sparse_using_template(&tmpl, &sg, "neumann", 0, &rhs));
  mode = 2;
  CHECK(tvdb_grid_solve_poisson(&rhs, &options, &solution, &solved, &err) ==
            TVDB_OK &&
        solved.converged);
  CHECK(tvdb_tree_index_create(&solution, 1, &si, &err) == TVDB_OK);
  for (size_t i = 0; i < sg.count; ++i) {
    int32_t c[3] = {sg.coords[i].x, sg.coords[i].y, 0};
    CHECK(fabs(tvdb_tree_get(&si, c, NULL) - (c[0] - 2)) < 1e-6);
  }
  tvdb_tree_index_destroy(&si);
  tvdb_grid_t keep_solution = solution;
  tvdb_poisson_result_t keep_solved = solved;
  *sdf_fixture_at(&rhs, 0, 0, 0) = 0;
  CHECK(tvdb_grid_solve_poisson(&rhs, &options, &solution, &solved, &err) ==
        TVDB_ERROR_INVALID_ARGUMENT);
  CHECK(!memcmp(&keep_solution, &solution, sizeof(solution)) &&
        keep_solved.iterations == solved.iterations &&
        keep_solved.converged == solved.converged &&
        keep_solved.initial_residual_norm == solved.initial_residual_norm &&
        keep_solved.final_residual_norm == solved.final_residual_norm);
  mode = 4;
  CHECK(tvdb_grid_solve_poisson(&rhs, &options, &solution, &solved, &err) ==
        TVDB_ERROR_INVALID_DATA);
  mode = 5;
  CHECK(tvdb_grid_solve_poisson(&rhs, &options, &solution, &solved, &err) ==
        TVDB_ERROR_INVALID_DATA);
  mode = 6;
  options.coefficient = coefficient;
  CHECK(tvdb_grid_solve_poisson(&rhs, &options, &solution, &solved, &err) ==
        TVDB_ERROR_INVALID_DATA);
  options.coefficient = NULL;
  mode = 0;
  options.max_iterations = 0;
  CHECK(tvdb_grid_solve_poisson(&rhs, &options, &solution, &solved, &err) ==
            TVDB_OK &&
        !solved.converged && solved.iterations == 0);
  options.max_iterations = 1;
  CHECK(tvdb_grid_solve_poisson(&rhs, &options, &solution, &solved, &err) ==
            TVDB_OK &&
        !solved.converged);
  tvdb_grid_t active_tile = {0};
  CHECK(tvdb_grid_prune(&tile, &active_tile, &err) == TVDB_OK);
  tvdb_sparse_poisson_options_t tile_options = {300,  1e-6, 10000,
                                                NULL, NULL, NULL};
  CHECK(tvdb_grid_solve_poisson(&active_tile, &tile_options, &solution, &solved,
                                &err) == TVDB_OK &&
        solved.converged);
  CHECK(tvdb_grid_active_voxel_count(&solution) == 512);
  tvdb_grid_destroy_owned(&active_tile);
  /* Empty trees and full negative int32 coordinates are supported by builders.
   */
  sg.count = 0;
  CHECK(tvdb_grid_from_sparse_using_template(&tmpl, &sg, "empty", 2, &empty));
  CHECK(tvdb_grid_resample(&empty, &saved, TVDB_SAMPLE_LINEAR, 0, &sampled,
                           &err) == TVDB_OK &&
        tvdb_grid_active_voxel_count(&sampled) == 0);
  tvdb_grid_destroy_owned(&sampled);
  CHECK(tvdb_grid_level_set_track(&empty, 3, 3, 0, &sampled, &info, &err) ==
            TVDB_OK &&
        info.active_voxels == 0);
  tvdb_grid_destroy_owned(&sampled);
  CHECK(tvdb_grid_solve_poisson(&empty, &options, &sampled, &solved, &err) ==
            TVDB_OK &&
        solved.converged);
  tvdb_grid_destroy_owned(&sampled);
  sg.count = 1;
  sg.coords[0] = (tvdb_vec3i){INT32_MIN, 0, 0};
  sg.values[0] = 1;
  CHECK(
      tvdb_grid_from_sparse_using_template(&tmpl, &sg, "extreme", 0, &sampled));
  CHECK(tvdb_tree_index_create(&sampled, 1, &si, &err) == TVDB_OK);
  tvdb_tree_index_destroy(&si);
  tvdb_grid_t extreme_copy = {0};
  CHECK(tvdb_grid_resample(&sampled, &saved, TVDB_SAMPLE_NEAREST, 1000,
                           &extreme_copy, &err) == TVDB_OK);
  CHECK(tvdb_grid_active_voxel_count(&extreme_copy) == 1);
  tvdb_grid_destroy_owned(&extreme_copy);
  CHECK(tvdb_grid_solve_poisson(&sampled, &tile_options, &extreme_copy, &solved,
                                &err) == TVDB_OK &&
        solved.converged);
  CHECK(tvdb_tree_index_create(&extreme_copy, 1, &si, &err) == TVDB_OK);
  int32_t extreme_coord[3] = {INT32_MIN, 0, 0};
  CHECK(fabs(tvdb_tree_get(&si, extreme_coord, NULL) - 1.0 / 6) < 1e-7);
  tvdb_tree_index_destroy(&si);
  tvdb_grid_destroy_owned(&extreme_copy);
  tvdb_grid_destroy_owned(&sampled);
  /* Two distant components must not cause a bounding-box allocation. */
  sg.count = 2;
  sg.coords[0] = (tvdb_vec3i){-1000000, 0, 0};
  sg.coords[1] = (tvdb_vec3i){1000000, 0, 0};
  sg.values[0] = sg.values[1] = -1;
  CHECK(
      tvdb_grid_from_sparse_using_template(&tmpl, &sg, "distant", 1, &sampled));
  CHECK(tvdb_grid_volume_to_mesh(&sampled, 0, 0, 1000, &reflected, &err) ==
        TVDB_OK);
  CHECK(reflected.face_count == 16 && reflected.vertex_count == 12);
  tvdb_triangle_mesh_free(&reflected);
  tvdb_grid_destroy_owned(&sampled);
  /* Failed array alias preflight must not free either overlapping buffer. */
  tvdb_triangle_mesh bad_mesh = {mesh.vertices,
                                 mesh.vertex_count,
                                 mesh.vertex_capacity,
                                 (tvdb_triangle*)mesh.vertices,
                                 1,
                                 1};
  CHECK(tvdb_grid_volume_to_mesh(&sphere, 0, 0, 100000, &bad_mesh, &err) ==
        TVDB_ERROR_INVALID_ARGUMENT);
  tvdb_grid_destroy_owned(&empty);
  tvdb_grid_destroy_owned(&solution);
  tvdb_grid_destroy_owned(&rhs);
  tvdb_grid_destroy_owned(&tile);
  tvdb_grid_destroy_owned(&pruned);
  tvdb_grid_destroy_owned(&field);
  tvdb_sparse_grid_free(&sg);
  tvdb_tree_index_destroy(&pi);
  tvdb_tree_index_destroy(&ri);
  tvdb_grid_destroy_owned(&sphere);
  tvdb_grid_destroy_owned(&rebuilt);
  tvdb_triangle_mesh_free(&mesh);
  tvdb_triangle_mesh_free(&adaptive);
  tvdb_triangle_mesh_free(&dense_mesh);
  tvdb_dense_grid_free(&dense);
  printf(
      "sparse tracking/resampling/meshing/PDE passed; sphere distance error "
      "%.6g\n",
      maxerr);
  return 0;
}
