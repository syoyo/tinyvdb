#include <openvdb/openvdb.h>
#include <openvdb/tools/Interpolation.h>
#include <openvdb/tools/LevelSetRebuild.h>
#include <openvdb/tools/PoissonSolver.h>
#include <openvdb/tools/SignedFloodFill.h>
#include <openvdb/tools/VolumeToMesh.h>

#include <cstdio>
#include <vector>

#include "sdf_tree_fixture.h"
#include "tinyvdb_sparse_tools.h"
#include "tinyvdb_tree_internal.h"
#define CHECK(x)                                                             \
  do {                                                                       \
    if (!(x)) {                                                              \
      std::fprintf(stderr, "line %d: %s (%s)\n", __LINE__, #x, err.message); \
      return 1;                                                              \
    }                                                                        \
  } while (0)
int main() {
  openvdb::initialize();
  tvdb_error_t err = {};
  tvdb_grid_t tmpl, source = {}, sampled = {}, rebuilt = {}, solution = {};
  sdf_fixture_template(&tmpl);
  std::vector<tvdb_vec3i> coords;
  std::vector<float> values;
  auto ref = openvdb::FloatGrid::create(4);
  auto a = ref->getAccessor();
  ref->setGridClass(openvdb::GRID_LEVEL_SET);
  for (int x = -8; x <= 8; ++x)
    for (int y = -8; y <= 8; ++y)
      for (int z = -8; z <= 8; ++z) {
        float v = 2 * (std::sqrt(float(x * x + y * y + z * z)) - 5);
        if (std::fabs(v) < 4) {
          coords.push_back({x, y, z});
          values.push_back(v);
          a.setValue(openvdb::Coord(x, y, z), v);
        }
      }
  tvdb_sparse_grid sg = {
      coords.data(), values.data(), coords.size(), 0, 1, 0, 0, 0};
  tvdb_grid_t raw = {};
  CHECK(tvdb_grid_from_sparse_using_template(&tmpl, &sg, "oracle", 4, &raw));
  CHECK(tvdb_grid_signed_flood_fill(&raw, 4, -4, &source, &err) == TVDB_OK);
  tvdb_grid_destroy_owned(&raw);
  openvdb::tools::signedFloodFill(ref->tree());
  tvdb_transform_t target = {};
  target.type = TVDB_TRANSFORM_AFFINE;
  target.matrix[3][3] = 1;
  target.matrix[0][1] = -.5;
  target.matrix[1][0] = .5;
  target.matrix[0][2] = .2;
  target.matrix[2][2] = .75;
  target.matrix[0][3] = .25;
  CHECK(tvdb_grid_resample(&source, &target, TVDB_SAMPLE_LINEAR, 200000,
                           &sampled, &err) == TVDB_OK);
  tvdb_tree_index index = {};
  CHECK(tvdb_tree_index_create(&sampled, 1, &index, &err) == TVDB_OK);
  for (int x = -10; x <= 10; ++x)
    for (int y = -10; y <= 10; ++y)
      for (int z = -10; z <= 10; ++z) {
        int32_t c[3] = {x, y, z};
        openvdb::Vec3R p(-.5 * y + .2 * z + .25, .5 * x, .75 * z);
        float expected = openvdb::tools::BoxSampler::sample(ref->tree(), p);
        CHECK(std::fabs(tvdb_tree_get(&index, c, nullptr) - expected) < 2e-6);
      }
  tvdb_tree_index_destroy(&index);
  tvdb_level_set_rebuild_result_t report = {};
  CHECK(tvdb_grid_level_set_track(&source, 3, 3, 200000, &rebuilt, &report,
                                  &err) == TVDB_OK);
  auto rebuilt_ref = openvdb::tools::levelSetRebuild(*ref, 0.f, 3.f, 3.f);
  CHECK(tvdb_tree_index_create(&rebuilt, 1, &index, &err) == TVDB_OK);
  double difference = 0;
  for (int x = -7; x <= 7; ++x)
    for (int y = -7; y <= 7; ++y)
      for (int z = -7; z <= 7; ++z) {
        int32_t c[3] = {x, y, z};
        double tiny = tvdb_tree_get(&index, c, nullptr),
               v = rebuilt_ref->tree().getValue(openvdb::Coord(x, y, z));
        difference = std::max(difference, std::fabs(tiny - v));
      }
  CHECK(difference < .35);
  tvdb_tree_index_destroy(&index);
  tvdb_triangle_mesh mesh = {};
  CHECK(tvdb_grid_volume_to_mesh(&source, 0, 0, 100000, &mesh, &err) ==
        TVDB_OK);
  std::vector<openvdb::Vec3s> points;
  std::vector<openvdb::Vec4I> quads;
  openvdb::tools::volumeToMesh(*ref, points, quads, 0.0);
  CHECK(mesh.vertex_count && !points.empty() && !quads.empty());
  for (const auto& p : points) CHECK(std::fabs(p.length() - 5) < .2);
  for (size_t i = 0; i < mesh.vertex_count; ++i) {
    auto v = mesh.vertices[i];
    CHECK(std::fabs(std::sqrt(v.x * v.x + v.y * v.y + v.z * v.z) - 5) < .2);
  }
  tvdb_triangle_mesh_free(&mesh);
  tvdb_grid_destroy_owned(&source);
  /* OpenVDB solves +Laplacian; tinyvdb uses the positive -Laplacian. */
  coords.clear();
  values.clear();
  openvdb::FloatTree rhs_ref(0);
  for (int x = 0; x < 4; ++x)
    for (int y = 0; y < 4; ++y)
      for (int z = 0; z < 4; ++z) {
        coords.push_back({x, y, z});
        values.push_back(1);
        rhs_ref.setValue(openvdb::Coord(x, y, z), -1);
      }
  sg.coords = coords.data();
  sg.values = values.data();
  sg.count = coords.size();
  CHECK(tvdb_grid_from_sparse_using_template(&tmpl, &sg, "rhs", 0, &source));
  tvdb_sparse_poisson_options_t options = {300,     1e-6,    10000,
                                           nullptr, nullptr, nullptr};
  tvdb_poisson_result_t solved;
  CHECK(tvdb_grid_solve_poisson(&source, &options, &solution, &solved, &err) ==
            TVDB_OK &&
        solved.converged);
  auto state = openvdb::math::pcg::terminationDefaults<double>();
  state.iterations = 300;
  state.relativeError = 1e-7;
  state.absoluteError = 1e-7;
  // The staggered option selects immediate six-neighbor differences;
  // OpenVDB's default collocated operator uses two-voxel offsets.
  auto expected = openvdb::tools::poisson::solve(rhs_ref, state, true);
  CHECK(state.success);
  CHECK(tvdb_tree_index_create(&solution, 1, &index, &err) == TVDB_OK);
  for (auto c : coords) {
    int32_t xyz[3] = {c.x, c.y, c.z};
    CHECK(std::fabs(tvdb_tree_get(&index, xyz, nullptr) -
                    expected->getValue(openvdb::Coord(c.x, c.y, c.z))) < 1e-5);
  }
  tvdb_tree_index_destroy(&index);
  tvdb_grid_destroy_owned(&source);
  tvdb_grid_destroy_owned(&sampled);
  tvdb_grid_destroy_owned(&rebuilt);
  tvdb_grid_destroy_owned(&solution);
  std::printf(
      "OpenVDB %s sparse tools oracle passed; rebuild difference %.6g\n",
      OPENVDB_LIBRARY_VERSION_STRING, difference);
  return 0;
}
