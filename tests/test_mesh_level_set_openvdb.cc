// tvdb_mesh_to_level_set against openvdb::tools::meshToLevelSet on a closed
// sphere mesh, and OpenVDB reading tinyvdb's serialized level set.
#include <openvdb/openvdb.h>
#include <openvdb/io/Stream.h>
#include <openvdb/tools/MeshToVolume.h>

#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <sstream>
#include <string>
#include <vector>

#include "tinyvdb_sparse_tools.h"
#include "tinyvdb_sparse_tree.h"
#define CHECK(x)                                                             \
  do {                                                                       \
    if (!(x)) {                                                              \
      std::fprintf(stderr, "line %d: %s (%s)\n", __LINE__, #x, err.message); \
      return 1;                                                              \
    }                                                                        \
  } while (0)

// Independent closest-point distance (Ericson, Real-Time Collision Detection).
static double point_triangle(const openvdb::Vec3d& p, const openvdb::Vec3d& a,
                             const openvdb::Vec3d& b, const openvdb::Vec3d& c) {
  const openvdb::Vec3d ab = b - a, ac = c - a, ap = p - a;
  const double d1 = ab.dot(ap), d2 = ac.dot(ap);
  if (d1 <= 0 && d2 <= 0) return (p - a).length();
  const openvdb::Vec3d bp = p - b;
  const double d3 = ab.dot(bp), d4 = ac.dot(bp);
  if (d3 >= 0 && d4 <= d3) return (p - b).length();
  const double vc = d1 * d4 - d3 * d2;
  if (vc <= 0 && d1 >= 0 && d3 <= 0) return (p - (a + ab * (d1 / (d1 - d3)))).length();
  const openvdb::Vec3d cp = p - c;
  const double d5 = ab.dot(cp), d6 = ac.dot(cp);
  if (d6 >= 0 && d5 <= d6) return (p - c).length();
  const double vb = d5 * d2 - d1 * d6;
  if (vb <= 0 && d2 >= 0 && d6 <= 0) return (p - (a + ac * (d2 / (d2 - d6)))).length();
  const double va = d3 * d6 - d5 * d4;
  if (va <= 0 && (d4 - d3) >= 0 && (d5 - d6) >= 0)
    return (p - (b + (c - b) * ((d4 - d3) / ((d4 - d3) + (d5 - d6))))).length();
  const double den = 1.0 / (va + vb + vc);
  return (p - (a + ab * (vb * den) + ac * (vc * den))).length();
}

int main() {
  openvdb::initialize();
  tvdb_error_t err = {};
  // Latitude-longitude sphere of radius 1, outward winding.
  const int nlat = 32, nlon = 64;
  std::vector<openvdb::Vec3s> points;
  std::vector<openvdb::Vec3I> tris;
  points.push_back({0, 0, 1});
  points.push_back({0, 0, -1});
  for (int i = 1; i < nlat; ++i)
    for (int j = 0; j < nlon; ++j) {
      const double th = M_PI * i / nlat, ph = 2 * M_PI * j / nlon;
      points.push_back({float(std::sin(th) * std::cos(ph)), float(std::sin(th) * std::sin(ph)),
                        float(std::cos(th))});
    }
  auto ring = [&](int i, int j) {
    return unsigned(2 + (i - 1) * nlon + ((j % nlon) + nlon) % nlon);
  };
  for (int j = 0; j < nlon; ++j) {
    tris.push_back({0, ring(1, j), ring(1, j + 1)});
    tris.push_back({1, ring(nlat - 1, j + 1), ring(nlat - 1, j)});
  }
  for (int i = 1; i + 1 < nlat; ++i)
    for (int j = 0; j < nlon; ++j) {
      tris.push_back({ring(i, j), ring(i + 1, j), ring(i + 1, j + 1)});
      tris.push_back({ring(i, j), ring(i + 1, j + 1), ring(i, j + 1)});
    }
  const double h = 0.05;
  const float width = float(3 * h);

  tvdb_triangle_mesh mesh = {};
  std::vector<tvdb_vec3f> v(points.size());
  std::vector<tvdb_triangle> f(tris.size());
  for (size_t i = 0; i < points.size(); ++i) v[i] = {points[i].x(), points[i].y(), points[i].z()};
  for (size_t i = 0; i < tris.size(); ++i) f[i] = {tris[i].x(), tris[i].y(), tris[i].z()};
  mesh.vertices = v.data();
  mesh.vertex_count = mesh.vertex_capacity = v.size();
  mesh.faces = f.data();
  mesh.face_count = mesh.face_capacity = f.size();
  tvdb_mesh_level_set_options_t o = {};
  o.voxel_size = float(h);
  o.exterior_width = o.interior_width = width;
  tvdb_grid_t grid = {};
  CHECK(tvdb_mesh_to_level_set(&mesh, &o, nullptr, &grid, nullptr, &err) == TVDB_OK);

  tvdb_sparse_grid sg = {};
  CHECK(tvdb_grid_to_sparse(&grid, &sg));
  // Exact: every 7th active voxel against brute-force closest distances.
  double worst_exact = 0;
  for (size_t i = 0; i < sg.count; i += 7) {
    const openvdb::Vec3d p(sg.coords[i].x * h, sg.coords[i].y * h, sg.coords[i].z * h);
    double brute = 1e300;
    for (const auto& t : tris)
      brute = std::min(brute, point_triangle(p, openvdb::Vec3d(points[t.x()]),
                                             openvdb::Vec3d(points[t.y()]),
                                             openvdb::Vec3d(points[t.z()])));
    const double inside = p.length() < 1 ? -1 : 1; // the mesh is inscribed in r = 1
    if (std::fabs(p.length() - 1) > 0.01)          // sign is unambiguous off the surface
      CHECK((sg.values[i] < 0) == (inside < 0));
    worst_exact = std::max(worst_exact, std::fabs(std::fabs(double(sg.values[i])) - brute));
  }
  std::printf("max |tinyvdb| - brute force = %.3g\n", worst_exact);
  CHECK(worst_exact < 1e-5);
  // OpenVDB's meshToLevelSet (exact only next to the polygons, propagated
  // outwards, then renormalized) agrees in sign and within 0.3 voxel.
  auto xform = openvdb::math::Transform::createLinearTransform(double(o.voxel_size));
  auto ref = openvdb::tools::meshToLevelSet<openvdb::FloatGrid>(*xform, points, tris, 3.0f);
  auto acc = ref->getConstAccessor();
  size_t compared = 0;
  double dev = 0;
  for (size_t i = 0; i < sg.count; ++i) {
    const openvdb::Coord c(sg.coords[i].x, sg.coords[i].y, sg.coords[i].z);
    if (std::fabs(sg.values[i]) > 0.8f * width || !acc.isValueOn(c)) continue;
    const float r = acc.getValue(c);
    if (std::fabs(r) > 0.8f * width) continue;
    if (std::fabs(sg.values[i]) > 0.3 * h) CHECK((r < 0) == (sg.values[i] < 0));
    dev = std::max(dev, double(std::fabs(r - sg.values[i])));
    ++compared;
  }
  std::printf("compared %zu voxels with OpenVDB, max deviation %.3g\n", compared, dev);
  CHECK(compared > 10000 && dev < 0.3 * h);
  // Every OpenVDB active voxel near the surface is active here too.
  size_t missing = 0;
  for (auto it = ref->cbeginValueOn(); it; ++it) {
    if (std::fabs(*it) > 0.8f * width) continue;
    bool found = false;
    const openvdb::Coord c = it.getCoord();
    for (size_t i = 0; i < sg.count && !found; ++i)
      found = sg.coords[i].x == c.x() && sg.coords[i].y == c.y() && sg.coords[i].z == c.z();
    missing += !found;
  }
  CHECK(missing == 0);
  tvdb_sparse_grid_free(&sg);

  // OpenVDB reads tinyvdb's level set.
  tvdb_file_t file;
  tvdb_file_init_for_write(&file, nullptr);
  file.grids = &grid;
  file.num_grids = 1;
  uint8_t* bytes = nullptr;
  size_t size = 0;
  CHECK(tvdb_write_to_memory(&file, TVDB_COMPRESS_ZIP | TVDB_COMPRESS_ACTIVE_MASK, 0, &bytes,
                             &size, &err) == TVDB_OK);
  std::istringstream in(std::string(reinterpret_cast<char*>(bytes), size));
  openvdb::io::Stream stream(in);
  auto grids = stream.getGrids();
  CHECK(grids && grids->size() == 1);
  auto read = openvdb::gridPtrCast<openvdb::FloatGrid>((*grids)[0]);
  CHECK(read && read->getGridClass() == openvdb::GRID_LEVEL_SET);
  CHECK(std::fabs(read->voxelSize()[0] - double(o.voxel_size)) < 1e-12);
  CHECK(read->background() == width);
  auto racc = read->getConstAccessor();
  CHECK(racc.getValue(openvdb::Coord(0, 0, 0)) == -width);  // flood-filled interior
  tvdb_sparse_grid sg2 = {};
  CHECK(tvdb_grid_to_sparse(&grid, &sg2));
  for (size_t i = 0; i < sg2.count; ++i)
    CHECK(racc.getValue(openvdb::Coord(sg2.coords[i].x, sg2.coords[i].y, sg2.coords[i].z)) ==
          sg2.values[i]);
  CHECK(read->activeVoxelCount() == openvdb::Index64(sg2.count));
  tvdb_sparse_grid_free(&sg2);
  std::free(bytes);
  tvdb_grid_destroy_owned(&grid);
  std::printf("test_mesh_level_set_openvdb: ok\n");
  return 0;
}
