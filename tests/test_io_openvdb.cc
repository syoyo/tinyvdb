// OpenVDB oracle for tinyvdb I/O: transforms (affine maps in both
// directions), per-grid and header-only reads, and typed grids written by
// OpenVDB. Built with -DTINYVDB_BUILD_OPENVDB_TESTS=ON.
#include <openvdb/openvdb.h>
#include <openvdb/tools/Interpolation.h>

#include <type_traits>

#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <sstream>
#include <string>
#include <vector>

extern "C" {
#include "tinyvdb_io.h"
#include "tinyvdb_tree_internal.h"
#include "tinyvdb_volume.h"
}
#include "tinyvdb_nanovdb.h"
/* PNanoVDB (C flavor) reads the converted grids, as GPU code would. */
#define PNANOVDB_C
#include "third_party/nanovdb/PNanoVDB.h"

static int g_failures;
#define CHECK(x)                                                      \
  do {                                                                \
    if (!(x)) {                                                       \
      std::fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #x);    \
      ++g_failures;                                                   \
    }                                                                 \
  } while (0)

/* io::File, not io::Stream: tinyvdb needs the grid offsets of the file format. */
static std::string TempPath(const char* name) {
  const char* dir = std::getenv("TMPDIR");
  return std::string(dir && *dir ? dir : "/tmp") + "/tinyvdb_io_openvdb_" + name + ".vdb";
}
static std::vector<uint8_t> WriteToMemory(const openvdb::GridPtrVec& grids) {
  const std::string path = TempPath("grids");
  openvdb::io::File(path).write(grids);
  std::vector<uint8_t> bytes;
  if (FILE* f = std::fopen(path.c_str(), "rb")) {
    int c;
    while ((c = std::fgetc(f)) != EOF) bytes.push_back(uint8_t(c));
    std::fclose(f);
  }
  std::remove(path.c_str());
  return bytes;
}
static bool Open(tvdb_file_t* f, const std::vector<uint8_t>& bytes) {
  tvdb_error_t e;
  if (tvdb_file_open_memory(f, bytes.data(), bytes.size(), nullptr, &e) != TVDB_OK) {
    std::fprintf(stderr, "open: %s\n", e.message);
    ++g_failures;
    return false;
  }
  return true;
}

static openvdb::math::Transform::Ptr AffineTransform() {
  openvdb::math::Mat4d m(2, 0, 0, 0, 0, 3, 0, 0, 0, 0, 4, 0, 10, 20, 30, 1);
  m = openvdb::math::rotation<openvdb::math::Mat4d>(openvdb::math::Z_AXIS, 0.5) * m;
  m = openvdb::math::rotation<openvdb::math::Mat4d>(openvdb::math::X_AXIS, -0.3) * m;
  return openvdb::math::Transform::Ptr(new openvdb::math::Transform(
      openvdb::math::MapBase::Ptr(new openvdb::math::AffineMap(m))));
}

/* OpenVDB-written affine maps read with OpenVDB's index -> world. */
static void TestAffineRead() {
  auto g = openvdb::FloatGrid::create(0.f);
  g->setName("density");
  g->setTransform(AffineTransform());
  g->tree().setValue(openvdb::Coord(1, 2, 3), 5.f);
  const std::vector<uint8_t> bytes = WriteToMemory({g});
  tvdb_file_t f;
  tvdb_error_t e;
  if (!Open(&f, bytes)) return;
  CHECK(tvdb_read_all_grids(&f, &e) == TVDB_OK);
  double m[4][4];
  CHECK(tvdb_tree_matrix(&f.grids[0].transform, m));
  double worst = 0;
  for (int i = -3; i <= 3; ++i)
    for (int j = -3; j <= 3; ++j)
      for (int k = -3; k <= 3; ++k) {
        const openvdb::Vec3d w = g->transform().indexToWorld(openvdb::Vec3d(i, j, k));
        for (int a = 0; a < 3; ++a)
          worst = std::fmax(worst, std::fabs(m[a][0] * i + m[a][1] * j + m[a][2] * k + m[a][3] - w[a]));
      }
  std::printf("affine read: max |index->world - OpenVDB| = %.3g\n", worst);
  CHECK(worst < 1e-12);
  tvdb_file_close(&f);
}

/* tinyvdb-written affine maps read back by OpenVDB. */
static void TestAffineWrite() {
  auto g = openvdb::FloatGrid::create(0.f);
  g->setName("density");
  g->setTransform(AffineTransform());
  g->tree().setValue(openvdb::Coord(-4, 7, 1), 2.f);
  const std::vector<uint8_t> bytes = WriteToMemory({g});
  tvdb_file_t f;
  tvdb_error_t e;
  if (!Open(&f, bytes)) return;
  CHECK(tvdb_read_all_grids(&f, &e) == TVDB_OK);
  uint8_t* out = nullptr;
  size_t size = 0;
  CHECK(tvdb_write_to_memory(&f, TVDB_COMPRESS_ZIP | TVDB_COMPRESS_ACTIVE_MASK, 0, &out, &size, &e) ==
        TVDB_OK);
  tvdb_file_close(&f);
  const std::string path = TempPath("written");
  if (FILE* fp = std::fopen(path.c_str(), "wb")) {
    std::fwrite(out, 1, size, fp);
    std::fclose(fp);
  }
  std::free(out);
  openvdb::io::File file(path);
  file.open();
  openvdb::GridPtrVecPtr grids = file.getGrids();
  file.close();
  std::remove(path.c_str());
  CHECK(grids && grids->size() == 1);
  if (!grids || grids->empty()) return;
  const openvdb::math::Transform& back = (*grids)[0]->transform();
  CHECK(back.mapType() == openvdb::math::AffineMap::mapType());
  double worst = 0;
  for (int i = -3; i <= 3; ++i)
    for (int j = -3; j <= 3; ++j) {
      const openvdb::Vec3d p(i, j, i - j);
      worst = std::fmax(worst, (back.indexToWorld(p) - g->transform().indexToWorld(p)).length());
    }
  std::printf("affine write: max |OpenVDB(tinyvdb file) - original| = %.3g\n", worst);
  CHECK(worst < 1e-12);
}

static const char* MetaString(const tvdb_grid_t& g, const char* key) {
  for (size_t i = 0; i < g.metadata.count; ++i) {
    const tvdb_meta_entry_t& m = g.metadata.entries[i];
    if (m.name && !std::strcmp(m.name, key) && m.value.type == TVDB_VALUE_STRING)
      return m.value.u.s.str;
  }
  return nullptr;
}

/* Per-grid and header-only reads of a multi-grid file match a full read. */
static void TestLazyReads() {
  auto density = openvdb::FloatGrid::create(0.f);
  density->setName("density");
  density->setGridClass(openvdb::GRID_FOG_VOLUME);
  auto sdf = openvdb::FloatGrid::create(0.3f);
  sdf->setName("sdf");
  sdf->setGridClass(openvdb::GRID_LEVEL_SET);
  sdf->setTransform(openvdb::math::Transform::createLinearTransform(0.1));
  for (int i = 0; i < 40; ++i) {
    density->tree().setValue(openvdb::Coord(i, i / 2, -i), float(i));
    sdf->tree().setValue(openvdb::Coord(-i, i, i / 3), -0.1f * float(i % 4));
  }
  const std::vector<uint8_t> bytes = WriteToMemory({density, sdf});
  tvdb_file_t all, lazy;
  tvdb_error_t e;
  if (!Open(&all, bytes) || !Open(&lazy, bytes)) return;
  CHECK(tvdb_read_all_grids(&all, &e) == TVDB_OK);
  CHECK(tvdb_grid_count(&lazy) == 2);
  /* Header only: metadata and transform, no tree. */
  CHECK(tvdb_read_grid_header(&lazy, 1, &e) == TVDB_OK);
  CHECK(lazy.grids[1].tree.nodes == nullptr);
  CHECK(lazy.grids[0].metadata.count == 0);
  const char* cls = MetaString(lazy.grids[1], "class");
  CHECK(cls && !std::strcmp(cls, "level set"));
  double ma[4][4], ml[4][4];
  CHECK(tvdb_tree_matrix(&lazy.grids[1].transform, ml) && tvdb_tree_matrix(&all.grids[1].transform, ma));
  CHECK(!std::memcmp(ma, ml, sizeof(ma)));
  /* Then just that grid's tree; the other grid stays unread. */
  CHECK(tvdb_read_grid(&lazy, 1, &e) == TVDB_OK);
  CHECK(lazy.grids[1].tree.nodes != nullptr && lazy.grids[0].tree.nodes == nullptr);
  CHECK(tvdb_read_grid(&lazy, 2, &e) == TVDB_ERROR_INVALID_ARGUMENT);
  tvdb_tree_index a, b;
  CHECK(tvdb_tree_index_create(&all.grids[1], 1, &a, &e) == TVDB_OK);
  CHECK(tvdb_tree_index_create(&lazy.grids[1], 1, &b, &e) == TVDB_OK);
  CHECK(a.active_voxels == b.active_voxels && a.active_voxels == 40);
  int differ = 0;
  for (int i = -45; i <= 45; ++i) {
    const int32_t c[3] = {-i, i, i / 3};
    differ += tvdb_tree_get(&a, c, nullptr) != tvdb_tree_get(&b, c, nullptr);
  }
  CHECK(differ == 0);
  tvdb_tree_index_destroy(&a);
  tvdb_tree_index_destroy(&b);
  /* A second read replaces the grid without leaking (ASan builds). */
  CHECK(tvdb_read_grid(&lazy, 1, &e) == TVDB_OK);
  CHECK(tvdb_read_grid_header(&lazy, 0, &e) == TVDB_OK);
  CHECK(!std::strcmp(MetaString(lazy.grids[0], "class"), "fog volume"));
  tvdb_file_close(&all);
  tvdb_file_close(&lazy);
  std::printf("lazy reads: OK\n");
}

/* ---- Typed grids: dense extraction, sampling and info vs OpenVDB ---- */
template <class T> static void ToFloats(const T& v, float* o) { o[0] = float(v); }
template <> void ToFloats(const bool& v, float* o) { o[0] = v ? 1.f : 0.f; }
template <> void ToFloats(const openvdb::Vec3f& v, float* o) { for (int k = 0; k < 3; ++k) o[k] = v[k]; }
template <> void ToFloats(const openvdb::Vec3d& v, float* o) { for (int k = 0; k < 3; ++k) o[k] = float(v[k]); }
template <> void ToFloats(const openvdb::Vec3i& v, float* o) { for (int k = 0; k < 3; ++k) o[k] = float(v[k]); }

/* NanoVDB conversion read back through PNanoVDB: values and activity over the
 * window, the map, class and world box. */
template <class GridT>
static void CheckNanoVDB(const char* label, typename GridT::Ptr g, const tvdb_grid_t& tg,
                         const tvdb_dense_volume_options_t& o, int comps) {
  uint8_t* data = nullptr;
  size_t size = 0;
  tvdb_error_t e;
  const tvdb_status_t st = tvdb_grid_to_nanovdb(&tg, &data, &size, &e);
  /* NanoVDB has no bool-valued (as written here) or vec3i grids. */
  if ((std::is_same<typename GridT::ValueType, bool>::value && !tg.tree.is_mask_grid) ||
      std::is_same<typename GridT::ValueType, openvdb::Vec3i>::value) {
    CHECK(st == TVDB_ERROR_UNSUPPORTED_GRID_TYPE);
    return;
  }
  CHECK(st == TVDB_OK);
  if (st != TVDB_OK) return;
  pnanovdb_buf_t buf = pnanovdb_make_buf(reinterpret_cast<uint32_t*>(data), size / 4);
  pnanovdb_grid_handle_t grid = {pnanovdb_address_null()};
  const pnanovdb_grid_type_t gt = pnanovdb_grid_get_grid_type(buf, grid);
  pnanovdb_tree_handle_t tree = pnanovdb_grid_get_tree(buf, grid);
  pnanovdb_root_handle_t root = pnanovdb_tree_get_root(buf, tree);
  pnanovdb_readaccessor_t acc;
  pnanovdb_readaccessor_init(&acc, root);
  auto ref = g->getConstAccessor();
  size_t bad = 0, bad_active = 0;
  for (int z = o.window_min[2]; z <= o.window_max[2]; ++z)
    for (int y = o.window_min[1]; y <= o.window_max[1]; ++y)
      for (int x = o.window_min[0]; x <= o.window_max[0]; ++x) {
        pnanovdb_coord_t ijk = {x, y, z};
        bad_active += int(pnanovdb_readaccessor_is_active(gt, buf, &acc, &ijk)) !=
                      int(ref.isValueOn(openvdb::Coord(x, y, z)));
        if (gt == PNANOVDB_GRID_TYPE_MASK) continue;
        float want[3], got[3] = {0, 0, 0};
        ToFloats(ref.getValue(openvdb::Coord(x, y, z)), want);
        pnanovdb_address_t a = pnanovdb_readaccessor_get_value_address(gt, buf, &acc, &ijk);
        switch (gt) {
          case PNANOVDB_GRID_TYPE_FLOAT: got[0] = pnanovdb_read_float(buf, a); break;
          case PNANOVDB_GRID_TYPE_DOUBLE: got[0] = float(pnanovdb_read_double(buf, a)); break;
          case PNANOVDB_GRID_TYPE_INT32: got[0] = float(pnanovdb_read_int32(buf, a)); break;
          case PNANOVDB_GRID_TYPE_INT64: got[0] = float(pnanovdb_read_int64(buf, a)); break;
          case PNANOVDB_GRID_TYPE_VEC3F: {
            pnanovdb_vec3_t v = pnanovdb_read_vec3(buf, a);
            got[0] = v.x; got[1] = v.y; got[2] = v.z;
            break;
          }
          case PNANOVDB_GRID_TYPE_VEC3D:
            for (int k = 0; k < 3; ++k)
              got[k] = float(pnanovdb_read_double(buf, pnanovdb_address_offset(a, 8u * k)));
            break;
          default: break;
        }
        for (int k = 0; k < comps; ++k) bad += got[k] != want[k];
      }
  /* Map: index -> world matches OpenVDB (float precision). */
  double worst = 0;
  for (int i = -2; i <= 2; ++i) {
    pnanovdb_vec3_t ip = {float(i), float(2 * i), float(-i)};
    pnanovdb_vec3_t w = pnanovdb_grid_index_to_worldf(buf, grid, &ip);
    const openvdb::Vec3d r = g->transform().indexToWorld(openvdb::Vec3d(i, 2 * i, -i));
    worst = std::fmax(worst, (openvdb::Vec3d(w.x, w.y, w.z) - r).length());
  }
  const uint32_t cls = pnanovdb_grid_get_grid_class(buf, grid);
  std::printf("%-12s NanoVDB %zu bytes: %zu value / %zu activity mismatches, map err %.2g, class %u\n",
              label, size, bad, bad_active, worst, cls);
  CHECK(bad == 0 && bad_active == 0 && worst < 1e-4);
  CHECK(cls == (gt == PNANOVDB_GRID_TYPE_MASK ? PNANOVDB_GRID_CLASS_TOPOLOGY
                                               : PNANOVDB_GRID_CLASS_FOG_VOLUME));
  std::free(data);
}

template <class GridT>
static void CheckTyped(const char* label, typename GridT::Ptr g, int comps, bool half = false,
                       const openvdb::CoordBBox* window = nullptr) {
  g->setName(label);
  g->setGridClass(openvdb::GRID_FOG_VOLUME);
  if (half) g->setSaveFloatAsHalf(true);
  g->setTransform(AffineTransform());
  const std::vector<uint8_t> bytes = WriteToMemory({g});
  tvdb_file_t f;
  tvdb_error_t e;
  if (!Open(&f, bytes)) return;
  /* Info from the header alone, then from the tree. */
  tvdb_grid_info_t hinfo, info;
  CHECK(tvdb_read_grid_header(&f, 0, &e) == TVDB_OK);
  CHECK(tvdb_grid_get_info(&f.grids[0], &hinfo, &e) == TVDB_OK);
  CHECK(tvdb_read_grid(&f, 0, &e) == TVDB_OK);
  CHECK(tvdb_grid_get_info(&f.grids[0], &info, &e) == TVDB_OK);
  const openvdb::CoordBBox box = g->evalActiveVoxelBoundingBox();
  CHECK(info.has_tree && info.has_bounds && info.components == comps);
  CHECK(info.grid_class == TVDB_GRID_CLASS_FOG_VOLUME);
  CHECK(info.active_voxels == g->activeVoxelCount());
  for (int a = 0; a < 3; ++a) {
    CHECK(info.index_min[a] == box.min()[a] && info.index_max[a] == box.max()[a]);
    CHECK(!hinfo.has_tree && hinfo.has_bounds && hinfo.index_min[a] == box.min()[a] &&
          hinfo.index_max[a] == box.max()[a]);
  }
  CHECK(hinfo.active_voxels == g->activeVoxelCount());
  /* Dense (stride 1) over a window one voxel larger than the active box. */
  tvdb_dense_volume_options_t o = {};
  o.use_window = 1;
  for (int a = 0; a < 3; ++a) {
    o.window_min[a] = window ? window->min()[a] : box.min()[a] - 1;
    o.window_max[a] = window ? window->max()[a] : box.max()[a] + 1;
  }
  tvdb_dense_volume_t d = {};
  if (tvdb_grid_to_dense_volume(&f.grids[0], &o, &d, &e) != TVDB_OK) {
    std::fprintf(stderr, "%s: dense: %s\n", label, e.message);
    ++g_failures;
  }
  tvdb_volume_sampler_t* s = nullptr;
  CHECK(tvdb_volume_sampler_create(&f.grids[0], &s, &e) == TVDB_OK);
  auto acc = g->getConstAccessor();
  size_t bad = 0, bad_sample = 0, bad_active = 0;
  for (int z = o.window_min[2]; z <= o.window_max[2] && d.data; ++z)
    for (int y = o.window_min[1]; y <= o.window_max[1]; ++y)
      for (int x = o.window_min[0]; x <= o.window_max[0]; ++x) {
        float ref[3], got[3];
        ToFloats(acc.getValue(openvdb::Coord(x, y, z)), ref);
        const size_t cell = size_t(x - o.window_min[0]) +
                            size_t(d.dims[0]) * (size_t(y - o.window_min[1]) +
                                                 size_t(d.dims[1]) * size_t(z - o.window_min[2]));
        const int32_t c[3] = {x, y, z};
        int on = 0;
        tvdb_volume_sampler_get(s, c, got, &on);
        bad_active += on != int(acc.isValueOn(openvdb::Coord(x, y, z)));
        for (int k = 0; k < comps; ++k) {
          bad += d.data[size_t(comps) * cell + size_t(k)] != ref[k];
          bad_sample += got[k] != ref[k];
        }
      }
  /* World-space trilinear vs OpenVDB's BoxSampler (scalar float grids). */
  double worst = 0;
  if constexpr (std::is_same<typename GridT::ValueType, float>::value) {
    for (int i = 0; i < 2000; ++i) {
      const openvdb::CoordBBox wb(openvdb::Coord(o.window_min[0], o.window_min[1], o.window_min[2]),
                                  openvdb::Coord(o.window_max[0], o.window_max[1], o.window_max[2]));
      const openvdb::Vec3d ip(wb.min()[0] + (wb.dim()[0] - 1) * ((i * 37 % 1000) / 1000.0),
                              wb.min()[1] + (wb.dim()[1] - 1) * ((i * 61 % 1000) / 1000.0),
                              wb.min()[2] + (wb.dim()[2] - 1) * ((i * 83 % 1000) / 1000.0));
      const openvdb::Vec3d w = g->transform().indexToWorld(ip);
      const double pw[3] = {w.x(), w.y(), w.z()};
      float got = 0;
      CHECK(tvdb_volume_sample_world(s, pw, 1, TVDB_VOLUME_FILTER_TRILINEAR, &got, &e) == TVDB_OK);
      const float ref = float(openvdb::tools::BoxSampler::sample(g->tree(), ip));
      worst = std::fmax(worst, std::fabs(double(got) - double(ref)));
    }
  }
  std::printf("%-12s dense %dx%dx%d: %zu value / %zu sample / %zu activity mismatches, "
              "trilinear max diff %.3g\n",
              label, d.dims[0], d.dims[1], d.dims[2], bad, bad_sample, bad_active, worst);
  CHECK(bad == 0 && bad_sample == 0 && bad_active == 0 && worst < 1e-5);
  CheckNanoVDB<GridT>(label, g, f.grids[0], o, comps);
  tvdb_volume_sampler_destroy(s);
  tvdb_dense_volume_free(&d);
  tvdb_file_close(&f);
}

template <class GridT, class Fn>
static typename GridT::Ptr Fill(typename GridT::ValueType background, Fn value) {
  auto g = GridT::create(background);
  auto acc = g->getAccessor();
  for (int i = -6; i <= 9; ++i)
    for (int j = -3; j <= 4; ++j)
      for (int k = 0; k <= 11; ++k)
        if ((i * 7 + j * 3 + k) % 5 != 0) acc.setValue(openvdb::Coord(i, j, k), value(i, j, k));
  /* One inactive voxel with a non-background value. */
  acc.setValueOff(openvdb::Coord(2, 2, 2), value(9, 9, 9));
  return g;
}

static void TestTypedGrids() {
  CheckTyped<openvdb::FloatGrid>("float", Fill<openvdb::FloatGrid>(0.5f, [](int i, int j, int k) {
    return 0.25f * float(i) - float(j * k); }), 1);
  {
    /* A float grid with active and inactive tiles. */
    auto g = Fill<openvdb::FloatGrid>(0.f, [](int i, int, int) { return float(i); });
    g->tree().addTile(1, openvdb::Coord(64, 0, 0), 3.f, true);
    g->tree().addTile(1, openvdb::Coord(0, 64, 0), 4.f, false);
    CheckTyped<openvdb::FloatGrid>("float+tiles", g, 1);
  }
  {
    /* A root-level tile (4096^3): the window covers only its corner. */
    auto g = Fill<openvdb::FloatGrid>(0.f, [](int i, int, int) { return float(i); });
    g->tree().addTile(3, openvdb::Coord(4096, 0, 0), 7.f, true);
    auto acc = g->getAccessor();
    acc.setValue(openvdb::Coord(4100, 3, 3), 1.f); /* splits the tile near its corner */
    const openvdb::CoordBBox corner(openvdb::Coord(4080, -4, -4), openvdb::Coord(4110, 12, 12));
    CheckTyped<openvdb::FloatGrid>("root tile", g, 1, false, &corner);
  }
  CheckTyped<openvdb::FloatGrid>("half", Fill<openvdb::FloatGrid>(0.f, [](int i, int j, int) {
    return 0.5f * float(i + j); }), 1, true);
  CheckTyped<openvdb::DoubleGrid>("double", Fill<openvdb::DoubleGrid>(-1.0, [](int i, int j, int k) {
    return 1e-3 * double(i * j * k); }), 1);
  CheckTyped<openvdb::Int32Grid>("int32", Fill<openvdb::Int32Grid>(-7, [](int i, int j, int k) {
    return i * 100 + j * 10 + k; }), 1);
  CheckTyped<openvdb::Int64Grid>("int64", Fill<openvdb::Int64Grid>(3, [](int i, int j, int k) {
    return int64_t(i - j + k) * 1000; }), 1);
  CheckTyped<openvdb::BoolGrid>("bool", Fill<openvdb::BoolGrid>(false, [](int i, int, int) {
    return (i & 1) != 0; }), 1);
  {
    auto m = openvdb::MaskGrid::create(false);
    for (int i = -4; i < 20; i += 3)
      for (int j = 0; j < 9; ++j) m->tree().setValueOn(openvdb::Coord(i, j, i - j));
    CheckTyped<openvdb::MaskGrid>("mask", m, 1);
  }
  CheckTyped<openvdb::Vec3SGrid>("vec3f", Fill<openvdb::Vec3SGrid>(openvdb::Vec3f(0, 1, 0),
    [](int i, int j, int k) { return openvdb::Vec3f(float(i), float(-j), 0.5f * float(k)); }), 3);
  CheckTyped<openvdb::Vec3DGrid>("vec3d", Fill<openvdb::Vec3DGrid>(openvdb::Vec3d(0),
    [](int i, int j, int k) { return openvdb::Vec3d(i * 0.1, j * 0.2, k * 0.3); }), 3);
  CheckTyped<openvdb::Vec3IGrid>("vec3i", Fill<openvdb::Vec3IGrid>(openvdb::Vec3i(1, 2, 3),
    [](int i, int j, int k) { return openvdb::Vec3i(i, j, k); }), 3);
}

int main() {
  std::setvbuf(stdout, nullptr, _IONBF, 0);
  openvdb::initialize();
  TestAffineRead();
  TestAffineWrite();
  TestLazyReads();
  TestTypedGrids();
  if (g_failures) {
    std::printf("%d failure(s)\n", g_failures);
    return 1;
  }
  std::printf("tinyvdb I/O vs OpenVDB: OK\n");
  return 0;
}
