/*
 * tinyvdb_embind.cc — Emscripten/Embind bindings for TinyVDB.
 *
 * Exposes: VDB file I/O (from memory), mesh-to-SDF, SDF-to-mesh, CSG,
 *          morphology, filtering, measurement.
 *
 * Updated for tinyvdb v0.9.0: the legacy C++ wrapper namespaces
 * (`tvdb_mesh::`, `tvdb_ops::`) were dropped; this file now binds the
 * C API directly. DenseGridWrap / TriangleMeshWrap are thin C++ shells
 * around the C structs so embind can hold them by value.
 *
 * Build with Emscripten: emcmake cmake .. && emmake make
 */

#include <emscripten/bind.h>
#include <emscripten/val.h>

#include <cstdlib>
#include <cstring>
#include <stdexcept>
#include <string>
#include <vector>

#include "tinyvdb_io.h"
#include "tinyvdb_mesh.h"
#include "tinyvdb_ops.h"

using namespace emscripten;

/* ======================================================================== */
/*  VDB File I/O wrapper (memory-based, no filesystem)                      */
/* ======================================================================== */

class VDBFile {
public:
    VDBFile() : is_open_(false) { memset(&file_, 0, sizeof(file_)); }
    ~VDBFile() { close(); }

    void openMemory(const std::string &data) {
        close();
        tvdb_error_t err; memset(&err, 0, sizeof(err));
        buf_ = data;
        tvdb_status_t st = tvdb_file_open_memory(
            &file_, reinterpret_cast<const uint8_t *>(buf_.data()),
            buf_.size(), NULL, &err);
        if (st != TVDB_OK)
            throw std::runtime_error(std::string("openMemory failed: ") + err.message);
        is_open_ = true;
    }

    void openMemoryFromArray(const val &arr) {
        close();
        unsigned len = arr["length"].as<unsigned>();
        buf_.resize(len);
        val memview = val(typed_memory_view(len,
            reinterpret_cast<uint8_t *>(&buf_[0])));
        memview.call<void>("set", arr);
        tvdb_error_t err; memset(&err, 0, sizeof(err));
        tvdb_status_t st = tvdb_file_open_memory(
            &file_, reinterpret_cast<const uint8_t *>(buf_.data()),
            buf_.size(), NULL, &err);
        if (st != TVDB_OK)
            throw std::runtime_error(std::string("openMemory failed: ") + err.message);
        is_open_ = true;
    }

    void readGrids() {
        checkOpen();
        tvdb_error_t err; memset(&err, 0, sizeof(err));
        tvdb_status_t st = tvdb_read_all_grids(&file_, &err);
        if (st != TVDB_OK)
            throw std::runtime_error(std::string("readGrids failed: ") + err.message);
    }

    void close() {
        if (is_open_) { tvdb_file_close(&file_); is_open_ = false; }
        buf_.clear();
    }

    int gridCount() const { return is_open_ ? (int)tvdb_grid_count(&file_) : 0; }

    std::string gridName(int idx) const {
        checkOpen();
        const char *n = tvdb_grid_name(&file_, (size_t)idx);
        return n ? n : "";
    }

    std::string gridTypeName(int idx) const {
        checkOpen();
        const char *n = tvdb_grid_type_name(&file_, (size_t)idx);
        return n ? n : "";
    }

    val toBytes(int compression, int level) const {
        checkOpen();
        tvdb_error_t err; memset(&err, 0, sizeof(err));
        uint8_t *out = NULL; size_t out_sz = 0;
        tvdb_status_t st = tvdb_write_to_memory(
            &file_, (uint32_t)compression, level, &out, &out_sz, &err);
        if (st != TVDB_OK)
            throw std::runtime_error(std::string("toBytes failed: ") + err.message);
        val view = val(typed_memory_view(out_sz, out));
        val js_arr = val::global("Uint8Array").new_(view);
        free(out);
        return js_arr;
    }

    val header() const {
        checkOpen();
        val h = val::object();
        h.set("fileVersion",      (int)file_.header.file_version);
        h.set("majorVersion",     (int)file_.header.major_version);
        h.set("minorVersion",     (int)file_.header.minor_version);
        h.set("compressionFlags", (int)file_.header.compression_flags);
        h.set("uuid",             std::string(file_.header.uuid));
        return h;
    }

    val gridMetadata(int idx) const {
        checkOpen();
        if ((size_t)idx >= file_.num_grids)
            throw std::runtime_error("grid index out of range");
        const tvdb_grid_t &g = file_.grids[idx];
        val d = val::object();
        for (size_t i = 0; i < g.metadata.count; i++) {
            const tvdb_meta_entry_t &e = g.metadata.entries[i];
            if (!e.name) continue;
            std::string key(e.name);
            switch (e.value.type) {
                case TVDB_VALUE_FLOAT:  d.set(key, (double)e.value.u.f); break;
                case TVDB_VALUE_DOUBLE: d.set(key, e.value.u.d); break;
                case TVDB_VALUE_INT32:  d.set(key, e.value.u.i32); break;
                case TVDB_VALUE_INT64:  d.set(key, (double)e.value.u.i64); break;
                case TVDB_VALUE_BOOL:   d.set(key, (bool)e.value.u.b); break;
                case TVDB_VALUE_STRING:
                    if (e.value.u.s.str)
                        d.set(key, std::string(e.value.u.s.str, e.value.u.s.len));
                    break;
                default: break;
            }
        }
        return d;
    }

    val gridTransform(int idx) const {
        checkOpen();
        if ((size_t)idx >= file_.num_grids)
            throw std::runtime_error("grid index out of range");
        const tvdb_transform_t &t = file_.grids[idx].transform;
        val d = val::object();
        val vs = val::array();
        vs.call<void>("push", t.voxel_size[0]);
        vs.call<void>("push", t.voxel_size[1]);
        vs.call<void>("push", t.voxel_size[2]);
        d.set("voxelSize", vs);
        val tr = val::array();
        tr.call<void>("push", t.translation[0]);
        tr.call<void>("push", t.translation[1]);
        tr.call<void>("push", t.translation[2]);
        d.set("translation", tr);
        return d;
    }

    int treeNodeCount(int idx) const {
        checkOpen();
        if ((size_t)idx >= file_.num_grids) return 0;
        return (int)file_.grids[idx].tree.num_nodes;
    }

    val treeNodeInfo(int gridIdx, int nodeIdx) const {
        checkOpen();
        if ((size_t)gridIdx >= file_.num_grids)
            throw std::runtime_error("grid index out of range");
        const tvdb_tree_t &tree = file_.grids[gridIdx].tree;
        if ((size_t)nodeIdx >= tree.num_nodes)
            throw std::runtime_error("node index out of range");
        const tvdb_tree_node_t &n = tree.nodes[nodeIdx];
        val d = val::object();
        const char *types[] = {"root", "internal", "leaf"};
        d.set("type",  std::string(types[n.type]));
        d.set("level", n.level);
        val origin = val::array();
        origin.call<void>("push", n.origin[0]);
        origin.call<void>("push", n.origin[1]);
        origin.call<void>("push", n.origin[2]);
        d.set("origin", origin);
        if (n.type == TVDB_NODE_LEAF) {
            d.set("activeVoxelCount",
                  (int)tvdb_nodemask_count_on(&n.u.leaf.value_mask));
            d.set("dataSize", (int)n.u.leaf.data_size);
        }
        return d;
    }

private:
    void checkOpen() const {
        if (!is_open_) throw std::runtime_error("VDB file is not open");
    }
    tvdb_file_t file_;
    bool is_open_;
    std::string buf_;
};

/* ======================================================================== */
/*  DenseGrid wrapper (RAII over the C tvdb_dense_grid)                     */
/* ======================================================================== */

class DenseGridWrap {
public:
    tvdb_dense_grid grid;

    DenseGridWrap() {
        std::memset(&grid, 0, sizeof(grid));
        grid.voxel_size = 1.0f;
    }

    DenseGridWrap(int nx, int ny, int nz, float vs) {
        tvdb_dense_grid_init(&grid, nx, ny, nz);
        grid.voxel_size = vs;
    }

    DenseGridWrap(const DenseGridWrap& other) {
        tvdb_dense_grid_init(&grid, other.grid.nx, other.grid.ny, other.grid.nz);
        grid.ox = other.grid.ox; grid.oy = other.grid.oy; grid.oz = other.grid.oz;
        grid.voxel_size = other.grid.voxel_size;
        const size_t n = (size_t)grid.nx * grid.ny * grid.nz;
        if (grid.data && other.grid.data && n)
            std::memcpy(grid.data, other.grid.data, n * sizeof(float));
    }

    DenseGridWrap& operator=(const DenseGridWrap& other) {
        if (this != &other) {
            tvdb_dense_grid_free(&grid);
            tvdb_dense_grid_init(&grid, other.grid.nx, other.grid.ny, other.grid.nz);
            grid.ox = other.grid.ox; grid.oy = other.grid.oy; grid.oz = other.grid.oz;
            grid.voxel_size = other.grid.voxel_size;
            const size_t n = (size_t)grid.nx * grid.ny * grid.nz;
            if (grid.data && other.grid.data && n)
                std::memcpy(grid.data, other.grid.data, n * sizeof(float));
        }
        return *this;
    }

    ~DenseGridWrap() { tvdb_dense_grid_free(&grid); }

    int  getNx() const { return grid.nx; }
    int  getNy() const { return grid.ny; }
    int  getNz() const { return grid.nz; }
    float getOx() const { return grid.ox; }
    float getOy() const { return grid.oy; }
    float getOz() const { return grid.oz; }
    float getVoxelSize() const { return grid.voxel_size; }
    int   size() const { return grid.nx * grid.ny * grid.nz; }

    float get(int x, int y, int z) const {
        return grid.data[((size_t)z * grid.ny + y) * grid.nx + x];
    }
    void set(int x, int y, int z, float v) {
        grid.data[((size_t)z * grid.ny + y) * grid.nx + x] = v;
    }

    val getData() const {
        const size_t n = (size_t)grid.nx * grid.ny * grid.nz;
        return val(typed_memory_view(n, grid.data));
    }

    void setData(const val &arr) {
        const size_t n = (size_t)grid.nx * grid.ny * grid.nz;
        val memview = val(typed_memory_view(n, grid.data));
        memview.call<void>("set", arr);
    }
};

/* ======================================================================== */
/*  TriangleMesh wrapper (RAII over tvdb_triangle_mesh)                     */
/* ======================================================================== */

class TriangleMeshWrap {
public:
    tvdb_triangle_mesh mesh;

    TriangleMeshWrap() { tvdb_triangle_mesh_init(&mesh); }
    ~TriangleMeshWrap() { tvdb_triangle_mesh_free(&mesh); }

    TriangleMeshWrap(const TriangleMeshWrap& other) {
        tvdb_triangle_mesh_init(&mesh);
        copyFrom(other.mesh);
    }

    TriangleMeshWrap& operator=(const TriangleMeshWrap& other) {
        if (this != &other) {
            tvdb_triangle_mesh_free(&mesh);
            tvdb_triangle_mesh_init(&mesh);
            copyFrom(other.mesh);
        }
        return *this;
    }

    int numVertices() const { return (int)mesh.vertex_count; }
    int numFaces()    const { return (int)mesh.face_count; }

    val getVertices() const {
        return val(typed_memory_view(
            mesh.vertex_count * 3,
            reinterpret_cast<const float *>(mesh.vertices)));
    }

    val getFaces() const {
        return val(typed_memory_view(
            mesh.face_count * 3,
            reinterpret_cast<const uint32_t *>(mesh.faces)));
    }

    void setVertices(const val &arr) {
        unsigned len = arr["length"].as<unsigned>();
        const size_t V = len / 3;
        ensureVertexCap(V);
        mesh.vertex_count = V;
        val memview = val(typed_memory_view(
            len, reinterpret_cast<float *>(mesh.vertices)));
        memview.call<void>("set", arr);
    }

    void setFaces(const val &arr) {
        unsigned len = arr["length"].as<unsigned>();
        const size_t F = len / 3;
        ensureFaceCap(F);
        mesh.face_count = F;
        val memview = val(typed_memory_view(
            len, reinterpret_cast<uint32_t *>(mesh.faces)));
        memview.call<void>("set", arr);
    }

private:
    void ensureVertexCap(size_t cap) {
        if (mesh.vertex_capacity < cap) {
            mesh.vertices = (tvdb_vec3f*)std::realloc(
                mesh.vertices, cap * sizeof(tvdb_vec3f));
            mesh.vertex_capacity = cap;
        }
    }
    void ensureFaceCap(size_t cap) {
        if (mesh.face_capacity < cap) {
            mesh.faces = (tvdb_triangle*)std::realloc(
                mesh.faces, cap * sizeof(tvdb_triangle));
            mesh.face_capacity = cap;
        }
    }
    void copyFrom(const tvdb_triangle_mesh& src) {
        ensureVertexCap(src.vertex_count);
        mesh.vertex_count = src.vertex_count;
        if (src.vertex_count) std::memcpy(mesh.vertices, src.vertices,
                                          src.vertex_count * sizeof(tvdb_vec3f));
        ensureFaceCap(src.face_count);
        mesh.face_count = src.face_count;
        if (src.face_count) std::memcpy(mesh.faces, src.faces,
                                        src.face_count * sizeof(tvdb_triangle));
    }
};

/* ======================================================================== */
/*  Free functions                                                          */
/* ======================================================================== */

DenseGridWrap meshToSDF(TriangleMeshWrap &m, float voxelSize,
                        float bandWidth, int signMethod) {
    DenseGridWrap result;
    tvdb_sign_method sm = (signMethod == 1) ? TVDB_SIGN_SWEEP
                                              : TVDB_SIGN_FLOOD_FILL;
    bool ok = tvdb_mesh_to_sdf_vdb(&m.mesh, voxelSize, bandWidth,
                                    &result.grid, sm, /*arena=*/nullptr);
    if (!ok) throw std::runtime_error("tvdb_mesh_to_sdf_vdb failed");
    return result;
}

TriangleMeshWrap sdfToMesh(const DenseGridWrap &g, float isovalue) {
    TriangleMeshWrap result;
    bool ok = tvdb_sdf_to_mesh(&g.grid, isovalue, &result.mesh,
                                /*arena=*/nullptr);
    if (!ok) throw std::runtime_error("tvdb_sdf_to_mesh failed");
    return result;
}

TriangleMeshWrap makeManifold(TriangleMeshWrap &m, double resolution,
                              double isovalue, int signMethod) {
    TriangleMeshWrap result;
    tvdb_sign_method sm = (signMethod == 1) ? TVDB_SIGN_SWEEP
                                              : TVDB_SIGN_FLOOD_FILL;
    bool ok = tvdb_make_manifold_vdb(&m.mesh, resolution, isovalue,
                                      &result.mesh, sm, /*arena=*/nullptr);
    if (!ok) throw std::runtime_error("tvdb_make_manifold_vdb failed");
    return result;
}

/* --- Morphology / filtering / CSG / measurement: thin wrappers ---------- */

DenseGridWrap dilate(const DenseGridWrap &g, int iterations) {
    DenseGridWrap r(g); tvdb_dilate(&r.grid, iterations); return r;
}
DenseGridWrap erode(const DenseGridWrap &g, int iterations) {
    DenseGridWrap r(g); tvdb_erode(&r.grid, iterations); return r;
}
DenseGridWrap morphOpen(const DenseGridWrap &g, int iterations) {
    DenseGridWrap r(g); tvdb_open(&r.grid, iterations); return r;
}
DenseGridWrap morphClose(const DenseGridWrap &g, int iterations) {
    DenseGridWrap r(g); tvdb_close(&r.grid, iterations); return r;
}

DenseGridWrap gaussianFilter(const DenseGridWrap &g, int width, int iterations) {
    DenseGridWrap r(g); tvdb_gaussian_filter(&r.grid, width, iterations); return r;
}
DenseGridWrap meanFilter(const DenseGridWrap &g, int width, int iterations) {
    DenseGridWrap r(g); tvdb_mean_filter(&r.grid, width, iterations); return r;
}
DenseGridWrap laplacianFilter(const DenseGridWrap &g, int iterations) {
    DenseGridWrap r(g); tvdb_laplacian_filter(&r.grid, iterations); return r;
}

DenseGridWrap csgUnion(const DenseGridWrap &a, const DenseGridWrap &b) {
    DenseGridWrap r(a);
    tvdb_csg_union(&a.grid, &b.grid, &r.grid);
    return r;
}
DenseGridWrap csgIntersection(const DenseGridWrap &a, const DenseGridWrap &b) {
    DenseGridWrap r(a);
    tvdb_csg_intersection(&a.grid, &b.grid, &r.grid);
    return r;
}
DenseGridWrap csgDifference(const DenseGridWrap &a, const DenseGridWrap &b) {
    DenseGridWrap r(a);
    tvdb_csg_difference(&a.grid, &b.grid, &r.grid);
    return r;
}

float surfaceArea(const DenseGridWrap &g) { return tvdb_surface_area(&g.grid); }
float volume(const DenseGridWrap &g)      { return tvdb_volume(&g.grid); }

/* ======================================================================== */
/*  Embind registration                                                     */
/* ======================================================================== */

EMSCRIPTEN_BINDINGS(tinyvdb) {

    /* --- Constants --- */
    constant("COMPRESS_NONE",        (int)TVDB_COMPRESS_NONE);
    constant("COMPRESS_ZIP",         (int)TVDB_COMPRESS_ZIP);
    constant("COMPRESS_ACTIVE_MASK", (int)TVDB_COMPRESS_ACTIVE_MASK);
    constant("COMPRESS_BLOSC",       (int)TVDB_COMPRESS_BLOSC);
    constant("SIGN_FLOOD_FILL",      (int)TVDB_SIGN_FLOOD_FILL);
    constant("SIGN_SWEEP",           (int)TVDB_SIGN_SWEEP);

    class_<VDBFile>("VDBFile")
        .constructor<>()
        .function("openMemory",          &VDBFile::openMemory)
        .function("openMemoryFromArray", &VDBFile::openMemoryFromArray)
        .function("readGrids",           &VDBFile::readGrids)
        .function("close",               &VDBFile::close)
        .function("gridCount",           &VDBFile::gridCount)
        .function("gridName",            &VDBFile::gridName)
        .function("gridTypeName",        &VDBFile::gridTypeName)
        .function("toBytes",             &VDBFile::toBytes)
        .function("header",              &VDBFile::header)
        .function("gridMetadata",        &VDBFile::gridMetadata)
        .function("gridTransform",       &VDBFile::gridTransform)
        .function("treeNodeCount",       &VDBFile::treeNodeCount)
        .function("treeNodeInfo",        &VDBFile::treeNodeInfo)
        ;

    class_<DenseGridWrap>("DenseGrid")
        .constructor<>()
        .constructor<int, int, int, float>()
        .property("nx", &DenseGridWrap::getNx)
        .property("ny", &DenseGridWrap::getNy)
        .property("nz", &DenseGridWrap::getNz)
        .property("ox", &DenseGridWrap::getOx)
        .property("oy", &DenseGridWrap::getOy)
        .property("oz", &DenseGridWrap::getOz)
        .property("voxelSize", &DenseGridWrap::getVoxelSize)
        .function("size",    &DenseGridWrap::size)
        .function("get",     &DenseGridWrap::get)
        .function("set",     &DenseGridWrap::set)
        .function("getData", &DenseGridWrap::getData)
        .function("setData", &DenseGridWrap::setData)
        ;

    class_<TriangleMeshWrap>("TriangleMesh")
        .constructor<>()
        .function("numVertices", &TriangleMeshWrap::numVertices)
        .function("numFaces",    &TriangleMeshWrap::numFaces)
        .function("getVertices", &TriangleMeshWrap::getVertices)
        .function("getFaces",    &TriangleMeshWrap::getFaces)
        .function("setVertices", &TriangleMeshWrap::setVertices)
        .function("setFaces",    &TriangleMeshWrap::setFaces)
        ;

    function("meshToSDF",     &meshToSDF);
    function("sdfToMesh",     &sdfToMesh);
    function("makeManifold",  &makeManifold);

    function("dilate",        &dilate);
    function("erode",         &erode);
    function("morphOpen",     &morphOpen);
    function("morphClose",    &morphClose);

    function("gaussianFilter",  &gaussianFilter);
    function("meanFilter",      &meanFilter);
    function("laplacianFilter", &laplacianFilter);

    function("csgUnion",        &csgUnion);
    function("csgIntersection", &csgIntersection);
    function("csgDifference",   &csgDifference);

    function("surfaceArea", &surfaceArea);
    function("volume",      &volume);
}
