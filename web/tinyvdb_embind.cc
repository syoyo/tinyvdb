/*
 * tinyvdb_embind.cc — Emscripten/Embind bindings for TinyVDB.
 *
 * Exposes: VDB file I/O (from memory), mesh-to-SDF, SDF-to-mesh, CSG,
 *          morphology, filtering, measurement, differential operators,
 *          ray casting, and more.
 *
 * Build with Emscripten: emcmake cmake .. && emmake make
 */

#include <emscripten/bind.h>
#include <emscripten/val.h>

#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

/* C I/O library */
#include "tinyvdb_io.h"

/* C++ mesh & ops (include implementations here) */
#define TINYVDB_MESH_IMPLEMENTATION
#include "tinyvdb_mesh.h"

#define TINYVDB_OPS_IMPLEMENTATION
#include "tinyvdb_ops.h"

using namespace emscripten;

/* ======================================================================== */
/*  Helper: typed_memory_view for returning data to JS without copy          */
/* ======================================================================== */

/* ======================================================================== */
/*  VDB File I/O wrapper (memory-based, no filesystem)                      */
/* ======================================================================== */

class VDBFile {
public:
    VDBFile() : is_open_(false) { memset(&file_, 0, sizeof(file_)); }
    ~VDBFile() { close(); }

    void openMemory(const std::string &data) {
        close();
        tvdb_error_t err;
        memset(&err, 0, sizeof(err));
        buf_ = data;
        tvdb_status_t st = tvdb_file_open_memory(
            &file_, reinterpret_cast<const uint8_t *>(buf_.data()),
            buf_.size(), NULL, &err);
        if (st != TVDB_OK)
            throw std::runtime_error(
                std::string("openMemory failed: ") + err.message);
        is_open_ = true;
    }

    /* Accept Uint8Array from JS (avoids String.fromCharCode limits) */
    void openMemoryFromArray(const val &arr) {
        close();
        unsigned len = arr["length"].as<unsigned>();
        buf_.resize(len);
        /* Copy from JS typed array into C++ buffer */
        val memview = val(typed_memory_view(len,
            reinterpret_cast<uint8_t *>(&buf_[0])));
        memview.call<void>("set", arr);

        tvdb_error_t err;
        memset(&err, 0, sizeof(err));
        tvdb_status_t st = tvdb_file_open_memory(
            &file_, reinterpret_cast<const uint8_t *>(buf_.data()),
            buf_.size(), NULL, &err);
        if (st != TVDB_OK)
            throw std::runtime_error(
                std::string("openMemory failed: ") + err.message);
        is_open_ = true;
    }

    void readGrids() {
        checkOpen();
        tvdb_error_t err;
        memset(&err, 0, sizeof(err));
        tvdb_status_t st = tvdb_read_all_grids(&file_, &err);
        if (st != TVDB_OK)
            throw std::runtime_error(
                std::string("readGrids failed: ") + err.message);
    }

    void close() {
        if (is_open_) { tvdb_file_close(&file_); is_open_ = false; }
        buf_.clear();
    }

    int gridCount() const {
        return is_open_ ? (int)tvdb_grid_count(&file_) : 0;
    }

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
        tvdb_error_t err;
        memset(&err, 0, sizeof(err));
        uint8_t *out = NULL;
        size_t out_sz = 0;
        tvdb_status_t st = tvdb_write_to_memory(
            &file_, (uint32_t)compression, level, &out, &out_sz, &err);
        if (st != TVDB_OK) {
            throw std::runtime_error(
                std::string("toBytes failed: ") + err.message);
        }
        val result = val(typed_memory_view(out_sz, out));
        /* Copy into JS Uint8Array so we can free */
        val js_arr = val::global("Uint8Array").new_(result);
        free(out);
        return js_arr;
    }

    /* Header as JS object */
    val header() const {
        checkOpen();
        val h = val::object();
        h.set("fileVersion", (int)file_.header.file_version);
        h.set("majorVersion", (int)file_.header.major_version);
        h.set("minorVersion", (int)file_.header.minor_version);
        h.set("compressionFlags", (int)file_.header.compression_flags);
        h.set("uuid", std::string(file_.header.uuid));
        return h;
    }

    /* Grid metadata as JS object */
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

    /* Grid transform as JS object */
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

    /* Tree info for a grid */
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
        d.set("type", std::string(types[n.type]));
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
        if (!is_open_)
            throw std::runtime_error("VDB file is not open");
    }

    tvdb_file_t file_;
    bool is_open_;
    std::string buf_;  /* keep data alive for open_memory */
};

/* ======================================================================== */
/*  DenseGrid wrapper                                                       */
/* ======================================================================== */

class DenseGridWrap {
public:
    tvdb_mesh::DenseGrid grid;

    DenseGridWrap() { grid.nx = grid.ny = grid.nz = 0; grid.voxel_size = 1; }

    DenseGridWrap(int nx, int ny, int nz, float vs)  {
        grid.nx = nx; grid.ny = ny; grid.nz = nz;
        grid.ox = grid.oy = grid.oz = 0;
        grid.voxel_size = vs;
        grid.data.assign((size_t)nx * ny * nz, 0.0f);
    }

    int getNx() const { return grid.nx; }
    int getNy() const { return grid.ny; }
    int getNz() const { return grid.nz; }
    float getOx() const { return grid.ox; }
    float getOy() const { return grid.oy; }
    float getOz() const { return grid.oz; }
    float getVoxelSize() const { return grid.voxel_size; }
    int size() const { return (int)grid.data.size(); }

    float get(int x, int y, int z) const { return grid.at(x, y, z); }
    void set(int x, int y, int z, float v) { grid.at(x, y, z) = v; }

    /* Return data as JS Float32Array (copy) */
    val getData() const {
        return val(typed_memory_view(grid.data.size(), grid.data.data()));
    }

    /* Set data from JS Float32Array */
    void setData(const val &arr) {
        size_t n = (size_t)grid.nx * grid.ny * grid.nz;
        grid.data.resize(n);
        val memview = val(typed_memory_view(n, grid.data.data()));
        memview.call<void>("set", arr);
    }
};

/* ======================================================================== */
/*  TriangleMesh wrapper                                                    */
/* ======================================================================== */

class TriangleMeshWrap {
public:
    tvdb_mesh::TriangleMesh mesh;

    int numVertices() const { return (int)mesh.vertices.size(); }
    int numFaces() const { return (int)mesh.faces.size(); }

    /* Return vertices as Float32Array (3 * nv floats) */
    val getVertices() const {
        return val(typed_memory_view(
            mesh.vertices.size() * 3,
            reinterpret_cast<const float *>(mesh.vertices.data())));
    }

    /* Return faces as Uint32Array (3 * nf uint32) */
    val getFaces() const {
        return val(typed_memory_view(
            mesh.faces.size() * 3,
            reinterpret_cast<const uint32_t *>(mesh.faces.data())));
    }

    /* Set vertices from Float32Array (3N floats) */
    void setVertices(const val &arr) {
        unsigned len = arr["length"].as<unsigned>();
        mesh.vertices.resize(len / 3);
        val memview = val(typed_memory_view(
            len, reinterpret_cast<float *>(mesh.vertices.data())));
        memview.call<void>("set", arr);
    }

    /* Set faces from Uint32Array (3N uint32) */
    void setFaces(const val &arr) {
        unsigned len = arr["length"].as<unsigned>();
        mesh.faces.resize(len / 3);
        val memview = val(typed_memory_view(
            len, reinterpret_cast<uint32_t *>(mesh.faces.data())));
        memview.call<void>("set", arr);
    }
};

/* ======================================================================== */
/*  Free functions                                                          */
/* ======================================================================== */

/* --- Mesh --- */

DenseGridWrap meshToSDF(TriangleMeshWrap &m, float voxelSize,
                        float bandWidth, int signMethod) {
    DenseGridWrap result;
    bool ok = tvdb_mesh::MeshToSDF_VDB(
        m.mesh, voxelSize, bandWidth, &result.grid,
        static_cast<tvdb_mesh::SignMethod>(signMethod));
    if (!ok) throw std::runtime_error("MeshToSDF_VDB failed");
    return result;
}

TriangleMeshWrap sdfToMesh(const DenseGridWrap &g, float isovalue) {
    TriangleMeshWrap result;
    bool ok = tvdb_mesh::SDFToMesh(g.grid, isovalue, &result.mesh);
    if (!ok) throw std::runtime_error("SDFToMesh failed");
    return result;
}

TriangleMeshWrap makeManifold(TriangleMeshWrap &m, double resolution,
                              double isovalue, int signMethod) {
    TriangleMeshWrap result;
    bool ok = tvdb_mesh::MakeManifold_VDB(
        m.mesh, resolution, isovalue, &result.mesh,
        static_cast<tvdb_mesh::SignMethod>(signMethod));
    if (!ok) throw std::runtime_error("MakeManifold_VDB failed");
    return result;
}

/* --- Morphology --- */

DenseGridWrap dilate(const DenseGridWrap &g, int iterations) {
    DenseGridWrap r; r.grid = g.grid;
    tvdb_ops::Dilate(&r.grid, iterations);
    return r;
}
DenseGridWrap erode(const DenseGridWrap &g, int iterations) {
    DenseGridWrap r; r.grid = g.grid;
    tvdb_ops::Erode(&r.grid, iterations);
    return r;
}
DenseGridWrap morphOpen(const DenseGridWrap &g, int iterations) {
    DenseGridWrap r; r.grid = g.grid;
    tvdb_ops::Open(&r.grid, iterations);
    return r;
}
DenseGridWrap morphClose(const DenseGridWrap &g, int iterations) {
    DenseGridWrap r; r.grid = g.grid;
    tvdb_ops::Close(&r.grid, iterations);
    return r;
}

/* --- Filtering --- */

DenseGridWrap gaussianFilter(const DenseGridWrap &g, int width, int iterations) {
    DenseGridWrap r; r.grid = g.grid;
    tvdb_ops::GaussianFilter(&r.grid, width, iterations);
    return r;
}
DenseGridWrap meanFilter(const DenseGridWrap &g, int width, int iterations) {
    DenseGridWrap r; r.grid = g.grid;
    tvdb_ops::MeanFilter(&r.grid, width, iterations);
    return r;
}
DenseGridWrap laplacianFilter(const DenseGridWrap &g, int iterations) {
    DenseGridWrap r; r.grid = g.grid;
    tvdb_ops::LaplacianFilter(&r.grid, iterations);
    return r;
}

/* --- CSG --- */

DenseGridWrap csgUnion(const DenseGridWrap &a, const DenseGridWrap &b) {
    DenseGridWrap r;
    tvdb_ops::CSGUnion(a.grid, b.grid, &r.grid);
    return r;
}
DenseGridWrap csgIntersection(const DenseGridWrap &a, const DenseGridWrap &b) {
    DenseGridWrap r;
    tvdb_ops::CSGIntersection(a.grid, b.grid, &r.grid);
    return r;
}
DenseGridWrap csgDifference(const DenseGridWrap &a, const DenseGridWrap &b) {
    DenseGridWrap r;
    tvdb_ops::CSGDifference(a.grid, b.grid, &r.grid);
    return r;
}

/* --- Measurement --- */

float surfaceArea(const DenseGridWrap &g) { return tvdb_ops::SurfaceArea(g.grid); }
float volume(const DenseGridWrap &g) { return tvdb_ops::Volume(g.grid); }

/* --- Ray casting --- */

val rayCastSDF(const DenseGridWrap &g,
               float ox, float oy, float oz,
               float dx, float dy, float dz, float maxT) {
    tvdb_mesh::Vec3f origin = {ox, oy, oz};
    tvdb_mesh::Vec3f dir = {dx, dy, dz};
    tvdb_ops::RayHit hit;
    bool ok = tvdb_ops::RayCastSDF(g.grid, origin, dir, maxT, &hit);
    if (!ok) return val::null();
    val r = val::object();
    r.set("t", hit.t);
    val pos = val::array();
    pos.call<void>("push", hit.position.x);
    pos.call<void>("push", hit.position.y);
    pos.call<void>("push", hit.position.z);
    r.set("position", pos);
    val norm = val::array();
    norm.call<void>("push", hit.normal.x);
    norm.call<void>("push", hit.normal.y);
    norm.call<void>("push", hit.normal.z);
    r.set("normal", norm);
    return r;
}

/* ======================================================================== */
/*  Embind registration                                                     */
/* ======================================================================== */

EMSCRIPTEN_BINDINGS(tinyvdb) {

    /* --- Constants --- */
    constant("COMPRESS_NONE",        (int)TVDB_COMPRESS_NONE);
    constant("COMPRESS_ZIP",         (int)TVDB_COMPRESS_ZIP);
    constant("COMPRESS_ACTIVE_MASK", (int)TVDB_COMPRESS_ACTIVE_MASK);
    constant("COMPRESS_BLOSC",       (int)TVDB_COMPRESS_BLOSC);
    constant("SIGN_FLOOD_FILL",      0);
    constant("SIGN_SWEEP",           1);

    /* --- VDBFile --- */
    class_<VDBFile>("VDBFile")
        .constructor<>()
        .function("openMemory",          &VDBFile::openMemory)
        .function("openMemoryFromArray", &VDBFile::openMemoryFromArray)
        .function("readGrids",     &VDBFile::readGrids)
        .function("close",         &VDBFile::close)
        .function("gridCount",     &VDBFile::gridCount)
        .function("gridName",      &VDBFile::gridName)
        .function("gridTypeName",  &VDBFile::gridTypeName)
        .function("toBytes",       &VDBFile::toBytes)
        .function("header",        &VDBFile::header)
        .function("gridMetadata",  &VDBFile::gridMetadata)
        .function("gridTransform", &VDBFile::gridTransform)
        .function("treeNodeCount", &VDBFile::treeNodeCount)
        .function("treeNodeInfo",  &VDBFile::treeNodeInfo)
        ;

    /* --- DenseGrid --- */
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

    /* --- TriangleMesh --- */
    class_<TriangleMeshWrap>("TriangleMesh")
        .constructor<>()
        .function("numVertices",  &TriangleMeshWrap::numVertices)
        .function("numFaces",     &TriangleMeshWrap::numFaces)
        .function("getVertices",  &TriangleMeshWrap::getVertices)
        .function("getFaces",     &TriangleMeshWrap::getFaces)
        .function("setVertices",  &TriangleMeshWrap::setVertices)
        .function("setFaces",     &TriangleMeshWrap::setFaces)
        ;

    /* --- Mesh functions --- */
    function("meshToSDF",     &meshToSDF);
    function("sdfToMesh",     &sdfToMesh);
    function("makeManifold",  &makeManifold);

    /* --- Morphology --- */
    function("dilate",     &dilate);
    function("erode",      &erode);
    function("morphOpen",  &morphOpen);
    function("morphClose", &morphClose);

    /* --- Filtering --- */
    function("gaussianFilter",  &gaussianFilter);
    function("meanFilter",      &meanFilter);
    function("laplacianFilter", &laplacianFilter);

    /* --- CSG --- */
    function("csgUnion",        &csgUnion);
    function("csgIntersection", &csgIntersection);
    function("csgDifference",   &csgDifference);

    /* --- Measurement --- */
    function("surfaceArea", &surfaceArea);
    function("volume",      &volume);

    /* --- Ray casting --- */
    function("rayCastSDF",  &rayCastSDF);
}
