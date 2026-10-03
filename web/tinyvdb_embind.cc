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
#include "tinyvdb_mesh_conversion.h"
#include "tinyvdb_ops.h"
#include "tinyvdb_levelset.h"
#include "tinyvdb_ray.h"
#include "tinyvdb_topology.h"
#include "tinyvdb_stats.h"
#include "tinyvdb_sparse.h"

using namespace emscripten;

/* Error channel.
 *
 * This module is built with -fno-exceptions (see web/CMakeLists.txt), and
 * embind cannot carry a C++ exception message across the boundary anyway: with
 * exceptions enabled JS still caught a bare pointer (e.g. 120424) instead of
 * the text. So failures are reported the C way -- record a message, return a
 * null/empty result -- and JS reads it back with TinyVDB.lastError().
 *
 * Every fallible wrapper below sets this before returning, so a JS caller that
 * checks the result cannot miss it. lastError() is cleared on entry to each
 * fallible call, so it always describes the most recent failure. */
static thread_local std::string g_last_error;

static void setLastError(const std::string &m) { g_last_error = m; }
static void clearLastError() { g_last_error.clear(); }

static std::string lastError() { return g_last_error; }

/* Convenience for the common "native call returned false" shape. */
template <typename T>
static T fail(const std::string &m) {
    setLastError(m);
    return T();
}

static void failVoid(const std::string &m) { setLastError(m); }

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
        if (st != TVDB_OK) {
            failVoid(std::string("openMemory failed: ") + err.message);
            return;
        }
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
        if (st != TVDB_OK) {
            failVoid(std::string("openMemory failed: ") + err.message);
            return;
        }
        is_open_ = true;
    }

    void readGrids() {
        clearLastError();
        if (!checkOpen()) return;
        tvdb_error_t err; memset(&err, 0, sizeof(err));
        tvdb_status_t st = tvdb_read_all_grids(&file_, &err);
        if (st != TVDB_OK)
            failVoid(std::string("readGrids failed: ") + err.message); return;
    }

    void close() {
        if (is_open_) { tvdb_file_close(&file_); is_open_ = false; }
        buf_.clear();
    }

    int gridCount() const { return is_open_ ? (int)tvdb_grid_count(&file_) : 0; }

    std::string gridName(int idx) const {
        if (!checkOpen()) return std::string();
        const char *n = tvdb_grid_name(&file_, (size_t)idx);
        return n ? n : "";
    }

    std::string gridTypeName(int idx) const {
        if (!checkOpen()) return std::string();
        const char *n = tvdb_grid_type_name(&file_, (size_t)idx);
        return n ? n : "";
    }

    val toBytes(int compression, int level) const {
        if (!checkOpen()) return val::undefined();
        tvdb_error_t err; memset(&err, 0, sizeof(err));
        uint8_t *out = NULL; size_t out_sz = 0;
        tvdb_status_t st = tvdb_write_to_memory(
            &file_, (uint32_t)compression, level, &out, &out_sz, &err);
        if (st != TVDB_OK) {
            failVoid(std::string("toBytes failed: ") + err.message);
            return val::null();
        }
        val view = val(typed_memory_view(out_sz, out));
        val js_arr = val::global("Uint8Array").new_(view);
        free(out);
        return js_arr;
    }

    val header() const {
        if (!checkOpen()) return val::undefined();
        val h = val::object();
        h.set("fileVersion",      (int)file_.header.file_version);
        h.set("majorVersion",     (int)file_.header.major_version);
        h.set("minorVersion",     (int)file_.header.minor_version);
        h.set("compressionFlags", (int)file_.header.compression_flags);
        h.set("uuid",             std::string(file_.header.uuid));
        return h;
    }

    val gridMetadata(int idx) const {
        if (!checkOpen()) return val::undefined();
        if ((size_t)idx >= file_.num_grids)
            failVoid("grid index out of range"); return val::undefined();
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
        if (!checkOpen()) return val::undefined();
        if ((size_t)idx >= file_.num_grids)
            failVoid("grid index out of range"); return val::undefined();
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
        if (!checkOpen()) return 0;
        if ((size_t)idx >= file_.num_grids) return 0;
        return (int)file_.grids[idx].tree.num_nodes;
    }

    val treeNodeInfo(int gridIdx, int nodeIdx) const {
        if (!checkOpen()) return val::undefined();
        if ((size_t)gridIdx >= file_.num_grids)
            failVoid("grid index out of range"); return val::undefined();
        const tvdb_tree_t &tree = file_.grids[gridIdx].tree;
        if ((size_t)nodeIdx >= tree.num_nodes)
            failVoid("node index out of range"); return val::undefined();
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
    /* Returns false and records the error when the file is not open. Every
     * caller must bail out: continuing would dereference an unopened
     * tvdb_file_t. */
    bool checkOpen() const {
        if (!is_open_) { setLastError("VDB file is not open"); return false; }
        return true;
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
/*  DenseVecGrid wrapper (3-component vector field, interleaved)           */
/* ======================================================================== */

class DenseVecGridWrap {
public:
    tvdb_dense_vec_grid grid;

    DenseVecGridWrap() {
        std::memset(&grid, 0, sizeof(grid));
        grid.voxel_size = 1.0f;
    }

    DenseVecGridWrap(int nx, int ny, int nz, float vs) {
        tvdb_dense_vec_grid_init(&grid, nx, ny, nz);
        grid.voxel_size = vs;
    }

    /* Initialise before copyFrom: it frees `grid` first, which on a raw
     * uninitialized member would free a wild pointer. The copy constructor has
     * no destructor to have run yet. */
    DenseVecGridWrap(const DenseVecGridWrap& other) {
        tvdb_dense_vec_grid_init(&grid, 0, 0, 0);
        copyFrom(other.grid);
    }

    DenseVecGridWrap& operator=(const DenseVecGridWrap& other) {
        if (this != &other) copyFrom(other.grid);
        return *this;
    }

    ~DenseVecGridWrap() { tvdb_dense_vec_grid_free(&grid); }

    int   getNx() const { return grid.nx; }
    int   getNy() const { return grid.ny; }
    int   getNz() const { return grid.nz; }
    float getVoxelSize() const { return grid.voxel_size; }
    int   size() const { return grid.nx * grid.ny * grid.nz; }

    /* The three components are contiguous in the interleaved buffer, so this
     * returns a zero-copy Float32Array view of just that voxel's (x,y,z).
     * Out-parameters (float&) are not bindable by embind. */
    val get(int x, int y, int z) const {
        const size_t i = (((size_t)z * grid.ny + y) * grid.nx + x) * 3u;
        return val(typed_memory_view(3, &grid.data[i]));
    }
    void set(int x, int y, int z, float cx, float cy, float cz) {
        const size_t i = (((size_t)z * grid.ny + y) * grid.nx + x) * 3u;
        grid.data[i + 0] = cx; grid.data[i + 1] = cy; grid.data[i + 2] = cz;
    }

    val getData() const {
        const size_t n = (size_t)grid.nx * grid.ny * grid.nz * 3u;
        return val(typed_memory_view(n, grid.data));
    }

    void setData(const val& arr) {
        const size_t n = (size_t)grid.nx * grid.ny * grid.nz * 3u;
        val memview = val(typed_memory_view(n, grid.data));
        memview.call<void>("set", arr);
    }

private:
    void copyFrom(const tvdb_dense_vec_grid& o) {
        tvdb_dense_vec_grid_free(&grid);
        tvdb_dense_vec_grid_init(&grid, o.nx, o.ny, o.nz);
        grid.ox = o.ox; grid.oy = o.oy; grid.oz = o.oz;
        grid.voxel_size = o.voxel_size;
        const size_t n = (size_t)grid.nx * grid.ny * grid.nz * 3u;
        if (grid.data && o.data && n)
            std::memcpy(grid.data, o.data, n * sizeof(float));
    }
};

/* ======================================================================== */
/*  SparseGrid wrapper (RAII over tvdb_sparse_grid)                         */
/*                                                                        */
/*  coords/values are handed to JS as copies rather than views: a sparse    */
/*  grid can be reallocated by any subsequent op, and a stale view would    */
/*  silently read freed memory. tvdb_grid_batch_view() returns borrowed     */
/*  non-owning views, so this class always owns what it wraps.              */
/* ======================================================================== */

class SparseGridWrap {
public:
    tvdb_sparse_grid sg;

    SparseGridWrap() { tvdb_sparse_grid_init(&sg); }
    ~SparseGridWrap() { tvdb_sparse_grid_free(&sg); }

    SparseGridWrap(const SparseGridWrap& other) {
        tvdb_sparse_grid_init(&sg);
        copyFrom(other.sg);
    }
    SparseGridWrap& operator=(const SparseGridWrap& other) {
        if (this != &other) copyFrom(other.sg);
        return *this;
    }

    int   count() const { return (int)sg.count; }
    float getVoxelSize() const { return sg.voxel_size; }
    float getOx() const { return sg.ox; }
    float getOy() const { return sg.oy; }
    float getOz() const { return sg.oz; }

    /* Copies, not views: tvdb_vec3i is a struct so typed_memory_view cannot
     * take it directly, and more importantly a later op may reallocate the
     * coordinate array, which would leave JS holding a dangling view. */
    val getCoords() const {
        val out = val::global("Int32Array").new_((unsigned)(sg.count * 3));
        if (sg.count && sg.coords) {
            val mv = val::global("Int32Array").new_((unsigned)(sg.count * 3));
            for (size_t i = 0; i < sg.count; ++i) {
                mv.set(3 * i + 0, sg.coords[i].x);
                mv.set(3 * i + 1, sg.coords[i].y);
                mv.set(3 * i + 2, sg.coords[i].z);
            }
            out = mv;
        }
        return out;
    }
    val getValues() const {
        val out = val::global("Float32Array").new_((unsigned)sg.count);
        if (sg.count && sg.values) {
            val mv = val::global("Float32Array").new_((unsigned)sg.count);
            for (size_t i = 0; i < sg.count; ++i) mv.set((unsigned)i, sg.values[i]);
            out = mv;
        }
        return out;
    }

    /* Value lookup by integer coordinate; background when absent. */
    float valueAt(int x, int y, int z, float background) const {
        for (size_t i = 0; i < sg.count; ++i)
            if (sg.coords[i].x == x && sg.coords[i].y == y && sg.coords[i].z == z)
                return sg.values[i];
        return background;
    }

private:
    void copyFrom(const tvdb_sparse_grid& o) {
        tvdb_sparse_grid_free(&sg);
        tvdb_sparse_grid_init(&sg);
        sg.voxel_size = o.voxel_size;
        sg.ox = o.ox; sg.oy = o.oy; sg.oz = o.oz;
        if (o.count && tvdb_sparse_grid_reserve(&sg, o.count)) {
            if (o.coords) std::memcpy(sg.coords, o.coords, o.count * sizeof(tvdb_vec3i));
            if (o.values) std::memcpy(sg.values, o.values, o.count * sizeof(float));
            sg.count = o.count;
        }
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
    clearLastError();
    DenseGridWrap result;
    tvdb_sign_method sm = (signMethod == 1) ? TVDB_SIGN_SWEEP
                                              : TVDB_SIGN_FLOOD_FILL;
    bool ok = tvdb_mesh_to_sdf_vdb(&m.mesh, voxelSize, bandWidth,
                                    &result.grid, sm, /*arena=*/nullptr);
    if (!ok) { failVoid("tvdb_mesh_to_sdf_vdb failed"); return DenseGridWrap(); }
    return result;
}

TriangleMeshWrap sdfToMesh(const DenseGridWrap &g, float isovalue) {
    clearLastError();
    TriangleMeshWrap result;
    bool ok = tvdb_sdf_to_mesh(&g.grid, isovalue, &result.mesh,
                                /*arena=*/nullptr);
    if (!ok) { failVoid("tvdb_sdf_to_mesh failed"); return TriangleMeshWrap(); }
    return result;
}

TriangleMeshWrap makeManifold(TriangleMeshWrap &m, double resolution,
                              double isovalue, int signMethod) {
    clearLastError();
    TriangleMeshWrap result;
    tvdb_sign_method sm = (signMethod == 1) ? TVDB_SIGN_SWEEP
                                              : TVDB_SIGN_FLOOD_FILL;
    bool ok = tvdb_make_manifold_vdb(&m.mesh, resolution, isovalue,
                                      &result.mesh, sm, /*arena=*/nullptr);
    if (!ok) { failVoid("tvdb_make_manifold_vdb failed"); return TriangleMeshWrap(); }
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
/*  Mesh conversion, hardened variants                                     */
/*                                                                        */
/*  The legacy bool wrappers above cannot report *why* they failed. These   */
/*  wrap the _ex entry points, which return a tvdb_error_t, and add the    */
/*  outward-winding option the legacy path lacks.                          */
/* ======================================================================== */

static void throwOnError(tvdb_status_t st, const tvdb_error_t &err, const char *what) {
    if (st != TVDB_OK) {
        std::string msg = what;
        if (err.message[0]) { msg += ": "; msg += err.message; }
        failVoid(msg);
    }
}

DenseGridWrap meshToSDFEx(TriangleMeshWrap &m, float voxelSize, float bandWidth, int signMethod) {
    clearLastError();
    tvdb_error_t err; std::memset(&err, 0, sizeof(err));
    DenseGridWrap out;
    /* pool = NULL (serial; TINYVDB_THREAD_NONE forces size 1 anyway)
     * arena = NULL (malloc), matching the legacy wrappers above. */
    throwOnError(tvdb_mesh_to_sdf_ex(&m.mesh, voxelSize, bandWidth, /*pool=*/NULL,
                                     &out.grid, /*arena=*/NULL, &err),
                 err, "meshToSDFEx");
    return out;
}

TriangleMeshWrap sdfToMeshEx(const DenseGridWrap &g, float isovalue, int winding) {
    clearLastError();
    tvdb_error_t err; std::memset(&err, 0, sizeof(err));
    TriangleMeshWrap out;
    tvdb_mesh_winding_t w = (winding == 1) ? TVDB_MESH_WINDING_OUTWARD
                                          : TVDB_MESH_WINDING_TABLE;
    throwOnError(tvdb_sdf_to_mesh_ex(&g.grid, isovalue, w, /*pool=*/NULL,
                                     &out.mesh, /*arena=*/NULL, &err),
                 err, "sdfToMeshEx");
    return out;
}

/* Marching-cubes lookup tables, for callers that want to run their own
 * surface extraction in JS. Static storage, no ownership. */
val mcEdgeTable()    { return val(typed_memory_view(256, tvdb_mc_edge_table())); }
val mcTriTableFlat() { return val(typed_memory_view(256 * 16, tvdb_mc_tri_table_flat())); }

/* ======================================================================== */
/*  Dense grid operators                                                   */
/* ======================================================================== */

namespace {
/* `result` is pre-allocated and the inputs must be the same shape, so build
 * the target from `a` and reject a mismatch rather than scribbling past it. */
/* Returns false and records the error when the shapes differ. Callers MUST
   bail: tvdb_comp_* writes elementwise into a result sized like `a`, so a
   smaller `b` would be read past its end. */
bool requireSameShape(const DenseGridWrap &a, const DenseGridWrap &b, const char *what) {
    if (a.grid.nx != b.grid.nx || a.grid.ny != b.grid.ny || a.grid.nz == 0
        || b.grid.nz == 0 || a.grid.nz != b.grid.nz || a.grid.ny != b.grid.ny
        || a.grid.nx != b.grid.nx) {
        failVoid(std::string(what) + ": grid shapes differ (" +
            std::to_string(a.grid.nx) + "x" + std::to_string(a.grid.ny) + "x" + std::to_string(a.grid.nz) +
            " vs " + std::to_string(b.grid.nx) + "x" + std::to_string(b.grid.ny) + "x" + std::to_string(b.grid.nz) + ")");
        return false;
    }
    return true;
}

template <void (*Fn)(const tvdb_dense_grid *, const tvdb_dense_grid *, tvdb_dense_grid *)>
DenseGridWrap compOp(const DenseGridWrap &a, const DenseGridWrap &b, const char *what) {
    if (!requireSameShape(a, b, what)) return DenseGridWrap();
    DenseGridWrap r;
    tvdb_dense_grid_init(&r.grid, a.grid.nx, a.grid.ny, a.grid.nz);
    r.grid.ox = a.grid.ox; r.grid.oy = a.grid.oy; r.grid.oz = a.grid.oz;
    r.grid.voxel_size = a.grid.voxel_size;
    Fn(&a.grid, &b.grid, &r.grid);
    return r;
}
} // namespace

DenseGridWrap compMax(const DenseGridWrap &a, const DenseGridWrap &b) {
    return compOp<tvdb_comp_max>(a, b, "compMax");
}
DenseGridWrap compMin(const DenseGridWrap &a, const DenseGridWrap &b) {
    return compOp<tvdb_comp_min>(a, b, "compMin");
}
DenseGridWrap compSum(const DenseGridWrap &a, const DenseGridWrap &b) {
    return compOp<tvdb_comp_sum>(a, b, "compSum");
}
DenseGridWrap compMult(const DenseGridWrap &a, const DenseGridWrap &b) {
    return compOp<tvdb_comp_mult>(a, b, "compMult");
}

void medianFilter(DenseGridWrap &g, int radius, int iterations) {
    tvdb_median_filter(&g.grid, radius, iterations);
}
void meanCurvatureFlow(DenseGridWrap &g, float dt, int iterations) {
    tvdb_mean_curvature_flow(&g.grid, dt, iterations);
}
void signedFloodFill(DenseGridWrap &g, float bandWorld) {
    clearLastError();
    tvdb_signed_flood_fill(&g.grid, bandWorld);
}
int  fastSweeping(DenseGridWrap &g, float frozenBand, int maxIters, float tol) {
    return tvdb_fast_sweeping(&g.grid, frozenBand, maxIters, tol);
}

float centralDiffX(const DenseGridWrap &g, int x, int y, int z) {
    return tvdb_central_diff_x(&g.grid, x, y, z);
}
float centralDiffY(const DenseGridWrap &g, int x, int y, int z) {
    return tvdb_central_diff_y(&g.grid, x, y, z);
}
float centralDiffZ(const DenseGridWrap &g, int x, int y, int z) {
    return tvdb_central_diff_z(&g.grid, x, y, z);
}

/* --- vector fields --- */

DenseVecGridWrap gradient(const DenseGridWrap &g) {
    DenseVecGridWrap out(g.grid.nx, g.grid.ny, g.grid.nz, g.grid.voxel_size);
    out.grid.ox = g.grid.ox; out.grid.oy = g.grid.oy; out.grid.oz = g.grid.oz;
    tvdb_gradient(&g.grid, &out.grid);
    return out;
}
DenseGridWrap divergence(const DenseVecGridWrap &v) {
    DenseGridWrap out;
    tvdb_dense_grid_init(&out.grid, v.grid.nx, v.grid.ny, v.grid.nz);
    out.grid.ox = v.grid.ox; out.grid.oy = v.grid.oy; out.grid.oz = v.grid.oz;
    out.grid.voxel_size = v.grid.voxel_size;
    tvdb_divergence(&v.grid, &out.grid);
    return out;
}
DenseVecGridWrap curl(const DenseVecGridWrap &v) {
    DenseVecGridWrap out(v.grid.nx, v.grid.ny, v.grid.nz, v.grid.voxel_size);
    out.grid.ox = v.grid.ox; out.grid.oy = v.grid.oy; out.grid.oz = v.grid.oz;
    tvdb_curl(&v.grid, &out.grid);
    return out;
}
DenseGridWrap magnitude(const DenseVecGridWrap &v) {
    DenseGridWrap out;
    tvdb_dense_grid_init(&out.grid, v.grid.nx, v.grid.ny, v.grid.nz);
    out.grid.ox = v.grid.ox; out.grid.oy = v.grid.oy; out.grid.oz = v.grid.oz;
    out.grid.voxel_size = v.grid.voxel_size;
    tvdb_magnitude(&v.grid, &out.grid);
    return out;
}
DenseVecGridWrap normalizeVec(const DenseVecGridWrap &v) {
    DenseVecGridWrap out(v.grid.nx, v.grid.ny, v.grid.nz, v.grid.voxel_size);
    out.grid.ox = v.grid.ox; out.grid.oy = v.grid.oy; out.grid.oz = v.grid.oz;
    tvdb_normalize_vec(&v.grid, &out.grid);
    return out;
}
/* Closest-point transform: world positions p - sdf(p) * grad(sdf)(p). */
DenseVecGridWrap closestPointTransform(const DenseGridWrap &sdf) {
    DenseVecGridWrap out(sdf.grid.nx, sdf.grid.ny, sdf.grid.nz, sdf.grid.voxel_size);
    out.grid.ox = sdf.grid.ox; out.grid.oy = sdf.grid.oy; out.grid.oz = sdf.grid.oz;
    tvdb_cpt(&sdf.grid, &out.grid);
    return out;
}

/* --- advection --- */

DenseGridWrap advectSemiLagrangian(const DenseGridWrap &field, const DenseVecGridWrap &vel,
                                   float dt) {
    DenseGridWrap out;
    tvdb_dense_grid_init(&out.grid, field.grid.nx, field.grid.ny, field.grid.nz);
    out.grid.ox = field.grid.ox; out.grid.oy = field.grid.oy; out.grid.oz = field.grid.oz;
    out.grid.voxel_size = field.grid.voxel_size;
    tvdb_advect_semi_lagrangian(&field.grid, &vel.grid, dt, &out.grid);
    return out;
}
DenseGridWrap advect(const DenseGridWrap &field, const DenseVecGridWrap &vel,
                     float dt, int scheme, int clamp) {
    DenseGridWrap out;
    tvdb_dense_grid_init(&out.grid, field.grid.nx, field.grid.ny, field.grid.nz);
    out.grid.ox = field.grid.ox; out.grid.oy = field.grid.oy; out.grid.oz = field.grid.oz;
    out.grid.voxel_size = field.grid.voxel_size;
    tvdb_advect(&field.grid, &vel.grid, dt, scheme, clamp, &out.grid);
    return out;
}

/* ======================================================================== */
/*  Statistics and health checks                                            */
/* ======================================================================== */

val statistics(const DenseGridWrap &g) {
    clearLastError();
    tvdb_grid_stats_t s;
    if (!tvdb_grid_statistics(&g.grid, &s))
        return fail<val>("gridStatistics failed");
    val d = val::object();
    d.set("min",    s.min);
    d.set("max",    s.max);
    d.set("mean",   s.mean);
    d.set("stddev", s.stddev);
    d.set("sum",    s.sum);
    d.set("count",  (double)s.count);
    return d;
}

val histogram(const DenseGridWrap &g, double rangeMin, double rangeMax, int nbins) {
    clearLastError();
    if (nbins <= 0) return fail<val>("histogram: nbins must be > 0");
    std::vector<size_t> counts((size_t)nbins, 0);
    if (!tvdb_grid_histogram(&g.grid, rangeMin, rangeMax, nbins, counts.data()))
        return fail<val>("gridHistogram failed");
    return val(typed_memory_view((size_t)nbins, counts.data()));
}

val checkLevelSet(const DenseGridWrap &g, double bandWorld, double tol) {
    tvdb_level_set_check_t c;
    if (!tvdb_check_level_set(&g.grid, bandWorld, tol, &c))
        return fail<val>("checkLevelSet failed");
    val d = val::object();
    d.set("meanGradMag",  c.mean_grad_mag);
    d.set("maxGradError", c.max_grad_error);
    d.set("badFraction",  c.bad_fraction);
    d.set("bandCount",    (double)c.band_count);
    return d;
}

val checkFogVolume(const DenseGridWrap &g, double eps) {
    int valid = 0; double mn = 0.0, mx = 0.0;
    if (!tvdb_check_fog_volume(&g.grid, eps, &valid, &mn, &mx))
        return fail<val>("checkFogVolume failed");
    val d = val::object();
    d.set("valid", (bool)valid);
    d.set("min",   mn);
    d.set("max",   mx);
    return d;
}

/* ======================================================================== */
/*  Level-set generators and measures                                      */
/*                                                                        */
/*  Generators allocate the output grid, so these need no caller-sized     */
/*  target. Values are negative inside.                                    */
/* ======================================================================== */

namespace {
void requireOk(bool ok, const char *what) {
    if (!ok) setLastError(std::string(what) + " failed");
}
} // namespace

DenseGridWrap levelSetSphere(float radius, float cx, float cy, float cz,
                             float voxelSize, float halfWidth) {
    clearLastError();
    const float c[3] = {cx, cy, cz};
    DenseGridWrap out;
    requireOk(tvdb_level_set_sphere(radius, c, voxelSize, halfWidth, &out.grid),
              "levelSetSphere");
    return out;
}
DenseGridWrap levelSetBox(float hx, float hy, float hz, float cx, float cy, float cz,
                          float voxelSize, float halfWidth) {
    clearLastError();
    const float he[3] = {hx, hy, hz};
    const float c[3]  = {cx, cy, cz};
    DenseGridWrap out;
    requireOk(tvdb_level_set_box(he, c, voxelSize, halfWidth, &out.grid), "levelSetBox");
    return out;
}
DenseGridWrap levelSetTorus(float major, float minor, float cx, float cy, float cz,
                            float voxelSize, float halfWidth) {
    clearLastError();
    const float c[3] = {cx, cy, cz};
    DenseGridWrap out;
    requireOk(tvdb_level_set_torus(major, minor, c, voxelSize, halfWidth, &out.grid),
              "levelSetTorus");
    return out;
}
DenseGridWrap levelSetCapsule(float x0, float y0, float z0, float x1, float y1, float z1,
                              float radius, float voxelSize, float halfWidth) {
    clearLastError();
    const float p0[3] = {x0, y0, z0};
    const float p1[3] = {x1, y1, z1};
    DenseGridWrap out;
    requireOk(tvdb_level_set_capsule(p0, p1, radius, voxelSize, halfWidth, &out.grid),
              "levelSetCapsule");
    return out;
}
DenseGridWrap levelSetPlatonic(int faces, float radius, float cx, float cy, float cz,
                               float voxelSize, float halfWidth) {
    clearLastError();
    const float c[3] = {cx, cy, cz};
    DenseGridWrap out;
    requireOk(tvdb_level_set_platonic(faces, radius, c, voxelSize, halfWidth, &out.grid),
              "levelSetPlatonic");
    return out;
}

DenseGridWrap sdfToFogVolume(const DenseGridWrap &sdf, float halfWidth) {
    clearLastError();
    DenseGridWrap out;
    requireOk(tvdb_sdf_to_fog_volume(&sdf.grid, halfWidth, &out.grid), "sdfToFogVolume");
    return out;
}
DenseGridWrap sdfInteriorMask(const DenseGridWrap &sdf, float isovalue) {
    clearLastError();
    DenseGridWrap out;
    requireOk(tvdb_sdf_interior_mask(&sdf.grid, isovalue, &out.grid), "sdfInteriorMask");
    return out;
}
DenseGridWrap sdfEnclosedRegions(const DenseGridWrap &sdf, float isovalue, int connectivity) {
    clearLastError();
    DenseGridWrap out;
    requireOk(tvdb_sdf_extract_enclosed_regions(&sdf.grid, isovalue, connectivity, &out.grid),
              "sdfEnclosedRegions");
    return out;
}

double levelSetEulerCharacteristic(const DenseGridWrap &sdf, float isovalue) {
    return tvdb_level_set_euler_characteristic(&sdf.grid, isovalue);
}
int levelSetGenus(const DenseGridWrap &sdf, float isovalue) {
    return tvdb_level_set_genus(&sdf.grid, isovalue);
}
DenseGridWrap levelSetRebuild(const DenseGridWrap &sdf, float isovalue,
                              float voxelSize, float halfWidth, int signMethod) {
    tvdb_sign_method sm = (signMethod == 1) ? TVDB_SIGN_SWEEP : TVDB_SIGN_FLOOD_FILL;
    DenseGridWrap out;
    requireOk(tvdb_level_set_rebuild(&sdf.grid, isovalue, voxelSize, halfWidth, sm, &out.grid),
              "levelSetRebuild");
    return out;
}

/* ======================================================================== */
/*  Ray traversal                                                           */
/* ======================================================================== */

namespace {
/* DDA voxel enumeration. Two-call idiom: pass cap 0 / null out to size it. */
val voxelsAlongRay(const DenseGridWrap &g, float ox, float oy, float oz,
                   float dx, float dy, float dz, float tmin, float tmax,
                   bool countOnly) {
    tvdb_ray r;
    r.origin.x = ox; r.origin.y = oy; r.origin.z = oz;
    r.dir.x = dx;    r.dir.y = dy;    r.dir.z = dz;
    r.tmin = tmin;   r.tmax = tmax;
    const size_t cap = countOnly ? 0 : (size_t)g.grid.nx + (size_t)g.grid.ny + (size_t)g.grid.nz;
    std::vector<tvdb_vec3i> vox(cap ? cap : 1);
    tvdb_vec3i *out = countOnly ? NULL : vox.data();
    const size_t n = tvdb_voxels_along_ray_dense(&g.grid, &r, out, cap);
    if (countOnly || n > cap)
        return val((double)n);
    /* tvdb_vec3i is a struct of 3 ints; hand back a plain Int32Array. */
    val res = val::global("Int32Array").new_((unsigned)(n * 3));
    for (size_t i = 0; i < n; ++i) {
        res.set((unsigned)(3 * i + 0), vox[i].x);
        res.set((unsigned)(3 * i + 1), vox[i].y);
        res.set((unsigned)(3 * i + 2), vox[i].z);
    }
    return res;
}
} // namespace

val uniformRaySamples(float ox, float oy, float oz, float dx, float dy, float dz,
                      float tmin, float tmax, int nSamples, bool wantT) {
    tvdb_ray r;
    r.origin.x = ox; r.origin.y = oy; r.origin.z = oz;
    r.dir.x = dx;    r.dir.y = dy;    r.dir.z = dz;
    r.tmin = tmin;   r.tmax = tmax;
    if (nSamples <= 0) return fail<val>("uniformRaySamples: nSamples must be > 0");
    std::vector<tvdb_vec3f> pts((size_t)nSamples);
    std::vector<float> ts((size_t)nSamples);
    tvdb_uniform_ray_samples(&r, (size_t)nSamples, pts.data(), wantT ? ts.data() : NULL);
    if (wantT) return val(typed_memory_view((size_t)nSamples, ts.data()));
    return val(typed_memory_view((size_t)nSamples * 3, &pts[0].x));
}

val segmentsAlongRay(const DenseGridWrap &g, float ox, float oy, float oz,
                     float dx, float dy, float dz, float tmin, float tmax,
                     float isovalue, int stepCount, bool countOnly) {
    tvdb_ray r;
    r.origin.x = ox; r.origin.y = oy; r.origin.z = oz;
    r.dir.x = dx;    r.dir.y = dy;    r.dir.z = dz;
    r.tmin = tmin;   r.tmax = tmax;
    const size_t cap = countOnly ? 0 : (size_t)stepCount * 2u;
    std::vector<float> pairs(cap ? cap : 1);
    float *out = countOnly ? NULL : pairs.data();
    const size_t n = tvdb_segments_along_ray(&g.grid, &r, isovalue, (size_t)stepCount,
                                             out, cap);
    /* n is a count of *pairs*, and the buffer is 2 floats per pair. */
    if (countOnly || n > cap) return val((double)n);
    return val(typed_memory_view(n * 2, pairs.data()));
}

/* ======================================================================== */
/*  Resampling and grid topology                                            */
/* ======================================================================== */

namespace {
/* These all take an arena; NULL selects malloc, matching the other wrappers.
 * On failure the native call may already have allocated `tmp`, so it has to be
 * released before throwing -- WASM has no swap and a leaked grid is fatal. */
DenseGridWrap resampleLike(tvdb_dense_grid *tmp, bool ok, const char *what) {
    if (!ok) {
        tvdb_dense_grid_free(tmp);
        setLastError(std::string(what) + " failed");
        return DenseGridWrap();
    }
    DenseGridWrap w;
    tvdb_dense_grid_free(&w.grid);
    w.grid = *tmp;                 /* transfer ownership of the buffers */
    std::memset(tmp, 0, sizeof(*tmp));
    return w;
}
} // namespace

DenseGridWrap coarsenGrid(const DenseGridWrap &in, int factor) {
    tvdb_dense_grid tmp;
    std::memset(&tmp, 0, sizeof(tmp));
    return resampleLike(&tmp, tvdb_coarsen_grid(&in.grid, factor, &tmp, NULL), "coarsenGrid");
}
DenseGridWrap refineGrid(const DenseGridWrap &in, int factor) {
    tvdb_dense_grid tmp;
    std::memset(&tmp, 0, sizeof(tmp));
    return resampleLike(&tmp, tvdb_refine_grid(&in.grid, factor, &tmp, NULL), "refineGrid");
}
DenseGridWrap resampleGrid(const DenseGridWrap &in, float voxelSize, int order) {
    tvdb_dense_grid tmp;
    std::memset(&tmp, 0, sizeof(tmp));
    return resampleLike(&tmp, tvdb_resample_grid(&in.grid, voxelSize, order, &tmp, NULL),
                        "resampleGrid");
}
DenseGridWrap clipGrid(const DenseGridWrap &in,
                       float minX, float minY, float minZ,
                       float maxX, float maxY, float maxZ) {
    const float bmin[3] = {minX, minY, minZ};
    const float bmax[3] = {maxX, maxY, maxZ};
    tvdb_dense_grid tmp;
    std::memset(&tmp, 0, sizeof(tmp));
    return resampleLike(&tmp, tvdb_clip_grid(&in.grid, bmin, bmax, &tmp, NULL), "clipGrid");
}
DenseGridWrap mergeGrids(const DenseGridWrap &a, const DenseGridWrap &b, float background) {
    tvdb_dense_grid tmp;
    std::memset(&tmp, 0, sizeof(tmp));
    return resampleLike(&tmp, tvdb_merge_grids(&a.grid, &b.grid, background, &tmp, NULL),
                        "mergeGrids");
}
DenseGridWrap maxPool(const DenseGridWrap &in, int kx, int ky, int kz) {
    tvdb_dense_grid tmp;
    std::memset(&tmp, 0, sizeof(tmp));
    tvdb_max_pool(&in.grid, kx, ky, kz, &tmp, /*arena=*/NULL);
    return resampleLike(&tmp, true, "maxPool");
}
DenseGridWrap avgPool(const DenseGridWrap &in, int kx, int ky, int kz) {
    tvdb_dense_grid tmp;
    std::memset(&tmp, 0, sizeof(tmp));
    tvdb_avg_pool(&in.grid, kx, ky, kz, &tmp, /*arena=*/NULL);
    return resampleLike(&tmp, true, "avgPool");
}
void pruneGrid(DenseGridWrap &g, float background, float tolerance) {
    tvdb_prune_grid(&g.grid, background, tolerance);
}

/* ======================================================================== */
/*  Sparse grids                                                            */
/* ======================================================================== */

namespace {
/* Same ownership discipline as resampleLike: free before throwing. */
SparseGridWrap sparseLike(tvdb_sparse_grid *tmp, bool ok, const char *what) {
    if (!ok) {
        tvdb_sparse_grid_free(tmp);
        setLastError(std::string(what) + " failed");
        return SparseGridWrap();
    }
    SparseGridWrap w;
    tvdb_sparse_grid_free(&w.sg);
    w.sg = *tmp;                 /* transfer ownership */
    std::memset(tmp, 0, sizeof(*tmp));
    return w;
}
} // namespace

SparseGridWrap denseToSparse(const DenseGridWrap &d, float background, float tolerance) {
    tvdb_sparse_grid tmp;
    tvdb_sparse_grid_init(&tmp);
    const bool ok = tvdb_dense_to_sparse(&d.grid, background, tolerance, &tmp);
    return sparseLike(&tmp, ok, "denseToSparse");
}
SparseGridWrap activeGridCoords(const DenseGridWrap &d, float background) {
    tvdb_sparse_grid tmp;
    tvdb_sparse_grid_init(&tmp);
    const bool ok = tvdb_active_grid_coords(&d.grid, background, &tmp);
    return sparseLike(&tmp, ok, "activeGridCoords");
}
DenseGridWrap sparseToDense(const SparseGridWrap &s, float background) {
    DenseGridWrap out;
    tvdb_dense_grid_init(&out.grid, 0, 0, 0);
    /* sparse_to_dense fills an already-allocated target, so derive the extent
     * from the voxel count and transform. */
    int nx = 0, ny = 0, nz = 0;
    if (s.sg.count) {
        int lo[3] = {0x7fffffff, 0x7fffffff, 0x7fffffff};
        int hi[3] = {-0x7fffffff - 1, -0x7fffffff - 1, -0x7fffffff - 1};
        for (size_t i = 0; i < s.sg.count; ++i) {
            const tvdb_vec3i &c = s.sg.coords[i];
            const int v[3] = {c.x, c.y, c.z};
            for (int k = 0; k < 3; ++k) {
                if (v[k] < lo[k]) lo[k] = v[k];
                if (v[k] > hi[k]) hi[k] = v[k];
            }
        }
        nx = hi[0] - lo[0] + 1; ny = hi[1] - lo[1] + 1; nz = hi[2] - lo[2] + 1;
        tvdb_dense_grid_free(&out.grid);
        tvdb_dense_grid_init(&out.grid, nx, ny, nz);
        out.grid.ox = s.sg.ox + (float)lo[0] * s.sg.voxel_size;
        out.grid.oy = s.sg.oy + (float)lo[1] * s.sg.voxel_size;
        out.grid.oz = s.sg.oz + (float)lo[2] * s.sg.voxel_size;
        out.grid.voxel_size = s.sg.voxel_size;
    }
    const bool ok = tvdb_sparse_to_dense(&s.sg, background, &out.grid);
    requireOk(ok, "sparseToDense");
    return out;
}

SparseGridWrap csgUnionSparse(const SparseGridWrap &a, const SparseGridWrap &b, float bg) {
    tvdb_sparse_grid tmp; tvdb_sparse_grid_init(&tmp);
    const bool ok = tvdb_csg_union_sparse(&a.sg, &b.sg, bg, &tmp);
    return sparseLike(&tmp, ok, "csgUnionSparse");
}
SparseGridWrap csgIntersectionSparse(const SparseGridWrap &a, const SparseGridWrap &b, float bg) {
    tvdb_sparse_grid tmp; tvdb_sparse_grid_init(&tmp);
    const bool ok = tvdb_csg_intersection_sparse(&a.sg, &b.sg, bg, &tmp);
    return sparseLike(&tmp, ok, "csgIntersectionSparse");
}
SparseGridWrap csgDifferenceSparse(const SparseGridWrap &a, const SparseGridWrap &b, float bg) {
    tvdb_sparse_grid tmp; tvdb_sparse_grid_init(&tmp);
    const bool ok = tvdb_csg_difference_sparse(&a.sg, &b.sg, bg, &tmp);
    return sparseLike(&tmp, ok, "csgDifferenceSparse");
}
SparseGridWrap dilateSparse(const SparseGridWrap &a, float background, int iterations) {
    tvdb_sparse_grid tmp; tvdb_sparse_grid_init(&tmp);
    const bool ok = tvdb_dilate_sparse(&a.sg, background, iterations, &tmp);
    return sparseLike(&tmp, ok, "dilateSparse");
}
SparseGridWrap erodeSparse(const SparseGridWrap &a, int iterations) {
    tvdb_sparse_grid tmp; tvdb_sparse_grid_init(&tmp);
    const bool ok = tvdb_erode_sparse(&a.sg, iterations, &tmp);
    return sparseLike(&tmp, ok, "erodeSparse");
}

/* Separable box convolution. Kernel is passed as a flat JS array in
 * kz-major, ky, kx order to match kernel[((kz*ky)+ky)*kx+kx]. */
SparseGridWrap sparseConv3d(const SparseGridWrap &a, const val &kernel,
                            int kx, int ky, int kz, float padValue) {
    const int klen = kx * ky * kz;
    if (klen <= 0) return fail<SparseGridWrap>("sparseConv3d: empty kernel");
    std::vector<float> k((size_t)klen);
    val(typed_memory_view(klen, k.data())).call<void>("set", kernel);
    tvdb_sparse_grid tmp; tvdb_sparse_grid_init(&tmp);
    const bool ok = tvdb_sparse_conv3d(&a.sg, k.data(), kx, ky, kz, padValue, &tmp);
    return sparseLike(&tmp, ok, "sparseConv3d");
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
    constant("SIGN_FLOOD_FILL",      (int)TVDB_SIGN_FLOOD_FILL);
    constant("SIGN_SWEEP",           (int)TVDB_SIGN_SWEEP);
    constant("WINDING_TABLE",        (int)TVDB_MESH_WINDING_TABLE);
    constant("WINDING_OUTWARD",      (int)TVDB_MESH_WINDING_OUTWARD);
    constant("ADVECT_RK1",           (int)TVDB_ADVECT_RK1);
    constant("ADVECT_RK2",           (int)TVDB_ADVECT_RK2);
    constant("ADVECT_RK3",           (int)TVDB_ADVECT_RK3);
    constant("ADVECT_RK4",           (int)TVDB_ADVECT_RK4);
    constant("ADVECT_MACCORMACK",    (int)TVDB_ADVECT_MACCORMACK);
    constant("ADVECT_BFECC",         (int)TVDB_ADVECT_BFECC);

    /* Error channel (see the note above thread_local std::string g_last_error).
       Failures are reported here rather than by throwing, so this module needs
       no C++ exceptions and JS can finally read the message. */
    function("lastError",     &lastError);
    function("clearLastError", &clearLastError);

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

    class_<DenseVecGridWrap>("DenseVecGrid")
        .constructor<>()
        .constructor<int, int, int, float>()
        .property("nx", &DenseVecGridWrap::getNx)
        .property("ny", &DenseVecGridWrap::getNy)
        .property("nz", &DenseVecGridWrap::getNz)
        .property("voxelSize", &DenseVecGridWrap::getVoxelSize)
        .function("size",    &DenseVecGridWrap::size)
        .function("get",     &DenseVecGridWrap::get)
        .function("set",     &DenseVecGridWrap::set)
        .function("getData", &DenseVecGridWrap::getData)
        .function("setData", &DenseVecGridWrap::setData)
        ;

    class_<SparseGridWrap>("SparseGrid")
        .constructor<>()
        .property("count",     &SparseGridWrap::count)
        .property("voxelSize", &SparseGridWrap::getVoxelSize)
        .property("ox",        &SparseGridWrap::getOx)
        .property("oy",        &SparseGridWrap::getOy)
        .property("oz",        &SparseGridWrap::getOz)
        .function("getCoords",  &SparseGridWrap::getCoords)
        .function("getValues",  &SparseGridWrap::getValues)
        .function("valueAt",    &SparseGridWrap::valueAt)
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

    /* --- hardened mesh conversion + MC tables --- */
    function("meshToSDFEx",   &meshToSDFEx);
    function("sdfToMeshEx",   &sdfToMeshEx);
    function("mcEdgeTable",   &mcEdgeTable);
    function("mcTriTableFlat", &mcTriTableFlat);

    /* --- dense operators --- */
    function("compMax",  &compMax);
    function("compMin",  &compMin);
    function("compSum",  &compSum);
    function("compMult", &compMult);
    function("medianFilter",     &medianFilter);
    function("meanCurvatureFlow", &meanCurvatureFlow);
    function("signedFloodFill",  &signedFloodFill);
    function("fastSweeping",     &fastSweeping);
    function("centralDiffX",     &centralDiffX);
    function("centralDiffY",     &centralDiffY);
    function("centralDiffZ",     &centralDiffZ);

    /* --- vector fields and advection --- */
    function("gradient",       &gradient);
    function("divergence",     &divergence);
    function("curl",           &curl);
    function("magnitude",      &magnitude);
    function("normalizeVec",   &normalizeVec);
    function("closestPointTransform", &closestPointTransform);
    function("advectSemiLagrangian",  &advectSemiLagrangian);
    function("advect",         &advect);

    /* --- statistics and health checks --- */
    function("statistics",     &statistics);
    function("histogram",      &histogram);
    function("checkLevelSet",  &checkLevelSet);
    function("checkFogVolume", &checkFogVolume);

    /* --- level-set generators and measures --- */
    function("levelSetSphere",   &levelSetSphere);
    function("levelSetBox",      &levelSetBox);
    function("levelSetTorus",    &levelSetTorus);
    function("levelSetCapsule",  &levelSetCapsule);
    function("levelSetPlatonic", &levelSetPlatonic);
    function("sdfToFogVolume",        &sdfToFogVolume);
    function("sdfInteriorMask",       &sdfInteriorMask);
    function("sdfEnclosedRegions",    &sdfEnclosedRegions);
    function("levelSetEulerCharacteristic", &levelSetEulerCharacteristic);
    function("levelSetGenus",         &levelSetGenus);
    function("levelSetRebuild",       &levelSetRebuild);

    /* --- ray traversal --- */
    function("voxelsAlongRay",     &voxelsAlongRay);
    function("uniformRaySamples",  &uniformRaySamples);
    function("segmentsAlongRay",   &segmentsAlongRay);

    /* --- resampling and topology --- */
    function("coarsenGrid",  &coarsenGrid);
    function("refineGrid",   &refineGrid);
    function("resampleGrid", &resampleGrid);
    function("clipGrid",     &clipGrid);
    function("mergeGrids",   &mergeGrids);
    function("maxPool",      &maxPool);
    function("avgPool",      &avgPool);
    function("pruneGrid",    &pruneGrid);

    /* --- sparse grids --- */
    function("denseToSparse",            &denseToSparse);
    function("activeGridCoords",         &activeGridCoords);
    function("sparseToDense",            &sparseToDense);
    function("csgUnionSparse",           &csgUnionSparse);
    function("csgIntersectionSparse",    &csgIntersectionSparse);
    function("csgDifferenceSparse",      &csgDifferenceSparse);
    function("dilateSparse",             &dilateSparse);
    function("erodeSparse",              &erodeSparse);
    function("sparseConv3d",             &sparseConv3d);
}
