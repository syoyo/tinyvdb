/*
 * _tinyvdb.c — Python C extension for tinyvdb (Stable ABI / abi3).
 *
 * Uses Py_LIMITED_API targeting Python 3.11+.
 * All types are heap types created via PyType_FromSpec.
 */

/* Py_LIMITED_API is set by CMake's USE_SABI flag */
#ifndef Py_LIMITED_API
#define Py_LIMITED_API 0x030B0000
#endif
#include <Python.h>

#include "tinyvdb_io.h"

#include <string.h>
#include <stdlib.h>

/* ======================================================================== */
/*  Limited API allocation helpers                                          */
/* ======================================================================== */

typedef void *(*allocfunc_t)(PyTypeObject *, Py_ssize_t);
typedef void (*freefunc_t)(void *);

static PyObject *alloc_from_type(PyObject *type_obj) {
    PyTypeObject *tp = (PyTypeObject *)type_obj;
    allocfunc_t alloc = (allocfunc_t)PyType_GetSlot(tp, Py_tp_alloc);
    return (PyObject *)alloc(tp, 0);
}

static void dealloc_free(PyObject *self) {
    PyTypeObject *tp = Py_TYPE(self);
    freefunc_t freefn = (freefunc_t)PyType_GetSlot(tp, Py_tp_free);
    freefn(self);
    Py_DECREF(tp);
}

/* ======================================================================== */
/*  Forward declarations for C++ mesh/ops wrappers                          */
/* ======================================================================== */

extern const char *tvdb_py_last_error(void);

extern int tvdb_py_mesh_to_sdf(const float *verts, size_t nv,
                               const uint32_t *tris, size_t nt,
                               float voxel_size, float band_width,
                               int sign_method,
                               float **out_data, int *nx, int *ny, int *nz,
                               float *out_voxel_size,
                               float *ox, float *oy, float *oz);

extern int tvdb_py_sdf_to_mesh(const float *data, int nx, int ny, int nz,
                               float voxel_size, float ox, float oy, float oz,
                               float isovalue,
                               float **out_verts, size_t *out_nv,
                               uint32_t **out_tris, size_t *out_nt);

extern int tvdb_py_make_manifold(const float *verts, size_t nv,
                                 const uint32_t *tris, size_t nt,
                                 double resolution, double isovalue,
                                 int sign_method,
                                 float **out_verts, size_t *out_nv,
                                 uint32_t **out_tris, size_t *out_nt);

extern int tvdb_py_dilate(float *, int, int, int, float, float, float, float, int);
extern int tvdb_py_erode(float *, int, int, int, float, float, float, float, int);
extern int tvdb_py_open(float *, int, int, int, float, float, float, float, int);
extern int tvdb_py_close(float *, int, int, int, float, float, float, float, int);

extern int tvdb_py_gaussian_filter(float *, int, int, int, float, float, float, float, int, int);
extern int tvdb_py_mean_filter(float *, int, int, int, float, float, float, float, int, int);
extern int tvdb_py_laplacian_filter(float *, int, int, int, float, float, float, float, int);

extern int tvdb_py_csg_union(const float *, const float *, int, int, int, float, float, float, float, float **);
extern int tvdb_py_csg_intersection(const float *, const float *, int, int, int, float, float, float, float, float **);
extern int tvdb_py_csg_difference(const float *, const float *, int, int, int, float, float, float, float, float **);

extern float tvdb_py_surface_area(const float *, int, int, int, float, float, float, float);
extern float tvdb_py_volume(const float *, int, int, int, float, float, float, float);

extern int tvdb_py_gradient(const float *, int, int, int, float, float, float, float, float **);
extern int tvdb_py_divergence(const float *, int, int, int, float, float, float, float, float **);
extern int tvdb_py_laplacian(const float *, int, int, int, float, float, float, float, float **);
extern int tvdb_py_curl(const float *, int, int, int, float, float, float, float, float **);

extern int tvdb_py_advect(const float *, const float *, int, int, int, float, float, float, float, float, float **);
extern int tvdb_py_solve_poisson(const float *, int, int, int, float, float, float, float, int, float, float **, int *);

extern int tvdb_py_ray_cast_sdf(const float *, int, int, int, float, float, float, float,
                                float, float, float, float, float, float, float,
                                int *, float *, float *, float *, float *, float *, float *, float *);

extern int tvdb_py_particles_to_sdf(const float *, const float *, size_t,
                                    float, float, float **, int *, int *, int *,
                                    float *, float *, float *, float *);

extern int tvdb_py_volume_to_spheres(const float *, int, int, int, float, float, float, float,
                                     float, int, float, float **, float **, size_t *);

extern int tvdb_py_fracture(const float *, int, int, int, float, float, float, float,
                            const float **, int, float ***, int *);

/* ======================================================================== */
/*  Module state & exception                                                */
/* ======================================================================== */

typedef struct {
    PyObject *VDBError;
    PyObject *VDBFileType;
    PyObject *VDBGridType;
    PyObject *VDBTreeType;
    PyObject *VDBNodeType;
    PyObject *DenseGridType;
    PyObject *DenseVecGridType;
    PyObject *TriangleMeshType;
} module_state;

static module_state *get_state(PyObject *module) {
    return (module_state *)PyModule_GetState(module);
}

static struct PyModuleDef tinyvdb_module;

static PyObject *get_vdb_error(void) {
    PyObject *mod = PyState_FindModule(&tinyvdb_module);
    if (!mod) return PyExc_RuntimeError;
    module_state *st = get_state(mod);
    return st ? st->VDBError : PyExc_RuntimeError;
}

static PyObject *raise_vdb_error(const char *msg) {
    PyErr_SetString(get_vdb_error(), msg);
    return NULL;
}

static PyObject *raise_tvdb_status(tvdb_status_t status, const tvdb_error_t *err) {
    if (err && err->message[0])
        return raise_vdb_error(err->message);
    return raise_vdb_error(tvdb_status_string(status));
}

/* ======================================================================== */
/*  DenseGrid type                                                          */
/* ======================================================================== */

typedef struct {
    PyObject_HEAD
    float *data;
    int nx, ny, nz;
    float ox, oy, oz;
    float voxel_size;
} PyDenseGrid;

static void DenseGrid_dealloc(PyObject *self) {
    free(((PyDenseGrid *)self)->data);
    dealloc_free(self);
}

static PyObject *DenseGrid_new(PyTypeObject *type, PyObject *args, PyObject *kw) {
    PyDenseGrid *self = (PyDenseGrid *)alloc_from_type((PyObject *)type);
    if (self) {
        self->data = NULL;
        self->nx = self->ny = self->nz = 0;
        self->ox = self->oy = self->oz = 0.0f;
        self->voxel_size = 1.0f;
    }
    return (PyObject *)self;
}

static int DenseGrid_init(PyObject *self, PyObject *args, PyObject *kw) {
    PyDenseGrid *g = (PyDenseGrid *)self;
    int nx = 0, ny = 0, nz = 0;
    float voxel_size = 1.0f, ox = 0, oy = 0, oz = 0;
    static char *kwlist[] = {"nx", "ny", "nz", "voxel_size", "ox", "oy", "oz", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "|iiiffff", kwlist,
                                     &nx, &ny, &nz, &voxel_size, &ox, &oy, &oz))
        return -1;
    g->nx = nx; g->ny = ny; g->nz = nz;
    g->voxel_size = voxel_size;
    g->ox = ox; g->oy = oy; g->oz = oz;
    if (nx > 0 && ny > 0 && nz > 0) {
        size_t n = (size_t)nx * ny * nz;
        g->data = (float *)calloc(n, sizeof(float));
        if (!g->data) { PyErr_NoMemory(); return -1; }
    }
    return 0;
}

static PyObject *DenseGrid_get_shape(PyObject *self, void *closure) {
    PyDenseGrid *g = (PyDenseGrid *)self;
    return Py_BuildValue("(iii)", g->nx, g->ny, g->nz);
}

static PyObject *DenseGrid_get_origin(PyObject *self, void *closure) {
    PyDenseGrid *g = (PyDenseGrid *)self;
    return Py_BuildValue("(fff)", g->ox, g->oy, g->oz);
}

static PyObject *DenseGrid_get_voxel_size(PyObject *self, void *closure) {
    return PyFloat_FromDouble(((PyDenseGrid *)self)->voxel_size);
}

static PyObject *DenseGrid_to_bytes(PyObject *self, PyObject *Py_UNUSED(args)) {
    PyDenseGrid *g = (PyDenseGrid *)self;
    if (!g->data) Py_RETURN_NONE;
    size_t n = (size_t)g->nx * g->ny * g->nz;
    return PyBytes_FromStringAndSize((const char *)g->data, (Py_ssize_t)(n * sizeof(float)));
}

static int DenseGrid_getbuffer(PyObject *self, Py_buffer *view, int flags) {
    PyDenseGrid *g = (PyDenseGrid *)self;
    if (!g->data) {
        PyErr_SetString(PyExc_BufferError, "DenseGrid has no data");
        return -1;
    }
    size_t n = (size_t)g->nx * g->ny * g->nz;
    return PyBuffer_FillInfo(view, self, g->data, (Py_ssize_t)(n * sizeof(float)), 0, flags);
}

static PyObject *DenseGrid_getitem(PyObject *self, PyObject *args) {
    PyDenseGrid *g = (PyDenseGrid *)self;
    int x, y, z;
    if (!PyArg_ParseTuple(args, "(iii)", &x, &y, &z)) return NULL;
    if (!g->data || x < 0 || x >= g->nx || y < 0 || y >= g->ny || z < 0 || z >= g->nz) {
        PyErr_SetString(PyExc_IndexError, "index out of range");
        return NULL;
    }
    return PyFloat_FromDouble(g->data[x + g->nx * (y + g->ny * z)]);
}

static PyObject *DenseGrid_setitem(PyObject *self, PyObject *args) {
    PyDenseGrid *g = (PyDenseGrid *)self;
    int x, y, z;
    float val;
    if (!PyArg_ParseTuple(args, "(iii)f", &x, &y, &z, &val)) return NULL;
    if (!g->data || x < 0 || x >= g->nx || y < 0 || y >= g->ny || z < 0 || z >= g->nz) {
        PyErr_SetString(PyExc_IndexError, "index out of range");
        return NULL;
    }
    g->data[x + g->nx * (y + g->ny * z)] = val;
    Py_RETURN_NONE;
}

static PyObject *DenseGrid_size(PyObject *self, PyObject *Py_UNUSED(args)) {
    PyDenseGrid *g = (PyDenseGrid *)self;
    return PyLong_FromSsize_t((Py_ssize_t)g->nx * g->ny * g->nz);
}

static PyGetSetDef DenseGrid_getset[] = {
    {"shape", DenseGrid_get_shape, NULL, "Grid dimensions (nx, ny, nz)", NULL},
    {"origin", DenseGrid_get_origin, NULL, "Grid origin (ox, oy, oz)", NULL},
    {"voxel_size", DenseGrid_get_voxel_size, NULL, "Voxel size", NULL},
    {NULL}
};

static PyMethodDef DenseGrid_methods[] = {
    {"get", DenseGrid_getitem, METH_VARARGS, "Get voxel at (x, y, z)"},
    {"set", DenseGrid_setitem, METH_VARARGS, "Set voxel at (x, y, z) to value"},
    {"size", DenseGrid_size, METH_NOARGS, "Total number of voxels"},
    {"to_bytes", DenseGrid_to_bytes, METH_NOARGS, "Return raw data as bytes"},
    {NULL}
};

static PyType_Slot DenseGrid_slots[] = {
    {Py_tp_dealloc, DenseGrid_dealloc},
    {Py_tp_new, DenseGrid_new},
    {Py_tp_init, DenseGrid_init},
    {Py_tp_getset, DenseGrid_getset},
    {Py_tp_methods, DenseGrid_methods},
    {Py_bf_getbuffer, DenseGrid_getbuffer},
    {0, NULL}
};

static PyType_Spec DenseGrid_spec = {
    .name = "tinyvdb._tinyvdb.DenseGrid",
    .basicsize = sizeof(PyDenseGrid),
    .flags = Py_TPFLAGS_DEFAULT,
    .slots = DenseGrid_slots,
};

static PyObject *DenseGrid_from_c(PyObject *type, float *data,
                                  int nx, int ny, int nz,
                                  float voxel_size, float ox, float oy, float oz) {
    PyDenseGrid *g = (PyDenseGrid *)alloc_from_type(type);
    if (!g) { free(data); return NULL; }
    g->data = data;
    g->nx = nx; g->ny = ny; g->nz = nz;
    g->voxel_size = voxel_size;
    g->ox = ox; g->oy = oy; g->oz = oz;
    return (PyObject *)g;
}

/* ======================================================================== */
/*  DenseVecGrid type (3-component vector field)                            */
/* ======================================================================== */

typedef struct {
    PyObject_HEAD
    float *data;
    int nx, ny, nz;
    float ox, oy, oz;
    float voxel_size;
} PyDenseVecGrid;

static void DenseVecGrid_dealloc(PyObject *self) {
    free(((PyDenseVecGrid *)self)->data);
    dealloc_free(self);
}

static PyObject *DenseVecGrid_new(PyTypeObject *type, PyObject *args, PyObject *kw) {
    PyDenseVecGrid *self = (PyDenseVecGrid *)alloc_from_type((PyObject *)type);
    if (self) {
        self->data = NULL;
        self->nx = self->ny = self->nz = 0;
        self->voxel_size = 1.0f;
    }
    return (PyObject *)self;
}

static PyObject *DenseVecGrid_get_shape(PyObject *self, void *c) {
    PyDenseVecGrid *g = (PyDenseVecGrid *)self;
    return Py_BuildValue("(iii)", g->nx, g->ny, g->nz);
}
static PyObject *DenseVecGrid_get_origin(PyObject *self, void *c) {
    PyDenseVecGrid *g = (PyDenseVecGrid *)self;
    return Py_BuildValue("(fff)", g->ox, g->oy, g->oz);
}
static PyObject *DenseVecGrid_get_voxel_size(PyObject *self, void *c) {
    return PyFloat_FromDouble(((PyDenseVecGrid *)self)->voxel_size);
}

static int DenseVecGrid_getbuffer(PyObject *self, Py_buffer *view, int flags) {
    PyDenseVecGrid *g = (PyDenseVecGrid *)self;
    if (!g->data) {
        PyErr_SetString(PyExc_BufferError, "DenseVecGrid has no data");
        return -1;
    }
    size_t n = (size_t)g->nx * g->ny * g->nz * 3;
    return PyBuffer_FillInfo(view, self, g->data, (Py_ssize_t)(n * sizeof(float)), 0, flags);
}

static PyGetSetDef DenseVecGrid_getset[] = {
    {"shape", DenseVecGrid_get_shape, NULL, "Grid dimensions", NULL},
    {"origin", DenseVecGrid_get_origin, NULL, "Grid origin", NULL},
    {"voxel_size", DenseVecGrid_get_voxel_size, NULL, "Voxel size", NULL},
    {NULL}
};

static PyType_Slot DenseVecGrid_slots[] = {
    {Py_tp_dealloc, DenseVecGrid_dealloc},
    {Py_tp_new, DenseVecGrid_new},
    {Py_tp_getset, DenseVecGrid_getset},
    {Py_bf_getbuffer, DenseVecGrid_getbuffer},
    {0, NULL}
};

static PyType_Spec DenseVecGrid_spec = {
    .name = "tinyvdb._tinyvdb.DenseVecGrid",
    .basicsize = sizeof(PyDenseVecGrid),
    .flags = Py_TPFLAGS_DEFAULT,
    .slots = DenseVecGrid_slots,
};

static PyObject *DenseVecGrid_from_c(PyObject *type, float *data,
                                     int nx, int ny, int nz,
                                     float voxel_size,
                                     float ox, float oy, float oz) {
    PyDenseVecGrid *g = (PyDenseVecGrid *)alloc_from_type(type);
    if (!g) { free(data); return NULL; }
    g->data = data;
    g->nx = nx; g->ny = ny; g->nz = nz;
    g->voxel_size = voxel_size;
    g->ox = ox; g->oy = oy; g->oz = oz;
    return (PyObject *)g;
}

/* ======================================================================== */
/*  TriangleMesh type                                                       */
/* ======================================================================== */

typedef struct {
    PyObject_HEAD
    float *vertices;
    uint32_t *faces;
    size_t num_vertices;
    size_t num_faces;
} PyTriangleMesh;

static void TriangleMesh_dealloc(PyObject *self) {
    PyTriangleMesh *m = (PyTriangleMesh *)self;
    free(m->vertices);
    free(m->faces);
    dealloc_free(self);
}

static PyObject *TriangleMesh_new(PyTypeObject *type, PyObject *args, PyObject *kw) {
    PyTriangleMesh *self = (PyTriangleMesh *)alloc_from_type((PyObject *)type);
    if (self) { self->vertices = NULL; self->faces = NULL; self->num_vertices = 0; self->num_faces = 0; }
    return (PyObject *)self;
}

static PyObject *TriangleMesh_get_num_vertices(PyObject *self, void *c) {
    return PyLong_FromSize_t(((PyTriangleMesh *)self)->num_vertices);
}
static PyObject *TriangleMesh_get_num_faces(PyObject *self, void *c) {
    return PyLong_FromSize_t(((PyTriangleMesh *)self)->num_faces);
}
static PyObject *TriangleMesh_get_vertices(PyObject *self, void *c) {
    PyTriangleMesh *m = (PyTriangleMesh *)self;
    if (!m->vertices) Py_RETURN_NONE;
    return PyBytes_FromStringAndSize((const char *)m->vertices,
                                    (Py_ssize_t)(m->num_vertices * 3 * sizeof(float)));
}
static PyObject *TriangleMesh_get_faces(PyObject *self, void *c) {
    PyTriangleMesh *m = (PyTriangleMesh *)self;
    if (!m->faces) Py_RETURN_NONE;
    return PyBytes_FromStringAndSize((const char *)m->faces,
                                    (Py_ssize_t)(m->num_faces * 3 * sizeof(uint32_t)));
}

static int TriangleMesh_getbuffer(PyObject *self, Py_buffer *view, int flags) {
    PyTriangleMesh *m = (PyTriangleMesh *)self;
    if (!m->vertices) {
        PyErr_SetString(PyExc_BufferError, "TriangleMesh has no vertices");
        return -1;
    }
    return PyBuffer_FillInfo(view, self, m->vertices,
                            (Py_ssize_t)(m->num_vertices * 3 * sizeof(float)), 1, flags);
}

static PyGetSetDef TriangleMesh_getset[] = {
    {"num_vertices", TriangleMesh_get_num_vertices, NULL, "Number of vertices", NULL},
    {"num_faces", TriangleMesh_get_num_faces, NULL, "Number of faces", NULL},
    {"vertices_bytes", TriangleMesh_get_vertices, NULL, "Vertices as bytes", NULL},
    {"faces_bytes", TriangleMesh_get_faces, NULL, "Faces as bytes", NULL},
    {NULL}
};

static PyType_Slot TriangleMesh_slots[] = {
    {Py_tp_dealloc, TriangleMesh_dealloc},
    {Py_tp_new, TriangleMesh_new},
    {Py_tp_getset, TriangleMesh_getset},
    {Py_bf_getbuffer, TriangleMesh_getbuffer},
    {0, NULL}
};

static PyType_Spec TriangleMesh_spec = {
    .name = "tinyvdb._tinyvdb.TriangleMesh",
    .basicsize = sizeof(PyTriangleMesh),
    .flags = Py_TPFLAGS_DEFAULT,
    .slots = TriangleMesh_slots,
};

static PyObject *TriangleMesh_from_c(PyObject *type, float *verts, size_t nv,
                                     uint32_t *faces, size_t nt) {
    PyTriangleMesh *m = (PyTriangleMesh *)alloc_from_type(type);
    if (!m) { free(verts); free(faces); return NULL; }
    m->vertices = verts;
    m->faces = faces;
    m->num_vertices = nv;
    m->num_faces = nt;
    return (PyObject *)m;
}

/* ======================================================================== */
/*  VDBNode type                                                            */
/* ======================================================================== */

typedef struct {
    PyObject_HEAD
    PyObject *file_ref;
    tvdb_tree_node_t *node;
} PyVDBNode;

static void VDBNode_dealloc(PyObject *self) {
    Py_XDECREF(((PyVDBNode *)self)->file_ref);
    dealloc_free(self);
}

static PyObject *value_to_py(const tvdb_value_t *v) {
    switch (v->type) {
        case TVDB_VALUE_FLOAT: return PyFloat_FromDouble(v->u.f);
        case TVDB_VALUE_DOUBLE: return PyFloat_FromDouble(v->u.d);
        case TVDB_VALUE_INT32: return PyLong_FromLong(v->u.i32);
        case TVDB_VALUE_INT64: return PyLong_FromLongLong(v->u.i64);
        case TVDB_VALUE_BOOL: return PyBool_FromLong(v->u.b);
        case TVDB_VALUE_VEC3F:
            return Py_BuildValue("(fff)", v->u.vec3f[0], v->u.vec3f[1], v->u.vec3f[2]);
        case TVDB_VALUE_VEC3D:
            return Py_BuildValue("(ddd)", v->u.vec3d[0], v->u.vec3d[1], v->u.vec3d[2]);
        case TVDB_VALUE_VEC3I:
            return Py_BuildValue("(iii)", v->u.vec3i[0], v->u.vec3i[1], v->u.vec3i[2]);
        case TVDB_VALUE_STRING:
            if (v->u.s.str) return PyUnicode_FromStringAndSize(v->u.s.str, (Py_ssize_t)v->u.s.len);
            /* fall through */
        default: Py_RETURN_NONE;
    }
}

static PyObject *VDBNode_get_type(PyObject *self, void *c) {
    switch (((PyVDBNode *)self)->node->type) {
        case TVDB_NODE_ROOT: return PyUnicode_FromString("root");
        case TVDB_NODE_INTERNAL: return PyUnicode_FromString("internal");
        case TVDB_NODE_LEAF: return PyUnicode_FromString("leaf");
        default: return PyUnicode_FromString("unknown");
    }
}

static PyObject *VDBNode_get_level(PyObject *self, void *c) {
    return PyLong_FromLong(((PyVDBNode *)self)->node->level);
}

static PyObject *VDBNode_get_origin(PyObject *self, void *c) {
    tvdb_tree_node_t *n = ((PyVDBNode *)self)->node;
    return Py_BuildValue("(iii)", n->origin[0], n->origin[1], n->origin[2]);
}

static PyObject *VDBNode_get_active_voxel_count(PyObject *self, void *c) {
    tvdb_tree_node_t *n = ((PyVDBNode *)self)->node;
    if (n->type == TVDB_NODE_LEAF)
        return PyLong_FromSize_t(tvdb_nodemask_count_on(&n->u.leaf.value_mask));
    if (n->type == TVDB_NODE_INTERNAL)
        return PyLong_FromSize_t(tvdb_nodemask_count_on(&n->u.internal.value_mask));
    if (n->type == TVDB_NODE_ROOT)
        return PyLong_FromLong((long)n->u.root.num_tiles + n->u.root.num_children);
    return PyLong_FromLong(0);
}

static PyObject *VDBNode_get_data(PyObject *self, void *c) {
    tvdb_tree_node_t *n = ((PyVDBNode *)self)->node;
    if (n->type == TVDB_NODE_LEAF && n->u.leaf.data)
        return PyBytes_FromStringAndSize((const char *)n->u.leaf.data,
                                        (Py_ssize_t)n->u.leaf.data_size);
    Py_RETURN_NONE;
}

static PyObject *VDBNode_get_point_indices(PyObject *self, void *c) {
    tvdb_tree_node_t *n = ((PyVDBNode *)self)->node;
    if (n->type != TVDB_NODE_LEAF || !n->u.leaf.point_indices) Py_RETURN_NONE;
    return PyBytes_FromStringAndSize((const char *)n->u.leaf.point_indices,
                                     (Py_ssize_t)(n->u.leaf.num_point_indices * sizeof(int32_t)));
}

static PyObject *VDBNode_get_point_aux_data(PyObject *self, void *c) {
    tvdb_tree_node_t *n = ((PyVDBNode *)self)->node;
    if (n->type != TVDB_NODE_LEAF || !n->u.leaf.point_aux_data) Py_RETURN_NONE;
    return PyBytes_FromStringAndSize((const char *)n->u.leaf.point_aux_data,
                                     (Py_ssize_t)n->u.leaf.point_aux_data_size);
}

static PyObject *VDBNode_get_background(PyObject *self, void *c) {
    tvdb_tree_node_t *n = ((PyVDBNode *)self)->node;
    if (n->type != TVDB_NODE_ROOT) Py_RETURN_NONE;
    return value_to_py(&n->u.root.background);
}

static PyGetSetDef VDBNode_getset[] = {
    {"type", VDBNode_get_type, NULL, "Node type", NULL},
    {"level", VDBNode_get_level, NULL, "Tree level", NULL},
    {"origin", VDBNode_get_origin, NULL, "Node origin", NULL},
    {"active_voxel_count", VDBNode_get_active_voxel_count, NULL, "Active voxels", NULL},
    {"data", VDBNode_get_data, NULL, "Raw leaf data or None", NULL},
    {"point_indices", VDBNode_get_point_indices, NULL, "PointIndex leaf indices payload (bytes) or None", NULL},
    {"point_aux_data", VDBNode_get_point_aux_data, NULL, "PointIndex leaf auxiliary payload (bytes) or None", NULL},
    {"background", VDBNode_get_background, NULL, "Root background or None", NULL},
    {NULL}
};

static PyType_Slot VDBNode_slots[] = {
    {Py_tp_dealloc, VDBNode_dealloc},
    {Py_tp_getset, VDBNode_getset},
    {0, NULL}
};

static PyType_Spec VDBNode_spec = {
    .name = "tinyvdb._tinyvdb.VDBNode",
    .basicsize = sizeof(PyVDBNode),
    .flags = Py_TPFLAGS_DEFAULT,
    .slots = VDBNode_slots,
};

/* ======================================================================== */
/*  VDBTree type                                                            */
/* ======================================================================== */

typedef struct {
    PyObject_HEAD
    PyObject *file_ref;
    tvdb_tree_t *tree;
} PyVDBTree;

static void VDBTree_dealloc(PyObject *self) {
    Py_XDECREF(((PyVDBTree *)self)->file_ref);
    dealloc_free(self);
}

static PyObject *VDBTree_get_num_nodes(PyObject *self, void *c) {
    return PyLong_FromSize_t(((PyVDBTree *)self)->tree->num_nodes);
}

static PyObject *VDBTree_node(PyObject *self, PyObject *args) {
    Py_ssize_t idx;
    if (!PyArg_ParseTuple(args, "n", &idx)) return NULL;
    PyVDBTree *t = (PyVDBTree *)self;
    if (idx < 0 || (size_t)idx >= t->tree->num_nodes) {
        PyErr_SetString(PyExc_IndexError, "node index out of range");
        return NULL;
    }
    PyObject *mod = PyState_FindModule(&tinyvdb_module);
    if (!mod) return NULL;
    module_state *st = get_state(mod);

    PyVDBNode *n = (PyVDBNode *)alloc_from_type(st->VDBNodeType);
    if (!n) return NULL;
    n->file_ref = t->file_ref;
    Py_INCREF(n->file_ref);
    n->node = &t->tree->nodes[idx];
    return (PyObject *)n;
}

static PyGetSetDef VDBTree_getset[] = {
    {"num_nodes", VDBTree_get_num_nodes, NULL, "Number of tree nodes", NULL},
    {NULL}
};

static PyMethodDef VDBTree_methods[] = {
    {"node", VDBTree_node, METH_VARARGS, "Get tree node by index"},
    {NULL}
};

static PyType_Slot VDBTree_slots[] = {
    {Py_tp_dealloc, VDBTree_dealloc},
    {Py_tp_getset, VDBTree_getset},
    {Py_tp_methods, VDBTree_methods},
    {0, NULL}
};

static PyType_Spec VDBTree_spec = {
    .name = "tinyvdb._tinyvdb.VDBTree",
    .basicsize = sizeof(PyVDBTree),
    .flags = Py_TPFLAGS_DEFAULT,
    .slots = VDBTree_slots,
};

/* ======================================================================== */
/*  VDBGrid type                                                            */
/* ======================================================================== */

typedef struct {
    PyObject_HEAD
    PyObject *file_ref;
    tvdb_grid_t *grid;
} PyVDBGrid;

static void VDBGrid_dealloc(PyObject *self) {
    Py_XDECREF(((PyVDBGrid *)self)->file_ref);
    dealloc_free(self);
}

static PyObject *VDBGrid_get_name(PyObject *self, void *c) {
    tvdb_grid_t *g = ((PyVDBGrid *)self)->grid;
    return g->descriptor.grid_name ? PyUnicode_FromString(g->descriptor.grid_name)
                                   : PyUnicode_FromString("");
}

static PyObject *VDBGrid_get_type_name(PyObject *self, void *c) {
    tvdb_grid_t *g = ((PyVDBGrid *)self)->grid;
    return g->descriptor.grid_type ? PyUnicode_FromString(g->descriptor.grid_type)
                                   : PyUnicode_FromString("");
}

static PyObject *VDBGrid_get_metadata(PyObject *self, void *c) {
    tvdb_grid_t *g = ((PyVDBGrid *)self)->grid;
    PyObject *d = PyDict_New();
    if (!d) return NULL;
    for (size_t i = 0; i < g->metadata.count; i++) {
        tvdb_meta_entry_t *e = &g->metadata.entries[i];
        if (!e->name) continue;
        PyObject *key = PyUnicode_FromString(e->name);
        PyObject *val = value_to_py(&e->value);
        if (key && val) PyDict_SetItem(d, key, val);
        Py_XDECREF(key);
        Py_XDECREF(val);
    }
    return d;
}

static PyObject *VDBGrid_get_transform(PyObject *self, void *c) {
    tvdb_transform_t *t = &((PyVDBGrid *)self)->grid->transform;
    PyObject *d = PyDict_New();
    if (!d) return NULL;

    static const char *type_names[] = {
        "uniform_scale", "uniform_scale_translate", "scale",
        "scale_translate", "translation", "affine", "unknown"
    };
    int ti = (int)t->type;
    if (ti < 0 || ti > 6) ti = 6;

    PyObject *v;
    v = PyUnicode_FromString(type_names[ti]);
    PyDict_SetItemString(d, "type", v); Py_DECREF(v);
    v = Py_BuildValue("(ddd)", t->voxel_size[0], t->voxel_size[1], t->voxel_size[2]);
    PyDict_SetItemString(d, "voxel_size", v); Py_DECREF(v);
    v = Py_BuildValue("(ddd)", t->scale_values[0], t->scale_values[1], t->scale_values[2]);
    PyDict_SetItemString(d, "scale", v); Py_DECREF(v);
    v = Py_BuildValue("(ddd)", t->translation[0], t->translation[1], t->translation[2]);
    PyDict_SetItemString(d, "translation", v); Py_DECREF(v);

    PyObject *mat = PyTuple_New(4);
    for (int r = 0; r < 4; r++) {
        PyObject *row = Py_BuildValue("(dddd)",
            t->matrix[r][0], t->matrix[r][1], t->matrix[r][2], t->matrix[r][3]);
        PyTuple_SetItem(mat, r, row); /* steals ref */
    }
    PyDict_SetItemString(d, "matrix", mat); Py_DECREF(mat);
    return d;
}

static PyObject *VDBGrid_get_tree(PyObject *self, void *c) {
    PyVDBGrid *g = (PyVDBGrid *)self;
    PyObject *mod = PyState_FindModule(&tinyvdb_module);
    if (!mod) return NULL;
    module_state *st = get_state(mod);

    PyVDBTree *t = (PyVDBTree *)alloc_from_type(st->VDBTreeType);
    if (!t) return NULL;
    t->file_ref = g->file_ref;
    Py_INCREF(t->file_ref);
    t->tree = &g->grid->tree;
    return (PyObject *)t;
}

static PyObject *VDBGrid_get_is_point_data(PyObject *self, void *c) {
    tvdb_grid_t *g = ((PyVDBGrid *)self)->grid;
    return PyBool_FromLong(g->tree.is_point_data_grid ? 1 : 0);
}

static PyObject *VDBGrid_get_is_point_index(PyObject *self, void *c) {
    tvdb_grid_t *g = ((PyVDBGrid *)self)->grid;
    return PyBool_FromLong(g->tree.is_point_index_grid ? 1 : 0);
}

static PyObject *VDBGrid_point_data_blob(PyObject *self, PyObject *Py_UNUSED(args)) {
    tvdb_grid_t *g = ((PyVDBGrid *)self)->grid;
    if (!g->tree.is_point_data_grid || !g->point_data_blob) Py_RETURN_NONE;
    return PyBytes_FromStringAndSize((const char *)g->point_data_blob,
                                     (Py_ssize_t)g->point_data_blob_size);
}

static PyObject *VDBGrid_set_point_data_blob(PyObject *self, PyObject *args);

static PyGetSetDef VDBGrid_getset[] = {
    {"name", VDBGrid_get_name, NULL, "Grid name", NULL},
    {"type_name", VDBGrid_get_type_name, NULL, "Grid type name", NULL},
    {"metadata", VDBGrid_get_metadata, NULL, "Grid metadata", NULL},
    {"transform", VDBGrid_get_transform, NULL, "Grid transform", NULL},
    {"tree", VDBGrid_get_tree, NULL, "Grid tree", NULL},
    {"is_point_data", VDBGrid_get_is_point_data, NULL, "Whether this grid is PointDataGrid", NULL},
    {"is_point_index", VDBGrid_get_is_point_index, NULL, "Whether this grid is PointIndexGrid", NULL},
    {NULL}
};

static PyMethodDef VDBGrid_methods[] = {
    {"point_data_blob", VDBGrid_point_data_blob, METH_NOARGS, "Get opaque PointData payload as bytes"},
    {"set_point_data_blob", VDBGrid_set_point_data_blob, METH_VARARGS, "Replace opaque PointData payload from bytes"},
    {NULL}
};

static PyType_Slot VDBGrid_slots[] = {
    {Py_tp_dealloc, VDBGrid_dealloc},
    {Py_tp_getset, VDBGrid_getset},
    {Py_tp_methods, VDBGrid_methods},
    {0, NULL}
};

static PyType_Spec VDBGrid_spec = {
    .name = "tinyvdb._tinyvdb.VDBGrid",
    .basicsize = sizeof(PyVDBGrid),
    .flags = Py_TPFLAGS_DEFAULT,
    .slots = VDBGrid_slots,
};

/* ======================================================================== */
/*  VDBFile type                                                            */
/* ======================================================================== */

typedef struct {
    PyObject_HEAD
    tvdb_file_t file;
    int is_open;
    PyObject *bytes_ref;
} PyVDBFile;

static PyObject *VDBGrid_set_point_data_blob(PyObject *self, PyObject *args) {
    PyVDBGrid *g = (PyVDBGrid *)self;
    Py_buffer view;
    if (!PyArg_ParseTuple(args, "y*", &view)) return NULL;
    if (!g->file_ref) {
        PyBuffer_Release(&view);
        PyErr_SetString(PyExc_RuntimeError, "no file reference");
        return NULL;
    }
    PyVDBFile *f = (PyVDBFile *)g->file_ref;
    if (!f->is_open) {
        PyBuffer_Release(&view);
        PyErr_SetString(PyExc_RuntimeError, "file is closed");
        return NULL;
    }

    Py_ssize_t idx = (Py_ssize_t)(g->grid - f->file.grids);
    if (idx < 0 || (size_t)idx >= f->file.num_grids) {
        PyBuffer_Release(&view);
        PyErr_SetString(PyExc_IndexError, "grid index out of range");
        return NULL;
    }

    tvdb_error_t err;
    memset(&err, 0, sizeof(err));
    tvdb_status_t st = tvdb_grid_set_point_data_blob(&f->file, (size_t)idx,
                                                     (const uint8_t *)view.buf,
                                                     (size_t)view.len, &err);
    PyBuffer_Release(&view);
    if (st != TVDB_OK) return raise_tvdb_status(st, &err);
    Py_RETURN_NONE;
}

static void VDBFile_dealloc(PyObject *self) {
    PyVDBFile *f = (PyVDBFile *)self;
    if (f->is_open) { tvdb_file_close(&f->file); f->is_open = 0; }
    Py_XDECREF(f->bytes_ref);
    dealloc_free(self);
}

static PyObject *VDBFile_new(PyTypeObject *type, PyObject *args, PyObject *kw) {
    PyVDBFile *self = (PyVDBFile *)alloc_from_type((PyObject *)type);
    if (self) {
        memset(&self->file, 0, sizeof(self->file));
        self->is_open = 0;
        self->bytes_ref = NULL;
    }
    return (PyObject *)self;
}

static int VDBFile_init(PyObject *self, PyObject *args, PyObject *kw) {
    PyVDBFile *f = (PyVDBFile *)self;
    const char *path = NULL;
    Py_buffer buf = {0};
    static char *kwlist[] = {"path", "data", NULL};

    if (!PyArg_ParseTupleAndKeywords(args, kw, "|zy*", kwlist, &path, &buf))
        return -1;

    if (path && buf.buf) {
        PyErr_SetString(PyExc_ValueError, "Specify either path or data, not both");
        PyBuffer_Release(&buf);
        return -1;
    }

    tvdb_error_t err;
    memset(&err, 0, sizeof(err));
    tvdb_status_t status;

    if (path) {
        Py_BEGIN_ALLOW_THREADS
        status = tvdb_file_open(&f->file, path, NULL, &err);
        Py_END_ALLOW_THREADS
        if (status != TVDB_OK) { raise_tvdb_status(status, &err); return -1; }
        f->is_open = 1;
    } else if (buf.buf) {
        f->bytes_ref = PyBytes_FromStringAndSize(buf.buf, buf.len);
        PyBuffer_Release(&buf);
        if (!f->bytes_ref) return -1;

        const uint8_t *data = (const uint8_t *)PyBytes_AsString(f->bytes_ref);
        Py_ssize_t len = PyBytes_Size(f->bytes_ref);

        Py_BEGIN_ALLOW_THREADS
        status = tvdb_file_open_memory(&f->file, data, (size_t)len, NULL, &err);
        Py_END_ALLOW_THREADS
        if (status != TVDB_OK) { raise_tvdb_status(status, &err); return -1; }
        f->is_open = 1;
    }

    return 0;
}

#define CHECK_OPEN(f) do { \
    if (!(f)->is_open) { \
        PyErr_SetString(PyExc_ValueError, "VDB file is closed"); \
        return NULL; \
    } \
} while (0)

static PyObject *VDBFile_close(PyObject *self, PyObject *Py_UNUSED(a)) {
    PyVDBFile *f = (PyVDBFile *)self;
    if (f->is_open) { tvdb_file_close(&f->file); f->is_open = 0; }
    Py_RETURN_NONE;
}

static PyObject *VDBFile_read_grids(PyObject *self, PyObject *Py_UNUSED(a)) {
    PyVDBFile *f = (PyVDBFile *)self;
    CHECK_OPEN(f);
    tvdb_error_t err; memset(&err, 0, sizeof(err));
    tvdb_status_t status;
    Py_BEGIN_ALLOW_THREADS
    status = tvdb_read_all_grids(&f->file, &err);
    Py_END_ALLOW_THREADS
    if (status != TVDB_OK) return raise_tvdb_status(status, &err);
    Py_RETURN_NONE;
}

static PyObject *VDBFile_get_grid_count(PyObject *self, void *c) {
    PyVDBFile *f = (PyVDBFile *)self;
    if (!f->is_open) return PyLong_FromLong(0);
    return PyLong_FromSize_t(tvdb_grid_count(&f->file));
}

static PyObject *VDBFile_grid_name(PyObject *self, PyObject *args) {
    PyVDBFile *f = (PyVDBFile *)self; CHECK_OPEN(f);
    Py_ssize_t idx;
    if (!PyArg_ParseTuple(args, "n", &idx)) return NULL;
    if (idx < 0 || (size_t)idx >= tvdb_grid_count(&f->file)) {
        PyErr_SetString(PyExc_IndexError, "grid index out of range"); return NULL;
    }
    const char *name = tvdb_grid_name(&f->file, (size_t)idx);
    return name ? PyUnicode_FromString(name) : PyUnicode_FromString("");
}

static PyObject *VDBFile_grid_type_name(PyObject *self, PyObject *args) {
    PyVDBFile *f = (PyVDBFile *)self; CHECK_OPEN(f);
    Py_ssize_t idx;
    if (!PyArg_ParseTuple(args, "n", &idx)) return NULL;
    if (idx < 0 || (size_t)idx >= tvdb_grid_count(&f->file)) {
        PyErr_SetString(PyExc_IndexError, "grid index out of range"); return NULL;
    }
    const char *name = tvdb_grid_type_name(&f->file, (size_t)idx);
    return name ? PyUnicode_FromString(name) : PyUnicode_FromString("");
}

static PyObject *VDBFile_grid(PyObject *self, PyObject *args) {
    PyVDBFile *f = (PyVDBFile *)self; CHECK_OPEN(f);
    Py_ssize_t idx;
    if (!PyArg_ParseTuple(args, "n", &idx)) return NULL;
    if (idx < 0 || (size_t)idx >= f->file.num_grids) {
        PyErr_SetString(PyExc_IndexError, "grid index out of range"); return NULL;
    }
    PyObject *mod = PyState_FindModule(&tinyvdb_module);
    if (!mod) return NULL;
    module_state *st = get_state(mod);

    PyVDBGrid *g = (PyVDBGrid *)alloc_from_type(st->VDBGridType);
    if (!g) return NULL;
    g->file_ref = self;
    Py_INCREF(self);
    g->grid = &f->file.grids[idx];
    return (PyObject *)g;
}

static PyObject *VDBFile_save(PyObject *self, PyObject *args, PyObject *kw) {
    PyVDBFile *f = (PyVDBFile *)self; CHECK_OPEN(f);
    const char *path;
    unsigned int compression = 0; int level = 0, use_mmap = 0;
    static char *kwlist[] = {"path", "compression", "level", "use_mmap", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "s|Iip", kwlist,
                                     &path, &compression, &level, &use_mmap))
        return NULL;
    tvdb_error_t err; memset(&err, 0, sizeof(err));
    tvdb_status_t status;
    Py_BEGIN_ALLOW_THREADS
    status = tvdb_file_save(&f->file, path, compression, level, use_mmap, &err);
    Py_END_ALLOW_THREADS
    if (status != TVDB_OK) return raise_tvdb_status(status, &err);
    Py_RETURN_NONE;
}

static PyObject *VDBFile_to_bytes(PyObject *self, PyObject *args, PyObject *kw) {
    PyVDBFile *f = (PyVDBFile *)self; CHECK_OPEN(f);
    unsigned int compression = 0; int level = 0;
    static char *kwlist[] = {"compression", "level", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "|Ii", kwlist, &compression, &level))
        return NULL;
    tvdb_error_t err; memset(&err, 0, sizeof(err));
    uint8_t *out_data = NULL; size_t out_size = 0;
    tvdb_status_t status;
    Py_BEGIN_ALLOW_THREADS
    status = tvdb_write_to_memory(&f->file, compression, level, &out_data, &out_size, &err);
    Py_END_ALLOW_THREADS
    if (status != TVDB_OK) return raise_tvdb_status(status, &err);
    PyObject *result = PyBytes_FromStringAndSize((const char *)out_data, (Py_ssize_t)out_size);
    free(out_data);
    return result;
}

static PyObject *VDBFile_get_header(PyObject *self, void *c) {
    PyVDBFile *f = (PyVDBFile *)self;
    if (!f->is_open) Py_RETURN_NONE;
    tvdb_header_t *h = &f->file.header;
    PyObject *d = PyDict_New();
    if (!d) return NULL;
    PyObject *v;
#define SET_INT(key, val) v = PyLong_FromUnsignedLong(val); PyDict_SetItemString(d, key, v); Py_DECREF(v)
#define SET_BOOL(key, val) v = PyBool_FromLong(val); PyDict_SetItemString(d, key, v); Py_DECREF(v)
    SET_INT("file_version", h->file_version);
    SET_INT("major_version", h->major_version);
    SET_INT("minor_version", h->minor_version);
    SET_INT("compression_flags", h->compression_flags);
    SET_BOOL("has_grid_offsets", h->has_grid_offsets);
    SET_BOOL("half_precision", h->half_precision);
    v = PyUnicode_FromString(h->uuid); PyDict_SetItemString(d, "uuid", v); Py_DECREF(v);
#undef SET_INT
#undef SET_BOOL
    return d;
}

static PyObject *VDBFile_enter(PyObject *self, PyObject *Py_UNUSED(a)) {
    Py_INCREF(self); return self;
}

static PyObject *VDBFile_exit(PyObject *self, PyObject *args) {
    return VDBFile_close(self, NULL);
}

static PyGetSetDef VDBFile_getset[] = {
    {"grid_count", VDBFile_get_grid_count, NULL, "Number of grids", NULL},
    {"header", VDBFile_get_header, NULL, "File header as dict", NULL},
    {NULL}
};

static PyMethodDef VDBFile_methods[] = {
    {"close", VDBFile_close, METH_NOARGS, "Close the VDB file"},
    {"read_grids", VDBFile_read_grids, METH_NOARGS, "Read and decompress all grids"},
    {"grid_name", VDBFile_grid_name, METH_VARARGS, "Get grid name by index"},
    {"grid_type_name", VDBFile_grid_type_name, METH_VARARGS, "Get grid type name by index"},
    {"grid", VDBFile_grid, METH_VARARGS, "Get VDBGrid by index"},
    {"save", (PyCFunction)VDBFile_save, METH_VARARGS | METH_KEYWORDS, "Save to file"},
    {"to_bytes", (PyCFunction)VDBFile_to_bytes, METH_VARARGS | METH_KEYWORDS, "Serialize to bytes"},
    {"__enter__", VDBFile_enter, METH_NOARGS, NULL},
    {"__exit__", VDBFile_exit, METH_VARARGS, NULL},
    {NULL}
};

static PyType_Slot VDBFile_slots[] = {
    {Py_tp_dealloc, VDBFile_dealloc},
    {Py_tp_new, VDBFile_new},
    {Py_tp_init, VDBFile_init},
    {Py_tp_getset, VDBFile_getset},
    {Py_tp_methods, VDBFile_methods},
    {0, NULL}
};

static PyType_Spec VDBFile_spec = {
    .name = "tinyvdb._tinyvdb.VDBFile",
    .basicsize = sizeof(PyVDBFile),
    .flags = Py_TPFLAGS_DEFAULT,
    .slots = VDBFile_slots,
};

/* ======================================================================== */
/*  Module-level I/O helpers                                                */
/* ======================================================================== */

static PyObject *mod_open(PyObject *module, PyObject *args) {
    const char *path;
    if (!PyArg_ParseTuple(args, "s", &path)) return NULL;
    module_state *st = get_state(module);
    PyObject *a = Py_BuildValue("(s)", path);
    if (!a) return NULL;
    PyObject *obj = PyObject_Call(st->VDBFileType, a, NULL);
    Py_DECREF(a);
    return obj;
}

static PyObject *mod_from_bytes(PyObject *module, PyObject *args) {
    Py_buffer buf;
    if (!PyArg_ParseTuple(args, "y*", &buf)) return NULL;
    module_state *st = get_state(module);
    PyObject *kw = PyDict_New();
    PyObject *data = PyBytes_FromStringAndSize(buf.buf, buf.len);
    PyBuffer_Release(&buf);
    if (!kw || !data) { Py_XDECREF(kw); Py_XDECREF(data); return NULL; }
    PyDict_SetItemString(kw, "data", data);
    Py_DECREF(data);
    PyObject *empty = PyTuple_New(0);
    PyObject *obj = PyObject_Call(st->VDBFileType, empty, kw);
    Py_DECREF(empty);
    Py_DECREF(kw);
    return obj;
}

/* ======================================================================== */
/*  Buffer extraction helpers                                               */
/* ======================================================================== */

static float *extract_floats(PyObject *obj, Py_ssize_t *count) {
    Py_buffer buf;
    if (PyObject_GetBuffer(obj, &buf, PyBUF_C_CONTIGUOUS) < 0) return NULL;
    *count = buf.len / (Py_ssize_t)sizeof(float);
    float *data = (float *)malloc((size_t)buf.len);
    if (data) memcpy(data, buf.buf, (size_t)buf.len);
    PyBuffer_Release(&buf);
    return data;
}

static uint32_t *extract_uint32s(PyObject *obj, Py_ssize_t *count) {
    Py_buffer buf;
    if (PyObject_GetBuffer(obj, &buf, PyBUF_C_CONTIGUOUS) < 0) return NULL;
    *count = buf.len / (Py_ssize_t)sizeof(uint32_t);
    uint32_t *data = (uint32_t *)malloc((size_t)buf.len);
    if (data) memcpy(data, buf.buf, (size_t)buf.len);
    PyBuffer_Release(&buf);
    return data;
}

/* ======================================================================== */
/*  Mesh module functions                                                   */
/* ======================================================================== */

static PyObject *mod_mesh_to_sdf(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *verts_obj, *faces_obj;
    float voxel_size, band_width;
    int sign_method = 0;
    static char *kwlist[] = {"vertices", "faces", "voxel_size", "band_width", "sign_method", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "OOff|i", kwlist,
                                     &verts_obj, &faces_obj, &voxel_size, &band_width, &sign_method))
        return NULL;

    Py_ssize_t nfloats, nuints;
    float *verts = extract_floats(verts_obj, &nfloats);
    if (!verts) return NULL;
    uint32_t *faces = extract_uint32s(faces_obj, &nuints);
    if (!faces) { free(verts); return NULL; }

    float *out_data = NULL;
    int nx, ny, nz; float out_vs, ox, oy, oz;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_mesh_to_sdf(verts, (size_t)(nfloats/3), faces, (size_t)(nuints/3),
                             voxel_size, band_width, sign_method,
                             &out_data, &nx, &ny, &nz, &out_vs, &ox, &oy, &oz);
    Py_END_ALLOW_THREADS
    free(verts); free(faces);
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    return DenseGrid_from_c(get_state(module)->DenseGridType, out_data, nx, ny, nz, out_vs, ox, oy, oz);
}

static PyObject *mod_sdf_to_mesh(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *grid_obj; float isovalue = 0.0f;
    static char *kwlist[] = {"grid", "isovalue", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "O|f", kwlist, &grid_obj, &isovalue)) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    if (!g->data) return raise_vdb_error("DenseGrid has no data");
    float *out_verts = NULL; uint32_t *out_tris = NULL; size_t out_nv, out_nt;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_sdf_to_mesh(g->data, g->nx, g->ny, g->nz, g->voxel_size,
                             g->ox, g->oy, g->oz, isovalue,
                             &out_verts, &out_nv, &out_tris, &out_nt);
    Py_END_ALLOW_THREADS
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    return TriangleMesh_from_c(st->TriangleMeshType, out_verts, out_nv, out_tris, out_nt);
}

static PyObject *mod_make_manifold(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *verts_obj, *faces_obj;
    double resolution = 50.0, isovalue = 0.55;
    int sign_method = 0;
    static char *kwlist[] = {"vertices", "faces", "resolution", "isovalue", "sign_method", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "OO|ddi", kwlist,
                                     &verts_obj, &faces_obj, &resolution, &isovalue, &sign_method))
        return NULL;
    Py_ssize_t nfloats, nuints;
    float *verts = extract_floats(verts_obj, &nfloats);
    if (!verts) return NULL;
    uint32_t *faces = extract_uint32s(faces_obj, &nuints);
    if (!faces) { free(verts); return NULL; }
    float *out_verts = NULL; uint32_t *out_tris = NULL; size_t out_nv, out_nt;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_make_manifold(verts, (size_t)(nfloats/3), faces, (size_t)(nuints/3),
                               resolution, isovalue, sign_method,
                               &out_verts, &out_nv, &out_tris, &out_nt);
    Py_END_ALLOW_THREADS
    free(verts); free(faces);
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    return TriangleMesh_from_c(get_state(module)->TriangleMeshType,
                               out_verts, out_nv, out_tris, out_nt);
}

/* ======================================================================== */
/*  Ops: morphology / filtering (returns new DenseGrid)                     */
/* ======================================================================== */

/* Generic helper: copy grid data, apply in-place op, return new grid */
static PyObject *grid_unary_op(PyObject *module, PyObject *grid_obj,
                               int (*fn)(float *, int, int, int, float, float, float, float, int),
                               int iarg) {
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    if (!g->data) return raise_vdb_error("DenseGrid has no data");
    size_t n = (size_t)g->nx * g->ny * g->nz;
    float *copy = (float *)malloc(n * sizeof(float));
    if (!copy) return PyErr_NoMemory();
    memcpy(copy, g->data, n * sizeof(float));
    Py_BEGIN_ALLOW_THREADS
    fn(copy, g->nx, g->ny, g->nz, g->voxel_size, g->ox, g->oy, g->oz, iarg);
    Py_END_ALLOW_THREADS
    return DenseGrid_from_c(st->DenseGridType, copy, g->nx, g->ny, g->nz,
                            g->voxel_size, g->ox, g->oy, g->oz);
}

static PyObject *mod_dilate(PyObject *m, PyObject *a, PyObject *k) {
    PyObject *g; int it = 1;
    static char *kl[] = {"grid", "iterations", NULL};
    if (!PyArg_ParseTupleAndKeywords(a, k, "O|i", kl, &g, &it)) return NULL;
    return grid_unary_op(m, g, tvdb_py_dilate, it);
}
static PyObject *mod_erode(PyObject *m, PyObject *a, PyObject *k) {
    PyObject *g; int it = 1;
    static char *kl[] = {"grid", "iterations", NULL};
    if (!PyArg_ParseTupleAndKeywords(a, k, "O|i", kl, &g, &it)) return NULL;
    return grid_unary_op(m, g, tvdb_py_erode, it);
}
static PyObject *mod_open_op(PyObject *m, PyObject *a, PyObject *k) {
    PyObject *g; int it = 1;
    static char *kl[] = {"grid", "iterations", NULL};
    if (!PyArg_ParseTupleAndKeywords(a, k, "O|i", kl, &g, &it)) return NULL;
    return grid_unary_op(m, g, tvdb_py_open, it);
}
static PyObject *mod_close_op(PyObject *m, PyObject *a, PyObject *k) {
    PyObject *g; int it = 1;
    static char *kl[] = {"grid", "iterations", NULL};
    if (!PyArg_ParseTupleAndKeywords(a, k, "O|i", kl, &g, &it)) return NULL;
    return grid_unary_op(m, g, tvdb_py_close, it);
}

/* Filtering with width param */
static PyObject *grid_filter_op(PyObject *module, PyObject *grid_obj,
                                int (*fn)(float *, int, int, int, float, float, float, float, int, int),
                                int width, int iterations) {
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    if (!g->data) return raise_vdb_error("DenseGrid has no data");
    size_t n = (size_t)g->nx * g->ny * g->nz;
    float *copy = (float *)malloc(n * sizeof(float));
    if (!copy) return PyErr_NoMemory();
    memcpy(copy, g->data, n * sizeof(float));
    Py_BEGIN_ALLOW_THREADS
    fn(copy, g->nx, g->ny, g->nz, g->voxel_size, g->ox, g->oy, g->oz, width, iterations);
    Py_END_ALLOW_THREADS
    return DenseGrid_from_c(st->DenseGridType, copy, g->nx, g->ny, g->nz,
                            g->voxel_size, g->ox, g->oy, g->oz);
}

static PyObject *mod_gaussian_filter(PyObject *m, PyObject *a, PyObject *k) {
    PyObject *g; int w = 1, it = 1;
    static char *kl[] = {"grid", "width", "iterations", NULL};
    if (!PyArg_ParseTupleAndKeywords(a, k, "O|ii", kl, &g, &w, &it)) return NULL;
    return grid_filter_op(m, g, tvdb_py_gaussian_filter, w, it);
}
static PyObject *mod_mean_filter(PyObject *m, PyObject *a, PyObject *k) {
    PyObject *g; int w = 1, it = 1;
    static char *kl[] = {"grid", "width", "iterations", NULL};
    if (!PyArg_ParseTupleAndKeywords(a, k, "O|ii", kl, &g, &w, &it)) return NULL;
    return grid_filter_op(m, g, tvdb_py_mean_filter, w, it);
}
static PyObject *mod_laplacian_filter(PyObject *m, PyObject *a, PyObject *k) {
    PyObject *g; int it = 1;
    static char *kl[] = {"grid", "iterations", NULL};
    if (!PyArg_ParseTupleAndKeywords(a, k, "O|i", kl, &g, &it)) return NULL;
    return grid_unary_op(m, g, tvdb_py_laplacian_filter, it);
}

/* ======================================================================== */
/*  CSG                                                                     */
/* ======================================================================== */

static PyObject *csg_op_impl(PyObject *module, PyObject *args,
                             int (*func)(const float *, const float *,
                                         int, int, int, float, float, float, float, float **)) {
    PyObject *a_obj, *b_obj;
    if (!PyArg_ParseTuple(args, "OO", &a_obj, &b_obj)) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(a_obj, st->DenseGridType) ||
        !PyObject_IsInstance(b_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected two DenseGrid objects"); return NULL;
    }
    PyDenseGrid *a = (PyDenseGrid *)a_obj, *b = (PyDenseGrid *)b_obj;
    if (!a->data || !b->data) return raise_vdb_error("DenseGrid has no data");
    if (a->nx != b->nx || a->ny != b->ny || a->nz != b->nz) {
        PyErr_SetString(PyExc_ValueError, "Grids must have same dimensions"); return NULL;
    }
    float *out = NULL;
    Py_BEGIN_ALLOW_THREADS
    func(a->data, b->data, a->nx, a->ny, a->nz, a->voxel_size, a->ox, a->oy, a->oz, &out);
    Py_END_ALLOW_THREADS
    return DenseGrid_from_c(st->DenseGridType, out, a->nx, a->ny, a->nz,
                            a->voxel_size, a->ox, a->oy, a->oz);
}

static PyObject *mod_csg_union(PyObject *m, PyObject *a) { return csg_op_impl(m, a, tvdb_py_csg_union); }
static PyObject *mod_csg_intersection(PyObject *m, PyObject *a) { return csg_op_impl(m, a, tvdb_py_csg_intersection); }
static PyObject *mod_csg_difference(PyObject *m, PyObject *a) { return csg_op_impl(m, a, tvdb_py_csg_difference); }

/* ======================================================================== */
/*  Measurement                                                             */
/* ======================================================================== */

static PyObject *mod_surface_area(PyObject *module, PyObject *args) {
    PyObject *grid_obj;
    if (!PyArg_ParseTuple(args, "O", &grid_obj)) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    if (!g->data) return raise_vdb_error("DenseGrid has no data");
    float result;
    Py_BEGIN_ALLOW_THREADS
    result = tvdb_py_surface_area(g->data, g->nx, g->ny, g->nz, g->voxel_size, g->ox, g->oy, g->oz);
    Py_END_ALLOW_THREADS
    return PyFloat_FromDouble(result);
}

static PyObject *mod_volume(PyObject *module, PyObject *args) {
    PyObject *grid_obj;
    if (!PyArg_ParseTuple(args, "O", &grid_obj)) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    if (!g->data) return raise_vdb_error("DenseGrid has no data");
    float result;
    Py_BEGIN_ALLOW_THREADS
    result = tvdb_py_volume(g->data, g->nx, g->ny, g->nz, g->voxel_size, g->ox, g->oy, g->oz);
    Py_END_ALLOW_THREADS
    return PyFloat_FromDouble(result);
}

/* ======================================================================== */
/*  Differential operators                                                  */
/* ======================================================================== */

static PyObject *mod_gradient(PyObject *module, PyObject *args) {
    PyObject *grid_obj;
    if (!PyArg_ParseTuple(args, "O", &grid_obj)) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    if (!g->data) return raise_vdb_error("DenseGrid has no data");
    float *out = NULL;
    Py_BEGIN_ALLOW_THREADS
    tvdb_py_gradient(g->data, g->nx, g->ny, g->nz, g->voxel_size, g->ox, g->oy, g->oz, &out);
    Py_END_ALLOW_THREADS
    return DenseVecGrid_from_c(st->DenseVecGridType, out, g->nx, g->ny, g->nz,
                               g->voxel_size, g->ox, g->oy, g->oz);
}

static PyObject *mod_divergence(PyObject *module, PyObject *args) {
    PyObject *grid_obj;
    if (!PyArg_ParseTuple(args, "O", &grid_obj)) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseVecGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseVecGrid"); return NULL;
    }
    PyDenseVecGrid *g = (PyDenseVecGrid *)grid_obj;
    if (!g->data) return raise_vdb_error("DenseVecGrid has no data");
    float *out = NULL;
    Py_BEGIN_ALLOW_THREADS
    tvdb_py_divergence(g->data, g->nx, g->ny, g->nz, g->voxel_size, g->ox, g->oy, g->oz, &out);
    Py_END_ALLOW_THREADS
    return DenseGrid_from_c(st->DenseGridType, out, g->nx, g->ny, g->nz,
                            g->voxel_size, g->ox, g->oy, g->oz);
}

static PyObject *mod_laplacian_op(PyObject *module, PyObject *args) {
    PyObject *grid_obj;
    if (!PyArg_ParseTuple(args, "O", &grid_obj)) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    if (!g->data) return raise_vdb_error("DenseGrid has no data");
    float *out = NULL;
    Py_BEGIN_ALLOW_THREADS
    tvdb_py_laplacian(g->data, g->nx, g->ny, g->nz, g->voxel_size, g->ox, g->oy, g->oz, &out);
    Py_END_ALLOW_THREADS
    return DenseGrid_from_c(st->DenseGridType, out, g->nx, g->ny, g->nz,
                            g->voxel_size, g->ox, g->oy, g->oz);
}

static PyObject *mod_curl(PyObject *module, PyObject *args) {
    PyObject *grid_obj;
    if (!PyArg_ParseTuple(args, "O", &grid_obj)) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseVecGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseVecGrid"); return NULL;
    }
    PyDenseVecGrid *g = (PyDenseVecGrid *)grid_obj;
    if (!g->data) return raise_vdb_error("DenseVecGrid has no data");
    float *out = NULL;
    Py_BEGIN_ALLOW_THREADS
    tvdb_py_curl(g->data, g->nx, g->ny, g->nz, g->voxel_size, g->ox, g->oy, g->oz, &out);
    Py_END_ALLOW_THREADS
    return DenseVecGrid_from_c(st->DenseVecGridType, out, g->nx, g->ny, g->nz,
                               g->voxel_size, g->ox, g->oy, g->oz);
}

/* ======================================================================== */
/*  Advection & Poisson                                                     */
/* ======================================================================== */

static PyObject *mod_advect(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *field_obj, *vel_obj; float dt;
    static char *kwlist[] = {"field", "velocity", "dt", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "OOf", kwlist, &field_obj, &vel_obj, &dt))
        return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(field_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected DenseGrid for field"); return NULL;
    }
    if (!PyObject_IsInstance(vel_obj, st->DenseVecGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected DenseVecGrid for velocity"); return NULL;
    }
    PyDenseGrid *f = (PyDenseGrid *)field_obj;
    PyDenseVecGrid *v = (PyDenseVecGrid *)vel_obj;
    if (!f->data || !v->data) return raise_vdb_error("Grid has no data");
    float *out = NULL;
    Py_BEGIN_ALLOW_THREADS
    tvdb_py_advect(f->data, v->data, f->nx, f->ny, f->nz,
                   f->voxel_size, f->ox, f->oy, f->oz, dt, &out);
    Py_END_ALLOW_THREADS
    return DenseGrid_from_c(st->DenseGridType, out, f->nx, f->ny, f->nz,
                            f->voxel_size, f->ox, f->oy, f->oz);
}

static PyObject *mod_solve_poisson(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *rhs_obj; int max_iters = 500; float tolerance = 1e-6f;
    static char *kwlist[] = {"rhs", "max_iters", "tolerance", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "O|if", kwlist, &rhs_obj, &max_iters, &tolerance))
        return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(rhs_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)rhs_obj;
    if (!g->data) return raise_vdb_error("DenseGrid has no data");
    float *out = NULL; int iters;
    Py_BEGIN_ALLOW_THREADS
    tvdb_py_solve_poisson(g->data, g->nx, g->ny, g->nz, g->voxel_size,
                          g->ox, g->oy, g->oz, max_iters, tolerance, &out, &iters);
    Py_END_ALLOW_THREADS
    PyObject *grid = DenseGrid_from_c(st->DenseGridType, out, g->nx, g->ny, g->nz,
                                      g->voxel_size, g->ox, g->oy, g->oz);
    if (!grid) return NULL;
    return Py_BuildValue("(Oi)", grid, iters);
}

/* ======================================================================== */
/*  Ray casting                                                             */
/* ======================================================================== */

static PyObject *mod_ray_cast_sdf(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *grid_obj, *origin_tuple, *dir_tuple;
    float max_t = 1e6f;
    static char *kwlist[] = {"grid", "origin", "direction", "max_t", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "OOO|f", kwlist,
                                     &grid_obj, &origin_tuple, &dir_tuple, &max_t))
        return NULL;
    float ray_ox, ray_oy, ray_oz, ray_dx, ray_dy, ray_dz;
    if (!PyArg_ParseTuple(origin_tuple, "fff", &ray_ox, &ray_oy, &ray_oz)) return NULL;
    if (!PyArg_ParseTuple(dir_tuple, "fff", &ray_dx, &ray_dy, &ray_dz)) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    if (!g->data) return raise_vdb_error("DenseGrid has no data");
    int hit; float t, px, py, pz, nx, ny, nz;
    Py_BEGIN_ALLOW_THREADS
    tvdb_py_ray_cast_sdf(g->data, g->nx, g->ny, g->nz, g->voxel_size,
                         g->ox, g->oy, g->oz,
                         ray_ox, ray_oy, ray_oz, ray_dx, ray_dy, ray_dz, max_t,
                         &hit, &t, &px, &py, &pz, &nx, &ny, &nz);
    Py_END_ALLOW_THREADS
    if (!hit) Py_RETURN_NONE;
    return Py_BuildValue("{s:f,s:(fff),s:(fff)}", "t", t,
                         "position", px, py, pz, "normal", nx, ny, nz);
}

/* ======================================================================== */
/*  Particles                                                               */
/* ======================================================================== */

static PyObject *mod_particles_to_sdf(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *pos_obj, *radii_obj; float voxel_size, band_width;
    static char *kwlist[] = {"positions", "radii", "voxel_size", "band_width", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "OOff", kwlist,
                                     &pos_obj, &radii_obj, &voxel_size, &band_width))
        return NULL;
    Py_ssize_t npos, nrad;
    float *positions = extract_floats(pos_obj, &npos);
    if (!positions) return NULL;
    float *radii = extract_floats(radii_obj, &nrad);
    if (!radii) { free(positions); return NULL; }
    float *out = NULL; int nx, ny, nz; float out_vs, ox, oy, oz;
    Py_BEGIN_ALLOW_THREADS
    tvdb_py_particles_to_sdf(positions, radii, (size_t)(npos/3), voxel_size, band_width,
                             &out, &nx, &ny, &nz, &out_vs, &ox, &oy, &oz);
    Py_END_ALLOW_THREADS
    free(positions); free(radii);
    return DenseGrid_from_c(get_state(module)->DenseGridType, out, nx, ny, nz, out_vs, ox, oy, oz);
}

static PyObject *mod_volume_to_spheres(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *grid_obj; float min_radius = 0.0f, overlap = 0.25f; int max_spheres = 1000;
    static char *kwlist[] = {"grid", "min_radius", "max_spheres", "overlap", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "O|fif", kwlist,
                                     &grid_obj, &min_radius, &max_spheres, &overlap))
        return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    if (!g->data) return raise_vdb_error("DenseGrid has no data");
    float *centers = NULL, *radii = NULL; size_t count;
    Py_BEGIN_ALLOW_THREADS
    tvdb_py_volume_to_spheres(g->data, g->nx, g->ny, g->nz, g->voxel_size,
                              g->ox, g->oy, g->oz, min_radius, max_spheres, overlap,
                              &centers, &radii, &count);
    Py_END_ALLOW_THREADS
    PyObject *c_bytes = PyBytes_FromStringAndSize((const char *)centers, (Py_ssize_t)(count * 3 * sizeof(float)));
    PyObject *r_bytes = PyBytes_FromStringAndSize((const char *)radii, (Py_ssize_t)(count * sizeof(float)));
    free(centers); free(radii);
    return Py_BuildValue("{s:N,s:N,s:n}", "centers", c_bytes, "radii", r_bytes, "count", (Py_ssize_t)count);
}

/* ======================================================================== */
/*  Fracture                                                                */
/* ======================================================================== */

static PyObject *mod_fracture(PyObject *module, PyObject *args) {
    PyObject *grid_obj, *cutters_list;
    if (!PyArg_ParseTuple(args, "OO", &grid_obj, &cutters_list)) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    if (!PyList_Check(cutters_list)) {
        PyErr_SetString(PyExc_TypeError, "Expected a list of DenseGrid cutters"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    if (!g->data) return raise_vdb_error("DenseGrid has no data");

    Py_ssize_t nc = PyList_Size(cutters_list);
    const float **cutter_ptrs = (const float **)malloc((size_t)nc * sizeof(float *));
    if (!cutter_ptrs) return PyErr_NoMemory();
    for (Py_ssize_t i = 0; i < nc; i++) {
        PyObject *c = PyList_GetItem(cutters_list, i);
        if (!PyObject_IsInstance(c, st->DenseGridType)) {
            free(cutter_ptrs);
            PyErr_SetString(PyExc_TypeError, "All cutters must be DenseGrid"); return NULL;
        }
        cutter_ptrs[i] = ((PyDenseGrid *)c)->data;
    }
    float **pieces = NULL; int num_pieces;
    Py_BEGIN_ALLOW_THREADS
    tvdb_py_fracture(g->data, g->nx, g->ny, g->nz, g->voxel_size,
                     g->ox, g->oy, g->oz, cutter_ptrs, (int)nc, &pieces, &num_pieces);
    Py_END_ALLOW_THREADS
    free(cutter_ptrs);

    PyObject *result = PyList_New(num_pieces);
    for (int i = 0; i < num_pieces; i++) {
        PyObject *piece = DenseGrid_from_c(st->DenseGridType, pieces[i],
                                           g->nx, g->ny, g->nz,
                                           g->voxel_size, g->ox, g->oy, g->oz);
        PyList_SetItem(result, i, piece); /* steals ref */
    }
    free(pieces);
    return result;
}

/* ======================================================================== */
/*  Module definition                                                       */
/* ======================================================================== */

static PyMethodDef module_methods[] = {
    {"open", mod_open, METH_VARARGS, "Open a VDB file by path"},
    {"from_bytes", mod_from_bytes, METH_VARARGS, "Open VDB from bytes"},
    {"mesh_to_sdf", (PyCFunction)mod_mesh_to_sdf, METH_VARARGS | METH_KEYWORDS, "Mesh to SDF"},
    {"sdf_to_mesh", (PyCFunction)mod_sdf_to_mesh, METH_VARARGS | METH_KEYWORDS, "SDF to mesh"},
    {"make_manifold", (PyCFunction)mod_make_manifold, METH_VARARGS | METH_KEYWORDS, "Make manifold"},
    {"dilate", (PyCFunction)mod_dilate, METH_VARARGS | METH_KEYWORDS, "Dilate SDF"},
    {"erode", (PyCFunction)mod_erode, METH_VARARGS | METH_KEYWORDS, "Erode SDF"},
    {"open_op", (PyCFunction)mod_open_op, METH_VARARGS | METH_KEYWORDS, "Morphological open"},
    {"close_op", (PyCFunction)mod_close_op, METH_VARARGS | METH_KEYWORDS, "Morphological close"},
    {"gaussian_filter", (PyCFunction)mod_gaussian_filter, METH_VARARGS | METH_KEYWORDS, "Gaussian filter"},
    {"mean_filter", (PyCFunction)mod_mean_filter, METH_VARARGS | METH_KEYWORDS, "Mean filter"},
    {"laplacian_filter", (PyCFunction)mod_laplacian_filter, METH_VARARGS | METH_KEYWORDS, "Laplacian filter"},
    {"csg_union", mod_csg_union, METH_VARARGS, "CSG union"},
    {"csg_intersection", mod_csg_intersection, METH_VARARGS, "CSG intersection"},
    {"csg_difference", mod_csg_difference, METH_VARARGS, "CSG difference"},
    {"surface_area", mod_surface_area, METH_VARARGS, "SDF surface area"},
    {"volume", mod_volume, METH_VARARGS, "SDF volume"},
    {"gradient", mod_gradient, METH_VARARGS, "Gradient"},
    {"divergence", mod_divergence, METH_VARARGS, "Divergence"},
    {"laplacian", mod_laplacian_op, METH_VARARGS, "Laplacian"},
    {"curl", mod_curl, METH_VARARGS, "Curl"},
    {"advect", (PyCFunction)mod_advect, METH_VARARGS | METH_KEYWORDS, "Advection"},
    {"solve_poisson", (PyCFunction)mod_solve_poisson, METH_VARARGS | METH_KEYWORDS, "Poisson solver"},
    {"ray_cast_sdf", (PyCFunction)mod_ray_cast_sdf, METH_VARARGS | METH_KEYWORDS, "Ray cast SDF"},
    {"particles_to_sdf", (PyCFunction)mod_particles_to_sdf, METH_VARARGS | METH_KEYWORDS, "Particles to SDF"},
    {"volume_to_spheres", (PyCFunction)mod_volume_to_spheres, METH_VARARGS | METH_KEYWORDS, "Volume to spheres"},
    {"fracture", mod_fracture, METH_VARARGS, "Fracture"},
    {NULL, NULL, 0, NULL}
};

static int module_traverse(PyObject *mod, visitproc visit, void *arg) {
    module_state *st = get_state(mod);
    Py_VISIT(st->VDBError);
    Py_VISIT(st->VDBFileType);
    Py_VISIT(st->VDBGridType);
    Py_VISIT(st->VDBTreeType);
    Py_VISIT(st->VDBNodeType);
    Py_VISIT(st->DenseGridType);
    Py_VISIT(st->DenseVecGridType);
    Py_VISIT(st->TriangleMeshType);
    return 0;
}

static int module_clear(PyObject *mod) {
    module_state *st = get_state(mod);
    Py_CLEAR(st->VDBError);
    Py_CLEAR(st->VDBFileType);
    Py_CLEAR(st->VDBGridType);
    Py_CLEAR(st->VDBTreeType);
    Py_CLEAR(st->VDBNodeType);
    Py_CLEAR(st->DenseGridType);
    Py_CLEAR(st->DenseVecGridType);
    Py_CLEAR(st->TriangleMeshType);
    return 0;
}

static void module_free(void *mod) { module_clear((PyObject *)mod); }

static struct PyModuleDef tinyvdb_module = {
    PyModuleDef_HEAD_INIT,
    "_tinyvdb",
    "TinyVDB Python bindings",
    sizeof(module_state),
    module_methods,
    NULL,
    module_traverse,
    module_clear,
    (freefunc)module_free,
};

#define ADD_TYPE(field, spec, name) do { \
    st->field = PyType_FromSpec(&spec); \
    if (!st->field) goto fail; \
    if (PyModule_AddObject(mod, name, Py_NewRef(st->field)) < 0) goto fail; \
} while(0)

PyMODINIT_FUNC PyInit__tinyvdb(void) {
    PyObject *mod = PyModule_Create(&tinyvdb_module);
    if (!mod) return NULL;
    module_state *st = get_state(mod);

    st->VDBError = PyErr_NewException("tinyvdb.VDBError", PyExc_RuntimeError, NULL);
    if (!st->VDBError) goto fail;
    if (PyModule_AddObject(mod, "VDBError", Py_NewRef(st->VDBError)) < 0) goto fail;

    ADD_TYPE(VDBFileType, VDBFile_spec, "VDBFile");
    ADD_TYPE(VDBGridType, VDBGrid_spec, "VDBGrid");
    ADD_TYPE(VDBTreeType, VDBTree_spec, "VDBTree");
    ADD_TYPE(VDBNodeType, VDBNode_spec, "VDBNode");
    ADD_TYPE(DenseGridType, DenseGrid_spec, "DenseGrid");
    ADD_TYPE(DenseVecGridType, DenseVecGrid_spec, "DenseVecGrid");
    ADD_TYPE(TriangleMeshType, TriangleMesh_spec, "TriangleMesh");

    PyModule_AddIntConstant(mod, "COMPRESS_NONE", TVDB_COMPRESS_NONE);
    PyModule_AddIntConstant(mod, "COMPRESS_ZIP", TVDB_COMPRESS_ZIP);
    PyModule_AddIntConstant(mod, "COMPRESS_ACTIVE_MASK", TVDB_COMPRESS_ACTIVE_MASK);
    PyModule_AddIntConstant(mod, "COMPRESS_BLOSC", TVDB_COMPRESS_BLOSC);
    PyModule_AddIntConstant(mod, "SIGN_FLOOD_FILL", 0);
    PyModule_AddIntConstant(mod, "SIGN_SWEEP", 1);

    if (PyState_AddModule(mod, &tinyvdb_module) < 0) goto fail;
    return mod;

fail:
    Py_DECREF(mod);
    return NULL;
}
