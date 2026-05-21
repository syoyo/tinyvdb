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

extern int tvdb_py_write_float_grid_dense(const char *path,
                                          const float *values, size_t count,
                                          int nx, int ny, int nz,
                                          double vsx, double vsy, double vsz,
                                          double ox, double oy, double oz,
                                          const char *grid_name, float background,
                                          unsigned int compression, int level);

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
extern int tvdb_py_solve_poisson_d(const float *, int, int, int, float, float, float, float, int, double, float **, int *);
extern int tvdb_py_fast_sweeping(const float *, int, int, int, float, float, float, float, float, int, float, float **, int *);

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

extern int tvdb_py_sample_trilinear(const float *, int, int, int, float, float, float, float,
                                    const float *, size_t, float **);
extern int tvdb_py_integrate_tsdf(const float *, int, int, float, float, float, float,
                                  const float *, float, float, float,
                                  int, int, int, float, float, float, float,
                                  float **, float **);
extern int tvdb_py_coarsen_grid(const float *, int, int, int, float, float, float, float,
                                int, float **, int *, int *, int *,
                                float *, float *, float *, float *);
extern int tvdb_py_refine_grid(const float *, int, int, int, float, float, float, float,
                               int, float **, int *, int *, int *,
                               float *, float *, float *, float *);
extern int tvdb_py_max_pool(const float *, int, int, int, float, float, float, float,
                            int, int, int, float **, int *, int *, int *,
                            float *, float *, float *, float *);
extern int tvdb_py_avg_pool(const float *, int, int, int, float, float, float, float,
                            int, int, int, float **, int *, int *, int *,
                            float *, float *, float *, float *);

extern int tvdb_py_splat_trilinear(float *, int, int, int, float, float, float, float,
                                   const float *, const float *, size_t, float *);
extern int tvdb_py_voxels_along_ray(const float *, int, int, int, float, float, float, float,
                                    float, float, float, float, float, float, float, float,
                                    int **, size_t *);
extern int tvdb_py_uniform_ray_samples(float, float, float, float, float, float,
                                       float, float, size_t, float **, float **);
extern int tvdb_py_segments_along_ray(const float *, int, int, int, float, float, float, float,
                                      float, float, float, float, float, float, float, float, float,
                                      size_t, size_t, float **, size_t *);
extern int tvdb_py_clip_grid(const float *, int, int, int, float, float, float, float,
                             const float *, const float *,
                             float **, int *, int *, int *,
                             float *, float *, float *, float *);
extern int tvdb_py_prune_grid(float *, int, int, int, float, float, float, float,
                              float, float);
extern int tvdb_py_merge_grids(const float *, int, int, int, float, float, float, float,
                               const float *, int, int, int, float, float, float, float,
                               float, float **, int *, int *, int *,
                               float *, float *, float *, float *);

extern int tvdb_py_integrate_tsdf_into(float *, float *, int, int, int, float,
                                       float, float, float,
                                       const float *, int, int, float, float, float, float,
                                       const float *, float, float, float);
extern int tvdb_py_integrate_tsdf_with_color_into(float *, float *, float *,
                                                  int, int, int, float, float, float, float,
                                                  const float *, int, int,
                                                  float, float, float, float,
                                                  const float *, float, float, float,
                                                  const uint8_t *);

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
    /* Cached for buffer protocol (filled on demand). Layout: data[x + nx*y +
       nx*ny*z] -> exposes shape (nz, ny, nx) C-contiguous, format 'f'. */
    Py_ssize_t buf_shape[3];
    Py_ssize_t buf_strides[3];
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
    /* Layout: linear index = x + nx*y + nx*ny*z, so axis 0 = z (slowest),
       axis 1 = y, axis 2 = x (fastest). Shape (nz, ny, nx) is C-contiguous.
       Numpy users index as arr[z, y, x]. */
    g->buf_shape[0] = g->nz; g->buf_shape[1] = g->ny; g->buf_shape[2] = g->nx;
    g->buf_strides[0] = (Py_ssize_t)g->ny * g->nx * (Py_ssize_t)sizeof(float);
    g->buf_strides[1] = (Py_ssize_t)g->nx * (Py_ssize_t)sizeof(float);
    g->buf_strides[2] = (Py_ssize_t)sizeof(float);

    Py_ssize_t total = (Py_ssize_t)g->nz * g->ny * g->nx * (Py_ssize_t)sizeof(float);
    view->buf      = g->data;
    view->obj      = (PyObject *)self;
    Py_INCREF(self);
    view->len      = total;
    view->readonly = 0;
    view->itemsize = (Py_ssize_t)sizeof(float);
    view->format   = (flags & PyBUF_FORMAT) ? (char *)"f" : NULL;
    view->ndim     = 3;
    view->shape    = (flags & PyBUF_ND) ? g->buf_shape : NULL;
    view->strides  = (flags & PyBUF_STRIDES) ? g->buf_strides : NULL;
    view->suboffsets = NULL;
    view->internal = NULL;
    return 0;
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
    Py_ssize_t buf_shape[4];
    Py_ssize_t buf_strides[4];
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
    /* Layout: data[((z * ny + y) * nx + x) * 3 + c] -> shape (nz, ny, nx, 3),
       C-contiguous. */
    g->buf_shape[0] = g->nz; g->buf_shape[1] = g->ny;
    g->buf_shape[2] = g->nx; g->buf_shape[3] = 3;
    g->buf_strides[3] = (Py_ssize_t)sizeof(float);
    g->buf_strides[2] = 3 * (Py_ssize_t)sizeof(float);
    g->buf_strides[1] = (Py_ssize_t)g->nx * 3 * (Py_ssize_t)sizeof(float);
    g->buf_strides[0] = (Py_ssize_t)g->ny * g->nx * 3 * (Py_ssize_t)sizeof(float);

    Py_ssize_t total = (Py_ssize_t)g->nz * g->ny * g->nx * 3 * (Py_ssize_t)sizeof(float);
    view->buf      = g->data;
    view->obj      = (PyObject *)self;
    Py_INCREF(self);
    view->len      = total;
    view->readonly = 0;
    view->itemsize = (Py_ssize_t)sizeof(float);
    view->format   = (flags & PyBUF_FORMAT) ? (char *)"f" : NULL;
    view->ndim     = 4;
    view->shape    = (flags & PyBUF_ND) ? g->buf_shape : NULL;
    view->strides  = (flags & PyBUF_STRIDES) ? g->buf_strides : NULL;
    view->suboffsets = NULL;
    view->internal = NULL;
    return 0;
}

static PyGetSetDef DenseVecGrid_getset[] = {
    {"shape", DenseVecGrid_get_shape, NULL, "Grid dimensions", NULL},
    {"origin", DenseVecGrid_get_origin, NULL, "Grid origin", NULL},
    {"voxel_size", DenseVecGrid_get_voxel_size, NULL, "Voxel size", NULL},
    {NULL}
};

static int DenseVecGrid_init(PyObject *self, PyObject *args, PyObject *kw) {
    PyDenseVecGrid *g = (PyDenseVecGrid *)self;
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
        size_t n = (size_t)nx * ny * nz * 3;
        g->data = (float *)calloc(n, sizeof(float));
        if (!g->data) { PyErr_NoMemory(); return -1; }
    }
    return 0;
}

static PyType_Slot DenseVecGrid_slots[] = {
    {Py_tp_dealloc, DenseVecGrid_dealloc},
    {Py_tp_new, DenseVecGrid_new},
    {Py_tp_init, DenseVecGrid_init},
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
    Py_ssize_t vert_shape[2];
    Py_ssize_t vert_strides[2];
    Py_ssize_t face_shape[2];
    Py_ssize_t face_strides[2];
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
static PyObject *TriangleMesh_get_vertices_bytes(PyObject *self, void *c) {
    PyTriangleMesh *m = (PyTriangleMesh *)self;
    if (!m->vertices) Py_RETURN_NONE;
    return PyBytes_FromStringAndSize((const char *)m->vertices,
                                    (Py_ssize_t)(m->num_vertices * 3 * sizeof(float)));
}
static PyObject *TriangleMesh_get_faces_bytes(PyObject *self, void *c) {
    PyTriangleMesh *m = (PyTriangleMesh *)self;
    if (!m->faces) Py_RETURN_NONE;
    return PyBytes_FromStringAndSize((const char *)m->faces,
                                    (Py_ssize_t)(m->num_faces * 3 * sizeof(uint32_t)));
}

/* Build a 2D memoryview backed by mesh data; mesh keeps memory alive. */
static PyObject *TriangleMesh_get_vertices(PyObject *self, void *c) {
    PyTriangleMesh *m = (PyTriangleMesh *)self;
    if (!m->vertices || m->num_vertices == 0) Py_RETURN_NONE;
    m->vert_shape[0] = (Py_ssize_t)m->num_vertices;
    m->vert_shape[1] = 3;
    m->vert_strides[0] = 3 * (Py_ssize_t)sizeof(float);
    m->vert_strides[1] = (Py_ssize_t)sizeof(float);
    Py_buffer view;
    view.buf       = m->vertices;
    view.obj       = self; Py_INCREF(self);
    view.len       = (Py_ssize_t)(m->num_vertices * 3 * sizeof(float));
    view.readonly  = 0;
    view.itemsize  = (Py_ssize_t)sizeof(float);
    view.format    = (char *)"f";
    view.ndim      = 2;
    view.shape     = m->vert_shape;
    view.strides   = m->vert_strides;
    view.suboffsets = NULL;
    view.internal  = NULL;
    return PyMemoryView_FromBuffer(&view);
}

static PyObject *TriangleMesh_get_faces(PyObject *self, void *c) {
    PyTriangleMesh *m = (PyTriangleMesh *)self;
    if (!m->faces || m->num_faces == 0) Py_RETURN_NONE;
    m->face_shape[0] = (Py_ssize_t)m->num_faces;
    m->face_shape[1] = 3;
    m->face_strides[0] = 3 * (Py_ssize_t)sizeof(uint32_t);
    m->face_strides[1] = (Py_ssize_t)sizeof(uint32_t);
    Py_buffer view;
    view.buf       = m->faces;
    view.obj       = self; Py_INCREF(self);
    view.len       = (Py_ssize_t)(m->num_faces * 3 * sizeof(uint32_t));
    view.readonly  = 0;
    view.itemsize  = (Py_ssize_t)sizeof(uint32_t);
    view.format    = (char *)"I";
    view.ndim      = 2;
    view.shape     = m->face_shape;
    view.strides   = m->face_strides;
    view.suboffsets = NULL;
    view.internal  = NULL;
    return PyMemoryView_FromBuffer(&view);
}

/* Object-level buffer protocol: 2D vertices view (format 'f', shape (nv, 3)). */
static int TriangleMesh_getbuffer(PyObject *self, Py_buffer *view, int flags) {
    PyTriangleMesh *m = (PyTriangleMesh *)self;
    if (!m->vertices) {
        PyErr_SetString(PyExc_BufferError, "TriangleMesh has no vertices");
        return -1;
    }
    m->vert_shape[0] = (Py_ssize_t)m->num_vertices;
    m->vert_shape[1] = 3;
    m->vert_strides[0] = 3 * (Py_ssize_t)sizeof(float);
    m->vert_strides[1] = (Py_ssize_t)sizeof(float);
    Py_ssize_t total = (Py_ssize_t)(m->num_vertices * 3 * sizeof(float));
    view->buf       = m->vertices;
    view->obj       = self; Py_INCREF(self);
    view->len       = total;
    view->readonly  = 0;
    view->itemsize  = (Py_ssize_t)sizeof(float);
    view->format    = (flags & PyBUF_FORMAT) ? (char *)"f" : NULL;
    view->ndim      = 2;
    view->shape     = (flags & PyBUF_ND) ? m->vert_shape : NULL;
    view->strides   = (flags & PyBUF_STRIDES) ? m->vert_strides : NULL;
    view->suboffsets = NULL;
    view->internal  = NULL;
    return 0;
}

static PyGetSetDef TriangleMesh_getset[] = {
    {"num_vertices", TriangleMesh_get_num_vertices, NULL, "Number of vertices", NULL},
    {"num_faces", TriangleMesh_get_num_faces, NULL, "Number of faces", NULL},
    {"vertices", TriangleMesh_get_vertices, NULL,
     "Vertices as a 2D memoryview, shape (nv, 3), float32", NULL},
    {"faces", TriangleMesh_get_faces, NULL,
     "Face indices as a 2D memoryview, shape (nf, 3), uint32", NULL},
    {"vertices_bytes", TriangleMesh_get_vertices_bytes, NULL, "Vertices as raw bytes", NULL},
    {"faces_bytes", TriangleMesh_get_faces_bytes, NULL, "Faces as raw bytes", NULL},
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

/* ---- bridge methods on VDBGrid ---- */

extern size_t tvdb_py_grid_active_voxel_count(const tvdb_grid_t *);
extern int    tvdb_py_grid_active_bbox(const tvdb_grid_t *, int32_t [3], int32_t [3]);
extern float  tvdb_py_grid_float_background(const tvdb_grid_t *);
extern int    tvdb_py_grid_materialize_dense(const tvdb_grid_t *,
                                             const int32_t [3], const int32_t [3],
                                             float, float **, int *, int *, int *,
                                             float *, float *, float *, float *);
extern int    tvdb_py_grid_dilate_active(const tvdb_grid_t *, int,
                                         int32_t **, float **, size_t *);
extern int    tvdb_py_grid_erode_active(const tvdb_grid_t *, int,
                                        int32_t **, float **, size_t *);
extern int    tvdb_py_grid_to_sparse(const tvdb_grid_t *,
                                     int32_t **, float **, size_t *);
extern int    tvdb_py_grid_dilate_topology(const tvdb_grid_t *, int,
                                           int32_t **, float **, size_t *);
extern int    tvdb_py_grid_erode_topology(const tvdb_grid_t *, int,
                                          int32_t **, float **, size_t *);
extern int    tvdb_py_grid_csg(const tvdb_grid_t *, const tvdb_grid_t *, int,
                               int32_t **, float **, size_t *);
extern int    tvdb_py_grid_update_from_sparse(tvdb_grid_t *,
                                              const int32_t *, const float *,
                                              size_t, size_t *, size_t *);

static PyObject *VDBGrid_active_voxel_count(PyObject *self, PyObject *Py_UNUSED(args)) {
    tvdb_grid_t *g = ((PyVDBGrid *)self)->grid;
    return PyLong_FromSize_t(tvdb_py_grid_active_voxel_count(g));
}

static PyObject *VDBGrid_active_bbox(PyObject *self, PyObject *Py_UNUSED(args)) {
    tvdb_grid_t *g = ((PyVDBGrid *)self)->grid;
    int32_t mn[3], mx[3];
    if (tvdb_py_grid_active_bbox(g, mn, mx) != 0) Py_RETURN_NONE;
    return Py_BuildValue("((iii)(iii))", mn[0], mn[1], mn[2], mx[0], mx[1], mx[2]);
}

static PyObject *VDBGrid_float_background(PyObject *self, PyObject *Py_UNUSED(args)) {
    tvdb_grid_t *g = ((PyVDBGrid *)self)->grid;
    return PyFloat_FromDouble((double)tvdb_py_grid_float_background(g));
}

static PyObject *VDBGrid_materialize_dense(PyObject *self, PyObject *args, PyObject *kw) {
    PyObject *bb_min_t, *bb_max_t;
    float background = 0.0f;
    static char *kwlist[] = {"bbox_min", "bbox_max", "background", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "OO|f", kwlist,
                                     &bb_min_t, &bb_max_t, &background)) return NULL;
    int32_t mn[3], mx[3];
    if (!PyArg_ParseTuple(bb_min_t, "iii", &mn[0], &mn[1], &mn[2])) return NULL;
    if (!PyArg_ParseTuple(bb_max_t, "iii", &mx[0], &mx[1], &mx[2])) return NULL;
    tvdb_grid_t *g = ((PyVDBGrid *)self)->grid;
    float *out = NULL; int onx, ony, onz; float ovs, oox, ooy, ooz;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_grid_materialize_dense(g, mn, mx, background,
                                        &out, &onx, &ony, &onz,
                                        &ovs, &oox, &ooy, &ooz);
    Py_END_ALLOW_THREADS
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    PyObject *mod = PyState_FindModule(&tinyvdb_module);
    return DenseGrid_from_c(get_state(mod)->DenseGridType, out, onx, ony, onz, ovs, oox, ooy, ooz);
}

static PyObject *VDBGrid_morph_active(PyObject *self, PyObject *args, PyObject *kw,
                                      int (*fn)(const tvdb_grid_t *, int,
                                                int32_t **, float **, size_t *)) {
    int iterations = 1;
    static char *kwlist[] = {"iterations", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "|i", kwlist, &iterations)) return NULL;
    tvdb_grid_t *g = ((PyVDBGrid *)self)->grid;
    int32_t *coords = NULL; float *values = NULL; size_t cnt = 0;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = fn(g, iterations, &coords, &values, &cnt);
    Py_END_ALLOW_THREADS
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    PyObject *cb = PyBytes_FromStringAndSize((const char *)coords, (Py_ssize_t)(cnt * 3 * sizeof(int32_t)));
    PyObject *vb = PyBytes_FromStringAndSize((const char *)values, (Py_ssize_t)(cnt * sizeof(float)));
    free(coords); free(values);
    return Py_BuildValue("{s:N,s:N,s:n}", "coords", cb, "values", vb, "count", (Py_ssize_t)cnt);
}

static PyObject *VDBGrid_dilate_active(PyObject *self, PyObject *args, PyObject *kw) {
    return VDBGrid_morph_active(self, args, kw, tvdb_py_grid_dilate_active);
}
static PyObject *VDBGrid_erode_active(PyObject *self, PyObject *args, PyObject *kw) {
    return VDBGrid_morph_active(self, args, kw, tvdb_py_grid_erode_active);
}
static PyObject *VDBGrid_dilate_topology(PyObject *self, PyObject *args, PyObject *kw) {
    return VDBGrid_morph_active(self, args, kw, tvdb_py_grid_dilate_topology);
}
static PyObject *VDBGrid_erode_topology(PyObject *self, PyObject *args, PyObject *kw) {
    return VDBGrid_morph_active(self, args, kw, tvdb_py_grid_erode_topology);
}

static PyObject *VDBGrid_update_from_sparse(PyObject *self, PyObject *args, PyObject *kw) {
    Py_buffer cb, vb;
    static char *kwlist[] = {"coords", "values", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "y*y*", kwlist, &cb, &vb)) return NULL;
    if (cb.len % (3 * (Py_ssize_t)sizeof(int32_t)) != 0 ||
        vb.len != (cb.len / 3 / (Py_ssize_t)sizeof(int32_t)) * (Py_ssize_t)sizeof(float)) {
        PyBuffer_Release(&cb); PyBuffer_Release(&vb);
        PyErr_SetString(PyExc_ValueError, "coords must be int32 xyz triples; values must be float32 of matching count");
        return NULL;
    }
    size_t count = (size_t)(cb.len / 3 / (Py_ssize_t)sizeof(int32_t));
    tvdb_grid_t *g = ((PyVDBGrid *)self)->grid;
    size_t updated = 0, skipped = 0;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_grid_update_from_sparse(g, (const int32_t *)cb.buf,
                                         (const float *)vb.buf, count,
                                         &updated, &skipped);
    Py_END_ALLOW_THREADS
    PyBuffer_Release(&cb); PyBuffer_Release(&vb);
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    return Py_BuildValue("{s:n,s:n}", "updated", (Py_ssize_t)updated,
                         "skipped", (Py_ssize_t)skipped);
}

static PyObject *VDBGrid_csg(PyObject *self, PyObject *args, PyObject *kw) {
    PyObject *other = NULL;
    int op = 0;
    static char *kwlist[] = {"other", "op", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "Oi", kwlist, &other, &op)) return NULL;
    PyObject *mod = PyState_FindModule(&tinyvdb_module);
    if (!PyObject_TypeCheck(other, (PyTypeObject *)get_state(mod)->VDBGridType)) {
        PyErr_SetString(PyExc_TypeError, "other must be a VDBGrid");
        return NULL;
    }
    tvdb_grid_t *a = ((PyVDBGrid *)self)->grid;
    tvdb_grid_t *b = ((PyVDBGrid *)other)->grid;
    int32_t *coords = NULL; float *values = NULL; size_t cnt = 0;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_grid_csg(a, b, op, &coords, &values, &cnt);
    Py_END_ALLOW_THREADS
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    PyObject *cb = PyBytes_FromStringAndSize((const char *)coords, (Py_ssize_t)(cnt * 3 * sizeof(int32_t)));
    PyObject *vb = PyBytes_FromStringAndSize((const char *)values, (Py_ssize_t)(cnt * sizeof(float)));
    free(coords); free(values);
    return Py_BuildValue("{s:N,s:N,s:n}", "coords", cb, "values", vb, "count", (Py_ssize_t)cnt);
}

static PyObject *VDBGrid_to_sparse(PyObject *self, PyObject *Py_UNUSED(args)) {
    tvdb_grid_t *g = ((PyVDBGrid *)self)->grid;
    int32_t *coords = NULL; float *values = NULL; size_t cnt = 0;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_grid_to_sparse(g, &coords, &values, &cnt);
    Py_END_ALLOW_THREADS
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    PyObject *cb = PyBytes_FromStringAndSize((const char *)coords, (Py_ssize_t)(cnt * 3 * sizeof(int32_t)));
    PyObject *vb = PyBytes_FromStringAndSize((const char *)values, (Py_ssize_t)(cnt * sizeof(float)));
    free(coords); free(values);
    return Py_BuildValue("{s:N,s:N,s:n}", "coords", cb, "values", vb, "count", (Py_ssize_t)cnt);
}

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
    {"active_voxel_count", VDBGrid_active_voxel_count, METH_NOARGS, "Number of active voxels across all leaves"},
    {"active_bbox", VDBGrid_active_bbox, METH_NOARGS, "Voxel-space ((min), (max)) bbox enclosing all active leaves; None if empty"},
    {"float_background", VDBGrid_float_background, METH_NOARGS, "Root-tile background value (float grids only; 0 otherwise)"},
    {"materialize_dense", (PyCFunction)VDBGrid_materialize_dense, METH_VARARGS | METH_KEYWORDS, "Materialize a voxel-space sub-bbox into a DenseGrid"},
    {"dilate_active", (PyCFunction)VDBGrid_dilate_active, METH_VARARGS | METH_KEYWORDS, "Leaf-stamp 6-neighbor min over active voxels; returns {coords, values, count}"},
    {"erode_active", (PyCFunction)VDBGrid_erode_active, METH_VARARGS | METH_KEYWORDS, "Leaf-stamp 6-neighbor max over active voxels; returns {coords, values, count}"},
    {"to_sparse", VDBGrid_to_sparse, METH_NOARGS, "Extract active voxels as {coords (int32 xyz triples bytes), values (float bytes), count}"},
    {"dilate_topology", (PyCFunction)VDBGrid_dilate_topology, METH_VARARGS | METH_KEYWORDS,
     "Topology-growing dilate: extracts active voxels, expands by `iterations` rings (6-connected); returns {coords, values, count}"},
    {"erode_topology", (PyCFunction)VDBGrid_erode_topology, METH_VARARGS | METH_KEYWORDS,
     "Topology-shrinking erode: drops voxels whose 6-neighborhood is not fully active; returns {coords, values, count}"},
    {"update_from_sparse", (PyCFunction)VDBGrid_update_from_sparse, METH_VARARGS | METH_KEYWORDS,
     "Update voxel values in-place from sparse (coords bytes, values bytes); coords outside active leaves are skipped. Returns {updated, skipped}."},
    {"csg", (PyCFunction)VDBGrid_csg, METH_VARARGS | METH_KEYWORDS,
     "Tree-aware sparse CSG with another VDBGrid; op=0 union, 1 intersection, 2 difference; returns {coords, values, count}"},
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

extern int tvdb_py_replace_grid_from_sparse(tvdb_file_t *file, size_t grid_idx,
                                            const int32_t *coords, const float *values, size_t count,
                                            const char *new_name, float background);
extern int tvdb_py_extend_grid_from_sparse(tvdb_file_t *file, size_t grid_idx,
                                           const int32_t *coords, const float *values, size_t count,
                                           const char *new_name, float background);

static PyObject *VDBFile_extend_grid_from_sparse(PyObject *self, PyObject *args, PyObject *kw) {
    PyVDBFile *f = (PyVDBFile *)self; CHECK_OPEN(f);
    Py_ssize_t grid_idx = 0;
    Py_buffer cb, vb;
    const char *new_name = NULL;
    float background = 0.0f;
    static char *kwlist[] = {"grid_idx", "coords", "values", "name", "background", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "ny*y*s|f", kwlist,
                                     &grid_idx, &cb, &vb, &new_name, &background))
        return NULL;
    if (grid_idx < 0 || (size_t)grid_idx >= f->file.num_grids) {
        PyBuffer_Release(&cb); PyBuffer_Release(&vb);
        PyErr_SetString(PyExc_IndexError, "grid_idx out of range");
        return NULL;
    }
    if (cb.len % (3 * (Py_ssize_t)sizeof(int32_t)) != 0) {
        PyBuffer_Release(&cb); PyBuffer_Release(&vb);
        PyErr_SetString(PyExc_ValueError, "coords must be int32 xyz triples");
        return NULL;
    }
    size_t count = (size_t)(cb.len / 3 / (Py_ssize_t)sizeof(int32_t));
    if (vb.len != (Py_ssize_t)(count * sizeof(float))) {
        PyBuffer_Release(&cb); PyBuffer_Release(&vb);
        PyErr_SetString(PyExc_ValueError, "values length must match coord count");
        return NULL;
    }
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_extend_grid_from_sparse(&f->file, (size_t)grid_idx,
                                         (const int32_t *)cb.buf,
                                         (const float *)vb.buf, count,
                                         new_name, background);
    Py_END_ALLOW_THREADS
    PyBuffer_Release(&cb); PyBuffer_Release(&vb);
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    Py_RETURN_NONE;
}

static PyObject *VDBFile_replace_grid_from_sparse(PyObject *self, PyObject *args, PyObject *kw) {
    PyVDBFile *f = (PyVDBFile *)self; CHECK_OPEN(f);
    Py_ssize_t grid_idx = 0;
    Py_buffer cb, vb;
    const char *new_name = NULL;
    float background = 0.0f;
    static char *kwlist[] = {"grid_idx", "coords", "values", "name", "background", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "ny*y*s|f", kwlist,
                                     &grid_idx, &cb, &vb, &new_name, &background))
        return NULL;
    if (grid_idx < 0 || (size_t)grid_idx >= f->file.num_grids) {
        PyBuffer_Release(&cb); PyBuffer_Release(&vb);
        PyErr_SetString(PyExc_IndexError, "grid_idx out of range");
        return NULL;
    }
    if (cb.len % (3 * (Py_ssize_t)sizeof(int32_t)) != 0) {
        PyBuffer_Release(&cb); PyBuffer_Release(&vb);
        PyErr_SetString(PyExc_ValueError, "coords must be int32 xyz triples");
        return NULL;
    }
    size_t count = (size_t)(cb.len / 3 / (Py_ssize_t)sizeof(int32_t));
    if (vb.len != (Py_ssize_t)(count * sizeof(float))) {
        PyBuffer_Release(&cb); PyBuffer_Release(&vb);
        PyErr_SetString(PyExc_ValueError, "values length must match coord count");
        return NULL;
    }
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_replace_grid_from_sparse(&f->file, (size_t)grid_idx,
                                          (const int32_t *)cb.buf,
                                          (const float *)vb.buf, count,
                                          new_name, background);
    Py_END_ALLOW_THREADS
    PyBuffer_Release(&cb); PyBuffer_Release(&vb);
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    Py_RETURN_NONE;
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
    {"replace_grid_from_sparse", (PyCFunction)VDBFile_replace_grid_from_sparse, METH_VARARGS | METH_KEYWORDS,
     "Replace grid at grid_idx with one freshly built from sparse coords/values, using the existing grid as template (descriptor + transform + tree layout). After this, call save() to persist."},
    {"extend_grid_from_sparse", (PyCFunction)VDBFile_extend_grid_from_sparse, METH_VARARGS | METH_KEYWORDS,
     "Topology-extending merge: rebuild grid_idx-th grid as existing ∪ sparse (sparse wins on overlap, new leaves are created where needed). After this, call save() to persist."},
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

static PyObject *mod_write_float_grid(PyObject *module, PyObject *args, PyObject *kw) {
    (void)module;
    const char *path;
    PyObject *values_obj;
    int nx, ny, nz;
    double vsx = 1.0, vsy = 1.0, vsz = 1.0;
    double ox = 0.0, oy = 0.0, oz = 0.0;
    const char *name = "sdf";
    float background = 0.0f;
    unsigned int compression = 0;
    int level = 0;
    static char *kwlist[] = {"path", "values", "nx", "ny", "nz",
                             "voxel_size", "origin", "name", "background",
                             "compression", "level", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "sOiii|(ddd)(ddd)sfIi", kwlist,
                                     &path, &values_obj, &nx, &ny, &nz,
                                     &vsx, &vsy, &vsz, &ox, &oy, &oz,
                                     &name, &background, &compression, &level))
        return NULL;

    Py_ssize_t nfloats;
    float *vals = extract_floats(values_obj, &nfloats);
    if (!vals) return NULL;
    if (nfloats != (Py_ssize_t)nx * ny * nz) {
        free(vals);
        PyErr_SetString(PyExc_ValueError, "values length must equal nx*ny*nz");
        return NULL;
    }

    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_write_float_grid_dense(path, vals, (size_t)nfloats, nx, ny, nz,
                                        vsx, vsy, vsz, ox, oy, oz,
                                        name, background, compression, level);
    Py_END_ALLOW_THREADS
    free(vals);
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    Py_RETURN_NONE;
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

static PyObject *mod_solve_poisson_d(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *rhs_obj; int max_iters = 500; double tolerance = 1e-10;
    static char *kwlist[] = {"rhs", "max_iters", "tolerance", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "O|id", kwlist, &rhs_obj, &max_iters, &tolerance))
        return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(rhs_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)rhs_obj;
    if (!g->data) return raise_vdb_error("DenseGrid has no data");
    float *out = NULL; int iters;
    Py_BEGIN_ALLOW_THREADS
    tvdb_py_solve_poisson_d(g->data, g->nx, g->ny, g->nz, g->voxel_size,
                            g->ox, g->oy, g->oz, max_iters, tolerance, &out, &iters);
    Py_END_ALLOW_THREADS
    PyObject *grid = DenseGrid_from_c(st->DenseGridType, out, g->nx, g->ny, g->nz,
                                      g->voxel_size, g->ox, g->oy, g->oz);
    if (!grid) return NULL;
    return Py_BuildValue("(Oi)", grid, iters);
}

static PyObject *mod_fast_sweeping(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *grid_obj; float frozen_band = 0.0f, tol = 1e-4f;
    int max_iters = 16;
    static char *kwlist[] = {"grid", "frozen_band", "max_iters", "tol", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "O|fif", kwlist, &grid_obj,
                                     &frozen_band, &max_iters, &tol))
        return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    if (!g->data) return raise_vdb_error("DenseGrid has no data");
    float *out = NULL; int iters = 0;
    Py_BEGIN_ALLOW_THREADS
    tvdb_py_fast_sweeping(g->data, g->nx, g->ny, g->nz, g->voxel_size,
                          g->ox, g->oy, g->oz, frozen_band, max_iters, tol,
                          &out, &iters);
    Py_END_ALLOW_THREADS
    if (!out) return raise_vdb_error("fast_sweeping allocation failed");
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
/*  Phase 4-6 dispatchers                                                    */
/* ======================================================================== */

static PyObject *mod_sample_trilinear(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *grid_obj, *pts_obj;
    static char *kwlist[] = {"grid", "points", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "OO", kwlist, &grid_obj, &pts_obj)) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    Py_ssize_t nfloats;
    float *pts = extract_floats(pts_obj, &nfloats);
    if (!pts) return NULL;
    size_t npts = (size_t)(nfloats / 3);
    float *out = NULL;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_sample_trilinear(g->data, g->nx, g->ny, g->nz, g->voxel_size,
                                  g->ox, g->oy, g->oz, pts, npts, &out);
    Py_END_ALLOW_THREADS
    free(pts);
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    PyObject *bytes = PyBytes_FromStringAndSize((const char *)out, (Py_ssize_t)(npts * sizeof(float)));
    free(out);
    return bytes;
}

static PyObject *mod_integrate_tsdf(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *depth_obj, *pose_obj;
    int W, H, nx, ny, nz;
    float fx, fy, cx_, cy_;
    float trunc_distance, dmin, dmax;
    float voxel_size, ox, oy, oz;
    static char *kwlist[] = {"depth", "width", "height", "fx", "fy", "cx", "cy",
                             "pose", "trunc", "depth_min", "depth_max",
                             "nx", "ny", "nz", "voxel_size", "ox", "oy", "oz", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "OiiffffOfffiiiffff", kwlist,
                                     &depth_obj, &W, &H, &fx, &fy, &cx_, &cy_,
                                     &pose_obj, &trunc_distance, &dmin, &dmax,
                                     &nx, &ny, &nz, &voxel_size, &ox, &oy, &oz))
        return NULL;
    Py_ssize_t nf;
    float *depth = extract_floats(depth_obj, &nf);
    if (!depth) return NULL;
    Py_ssize_t np;
    float *pose = extract_floats(pose_obj, &np);
    if (!pose || np < 12) { free(depth); free(pose);
        PyErr_SetString(PyExc_ValueError, "pose must contain 12 floats"); return NULL; }
    float *out_tsdf = NULL, *out_w = NULL;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_integrate_tsdf(depth, W, H, fx, fy, cx_, cy_, pose,
                                trunc_distance, dmin, dmax,
                                nx, ny, nz, voxel_size, ox, oy, oz,
                                &out_tsdf, &out_w);
    Py_END_ALLOW_THREADS
    free(depth); free(pose);
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    PyObject *gtsdf = DenseGrid_from_c(get_state(module)->DenseGridType,
                                       out_tsdf, nx, ny, nz, voxel_size, ox, oy, oz);
    PyObject *gw    = DenseGrid_from_c(get_state(module)->DenseGridType,
                                       out_w,    nx, ny, nz, voxel_size, ox, oy, oz);
    return Py_BuildValue("(OO)", gtsdf, gw);
}

static PyObject *mod_resize_op(PyObject *module, PyObject *args, PyObject *kw,
                               int (*fn)(const float *, int, int, int, float, float, float, float,
                                         int, float **, int *, int *, int *,
                                         float *, float *, float *, float *)) {
    PyObject *grid_obj; int factor;
    static char *kwlist[] = {"grid", "factor", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "Oi", kwlist, &grid_obj, &factor)) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    float *out = NULL;
    int onx, ony, onz; float ovs, oox, ooy, ooz;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = fn(g->data, g->nx, g->ny, g->nz, g->voxel_size, g->ox, g->oy, g->oz,
            factor, &out, &onx, &ony, &onz, &ovs, &oox, &ooy, &ooz);
    Py_END_ALLOW_THREADS
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    return DenseGrid_from_c(st->DenseGridType, out, onx, ony, onz, ovs, oox, ooy, ooz);
}

static PyObject *mod_coarsen_grid(PyObject *module, PyObject *args, PyObject *kw) {
    return mod_resize_op(module, args, kw, tvdb_py_coarsen_grid);
}
static PyObject *mod_refine_grid(PyObject *module, PyObject *args, PyObject *kw) {
    return mod_resize_op(module, args, kw, tvdb_py_refine_grid);
}

static PyObject *mod_pool_op(PyObject *module, PyObject *args, PyObject *kw,
                             int (*fn)(const float *, int, int, int, float, float, float, float,
                                       int, int, int, float **, int *, int *, int *,
                                       float *, float *, float *, float *)) {
    PyObject *grid_obj; int kx, ky, kz;
    static char *kwlist[] = {"grid", "kx", "ky", "kz", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "Oiii", kwlist, &grid_obj, &kx, &ky, &kz)) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    float *out = NULL;
    int onx, ony, onz; float ovs, oox, ooy, ooz;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = fn(g->data, g->nx, g->ny, g->nz, g->voxel_size, g->ox, g->oy, g->oz,
            kx, ky, kz, &out, &onx, &ony, &onz, &ovs, &oox, &ooy, &ooz);
    Py_END_ALLOW_THREADS
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    return DenseGrid_from_c(st->DenseGridType, out, onx, ony, onz, ovs, oox, ooy, ooz);
}

static PyObject *mod_max_pool(PyObject *module, PyObject *args, PyObject *kw) {
    return mod_pool_op(module, args, kw, tvdb_py_max_pool);
}
static PyObject *mod_avg_pool(PyObject *module, PyObject *args, PyObject *kw) {
    return mod_pool_op(module, args, kw, tvdb_py_avg_pool);
}

/* ---- splat / ray / clip / prune / merge ---- */

static PyObject *mod_splat_trilinear(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *grid_obj, *pts_obj, *vals_obj;
    int with_weights = 0;
    static char *kwlist[] = {"grid", "points", "values", "weights", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "OOO|p", kwlist,
                                     &grid_obj, &pts_obj, &vals_obj, &with_weights)) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    Py_ssize_t pn, vn;
    float *pts  = extract_floats(pts_obj,  &pn);
    float *vals = extract_floats(vals_obj, &vn);
    if (!pts || !vals) { free(pts); free(vals); return NULL; }
    size_t n = (size_t)(pn / 3);
    float *weights = NULL;
    if (with_weights) {
        weights = (float *)calloc((size_t)g->nx * g->ny * g->nz, sizeof(float));
        if (!weights) { free(pts); free(vals); return PyErr_NoMemory(); }
    }
    Py_BEGIN_ALLOW_THREADS
    tvdb_py_splat_trilinear(g->data, g->nx, g->ny, g->nz, g->voxel_size,
                            g->ox, g->oy, g->oz, pts, vals, n, weights);
    Py_END_ALLOW_THREADS
    free(pts); free(vals);
    if (!with_weights) { Py_RETURN_NONE; }
    PyObject *wgrid = DenseGrid_from_c(st->DenseGridType, weights,
                                       g->nx, g->ny, g->nz,
                                       g->voxel_size, g->ox, g->oy, g->oz);
    return wgrid;
}

static PyObject *mod_voxels_along_ray(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *grid_obj, *origin_t, *dir_t;
    float tmin = 0.0f, tmax = 1e6f;
    static char *kwlist[] = {"grid", "origin", "direction", "tmin", "tmax", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "OOO|ff", kwlist,
                                     &grid_obj, &origin_t, &dir_t, &tmin, &tmax)) return NULL;
    float rx, ry, rz, dx, dy, dz;
    if (!PyArg_ParseTuple(origin_t, "fff", &rx, &ry, &rz)) return NULL;
    if (!PyArg_ParseTuple(dir_t, "fff", &dx, &dy, &dz)) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    int *out = NULL; size_t cnt;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_voxels_along_ray(g->data, g->nx, g->ny, g->nz, g->voxel_size,
                                  g->ox, g->oy, g->oz,
                                  rx, ry, rz, dx, dy, dz, tmin, tmax,
                                  &out, &cnt);
    Py_END_ALLOW_THREADS
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    PyObject *bytes = PyBytes_FromStringAndSize((const char *)out, (Py_ssize_t)(cnt * 3 * sizeof(int)));
    free(out);
    return Py_BuildValue("(Nn)", bytes, (Py_ssize_t)cnt);
}

static PyObject *mod_uniform_ray_samples(PyObject *module, PyObject *args, PyObject *kw) {
    (void)module;
    PyObject *origin_t, *dir_t;
    int n;
    float tmin = 0.0f, tmax = 1.0f;
    static char *kwlist[] = {"origin", "direction", "n", "tmin", "tmax", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "OOi|ff", kwlist,
                                     &origin_t, &dir_t, &n, &tmin, &tmax)) return NULL;
    float rx, ry, rz, dx, dy, dz;
    if (!PyArg_ParseTuple(origin_t, "fff", &rx, &ry, &rz)) return NULL;
    if (!PyArg_ParseTuple(dir_t, "fff", &dx, &dy, &dz)) return NULL;
    if (n <= 0) { PyErr_SetString(PyExc_ValueError, "n must be > 0"); return NULL; }
    float *pts = NULL, *ts = NULL;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_uniform_ray_samples(rx, ry, rz, dx, dy, dz, tmin, tmax,
                                     (size_t)n, &pts, &ts);
    Py_END_ALLOW_THREADS
    if (rc != 0) return raise_vdb_error("uniform_ray_samples: alloc failed");
    PyObject *p_bytes = PyBytes_FromStringAndSize((const char *)pts, (Py_ssize_t)((size_t)n * 3 * sizeof(float)));
    PyObject *t_bytes = PyBytes_FromStringAndSize((const char *)ts,  (Py_ssize_t)((size_t)n * sizeof(float)));
    free(pts); free(ts);
    return Py_BuildValue("(NN)", p_bytes, t_bytes);
}

static PyObject *mod_segments_along_ray(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *grid_obj, *origin_t, *dir_t;
    float tmin = 0.0f, tmax = 1e6f, isovalue = 0.0f;
    int step_count = 256, cap = 16;
    static char *kwlist[] = {"grid", "origin", "direction", "isovalue",
                             "tmin", "tmax", "steps", "cap", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "OOO|fffii", kwlist,
                                     &grid_obj, &origin_t, &dir_t, &isovalue,
                                     &tmin, &tmax, &step_count, &cap)) return NULL;
    float rx, ry, rz, dx, dy, dz;
    if (!PyArg_ParseTuple(origin_t, "fff", &rx, &ry, &rz)) return NULL;
    if (!PyArg_ParseTuple(dir_t, "fff", &dx, &dy, &dz)) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    float *pairs = NULL; size_t cnt;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_segments_along_ray(g->data, g->nx, g->ny, g->nz, g->voxel_size,
                                    g->ox, g->oy, g->oz,
                                    rx, ry, rz, dx, dy, dz,
                                    tmin, tmax, isovalue,
                                    (size_t)step_count, (size_t)cap,
                                    &pairs, &cnt);
    Py_END_ALLOW_THREADS
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    if (cnt > (size_t)cap) cnt = (size_t)cap;
    PyObject *bytes = PyBytes_FromStringAndSize((const char *)pairs, (Py_ssize_t)(cnt * 2 * sizeof(float)));
    free(pairs);
    return Py_BuildValue("(Nn)", bytes, (Py_ssize_t)cnt);
}

static PyObject *mod_clip_grid(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *grid_obj, *bb_min_t, *bb_max_t;
    static char *kwlist[] = {"grid", "bbox_min", "bbox_max", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "OOO", kwlist,
                                     &grid_obj, &bb_min_t, &bb_max_t)) return NULL;
    float bb_min[3], bb_max[3];
    if (!PyArg_ParseTuple(bb_min_t, "fff", &bb_min[0], &bb_min[1], &bb_min[2])) return NULL;
    if (!PyArg_ParseTuple(bb_max_t, "fff", &bb_max[0], &bb_max[1], &bb_max[2])) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    float *out = NULL;
    int onx, ony, onz; float ovs, oox, ooy, ooz;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_clip_grid(g->data, g->nx, g->ny, g->nz, g->voxel_size,
                           g->ox, g->oy, g->oz, bb_min, bb_max,
                           &out, &onx, &ony, &onz, &ovs, &oox, &ooy, &ooz);
    Py_END_ALLOW_THREADS
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    return DenseGrid_from_c(st->DenseGridType, out, onx, ony, onz, ovs, oox, ooy, ooz);
}

static PyObject *mod_prune_grid(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *grid_obj;
    float background = 0.0f, tolerance = 1e-6f;
    static char *kwlist[] = {"grid", "background", "tolerance", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "O|ff", kwlist,
                                     &grid_obj, &background, &tolerance)) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(grid_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected a DenseGrid"); return NULL;
    }
    PyDenseGrid *g = (PyDenseGrid *)grid_obj;
    Py_BEGIN_ALLOW_THREADS
    tvdb_py_prune_grid(g->data, g->nx, g->ny, g->nz, g->voxel_size,
                       g->ox, g->oy, g->oz, background, tolerance);
    Py_END_ALLOW_THREADS
    Py_RETURN_NONE;
}

static PyObject *mod_integrate_tsdf_into(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *tsdf_obj, *wgt_obj, *depth_obj, *pose_obj;
    int W, H;
    float fx, fy, cx_, cy_, trunc_distance, dmin, dmax;
    static char *kwlist[] = {"tsdf", "weights", "depth", "width", "height",
                             "fx", "fy", "cx", "cy", "pose",
                             "trunc", "depth_min", "depth_max", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "OOOiiffffOfff", kwlist,
                                     &tsdf_obj, &wgt_obj, &depth_obj, &W, &H,
                                     &fx, &fy, &cx_, &cy_, &pose_obj,
                                     &trunc_distance, &dmin, &dmax))
        return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(tsdf_obj, st->DenseGridType) ||
        !PyObject_IsInstance(wgt_obj,  st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "tsdf and weights must be DenseGrid");
        return NULL;
    }
    PyDenseGrid *T = (PyDenseGrid *)tsdf_obj;
    PyDenseGrid *Wg = (PyDenseGrid *)wgt_obj;
    if (T->nx != Wg->nx || T->ny != Wg->ny || T->nz != Wg->nz) {
        PyErr_SetString(PyExc_ValueError, "tsdf and weights shape mismatch");
        return NULL;
    }
    Py_ssize_t nfd, np;
    float *depth = extract_floats(depth_obj, &nfd);
    if (!depth) return NULL;
    float *pose = extract_floats(pose_obj, &np);
    if (!pose || np < 12) { free(depth); free(pose);
        PyErr_SetString(PyExc_ValueError, "pose must contain 12 floats"); return NULL; }
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_integrate_tsdf_into(T->data, Wg->data,
                                     T->nx, T->ny, T->nz, T->voxel_size,
                                     T->ox, T->oy, T->oz,
                                     depth, W, H, fx, fy, cx_, cy_,
                                     pose, trunc_distance, dmin, dmax);
    Py_END_ALLOW_THREADS
    free(depth); free(pose);
    if (rc != 0) return raise_vdb_error("integrate_tsdf_into failed");
    Py_RETURN_NONE;
}

static PyObject *mod_integrate_tsdf_with_color_into(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *tsdf_obj, *wgt_obj, *col_obj, *depth_obj, *rgb_obj, *pose_obj;
    int W, H;
    float fx, fy, cx_, cy_, trunc_distance, dmin, dmax;
    static char *kwlist[] = {"tsdf", "weights", "color", "depth", "rgb",
                             "width", "height",
                             "fx", "fy", "cx", "cy", "pose",
                             "trunc", "depth_min", "depth_max", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "OOOOOiiffffOfff", kwlist,
                                     &tsdf_obj, &wgt_obj, &col_obj,
                                     &depth_obj, &rgb_obj, &W, &H,
                                     &fx, &fy, &cx_, &cy_, &pose_obj,
                                     &trunc_distance, &dmin, &dmax))
        return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(tsdf_obj, st->DenseGridType) ||
        !PyObject_IsInstance(wgt_obj,  st->DenseGridType) ||
        !PyObject_IsInstance(col_obj,  st->DenseVecGridType)) {
        PyErr_SetString(PyExc_TypeError,
                        "tsdf, weights must be DenseGrid; color must be DenseVecGrid");
        return NULL;
    }
    PyDenseGrid *T  = (PyDenseGrid *)tsdf_obj;
    PyDenseGrid *Wg = (PyDenseGrid *)wgt_obj;
    PyDenseVecGrid *C = (PyDenseVecGrid *)col_obj;
    if (T->nx != Wg->nx || T->ny != Wg->ny || T->nz != Wg->nz ||
        T->nx != C->nx  || T->ny != C->ny  || T->nz != C->nz) {
        PyErr_SetString(PyExc_ValueError, "tsdf/weights/color shape mismatch");
        return NULL;
    }
    Py_ssize_t nfd, np;
    float *depth = extract_floats(depth_obj, &nfd);
    if (!depth) return NULL;
    float *pose = extract_floats(pose_obj, &np);
    if (!pose || np < 12) { free(depth); free(pose);
        PyErr_SetString(PyExc_ValueError, "pose must contain 12 floats"); return NULL; }
    Py_buffer rgb_buf;
    if (PyObject_GetBuffer(rgb_obj, &rgb_buf, PyBUF_C_CONTIGUOUS) < 0) {
        free(depth); free(pose); return NULL;
    }
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_integrate_tsdf_with_color_into(
            T->data, Wg->data, C->data,
            T->nx, T->ny, T->nz, T->voxel_size, T->ox, T->oy, T->oz,
            depth, W, H, fx, fy, cx_, cy_, pose,
            trunc_distance, dmin, dmax,
            (const uint8_t *)rgb_buf.buf);
    Py_END_ALLOW_THREADS
    PyBuffer_Release(&rgb_buf);
    free(depth); free(pose);
    if (rc != 0) return raise_vdb_error("integrate_tsdf_with_color_into failed");
    Py_RETURN_NONE;
}

static PyObject *mod_merge_grids(PyObject *module, PyObject *args, PyObject *kw) {
    PyObject *a_obj, *b_obj;
    float background = 0.0f;
    static char *kwlist[] = {"a", "b", "background", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "OO|f", kwlist,
                                     &a_obj, &b_obj, &background)) return NULL;
    module_state *st = get_state(module);
    if (!PyObject_IsInstance(a_obj, st->DenseGridType) ||
        !PyObject_IsInstance(b_obj, st->DenseGridType)) {
        PyErr_SetString(PyExc_TypeError, "Expected two DenseGrids"); return NULL;
    }
    PyDenseGrid *A = (PyDenseGrid *)a_obj;
    PyDenseGrid *B = (PyDenseGrid *)b_obj;
    float *out = NULL;
    int onx, ony, onz; float ovs, oox, ooy, ooz;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_merge_grids(A->data, A->nx, A->ny, A->nz, A->voxel_size,
                             A->ox, A->oy, A->oz,
                             B->data, B->nx, B->ny, B->nz, B->voxel_size,
                             B->ox, B->oy, B->oz, background,
                             &out, &onx, &ony, &onz, &ovs, &oox, &ooy, &ooz);
    Py_END_ALLOW_THREADS
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    return DenseGrid_from_c(st->DenseGridType, out, onx, ony, onz, ovs, oox, ooy, ooz);
}

extern int tvdb_py_sparse_conv3d(const int32_t *in_coords, const float *in_values, size_t in_count,
                                 float voxel_size, float ox, float oy, float oz,
                                 const float *kernel, int kx, int ky, int kz, float pad_value,
                                 int32_t **out_coords, float **out_values, size_t *out_count);
extern int tvdb_py_sparse_conv3d_mc(const int32_t *in_coords, const float *in_values_mc, size_t in_count,
                                    int c_in, float voxel_size, float ox, float oy, float oz,
                                    const float *kernel, int kx, int ky, int kz, int c_out,
                                    float pad_value,
                                    int32_t **out_coords, float **out_values_mc, size_t *out_count);

static PyObject *mod_sparse_conv3d_mc(PyObject *module, PyObject *args, PyObject *kw) {
    Py_buffer cb, vb, kb;
    int c_in = 1, c_out = 1, kx, ky, kz;
    float voxel_size = 1.0f, ox = 0, oy = 0, oz = 0, pad_value = 0.0f;
    static char *kwlist[] = {"coords", "values", "kernel",
                             "kx", "ky", "kz", "c_in", "c_out",
                             "voxel_size", "ox", "oy", "oz", "pad_value", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "y*y*y*iiiii|fffff", kwlist,
                                     &cb, &vb, &kb, &kx, &ky, &kz, &c_in, &c_out,
                                     &voxel_size, &ox, &oy, &oz, &pad_value))
        return NULL;
    if (cb.len % (3 * (Py_ssize_t)sizeof(int32_t)) != 0) {
        PyBuffer_Release(&cb); PyBuffer_Release(&vb); PyBuffer_Release(&kb);
        PyErr_SetString(PyExc_ValueError, "coords must be int32 xyz triples");
        return NULL;
    }
    size_t in_count = (size_t)(cb.len / 3 / (Py_ssize_t)sizeof(int32_t));
    if (vb.len != (Py_ssize_t)((size_t)in_count * (size_t)c_in * sizeof(float))) {
        PyBuffer_Release(&cb); PyBuffer_Release(&vb); PyBuffer_Release(&kb);
        PyErr_SetString(PyExc_ValueError, "values length must equal in_count * c_in floats");
        return NULL;
    }
    Py_ssize_t want_kb = (Py_ssize_t)((size_t)kx * ky * kz * c_out * c_in * sizeof(float));
    if (kb.len != want_kb) {
        PyBuffer_Release(&cb); PyBuffer_Release(&vb); PyBuffer_Release(&kb);
        PyErr_SetString(PyExc_ValueError, "kernel length must equal kx*ky*kz*c_out*c_in floats");
        return NULL;
    }
    int32_t *out_coords = NULL; float *out_values_mc = NULL; size_t out_count = 0;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_sparse_conv3d_mc((const int32_t *)cb.buf, (const float *)vb.buf, in_count,
                                  c_in, voxel_size, ox, oy, oz,
                                  (const float *)kb.buf, kx, ky, kz, c_out, pad_value,
                                  &out_coords, &out_values_mc, &out_count);
    Py_END_ALLOW_THREADS
    PyBuffer_Release(&cb); PyBuffer_Release(&vb); PyBuffer_Release(&kb);
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    PyObject *cb_out = PyBytes_FromStringAndSize((const char *)out_coords,
                                                 (Py_ssize_t)(out_count * 3 * sizeof(int32_t)));
    PyObject *vb_out = PyBytes_FromStringAndSize((const char *)out_values_mc,
                                                 (Py_ssize_t)(out_count * (size_t)c_out * sizeof(float)));
    free(out_coords); free(out_values_mc);
    return Py_BuildValue("{s:N,s:N,s:n,s:i}", "coords", cb_out, "values", vb_out,
                         "count", (Py_ssize_t)out_count, "c_out", c_out);
}

static PyObject *mod_sparse_conv3d(PyObject *module, PyObject *args, PyObject *kw) {
    Py_buffer cb, vb, kb;
    int kx, ky, kz;
    float voxel_size = 1.0f, ox = 0, oy = 0, oz = 0;
    float pad_value = 0.0f;
    static char *kwlist[] = {"coords", "values", "kernel",
                             "kx", "ky", "kz",
                             "voxel_size", "ox", "oy", "oz", "pad_value", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "y*y*y*iii|fffff", kwlist,
                                     &cb, &vb, &kb, &kx, &ky, &kz,
                                     &voxel_size, &ox, &oy, &oz, &pad_value))
        return NULL;
    if (cb.len % (3 * (Py_ssize_t)sizeof(int32_t)) != 0) {
        PyBuffer_Release(&cb); PyBuffer_Release(&vb); PyBuffer_Release(&kb);
        PyErr_SetString(PyExc_ValueError, "coords must be int32 xyz triples");
        return NULL;
    }
    size_t in_count = (size_t)(cb.len / 3 / (Py_ssize_t)sizeof(int32_t));
    if (vb.len != (Py_ssize_t)(in_count * sizeof(float))) {
        PyBuffer_Release(&cb); PyBuffer_Release(&vb); PyBuffer_Release(&kb);
        PyErr_SetString(PyExc_ValueError, "values length must match coord count");
        return NULL;
    }
    if (kb.len != (Py_ssize_t)((size_t)kx * ky * kz * sizeof(float))) {
        PyBuffer_Release(&cb); PyBuffer_Release(&vb); PyBuffer_Release(&kb);
        PyErr_SetString(PyExc_ValueError, "kernel length must equal kx*ky*kz floats");
        return NULL;
    }
    int32_t *out_coords = NULL; float *out_values = NULL; size_t out_count = 0;
    int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_sparse_conv3d((const int32_t *)cb.buf, (const float *)vb.buf, in_count,
                               voxel_size, ox, oy, oz,
                               (const float *)kb.buf, kx, ky, kz, pad_value,
                               &out_coords, &out_values, &out_count);
    Py_END_ALLOW_THREADS
    PyBuffer_Release(&cb); PyBuffer_Release(&vb); PyBuffer_Release(&kb);
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    PyObject *cb_out = PyBytes_FromStringAndSize((const char *)out_coords,
                                                 (Py_ssize_t)(out_count * 3 * sizeof(int32_t)));
    PyObject *vb_out = PyBytes_FromStringAndSize((const char *)out_values,
                                                 (Py_ssize_t)(out_count * sizeof(float)));
    free(out_coords); free(out_values);
    return Py_BuildValue("{s:N,s:N,s:n}", "coords", cb_out, "values", vb_out,
                         "count", (Py_ssize_t)out_count);
}

extern int tvdb_py_sparse_conv3d_vjp_values(const int32_t *, size_t, const float *,
                                            const float *, int, int, int, float **);
extern int tvdb_py_sparse_conv3d_vjp_kernel(const int32_t *, const float *, size_t,
                                            const float *, int, int, int, float **);

static PyObject *mod_sparse_conv3d_vjp_values(PyObject *module, PyObject *args, PyObject *kw) {
    (void)module;
    Py_buffer cb, gb, kb;
    int kx, ky, kz;
    static char *kwlist[] = {"coords", "grad_out_values", "kernel", "kx", "ky", "kz", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "y*y*y*iii", kwlist,
                                     &cb, &gb, &kb, &kx, &ky, &kz))
        return NULL;
    if (cb.len % (3 * (Py_ssize_t)sizeof(int32_t)) != 0) {
        PyBuffer_Release(&cb); PyBuffer_Release(&gb); PyBuffer_Release(&kb);
        PyErr_SetString(PyExc_ValueError, "coords must be int32 xyz triples"); return NULL;
    }
    size_t in_count = (size_t)(cb.len / 3 / (Py_ssize_t)sizeof(int32_t));
    if (gb.len != (Py_ssize_t)(in_count * sizeof(float))) {
        PyBuffer_Release(&cb); PyBuffer_Release(&gb); PyBuffer_Release(&kb);
        PyErr_SetString(PyExc_ValueError, "grad_out_values length must match coord count"); return NULL;
    }
    if (kb.len != (Py_ssize_t)((size_t)kx * ky * kz * sizeof(float))) {
        PyBuffer_Release(&cb); PyBuffer_Release(&gb); PyBuffer_Release(&kb);
        PyErr_SetString(PyExc_ValueError, "kernel length must equal kx*ky*kz floats"); return NULL;
    }
    float *grad_in = NULL; int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_sparse_conv3d_vjp_values((const int32_t *)cb.buf, in_count,
                                          (const float *)gb.buf,
                                          (const float *)kb.buf, kx, ky, kz, &grad_in);
    Py_END_ALLOW_THREADS
    PyBuffer_Release(&cb); PyBuffer_Release(&gb); PyBuffer_Release(&kb);
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    PyObject *out = PyBytes_FromStringAndSize((const char *)grad_in,
                                              (Py_ssize_t)(in_count * sizeof(float)));
    free(grad_in);
    return out;
}

static PyObject *mod_sparse_conv3d_vjp_kernel(PyObject *module, PyObject *args, PyObject *kw) {
    (void)module;
    Py_buffer cb, vb, gb;
    int kx, ky, kz;
    static char *kwlist[] = {"coords", "in_values", "grad_out_values", "kx", "ky", "kz", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kw, "y*y*y*iii", kwlist,
                                     &cb, &vb, &gb, &kx, &ky, &kz))
        return NULL;
    if (cb.len % (3 * (Py_ssize_t)sizeof(int32_t)) != 0) {
        PyBuffer_Release(&cb); PyBuffer_Release(&vb); PyBuffer_Release(&gb);
        PyErr_SetString(PyExc_ValueError, "coords must be int32 xyz triples"); return NULL;
    }
    size_t in_count = (size_t)(cb.len / 3 / (Py_ssize_t)sizeof(int32_t));
    if (vb.len != (Py_ssize_t)(in_count * sizeof(float))) {
        PyBuffer_Release(&cb); PyBuffer_Release(&vb); PyBuffer_Release(&gb);
        PyErr_SetString(PyExc_ValueError, "in_values length must match coord count"); return NULL;
    }
    if (gb.len != (Py_ssize_t)(in_count * sizeof(float))) {
        PyBuffer_Release(&cb); PyBuffer_Release(&vb); PyBuffer_Release(&gb);
        PyErr_SetString(PyExc_ValueError, "grad_out_values length must match coord count"); return NULL;
    }
    float *grad_kern = NULL; int rc;
    Py_BEGIN_ALLOW_THREADS
    rc = tvdb_py_sparse_conv3d_vjp_kernel((const int32_t *)cb.buf,
                                          (const float *)vb.buf, in_count,
                                          (const float *)gb.buf, kx, ky, kz, &grad_kern);
    Py_END_ALLOW_THREADS
    PyBuffer_Release(&cb); PyBuffer_Release(&vb); PyBuffer_Release(&gb);
    if (rc != 0) return raise_vdb_error(tvdb_py_last_error());
    size_t klen = (size_t)kx * ky * kz;
    PyObject *out = PyBytes_FromStringAndSize((const char *)grad_kern,
                                              (Py_ssize_t)(klen * sizeof(float)));
    free(grad_kern);
    return out;
}

/* ======================================================================== */
/*  Module definition                                                       */
/* ======================================================================== */

static PyMethodDef module_methods[] = {
    {"open", mod_open, METH_VARARGS, "Open a VDB file by path"},
    {"from_bytes", mod_from_bytes, METH_VARARGS, "Open VDB from bytes"},
    {"mesh_to_sdf", (PyCFunction)mod_mesh_to_sdf, METH_VARARGS | METH_KEYWORDS, "Mesh to SDF"},
    {"write_float_grid", (PyCFunction)mod_write_float_grid, METH_VARARGS | METH_KEYWORDS,
     "Write a dense float grid (e.g. SDF) to a .vdb file. "
     "write_float_grid(path, values, nx, ny, nz, voxel_size=(sx,sy,sz), origin=(ox,oy,oz), "
     "name='sdf', background=0.0, compression=0, level=0); values is an nx*ny*nz float32 buffer "
     "in C order, world = voxel_size*index + origin."},
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
    {"solve_poisson", (PyCFunction)mod_solve_poisson, METH_VARARGS | METH_KEYWORDS, "Poisson solver (fp32 internals)"},
    {"solve_poisson_d", (PyCFunction)mod_solve_poisson_d, METH_VARARGS | METH_KEYWORDS,
     "Poisson solver with fp64 internals (tighter convergence; input/output remain fp32)"},
    {"fast_sweeping", (PyCFunction)mod_fast_sweeping, METH_VARARGS | METH_KEYWORDS,
     "Fast Sweeping Eikonal redistance for SDF dense grids (returns (grid, iters))"},
    {"ray_cast_sdf", (PyCFunction)mod_ray_cast_sdf, METH_VARARGS | METH_KEYWORDS, "Ray cast SDF"},
    {"particles_to_sdf", (PyCFunction)mod_particles_to_sdf, METH_VARARGS | METH_KEYWORDS, "Particles to SDF"},
    {"volume_to_spheres", (PyCFunction)mod_volume_to_spheres, METH_VARARGS | METH_KEYWORDS, "Volume to spheres"},
    {"fracture", mod_fracture, METH_VARARGS, "Fracture"},
    {"sample_trilinear", (PyCFunction)mod_sample_trilinear, METH_VARARGS | METH_KEYWORDS, "Trilinear sampling at world points; returns bytes of float32 values"},
    {"integrate_tsdf", (PyCFunction)mod_integrate_tsdf, METH_VARARGS | METH_KEYWORDS, "TSDF fusion from a depth frame; returns (tsdf, weights)"},
    {"coarsen_grid", (PyCFunction)mod_coarsen_grid, METH_VARARGS | METH_KEYWORDS, "Coarsen by integer factor (block average)"},
    {"refine_grid", (PyCFunction)mod_refine_grid, METH_VARARGS | METH_KEYWORDS, "Refine by integer factor (trilinear upsample)"},
    {"max_pool", (PyCFunction)mod_max_pool, METH_VARARGS | METH_KEYWORDS, "Max pool over kxxky*kz blocks"},
    {"avg_pool", (PyCFunction)mod_avg_pool, METH_VARARGS | METH_KEYWORDS, "Average pool over kxxky*kz blocks"},
    {"splat_trilinear", (PyCFunction)mod_splat_trilinear, METH_VARARGS | METH_KEYWORDS, "Trilinear splat of point values into a DenseGrid"},
    {"voxels_along_ray", (PyCFunction)mod_voxels_along_ray, METH_VARARGS | METH_KEYWORDS, "Enumerate voxels traversed by a ray; returns (bytes, count) of int32 xyz triples"},
    {"uniform_ray_samples", (PyCFunction)mod_uniform_ray_samples, METH_VARARGS | METH_KEYWORDS, "Generate uniformly-spaced ray samples; returns (point_bytes, t_bytes)"},
    {"segments_along_ray", (PyCFunction)mod_segments_along_ray, METH_VARARGS | METH_KEYWORDS, "Find isosurface entry/exit pairs along a ray; returns (bytes, count) of (t_in, t_out) float32 pairs"},
    {"clip_grid", (PyCFunction)mod_clip_grid, METH_VARARGS | METH_KEYWORDS, "Clip a DenseGrid to a world-space bbox"},
    {"prune_grid", (PyCFunction)mod_prune_grid, METH_VARARGS | METH_KEYWORDS, "Snap voxels near background to background"},
    {"merge_grids", (PyCFunction)mod_merge_grids, METH_VARARGS | METH_KEYWORDS, "Merge two DenseGrids (SDF union)"},
    {"integrate_tsdf_into", (PyCFunction)mod_integrate_tsdf_into, METH_VARARGS | METH_KEYWORDS, "Update existing (tsdf, weights) DenseGrids in place from a depth frame; supports multi-frame fusion"},
    {"integrate_tsdf_with_color_into", (PyCFunction)mod_integrate_tsdf_with_color_into, METH_VARARGS | METH_KEYWORDS, "Update (tsdf, weights, color) buffers in place from a (depth, rgb) frame pair"},
    {"sparse_conv3d", (PyCFunction)mod_sparse_conv3d, METH_VARARGS | METH_KEYWORDS,
     "3D convolution on a sparse grid (same-topology). coords/values/kernel are bytes; kernel is kx*ky*kz float32. Returns {coords, values, count}."},
    {"sparse_conv3d_mc", (PyCFunction)mod_sparse_conv3d_mc, METH_VARARGS | METH_KEYWORDS,
     "Multi-channel 3D convolution on a sparse grid. values laid out (count*c_in) channel-fastest; kernel laid out (kx*ky*kz*c_out*c_in) channel-fastest. Returns {coords, values, count, c_out}."},
    {"sparse_conv3d_vjp_values", (PyCFunction)mod_sparse_conv3d_vjp_values, METH_VARARGS | METH_KEYWORDS,
     "VJP of sparse_conv3d w.r.t. input values. Returns grad_in (bytes, length count*4)."},
    {"sparse_conv3d_vjp_kernel", (PyCFunction)mod_sparse_conv3d_vjp_kernel, METH_VARARGS | METH_KEYWORDS,
     "VJP of sparse_conv3d w.r.t. kernel. Returns grad_kernel (bytes, length kx*ky*kz*4)."},
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
