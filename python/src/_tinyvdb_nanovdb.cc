/*
 * _tinyvdb_nanovdb.c — Python C extension for tinyvdb NanoVDB support.
 *
 * Uses Py_LIMITED_API targeting Python 3.11+.
 */

#ifndef Py_LIMITED_API
#define Py_LIMITED_API 0x030B0000
#endif
#include <Python.h>

#include "tinyvdb_nanovdb.h"

#include <string.h>
#include <stdlib.h>
#include <cstdio>

/* ======================================================================== */
/*  Module globals                                                           */
/* ======================================================================== */

static struct PyModuleDef tvdb_nanovdb_module = {
    PyModuleDef_HEAD_INIT,
    .m_name = "_tinyvdb_nanovdb",
    .m_doc = "NanoVDB support for tinyvdb",
    .m_size = -1,
};

/* ======================================================================== */
/*  NanoVDBFile type                                                         */
/* ======================================================================== */

typedef struct {
    PyObject_HEAD
    tvdb_nanovdb_file_t file;
    int closed;
} NanoVDBFile;

static void NanoVDBFile_dealloc(void *self) {
    NanoVDBFile *nvdb = (NanoVDBFile *)self;
    if (!nvdb->closed && nvdb->file.num_grids > 0) {
        tvdb_nanovdb_file_close(&nvdb->file);
    }
    PyObject_Del(self);
}

static PyObject *NanoVDBFile_open(PyTypeObject *type, PyObject *args, PyObject *kwds) {
    static const char *kwlist[] = {"path", NULL};
    const char *path;

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "s", (char **)kwlist, &path))
        return NULL;

    NanoVDBFile *self = (NanoVDBFile *)PyObject_Malloc(sizeof(NanoVDBFile));
    if (!self) return NULL;
    PyObject_Init((PyObject *)self, (PyTypeObject *)type);

    memset(&self->file, 0, sizeof(self->file));
    self->closed = 0;

    tvdb_error_t err;
    memset(&err, 0, sizeof(err));

    tvdb_status_t st = tvdb_nanovdb_file_open(&self->file, path, NULL, &err);
    if (st != TVDB_OK) {
        PyErr_SetString(PyExc_IOError, err.message);
        PyObject_Del(self);
        return NULL;
    }

    return (PyObject *)self;
}

static PyObject *NanoVDBFile_close(NanoVDBFile *self, PyObject *Py_UNUSED(ignored)) {
    if (!self->closed) {
        tvdb_nanovdb_file_close(&self->file);
        self->closed = 1;
    }
    Py_RETURN_NONE;
}

static PyObject *NanoVDBFile_grid_count(NanoVDBFile *self, PyObject *Py_UNUSED(ignored)) {
    return PyLong_FromSize_t(tvdb_nanovdb_grid_count(&self->file));
}

static PyObject *NanoVDBFile_grid_name(NanoVDBFile *self, PyObject *args) {
    Py_ssize_t idx;
    if (!PyArg_ParseTuple(args, "n", &idx)) return NULL;
    const char *name = tvdb_nanovdb_grid_name(&self->file, (size_t)idx);
    if (!name) {
        PyErr_SetString(PyExc_IndexError, "Grid index out of range");
        return NULL;
    }
    return PyUnicode_FromString(name);
}

static PyObject *NanoVDBFile_grid_type(NanoVDBFile *self, PyObject *args) {
    Py_ssize_t idx;
    if (!PyArg_ParseTuple(args, "n", &idx)) return NULL;
    uint32_t grid_type = tvdb_nanovdb_grid_type(&self->file, (size_t)idx);
    const char *name = tvdb_nanovdb_grid_type_name(grid_type);
    return PyUnicode_FromString(name);
}

static PyObject *NanoVDBFile_grid_class(NanoVDBFile *self, PyObject *args) {
    Py_ssize_t idx;
    if (!PyArg_ParseTuple(args, "n", &idx)) return NULL;
    uint32_t grid_class = tvdb_nanovdb_grid_class(&self->file, (size_t)idx);
    const char *name = tvdb_nanovdb_grid_class_name(grid_class);
    return PyUnicode_FromString(name);
}

static PyObject *NanoVDBFile_voxel_size(NanoVDBFile *self, PyObject *args) {
    Py_ssize_t idx;
    int axis = 0;
    if (!PyArg_ParseTuple(args, "n|i", &idx, &axis)) return NULL;
    double vs = tvdb_nanovdb_grid_voxel_size(&self->file, (size_t)idx, axis);
    return PyFloat_FromDouble(vs);
}

static PyObject *NanoVDBFile_get(NanoVDBFile *self, PyObject *args) {
    Py_ssize_t idx;
    int x, y, z;
    if (!PyArg_ParseTuple(args, "niii", &idx, &x, &y, &z)) return NULL;

    if ((size_t)idx >= self->file.num_grids) {
        PyErr_SetString(PyExc_IndexError, "Grid index out of range");
        return NULL;
    }

    float val = tvdb_nanovdb_get_voxel_f(&self->file.grids[idx], x, y, z);
    return PyFloat_FromDouble(val);
}

static PyObject *NanoVDBFile_bbox(NanoVDBFile *self, PyObject *args) {
    Py_ssize_t idx;
    if (!PyArg_ParseTuple(args, "n", &idx)) return NULL;

    if ((size_t)idx >= self->file.num_grids) {
        PyErr_SetString(PyExc_IndexError, "Grid index out of range");
        return NULL;
    }

    tvdb_nanovdb_grid_t *g = &self->file.grids[idx];
    PyObject *result = PyTuple_New(2);
    PyObject *min_t = PyTuple_New(3);
    PyObject *max_t = PyTuple_New(3);

    PyTuple_SetItem(min_t, 0, PyFloat_FromDouble(g->index_bbox_min[0]));
    PyTuple_SetItem(min_t, 1, PyFloat_FromDouble(g->index_bbox_min[1]));
    PyTuple_SetItem(min_t, 2, PyFloat_FromDouble(g->index_bbox_min[2]));

    PyTuple_SetItem(max_t, 0, PyFloat_FromDouble(g->index_bbox_max[0]));
    PyTuple_SetItem(max_t, 1, PyFloat_FromDouble(g->index_bbox_max[1]));
    PyTuple_SetItem(max_t, 2, PyFloat_FromDouble(g->index_bbox_max[2]));

    PyTuple_SetItem(result, 0, min_t);
    PyTuple_SetItem(result, 1, max_t);

    return result;
}

static PyObject *NanoVDBFile_node_counts(NanoVDBFile *self, PyObject *args) {
    Py_ssize_t idx;
    if (!PyArg_ParseTuple(args, "n", &idx)) return NULL;

    if ((size_t)idx >= self->file.num_grids) {
        PyErr_SetString(PyExc_IndexError, "Grid index out of range");
        return NULL;
    }

    tvdb_nanovdb_grid_t *g = &self->file.grids[idx];
    PyObject *result = PyTuple_New(3);
    PyTuple_SetItem(result, 0, PyLong_FromUnsignedLongLong(g->node_count[0]));
    PyTuple_SetItem(result, 1, PyLong_FromUnsignedLongLong(g->node_count[1]));
    PyTuple_SetItem(result, 2, PyLong_FromUnsignedLongLong(g->node_count[2]));
    return result;
}

static PyObject *NanoVDBFile_save(NanoVDBFile *self, PyObject *args) {
    const char *path;
    int codec = 0;
    if (!PyArg_ParseTuple(args, "s|i", &path, &codec)) return NULL;

    tvdb_error_t err;
    memset(&err, 0, sizeof(err));

    tvdb_status_t st = tvdb_nanovdb_file_save(&self->file, path, codec, 0, &err);
    if (st != TVDB_OK) {
        PyErr_SetString(PyExc_IOError, err.message);
        return NULL;
    }
    Py_RETURN_NONE;
}

static PyObject *NanoVDBFile_write_to_bytes(NanoVDBFile *self, PyObject *args) {
    int codec = 0;
    if (!PyArg_ParseTuple(args, "|i", &codec)) return NULL;

    uint8_t *data = NULL;
    size_t size = 0;
    tvdb_error_t err;
    memset(&err, 0, sizeof(err));

    tvdb_status_t st = tvdb_nanovdb_write_to_memory(&self->file, codec, &data, &size, &err);
    if (st != TVDB_OK) {
        PyErr_SetString(PyExc_IOError, err.message);
        return NULL;
    }

    PyObject *result = PyBytes_FromStringAndSize((const char *)data, size);
    free(data);
    return result;
}

static PyObject *NanoVDBFile_active_voxel_count(NanoVDBFile *self, PyObject *args) {
    Py_ssize_t idx;
    if (!PyArg_ParseTuple(args, "n", &idx)) return NULL;

    if ((size_t)idx >= self->file.num_grids) {
        PyErr_SetString(PyExc_IndexError, "Grid index out of range");
        return NULL;
    }

    return PyLong_FromUnsignedLongLong(self->file.grids[idx].active_voxel_count);
}

static PyObject *NanoVDBFile_world_bbox(NanoVDBFile *self, PyObject *args) {
    Py_ssize_t idx;
    if (!PyArg_ParseTuple(args, "n", &idx)) return NULL;

    if ((size_t)idx >= self->file.num_grids) {
        PyErr_SetString(PyExc_IndexError, "Grid index out of range");
        return NULL;
    }

    tvdb_nanovdb_grid_t *g = &self->file.grids[idx];
    PyObject *result = PyTuple_New(2);
    PyObject *min_t = PyTuple_New(3);
    PyObject *max_t = PyTuple_New(3);

    PyTuple_SetItem(min_t, 0, PyFloat_FromDouble(g->world_bbox_min[0]));
    PyTuple_SetItem(min_t, 1, PyFloat_FromDouble(g->world_bbox_min[1]));
    PyTuple_SetItem(min_t, 2, PyFloat_FromDouble(g->world_bbox_min[2]));

    PyTuple_SetItem(max_t, 0, PyFloat_FromDouble(g->world_bbox_max[0]));
    PyTuple_SetItem(max_t, 1, PyFloat_FromDouble(g->world_bbox_max[1]));
    PyTuple_SetItem(max_t, 2, PyFloat_FromDouble(g->world_bbox_max[2]));

    PyTuple_SetItem(result, 0, min_t);
    PyTuple_SetItem(result, 1, max_t);

    return result;
}

static PyMethodDef NanoVDBFile_methods[] = {
    {"close", (PyCFunction)NanoVDBFile_close, METH_NOARGS, "Close the file"},
    {"grid_count", (PyCFunction)NanoVDBFile_grid_count, METH_NOARGS, "Number of grids"},
    {"grid_name", (PyCFunction)NanoVDBFile_grid_name, METH_VARARGS, "Get grid name by index"},
    {"grid_type", (PyCFunction)NanoVDBFile_grid_type, METH_VARARGS, "Get grid type by index"},
    {"grid_class", (PyCFunction)NanoVDBFile_grid_class, METH_VARARGS, "Get grid class by index"},
    {"voxel_size", (PyCFunction)NanoVDBFile_voxel_size, METH_VARARGS, "Get voxel size"},
    {"get", (PyCFunction)NanoVDBFile_get, METH_VARARGS, "Get voxel value at (x,y,z)"},
    {"bbox", (PyCFunction)NanoVDBFile_bbox, METH_VARARGS, "Get grid bounding box"},
    {"world_bbox", (PyCFunction)NanoVDBFile_world_bbox, METH_VARARGS, "Get world bounding box"},
    {"node_counts", (PyCFunction)NanoVDBFile_node_counts, METH_VARARGS, "Get node counts"},
    {"active_voxel_count", (PyCFunction)NanoVDBFile_active_voxel_count, METH_VARARGS, "Get active voxel count"},
    {"save", (PyCFunction)NanoVDBFile_save, METH_VARARGS, "Save to file"},
    {"to_bytes", (PyCFunction)NanoVDBFile_write_to_bytes, METH_VARARGS, "Write to bytes"},
    {NULL}
};

static PyType_Slot NanoVDBFile_slots[] = {
    {Py_tp_new, (void *)NanoVDBFile_open},
    {Py_tp_dealloc, (void *)NanoVDBFile_dealloc},
    {Py_tp_methods, NanoVDBFile_methods},
    {Py_tp_doc, (void *)"NanoVDB file object"},
    {0, NULL},
};

static PyType_Spec NanoVDBFile_spec = {
    .name = "_tinyvdb_nanovdb.NanoVDBFile",
    .basicsize = sizeof(NanoVDBFile),
    .itemsize = 0,
    .flags = Py_TPFLAGS_DEFAULT | Py_TPFLAGS_BASETYPE,
    .slots = NanoVDBFile_slots,
};

/* ======================================================================== */
/*  GaussianSplat type                                                        */
/* ======================================================================== */

typedef struct {
    PyObject_HEAD
    tvdb_gaussian_splat_t *splat;
} GaussianSplat;

static PyObject *GaussianSplat_type = NULL;

static void GaussianSplat_dealloc(void *self) {
    GaussianSplat *gs = (GaussianSplat *)self;
    if (gs->splat) {
        tvdb_gaussian_splat_destroy(gs->splat);
        gs->splat = NULL;
    }
    PyObject_Del(self);
}

static PyObject *GaussianSplat_get_count(GaussianSplat *self, PyObject *Py_UNUSED(ignored)) {
    return PyLong_FromUnsignedLongLong(tvdb_gaussian_splat_count(self->splat));
}

static PyObject *GaussianSplat_getitem(GaussianSplat *self, PyObject *args) {
    Py_ssize_t idx = PyLong_AsSsize_t(args);
    if ((idx == -1) && PyErr_Occurred()) {
        PyErr_SetString(PyExc_TypeError, "Index must be an integer");
        return NULL;
    }

    uint64_t count = tvdb_gaussian_splat_count(self->splat);
    if (idx < 0) idx += (Py_ssize_t)count;
    if (idx < 0 || (uint64_t)idx >= count) {
        PyErr_SetString(PyExc_IndexError, "Gaussian index out of range");
        return NULL;
    }

    float means[3], quats[4], scales[3], opacity;
    tvdb_gaussian_splat_get(self->splat, (uint32_t)idx, means, quats, scales, &opacity);

    return Py_BuildValue(
        "{s:f,s:f,s:f,s:f,s:f,s:f,s:f,s:f,s:f,s:f,s:f}",
        "mean", means[0],
        "mean_y", means[1],
        "mean_z", means[2],
        "quat_0", quats[0],
        "quat_1", quats[1],
        "quat_2", quats[2],
        "quat_3", quats[3],
        "scale_0", scales[0],
        "scale_1", scales[1],
        "scale_2", scales[2],
        "opacity", opacity
    );
}

static PyObject *GaussianSplat_to_arrays(GaussianSplat *self, PyObject *Py_UNUSED(ignored)) {
    uint32_t N = tvdb_gaussian_splat_count(self->splat);

    PyObject *result = PyDict_New();

    PyObject *means = PyList_New(N);
    PyObject *quats = PyList_New(N);
    PyObject *scales = PyList_New(N);
    PyObject *opacities = PyList_New(N);

    for (uint32_t i = 0; i < N; i++) {
        float m[3], q[4], s[3], op;
        tvdb_gaussian_splat_get(self->splat, i, m, q, s, &op);

        PyObject *m_t = PyTuple_New(3);
        PyTuple_SetItem(m_t, 0, PyFloat_FromDouble(m[0]));
        PyTuple_SetItem(m_t, 1, PyFloat_FromDouble(m[1]));
        PyTuple_SetItem(m_t, 2, PyFloat_FromDouble(m[2]));
        PyList_SetItem(means, (Py_ssize_t)i, m_t);

        PyObject *q_t = PyTuple_New(4);
        PyTuple_SetItem(q_t, 0, PyFloat_FromDouble(q[0]));
        PyTuple_SetItem(q_t, 1, PyFloat_FromDouble(q[1]));
        PyTuple_SetItem(q_t, 2, PyFloat_FromDouble(q[2]));
        PyTuple_SetItem(q_t, 3, PyFloat_FromDouble(q[3]));
        PyList_SetItem(quats, (Py_ssize_t)i, q_t);

        PyObject *s_t = PyTuple_New(3);
        PyTuple_SetItem(s_t, 0, PyFloat_FromDouble(s[0]));
        PyTuple_SetItem(s_t, 1, PyFloat_FromDouble(s[1]));
        PyTuple_SetItem(s_t, 2, PyFloat_FromDouble(s[2]));
        PyList_SetItem(scales, (Py_ssize_t)i, s_t);

        PyList_SetItem(opacities, (Py_ssize_t)i, PyFloat_FromDouble(op));
    }

    PyDict_SetItemString(result, "means", means);
    PyDict_SetItemString(result, "quats", quats);
    PyDict_SetItemString(result, "scales", scales);
    PyDict_SetItemString(result, "opacities", opacities);

    return result;
}

static Py_ssize_t GaussianSplat_len(GaussianSplat *self) {
    return (Py_ssize_t)tvdb_gaussian_splat_count(self->splat);
}

static PyObject *GaussianSplat_repr(GaussianSplat *self) {
    char buf[128];
    snprintf(buf, sizeof(buf), "<GaussianSplat: %u gaussians>",
             (unsigned)tvdb_gaussian_splat_count(self->splat));
    return PyUnicode_FromString(buf);
}

static PyMethodDef GaussianSplat_methods[] = {
    {"count", (PyCFunction)GaussianSplat_get_count, METH_NOARGS, "Number of gaussians"},
    {"to_arrays", (PyCFunction)GaussianSplat_to_arrays, METH_NOARGS, "Get all gaussians as arrays"},
    {NULL}
};

static PyType_Slot GaussianSplat_slots[] = {
    {Py_tp_dealloc, (void *)GaussianSplat_dealloc},
    {Py_tp_methods, GaussianSplat_methods},
    {Py_tp_repr, (void *)GaussianSplat_repr},
    {Py_sq_length, (void *)GaussianSplat_len},
    {Py_mp_subscript, (void *)GaussianSplat_getitem},
    {0, NULL},
};

static PyType_Spec GaussianSplat_spec = {
    .name = "_tinyvdb_nanovdb.GaussianSplat",
    .basicsize = sizeof(GaussianSplat),
    .itemsize = 0,
    .flags = Py_TPFLAGS_DEFAULT,
    .slots = GaussianSplat_slots,
};

/* ======================================================================== */
/*  Module functions                                                          */
/* ======================================================================== */

static PyObject *nanovdb_grid_type_name(PyObject *self, PyObject *args) {
    uint32_t grid_type;
    if (!PyArg_ParseTuple(args, "I", &grid_type)) return NULL;
    const char *name = tvdb_nanovdb_grid_type_name(grid_type);
    return PyUnicode_FromString(name);
}

static PyObject *nanovdb_grid_class_name(PyObject *self, PyObject *args) {
    uint32_t grid_class;
    if (!PyArg_ParseTuple(args, "I", &grid_class)) return NULL;
    const char *name = tvdb_nanovdb_grid_class_name(grid_class);
    return PyUnicode_FromString(name);
}

static PyObject *nanovdb_leaf_node_size(PyObject *self, PyObject *args) {
    uint32_t grid_type = TVDB_NANOVDB_GRID_TYPE_FLOAT;
    if (!PyArg_ParseTuple(args, "|I", &grid_type)) return NULL;
    return PyLong_FromUnsignedLongLong(tvdb_nanovdb_leaf_node_size(grid_type));
}

static PyObject *nanovdb_lower_node_size(PyObject *self, PyObject *args) {
    uint32_t grid_type = TVDB_NANOVDB_GRID_TYPE_FLOAT;
    if (!PyArg_ParseTuple(args, "|I", &grid_type)) return NULL;
    return PyLong_FromUnsignedLongLong(tvdb_nanovdb_lower_node_size(grid_type));
}

static PyObject *nanovdb_upper_node_size(PyObject *self, PyObject *args) {
    uint32_t grid_type = TVDB_NANOVDB_GRID_TYPE_FLOAT;
    if (!PyArg_ParseTuple(args, "|I", &grid_type)) return NULL;
    return PyLong_FromUnsignedLongLong(tvdb_nanovdb_upper_node_size(grid_type));
}

static PyObject *nanovdb_value_size(PyObject *self, PyObject *args) {
    uint32_t grid_type = TVDB_NANOVDB_GRID_TYPE_FLOAT;
    if (!PyArg_ParseTuple(args, "|I", &grid_type)) return NULL;
    return PyLong_FromUnsignedLongLong(tvdb_nanovdb_value_size(grid_type));
}

static PyObject *gaussian_splat_load(PyObject *self, PyObject *args) {
    const char *path;
    if (!PyArg_ParseTuple(args, "s", &path)) return NULL;

    tvdb_error_t err;
    memset(&err, 0, sizeof(err));

    tvdb_gaussian_splat_t *splat = tvdb_gaussian_splat_load(path, &err);
    if (!splat) {
        PyErr_SetString(PyExc_IOError, err.message);
        return NULL;
    }

    GaussianSplat *result = (GaussianSplat *)PyObject_Malloc(sizeof(GaussianSplat));
    if (!result) {
        tvdb_gaussian_splat_destroy(splat);
        return PyErr_NoMemory();
    }
    PyObject_Init((PyObject *)result, (PyTypeObject *)GaussianSplat_type);
    result->splat = splat;

    return (PyObject *)result;
}

static PyObject *gaussian_splat_save(PyObject *self, PyObject *args) {
    const char *path;
    PyObject *py_splat;
    if (!PyArg_ParseTuple(args, "sO", &path, &py_splat)) return NULL;

    if (!PyObject_TypeCheck(py_splat, (PyTypeObject *)GaussianSplat_type)) {
        PyErr_SetString(PyExc_TypeError, "Expected GaussianSplat object");
        return NULL;
    }

    GaussianSplat *gs = (GaussianSplat *)py_splat;

    tvdb_error_t err;
    memset(&err, 0, sizeof(err));

    tvdb_status_t st = tvdb_gaussian_splat_save(path, gs->splat, &err);
    if (st != TVDB_OK) {
        PyErr_SetString(PyExc_IOError, err.message);
        return NULL;
    }
    Py_RETURN_NONE;
}

static PyObject *gaussian_splat_create_from_arrays(PyObject *self, PyObject *args) {
    PyObject *py_means, *py_quats, *py_scales, *py_opacities;
    if (!PyArg_ParseTuple(args, "OOOO", &py_means, &py_quats, &py_scales, &py_opacities))
        return NULL;

    Py_ssize_t N = PySequence_Size(py_means);
    if (N <= 0) {
        PyErr_SetString(PyExc_ValueError, "Empty arrays not supported");
        return NULL;
    }

    tvdb_gaussian_splat_t *splat = (tvdb_gaussian_splat_t *)calloc(1, sizeof(tvdb_gaussian_splat_t));
    if (!splat) return PyErr_NoMemory();

    splat->num_gaussians = (uint32_t)N;
    splat->owns_data = 1;
    splat->sh_degree = 0;
    splat->sh_dim = 3;

    splat->means = (float *)malloc((size_t)N * 3 * sizeof(float));
    splat->quats = (float *)malloc((size_t)N * 4 * sizeof(float));
    splat->log_scales = (float *)malloc((size_t)N * 3 * sizeof(float));
    splat->logit_opacities = (float *)malloc((size_t)N * sizeof(float));
    splat->sh_coeffs = (float *)malloc((size_t)N * 3 * sizeof(float));

    if (!splat->means || !splat->quats || !splat->log_scales || !splat->logit_opacities || !splat->sh_coeffs) {
        tvdb_gaussian_splat_destroy(splat);
        return PyErr_NoMemory();
    }

    for (Py_ssize_t i = 0; i < N; i++) {
        PyObject *m = PySequence_GetItem(py_means, i);
        PyObject *q = PySequence_GetItem(py_quats, i);
        PyObject *s = PySequence_GetItem(py_scales, i);
        PyObject *op = PySequence_GetItem(py_opacities, i);

        for (int j = 0; j < 3; j++) {
            PyObject *mj = PySequence_GetItem(m, j);
            PyObject *sj = PySequence_GetItem(s, j);
            splat->means[i * 3 + j] = (float)PyFloat_AsDouble(mj);
            splat->log_scales[i * 3 + j] = (float)PyFloat_AsDouble(sj);
            Py_DECREF(mj);
            Py_DECREF(sj);
        }
        for (int j = 0; j < 4; j++) {
            PyObject *qj = PySequence_GetItem(q, j);
            splat->quats[i * 4 + j] = (float)PyFloat_AsDouble(qj);
            Py_DECREF(qj);
        }
        splat->logit_opacities[i] = (float)PyFloat_AsDouble(op);
        splat->sh_coeffs[i * 3 + 0] = 1.0f;
        splat->sh_coeffs[i * 3 + 1] = 0.0f;
        splat->sh_coeffs[i * 3 + 2] = 0.0f;

        Py_DECREF(m);
        Py_DECREF(q);
        Py_DECREF(s);
        Py_DECREF(op);
    }

    GaussianSplat *result = (GaussianSplat *)PyObject_Malloc(sizeof(GaussianSplat));
    if (!result) {
        tvdb_gaussian_splat_destroy(splat);
        return PyErr_NoMemory();
    }
    PyObject_Init((PyObject *)result, (PyTypeObject *)GaussianSplat_type);
    result->splat = splat;

    return (PyObject *)result;
}

static PyMethodDef module_functions[] = {
    {"grid_type_name", nanovdb_grid_type_name, METH_VARARGS, "Get name for grid type ID"},
    {"grid_class_name", nanovdb_grid_class_name, METH_VARARGS, "Get name for grid class ID"},
    {"leaf_node_size", nanovdb_leaf_node_size, METH_VARARGS, "Get leaf node size for grid type"},
    {"lower_node_size", nanovdb_lower_node_size, METH_VARARGS, "Get lower internal node size for grid type"},
    {"upper_node_size", nanovdb_upper_node_size, METH_VARARGS, "Get upper internal node size for grid type"},
    {"value_size", nanovdb_value_size, METH_VARARGS, "Get value size for grid type"},
    {"gaussian_splat_load", gaussian_splat_load, METH_VARARGS, "Load Gaussian splat from PLY file"},
    {"gaussian_splat_save", gaussian_splat_save, METH_VARARGS, "Save Gaussian splat to PLY file"},
    {"gaussian_splat_create_from_arrays", gaussian_splat_create_from_arrays, METH_VARARGS, "Create Gaussian splat from numpy arrays"},
    {NULL, NULL, 0, NULL}
};

/* ======================================================================== */
/*  Module initialization                                                    */
/* ======================================================================== */

PyMODINIT_FUNC PyInit__tinyvdb_nanovdb(void) {
    PyObject *m;

    m = PyModule_Create(&tvdb_nanovdb_module);
    if (!m) return NULL;

    if (PyModule_AddFunctions(m, module_functions) < 0) {
        Py_DECREF(m);
        return NULL;
    }

    PyObject *type = PyType_FromSpec(&NanoVDBFile_spec);
    if (!type) {
        Py_DECREF(m);
        return NULL;
    }
    Py_INCREF(type);
    if (PyModule_AddObject(m, "NanoVDBFile", type) < 0) {
        Py_DECREF(type);
        Py_DECREF(m);
        return NULL;
    }

    if (PyModule_AddIntConstant(m, "CODEC_NONE", TVDB_NANOVDB_CODEC_NONE) < 0) return NULL;
    if (PyModule_AddIntConstant(m, "CODEC_ZIP", TVDB_NANOVDB_CODEC_ZIP) < 0) return NULL;
    if (PyModule_AddIntConstant(m, "CODEC_BLOSC", TVDB_NANOVDB_CODEC_BLOSC) < 0) return NULL;

    if (PyModule_AddIntConstant(m, "GRID_TYPE_FLOAT", TVDB_NANOVDB_GRID_TYPE_FLOAT) < 0) return NULL;
    if (PyModule_AddIntConstant(m, "GRID_TYPE_DOUBLE", TVDB_NANOVDB_GRID_TYPE_DOUBLE) < 0) return NULL;
    if (PyModule_AddIntConstant(m, "GRID_TYPE_INT32", TVDB_NANOVDB_GRID_TYPE_INT32) < 0) return NULL;
    if (PyModule_AddIntConstant(m, "GRID_TYPE_INT64", TVDB_NANOVDB_GRID_TYPE_INT64) < 0) return NULL;
    if (PyModule_AddIntConstant(m, "GRID_TYPE_VEC3F", TVDB_NANOVDB_GRID_TYPE_VEC3F) < 0) return NULL;
    if (PyModule_AddIntConstant(m, "GRID_TYPE_VEC3D", TVDB_NANOVDB_GRID_TYPE_VEC3D) < 0) return NULL;

    if (PyModule_AddIntConstant(m, "GRID_CLASS_LEVEL_SET", TVDB_NANOVDB_GRID_CLASS_LEVEL_SET) < 0) return NULL;
    if (PyModule_AddIntConstant(m, "GRID_CLASS_FOG_VOLUME", TVDB_NANOVDB_GRID_CLASS_FOG_VOLUME) < 0) return NULL;
    if (PyModule_AddIntConstant(m, "GRID_CLASS_POINT_DATA", TVDB_NANOVDB_GRID_CLASS_POINT_DATA) < 0) return NULL;

    PyObject *gs_type = PyType_FromSpec(&GaussianSplat_spec);
    if (!gs_type) {
        Py_DECREF(m);
        return NULL;
    }
    Py_INCREF(gs_type);
    GaussianSplat_type = gs_type;
    if (PyModule_AddObject(m, "GaussianSplat", gs_type) < 0) {
        Py_DECREF(gs_type);
        Py_DECREF(m);
        return NULL;
    }

    if (PyModule_AddStringConstant(m, "__version__", "0.1.0") < 0) return NULL;

    return m;
}
