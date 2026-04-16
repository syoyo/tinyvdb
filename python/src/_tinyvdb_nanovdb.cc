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

static void NanoVDBFile_dealloc(NanoVDBFile *self) {
    if (!self->closed && self->file.num_grids > 0) {
        tvdb_nanovdb_file_close(&self->file);
    }
    Py_TYPE(self)->tp_free((PyObject *)self);
}

static PyObject *NanoVDBFile_open(PyTypeObject *type, PyObject *args, PyObject *kwds) {
    static char *kwlist[] = {"path", NULL};
    const char *path;

    if (!PyArg_ParseTupleAndKeywords(args, kwds, "s", kwlist, &path))
        return NULL;

    NanoVDBFile *self = (NanoVDBFile *)type->tp_alloc(type, 0);
    if (!self) return NULL;

    memset(&self->file, 0, sizeof(self->file));
    self->closed = 0;

    tvdb_error_t err;
    memset(&err, 0, sizeof(err));

    tvdb_status_t st = tvdb_nanovdb_file_open(&self->file, path, NULL, &err);
    if (st != TVDB_OK) {
        PyErr_SetString(PyExc_IOError, err.message);
        Py_DECREF(self);
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

    PyTuple_SET_ITEM(min_t, 0, PyFloat_FromDouble(g->index_bbox_min[0]));
    PyTuple_SET_ITEM(min_t, 1, PyFloat_FromDouble(g->index_bbox_min[1]));
    PyTuple_SET_ITEM(min_t, 2, PyFloat_FromDouble(g->index_bbox_min[2]));

    PyTuple_SET_ITEM(max_t, 0, PyFloat_FromDouble(g->index_bbox_max[0]));
    PyTuple_SET_ITEM(max_t, 1, PyFloat_FromDouble(g->index_bbox_max[1]));
    PyTuple_SET_ITEM(max_t, 2, PyFloat_FromDouble(g->index_bbox_max[2]));

    PyTuple_SET_ITEM(result, 0, min_t);
    PyTuple_SET_ITEM(result, 1, max_t);

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
    PyTuple_SET_ITEM(result, 0, PyLong_FromUnsignedLongLong(g->node_count[0]));
    PyTuple_SET_ITEM(result, 1, PyLong_FromUnsignedLongLong(g->node_count[1]));
    PyTuple_SET_ITEM(result, 2, PyLong_FromUnsignedLongLong(g->node_count[2]));
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

    PyTuple_SET_ITEM(min_t, 0, PyFloat_FromDouble(g->world_bbox_min[0]));
    PyTuple_SET_ITEM(min_t, 1, PyFloat_FromDouble(g->world_bbox_min[1]));
    PyTuple_SET_ITEM(min_t, 2, PyFloat_FromDouble(g->world_bbox_min[2]));

    PyTuple_SET_ITEM(max_t, 0, PyFloat_FromDouble(g->world_bbox_max[0]));
    PyTuple_SET_ITEM(max_t, 1, PyFloat_FromDouble(g->world_bbox_max[1]));
    PyTuple_SET_ITEM(max_t, 2, PyFloat_FromDouble(g->world_bbox_max[2]));

    PyTuple_SET_ITEM(result, 0, min_t);
    PyTuple_SET_ITEM(result, 1, max_t);

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
    {Py_tp_new, NanoVDBFile_open},
    {Py_tp_dealloc, NanoVDBFile_dealloc},
    {Py_tp_methods, NanoVDBFile_methods},
    {Py_tp_doc, "NanoVDB file object"},
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

static PyMethodDef module_functions[] = {
    {"grid_type_name", nanovdb_grid_type_name, METH_VARARGS, "Get name for grid type ID"},
    {"grid_class_name", nanovdb_grid_class_name, METH_VARARGS, "Get name for grid class ID"},
    {"leaf_node_size", nanovdb_leaf_node_size, METH_VARARGS, "Get leaf node size for grid type"},
    {"lower_node_size", nanovdb_lower_node_size, METH_VARARGS, "Get lower internal node size for grid type"},
    {"upper_node_size", nanovdb_upper_node_size, METH_VARARGS, "Get upper internal node size for grid type"},
    {"value_size", nanovdb_value_size, METH_VARARGS, "Get value size for grid type"},
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

    if (PyModule_AddStringConstant(m, "__version__", "0.1.0") < 0) return NULL;

    return m;
}
