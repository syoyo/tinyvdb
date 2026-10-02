#pragma once
#include <Python.h>

/* Python 3.12+ headers may return immortal None without incrementing it.
 * A cp311-abi3 wheel can run on 3.11, where None is still refcounted. Call
 * the stable-ABI function so ownership follows the runtime's rules. */
#define TVDB_PY_RETURN_NONE return (Py_NewRef)(Py_None)
