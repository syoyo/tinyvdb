cmake_minimum_required(VERSION 3.26)

find_package(Python3 3.11 REQUIRED COMPONENTS Interpreter Development.SABIModule)

Python3_add_library(_tinyvdb MODULE WITH_SOABI USE_SABI 3.11
    src/_tinyvdb.c
    src/_tinyvdb_mesh_ops.c
)

target_link_libraries(_tinyvdb PRIVATE tinyvdb tinyvdb_mesh_ops)
target_include_directories(_tinyvdb PRIVATE
    ${CMAKE_SOURCE_DIR}/src
    ${CMAKE_CURRENT_SOURCE_DIR}/src
)
# Py_LIMITED_API is defined in the source file itself

# C11 for the mesh/ops wrapper. It used to be a C++ translation unit, but it
# only ever used the Python C API (PyType_FromSpec / PyMethodDef) plus one
# std::vector, which is now a small growable buffer. No pybind11 or nanobind is
# involved anywhere in this package.
set_target_properties(_tinyvdb PROPERTIES
    C_STANDARD 11
    C_STANDARD_REQUIRED ON
)

install(TARGETS _tinyvdb DESTINATION tinyvdb)

# NanoVDB bindings
Python3_add_library(_tinyvdb_nanovdb MODULE WITH_SOABI USE_SABI 3.11
    src/_tinyvdb_nanovdb.c
)

target_link_libraries(_tinyvdb_nanovdb PRIVATE tinyvdb_nanovdb)
target_compile_definitions(_tinyvdb_nanovdb PRIVATE TINYVDB_PYTHON_VERSION="${PROJECT_VERSION}")
target_include_directories(_tinyvdb_nanovdb PRIVATE
    ${CMAKE_SOURCE_DIR}/src
    ${CMAKE_CURRENT_SOURCE_DIR}/src
)

install(TARGETS _tinyvdb_nanovdb DESTINATION tinyvdb)
