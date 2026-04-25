cmake_minimum_required(VERSION 3.5)

project(tinyvdb C CXX)

# options
option(TINYVDB_USE_CCACHE "Use ccache for faster recompile." ON)
option(TINYVDB_BUILD_TESTS "Build tests" OFF)
option(TINYVDB_BUILD_EXAMPLES "Build examples" ON)
option(TINYVDB_USE_SYSTEM_ZLIB "Use system zlib instead of bundled miniz" OFF)
option(TINYVDB_USE_ZSTD "Enable ZSTD compression support in BLOSC frames" ON)
option(TINYVDB_USE_SYSTEM_ZSTD "Use system zstd instead of bundled deps/zstd" OFF)
option(TINYVDB_BUILD_VDBRENDER "Build vdbrender volume path tracer example" ON)
option(TINYVDB_BUILD_PYTHON "Build Python extension" OFF)
option(TINYVDB_OPENMP "Enable OpenMP parallelism in mesh/ops kernels" OFF)

# cmake modules
list(APPEND CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
list(APPEND CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake/sanitizers)
find_package(Sanitizers QUIET)

# C11 for the library, C++11 for examples
set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# [ccache]
if(TINYVDB_USE_CCACHE)
  if(NOT MSVC)
    find_program(CCACHE_EXE ccache)
    if(CCACHE_EXE)
      message(STATUS "Using ccache: ${CCACHE_EXE}")
      set(CMAKE_C_COMPILER_LAUNCHER "${CCACHE_EXE}")
      set(CMAKE_CXX_COMPILER_LAUNCHER "${CCACHE_EXE}")
    endif()
  endif()
endif()

# tinyvdb static library (C11 implementation + miniz + lz4)
set(TINYVDB_C_SOURCES
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_io.c
  ${PROJECT_SOURCE_DIR}/src/lz4.c)
if(NOT TINYVDB_USE_SYSTEM_ZLIB)
  list(APPEND TINYVDB_C_SOURCES ${PROJECT_SOURCE_DIR}/src/miniz.c)
endif()

add_library(tinyvdb STATIC ${TINYVDB_C_SOURCES})

# Mesh/ops C helper library
add_library(tinyvdb_mesh_ops STATIC
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_mesh.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_ops.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_sample.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_tsdf.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_topology.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_ray.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_sparse.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_sparse_tree.c
  ${PROJECT_SOURCE_DIR}/src/tinyvdb_lifecycle.c
  ${PROJECT_SOURCE_DIR}/src/tvdb_memory.c)
if(NOT WIN32)
  target_link_libraries(tinyvdb_mesh_ops PUBLIC m)
endif()
# tinyvdb_sparse_tree depends on tinyvdb_io.h types (and tvdb_file_open at runtime)
target_link_libraries(tinyvdb_mesh_ops PUBLIC tinyvdb)
target_include_directories(tinyvdb_mesh_ops PUBLIC ${PROJECT_SOURCE_DIR}/src)

if(TINYVDB_OPENMP)
  find_package(OpenMP)
  if(OpenMP_C_FOUND)
    target_link_libraries(tinyvdb_mesh_ops PUBLIC OpenMP::OpenMP_C)
    target_compile_definitions(tinyvdb_mesh_ops PUBLIC TINYVDB_OPENMP_ENABLED=1)
    message(STATUS "OpenMP enabled for tinyvdb_mesh_ops (${OpenMP_C_FLAGS})")
  else()
    message(WARNING "TINYVDB_OPENMP=ON requested but OpenMP not found; building scalar")
  endif()
endif()
set_target_properties(tinyvdb_mesh_ops PROPERTIES
  C_STANDARD 11
  C_STANDARD_REQUIRED ON
  C_EXTENSIONS OFF)

# NanoVDB support library
add_library(tinyvdb_nanovdb STATIC ${PROJECT_SOURCE_DIR}/src/tinyvdb_nanovdb.c)
target_include_directories(tinyvdb_nanovdb PUBLIC ${PROJECT_SOURCE_DIR}/src)
target_link_libraries(tinyvdb_nanovdb PRIVATE tinyvdb)
target_include_directories(tinyvdb PUBLIC ${PROJECT_SOURCE_DIR}/src)
target_compile_definitions(tinyvdb PRIVATE TINYVDB_IO_IMPLEMENTATION MINIZ_NO_STDIO)

# When building the Python extension, static libs linked into modules must be PIC
if(TINYVDB_BUILD_PYTHON)
    set_target_properties(tinyvdb PROPERTIES POSITION_INDEPENDENT_CODE ON)
    set_target_properties(tinyvdb_mesh_ops PROPERTIES POSITION_INDEPENDENT_CODE ON)
    set_target_properties(tinyvdb_nanovdb PROPERTIES POSITION_INDEPENDENT_CODE ON)
endif()

# Force system zlib for iOS
if(IOS)
  set(TINYVDB_USE_SYSTEM_ZLIB ON CACHE INTERNAL "" FORCE)
endif()

if(TINYVDB_USE_SYSTEM_ZLIB)
  find_package(ZLIB REQUIRED)
  target_link_libraries(tinyvdb PUBLIC ZLIB::ZLIB)
  target_compile_definitions(tinyvdb PUBLIC TVDB_USE_SYSTEM_ZLIB)
endif()

# ZSTD
if(TINYVDB_USE_ZSTD)
  if(TINYVDB_USE_SYSTEM_ZSTD)
    find_package(PkgConfig QUIET)
    if(PkgConfig_FOUND)
      pkg_check_modules(ZSTD IMPORTED_TARGET libzstd)
    endif()
    if(ZSTD_FOUND)
      target_link_libraries(tinyvdb PUBLIC PkgConfig::ZSTD)
    else()
      find_library(ZSTD_LIBRARY NAMES zstd)
      find_path(ZSTD_INCLUDE_DIR NAMES zstd.h)
      if(ZSTD_LIBRARY AND ZSTD_INCLUDE_DIR)
        target_link_libraries(tinyvdb PUBLIC ${ZSTD_LIBRARY})
        target_include_directories(tinyvdb PUBLIC ${ZSTD_INCLUDE_DIR})
      else()
        message(FATAL_ERROR "System zstd not found. Install libzstd-dev or set TINYVDB_USE_SYSTEM_ZSTD=OFF")
      endif()
    endif()
  else()
    # Use bundled single-file zstd from deps/
    target_sources(tinyvdb PRIVATE ${PROJECT_SOURCE_DIR}/deps/zstd.c)
    target_include_directories(tinyvdb PUBLIC ${PROJECT_SOURCE_DIR}/deps)
  endif()
  target_compile_definitions(tinyvdb PUBLIC TVDB_USE_ZSTD)
endif()

# Tests
if(TINYVDB_BUILD_TESTS)
  add_executable(test_ops ${PROJECT_SOURCE_DIR}/tests/test_ops.c)
  target_link_libraries(test_ops PRIVATE tinyvdb_mesh_ops)
  enable_testing()
  add_test(NAME test_ops COMMAND test_ops)

  add_executable(test_sparse_tree ${PROJECT_SOURCE_DIR}/tests/test_sparse_tree.c)
  target_link_libraries(test_sparse_tree PRIVATE tinyvdb_mesh_ops tinyvdb)
  add_test(NAME test_sparse_tree
           COMMAND test_sparse_tree ${PROJECT_SOURCE_DIR}/sphere.vdb)

  add_executable(test_grid_from_sparse ${PROJECT_SOURCE_DIR}/tests/test_grid_from_sparse.c)
  target_link_libraries(test_grid_from_sparse PRIVATE tinyvdb_mesh_ops tinyvdb)
  add_test(NAME test_grid_from_sparse
           COMMAND test_grid_from_sparse ${PROJECT_SOURCE_DIR}/sphere.vdb)

  if(TINYVDB_BUILD_PYTHON)
    find_program(PYTHON3_EXE NAMES python3 python)
    if(PYTHON3_EXE)
      add_test(NAME test_bridge_ops_py
               COMMAND ${PYTHON3_EXE} ${PROJECT_SOURCE_DIR}/tests/test_bridge_ops.py)
      set_tests_properties(test_bridge_ops_py PROPERTIES
        WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
        ENVIRONMENT "PYTHONPATH=${CMAKE_BINARY_DIR}")
    endif()
  endif()
endif()

# Examples
if(TINYVDB_BUILD_EXAMPLES)
  add_subdirectory(examples/vdbdump)
  add_subdirectory(examples/nanovdbdump)
  add_subdirectory(examples/nanovdb_test)
endif()

# vdbrender (volume path tracer)
if(TINYVDB_BUILD_VDBRENDER)
  add_subdirectory(examples/vdbrender)
endif()

# Python extension
if(TINYVDB_BUILD_PYTHON)
    add_subdirectory(python)
endif()

# [VisualStudio]
if(WIN32)
  set_property(DIRECTORY PROPERTY VS_STARTUP_PROJECT tinyvdb)
endif()
