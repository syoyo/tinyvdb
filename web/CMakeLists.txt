cmake_minimum_required(VERSION 3.13)
project(tinyvdb_wasm CXX C)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED ON)

# ---------------------------------------------------------------------------
#  tinyvdb C core (static lib, compiled as C)
# ---------------------------------------------------------------------------

set(TINYVDB_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/..")

set(TINYVDB_C_SOURCES
    ${TINYVDB_ROOT}/src/tinyvdb_io.c
    ${TINYVDB_ROOT}/src/lz4.c
    ${TINYVDB_ROOT}/src/miniz.c
    # v0.9.0: the formerly-single-header mesh / ops C++ wrappers became
    # standalone C TUs. Bind them in so the embind module can call the
    # new C API directly (tvdb_make_manifold_vdb, tvdb_dilate, …).
    ${TINYVDB_ROOT}/src/tinyvdb_lifecycle.c
    ${TINYVDB_ROOT}/src/tinyvdb_mesh.c
    ${TINYVDB_ROOT}/src/tinyvdb_ops.c
    ${TINYVDB_ROOT}/src/tvdb_memory.c
)

add_library(tinyvdb_c STATIC ${TINYVDB_C_SOURCES})
target_include_directories(tinyvdb_c PUBLIC ${TINYVDB_ROOT}/src)
target_compile_definitions(tinyvdb_c PRIVATE
    TINYVDB_IO_IMPLEMENTATION
    MINIZ_NO_STDIO
    TVDB_NO_MMAP          # WASM has no mmap
)

# ZSTD (bundled single-file)
if(EXISTS "${TINYVDB_ROOT}/deps/zstd.c")
    target_sources(tinyvdb_c PRIVATE ${TINYVDB_ROOT}/deps/zstd.c)
    target_include_directories(tinyvdb_c PUBLIC ${TINYVDB_ROOT}/deps)
    target_compile_definitions(tinyvdb_c PUBLIC TVDB_USE_ZSTD)
endif()

# ---------------------------------------------------------------------------
#  Embind binding module
# ---------------------------------------------------------------------------

add_executable(tinyvdb
    tinyvdb_embind.cc
)

target_link_libraries(tinyvdb PRIVATE tinyvdb_c)
target_include_directories(tinyvdb PRIVATE ${TINYVDB_ROOT}/src)

# Emscripten link flags
target_link_options(tinyvdb PRIVATE
    "SHELL:-s MODULARIZE=1"
    "SHELL:-s EXPORT_NAME='TinyVDB'"
    "SHELL:-s ALLOW_MEMORY_GROWTH=1"
    "SHELL:-s MAXIMUM_MEMORY=1073741824"   # 1 GB
    "SHELL:-s ENVIRONMENT='web,worker,node'"
    "SHELL:--bind"
)

# Produce .js + .wasm
set_target_properties(tinyvdb PROPERTIES
    SUFFIX ".js"
    RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}"
)
