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

# TINYVDB_IO_IMPLEMENTATION unlocks a ~205-function implementation block in
# tinyvdb_io.h. It must be defined for exactly ONE translation unit. Every TU
# that includes tinyvdb_io.h while the macro is visible re-emits all of those
# functions, and the link fails with duplicate symbols.
#
# So the io TUs and the mesh/ops TUs have to live in separate targets, exactly
# as the native CMakeLists.txt does (libtinyvdb vs libtinyvdb_mesh_ops). They
# were previously merged into one target here, which defined the macro for all
# of them and broke the link.
set(TINYVDB_C_SOURCES
    ${TINYVDB_ROOT}/src/tinyvdb_io.c
    ${TINYVDB_ROOT}/src/lz4.c
    ${TINYVDB_ROOT}/src/miniz.c
)

add_library(tinyvdb_c STATIC ${TINYVDB_C_SOURCES})
target_include_directories(tinyvdb_c PUBLIC ${TINYVDB_ROOT}/src)
target_compile_definitions(tinyvdb_c PRIVATE
    TINYVDB_IO_IMPLEMENTATION
    MINIZ_NO_STDIO
    TVDB_NO_MMAP          # WASM has no mmap
)

# v0.9.0: the formerly-single-header mesh / ops C++ wrappers became standalone
# C TUs. Bind them in so the embind module can call the new C API directly
# (tvdb_make_manifold_vdb, tvdb_dilate, ...).
#
# These include tinyvdb_io.h for its type declarations only. They must NOT see
# TINYVDB_IO_IMPLEMENTATION -- see the note above.
add_library(tinyvdb_mesh_ops STATIC
    ${TINYVDB_ROOT}/src/tinyvdb_lifecycle.c
    ${TINYVDB_ROOT}/src/tinyvdb_mesh.c
    ${TINYVDB_ROOT}/src/tinyvdb_ops.c
    ${TINYVDB_ROOT}/src/tinyvdb_thread.c
    ${TINYVDB_ROOT}/src/tvdb_memory.c
    # Modules exposed through embind. tinyvdb_sample.c comes first because
    # levelset.c, ray.c and topology.c all call into the sampler.
    ${TINYVDB_ROOT}/src/tinyvdb_sample.c
    ${TINYVDB_ROOT}/src/tinyvdb_levelset.c
    ${TINYVDB_ROOT}/src/tinyvdb_ray.c
    ${TINYVDB_ROOT}/src/tinyvdb_topology.c
    ${TINYVDB_ROOT}/src/tinyvdb_stats.c
    ${TINYVDB_ROOT}/src/tinyvdb_sparse.c
    # tinyvdb_ops.c references tvdb_poisson_solve_core unconditionally, so this
    # one is required even though nothing else pulls it in. wasm-ld only GC'd it
    # away while every Poisson entry point was unbound.
    ${TINYVDB_ROOT}/src/tinyvdb_poisson.c
)
target_include_directories(tinyvdb_mesh_ops PUBLIC ${TINYVDB_ROOT}/src)
target_link_libraries(tinyvdb_mesh_ops PUBLIC tinyvdb_c)
# Force the serial backend of tinyvdb_thread.c. Left to its own detection it
# would pick C11 <threads.h> under Emscripten and either fail to link or pull
# in a pthreads build, which needs SharedArrayBuffer and therefore
# cross-origin isolation. With NONE, tvdb_thread_pool_create() forces a pool of
# 1 and tvdb_thread_pool_for() takes its serial_for() path, so the whole module
# stays single-threaded and the .wasm loads on any static host.
target_compile_definitions(tinyvdb_mesh_ops PRIVATE TINYVDB_THREAD_NONE=1)

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

target_link_libraries(tinyvdb PRIVATE tinyvdb_c tinyvdb_mesh_ops)
target_include_directories(tinyvdb PRIVATE ${TINYVDB_ROOT}/src)

# Emscripten compiles C++ with -fno-exceptions by default, so every `throw` in
# the embind layer degrades to abort(). Enabling real unwinding costs nothing
# here and lets C++ destructors run while a failure propagates; the C sources
# never throw, so this applies to the C++ binding TU only.
#
# KNOWN LIMITATION: embind still does not carry the exception *message* across
# the boundary in this toolchain -- JS catches a bare number. try/catch works
# and the module stays usable afterwards, so treat a caught throw as a generic
# failure. Callers that need to distinguish causes should validate arguments
# before calling (the wrappers do this for shape mismatches, so those are
# rejected deterministically).
target_compile_options(tinyvdb PRIVATE -fexceptions)

# Emscripten link flags
#
# Single-threaded on purpose. The module is served as a plain static file, so
# it must not require COOP/COEP cross-origin isolation headers: no
# USE_PTHREADS, no -pthread, no SharedArrayBuffer. OpenMP is likewise never
# enabled here, so the `#pragma omp` directives in the CPU kernels compile away
# to serial loops. Keep it that way unless the host page is served with
# Cross-Origin-Opener-Policy: same-origin and Cross-Origin-Embedder-Policy:
# require-corp.
target_link_options(tinyvdb PRIVATE
    "SHELL:-s MODULARIZE=1"
    "SHELL:-s EXPORT_NAME='TinyVDB'"
    "SHELL:-s ALLOW_MEMORY_GROWTH=1"
    "SHELL:-s MAXIMUM_MEMORY=1073741824"   # 1 GB
    "SHELL:-s ENVIRONMENT='web,worker,node'"
    "SHELL:-s DISABLE_EXCEPTION_CATCHING=0"
    "SHELL:--bind"
)

# Produce .js + .wasm
set_target_properties(tinyvdb PROPERTIES
    SUFFIX ".js"
    RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}"
)
