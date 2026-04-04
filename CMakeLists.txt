cmake_minimum_required(VERSION 3.5)

project(tinyvdbio C CXX)

# options
option(TINYVDBIO_USE_CCACHE "Use ccache for faster recompile." ON)
option(TINYVDBIO_BUILD_TESTS "Build tests" OFF)
option(TINYVDBIO_BUILD_EXAMPLES "Build examples" ON)
option(TINYVDBIO_USE_BLOSC "Build with BLOSC compression support" ON)
option(TINYVDBIO_USE_SYSTEM_ZLIB "Use system zlib instead of bundled miniz" OFF)

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
if(TINYVDBIO_USE_CCACHE)
  if(NOT MSVC)
    find_program(CCACHE_EXE ccache)
    if(CCACHE_EXE)
      message(STATUS "Using ccache: ${CCACHE_EXE}")
      set(CMAKE_C_COMPILER_LAUNCHER "${CCACHE_EXE}")
      set(CMAKE_CXX_COMPILER_LAUNCHER "${CCACHE_EXE}")
    endif()
  endif()
endif()

# Header-only library as INTERFACE target
add_library(tinyvdbio INTERFACE)
target_include_directories(tinyvdbio INTERFACE ${PROJECT_SOURCE_DIR}/src)

# miniz (bundled C source, needed by implementations that #define
# TINYVDBIO_IMPLEMENTATION)
if(NOT TINYVDBIO_USE_SYSTEM_ZLIB)
  add_library(tinyvdbio_miniz STATIC ${PROJECT_SOURCE_DIR}/src/miniz.c)
  target_include_directories(tinyvdbio_miniz PUBLIC ${PROJECT_SOURCE_DIR}/src)
  target_compile_definitions(tinyvdbio_miniz PRIVATE MINIZ_NO_STDIO)
  target_link_libraries(tinyvdbio INTERFACE tinyvdbio_miniz)
endif()

# Force system zlib for iOS
if(IOS)
  set(TINYVDBIO_USE_SYSTEM_ZLIB ON CACHE INTERNAL "" FORCE)
endif()

if(TINYVDBIO_USE_SYSTEM_ZLIB)
  find_package(ZLIB REQUIRED)
  target_link_libraries(tinyvdbio INTERFACE ZLIB::ZLIB)
  target_compile_definitions(tinyvdbio INTERFACE TVDB_USE_SYSTEM_ZLIB)
endif()

# BLOSC (c-blosc2)
if(TINYVDBIO_USE_BLOSC)
  function(add_blosc2_lib)
    set(BUILD_TESTS OFF CACHE INTERNAL "" FORCE)
    set(BUILD_FUZZERS OFF CACHE INTERNAL "" FORCE)
    set(BUILD_BENCHMARKS OFF CACHE INTERNAL "" FORCE)
    set(BUILD_EXAMPLES OFF CACHE INTERNAL "" FORCE)
    set(BUILD_PLUGINS OFF CACHE INTERNAL "" FORCE)
    set(BUILD_SHARED OFF CACHE INTERNAL "" FORCE)
    set(BUILD_STATIC ON CACHE INTERNAL "" FORCE)
    set(DEACTIVATE_AVX2 OFF CACHE INTERNAL "" FORCE)
    set(DEACTIVATE_ZSTD ON CACHE INTERNAL "" FORCE)
    if(IOS)
      set(DEACTIVATE_ZLIB ON CACHE INTERNAL "" FORCE)
    endif()
    # blosc2 needs POSIX extensions (pthread_barrier_*) — allow C extensions
    # within the blosc2 subdirectory scope
    set(CMAKE_C_EXTENSIONS ON)
    add_subdirectory(${PROJECT_SOURCE_DIR}/third_party/c-blosc2)
  endfunction()

  add_blosc2_lib()

  target_link_libraries(tinyvdbio INTERFACE blosc2_static)
  target_include_directories(tinyvdbio INTERFACE
    ${PROJECT_SOURCE_DIR}/third_party/c-blosc2/include)
  target_compile_definitions(tinyvdbio INTERFACE TVDB_USE_BLOSC)
endif()

# Examples
if(TINYVDBIO_BUILD_EXAMPLES)
  add_subdirectory(examples/vdbdump)
endif()

# [VisualStudio]
if(WIN32)
  set_property(DIRECTORY PROPERTY VS_STARTUP_PROJECT tinyvdbio)
endif()
