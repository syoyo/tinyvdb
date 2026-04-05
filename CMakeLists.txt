cmake_minimum_required(VERSION 3.5)

project(tinyvdbio C CXX)

# options
option(TINYVDBIO_USE_CCACHE "Use ccache for faster recompile." ON)
option(TINYVDBIO_BUILD_TESTS "Build tests" OFF)
option(TINYVDBIO_BUILD_EXAMPLES "Build examples" ON)
option(TINYVDBIO_USE_SYSTEM_ZLIB "Use system zlib instead of bundled miniz" OFF)
option(TINYVDBIO_BUILD_VDBRENDER "Build vdbrender volume path tracer example" ON)

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

# tinyvdbio static library (C11 implementation + miniz + lz4)
set(TINYVDBIO_C_SOURCES
  ${PROJECT_SOURCE_DIR}/src/tinyvdbio.c
  ${PROJECT_SOURCE_DIR}/src/lz4.c)
if(NOT TINYVDBIO_USE_SYSTEM_ZLIB)
  list(APPEND TINYVDBIO_C_SOURCES ${PROJECT_SOURCE_DIR}/src/miniz.c)
endif()

add_library(tinyvdbio STATIC ${TINYVDBIO_C_SOURCES})
target_include_directories(tinyvdbio PUBLIC ${PROJECT_SOURCE_DIR}/src)
target_compile_definitions(tinyvdbio PRIVATE TINYVDBIO_IMPLEMENTATION MINIZ_NO_STDIO)

# Force system zlib for iOS
if(IOS)
  set(TINYVDBIO_USE_SYSTEM_ZLIB ON CACHE INTERNAL "" FORCE)
endif()

if(TINYVDBIO_USE_SYSTEM_ZLIB)
  find_package(ZLIB REQUIRED)
  target_link_libraries(tinyvdbio PUBLIC ZLIB::ZLIB)
  target_compile_definitions(tinyvdbio PUBLIC TVDB_USE_SYSTEM_ZLIB)
endif()

# Examples
if(TINYVDBIO_BUILD_EXAMPLES)
  add_subdirectory(examples/vdbdump)
endif()

# vdbrender (volume path tracer)
if(TINYVDBIO_BUILD_VDBRENDER)
  add_subdirectory(examples/vdbrender)
endif()

# [VisualStudio]
if(WIN32)
  set_property(DIRECTORY PROPERTY VS_STARTUP_PROJECT tinyvdbio)
endif()
