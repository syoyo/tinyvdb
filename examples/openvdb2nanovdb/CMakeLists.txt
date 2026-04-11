cmake_minimum_required(VERSION 3.5)

set(BUILD_TARGET "openvdb2nanovdb")

project(${BUILD_TARGET} C CXX)

# options
option(OPENVDB2NANOVDB_USE_CCACHE "Use ccache for faster recompile." ON)
option(OPENVDB2NANOVDB_WITH_BLOSC "Enable BLOSC." ON)
option(OPENVDB2NANOVDB_WITH_SYSTEM_ZLIB "Use system zlib." OFF)

if (OPENVDB2NANOVDB_WITH_SYSTEM_ZLIB)
  find_package(ZLIB REQUIRED)
endif (OPENVDB2NANOVDB_WITH_SYSTEM_ZLIB)

# cmake modules
list(APPEND CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/../common/cmake)
# list(APPEND CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake/sanitizers)
find_package(Sanitizers) # Address sanitizer (-DSANITIZE_ADDRESS=ON)
set(CMAKE_CXX_STANDARD 11)

# [ccache]
if(OPENVDB2NANOVDB_USE_CCACHE)
  if(MSVC)
    # No ccache support
  else()
    find_program(CCACHE_EXE ccache)
    if(CCACHE_EXE)

      message(STATUS "Use ccache : " ${CCACHE_EXE})
      # CMAKE_C_COMPILER_LAUNCHER = available from cmake 3.4+)
      if(CMAKE_C_COMPILER_LAUNCHER)
        set(CMAKE_C_COMPILER_LAUNCHER "${CMAKE_C_COMPILER_LAUNCHER}"
                                      "${CCACHE_EXE}")
      else()
        set(CMAKE_C_COMPILER_LAUNCHER "${CCACHE_EXE}")
      endif()

      if(CMAKE_CXX_COMPILER_LAUNCHER)
        set(CMAKE_CXX_COMPILER_LAUNCHER "${CMAKE_CXX_COMPILER_LAUNCHER}"
                                        "${CCACHE_EXE}")
      else()
        set(CMAKE_CXX_COMPILER_LAUNCHER "${CCACHE_EXE}")
      endif()

    endif(CCACHE_EXE)
  endif()
endif()

set(NANOVDB_BUILD_TOOLS OFF CACHE INTERNAL "" FORCE)
add_subdirectory(${PROJECT_SOURCE_DIR}/../../nanovdb nanovdb)


set(OPENVDB2NANOVDB_SOURCES
    openvdb2nanovdb.cc
    )

set(OPENVDB2NANOVDB_DEP_SOURCES
    )


add_executable(${BUILD_TARGET} ${OPENVDB2NANOVDB_SOURCES} ${OPENVDB2NANOVDB_DEP_SOURCES} ${OPENVDB2NANOVDB_GUI_SOURCES})
add_sanitizers(${BUILD_TARGET})

# [tinyvdb]
target_include_directories(${BUILD_TARGET} PRIVATE ${PROJECT_SOURCE_DIR}/../../)

target_include_directories(${BUILD_TARGET} PRIVATE ${PROJECT_SOURCE_DIR})

if (OPENVDB2NANOVDB_WITH_SYSTEM_ZLIB)
  target_compile_definitions(${BUILD_TARGET} PRIVATE TINYVDB_IO_USE_SYSTEM_ZLIB=1)
  target_link_libraries(${BUILD_TARGET} ${ZLIB_LIBRARIES})
else (OPENVDB2NANOVDB_WITH_SYSTEM_ZLIB)
  # Assume miniz is available at ../../
  target_include_directories(${BUILD_TARGET} PRIVATE "${PROJECT_SOURCE_DIR}/../../")
  list(APPEND OPENVDB2NANOVDB_DEP_SOURCES ../../miniz.c)

endif (OPENVDB2NANOVDB_WITH_SYSTEM_ZLIB)

# Increase warning level for clang.
IF (CMAKE_CXX_COMPILER_ID MATCHES "Clang")
    set_source_files_properties(${OPENVDB2NANOVDB_SOURCES} PROPERTIES COMPILE_FLAGS "-Weverything -Wno-system-headers -Werror -Wno-padded -Wno-c++98-compat-pedantic -Wno-documentation -Wno-documentation-unknown-command -Wno-reserved-id-macro -Wno-unused-variable -Wno-unused-function")
ENDIF ()


# [VisualStudio]
if(WIN32)
  # Set ${BUILD_TARGET} as a startup project for VS IDE
  set_property(DIRECTORY PROPERTY VS_STARTUP_PROJECT ${BUILD_TARGET})

  # For easier debugging in VS IDE(cmake 3.8.0 or later required) Set working
  # directory to ${BUILD_TARGET} git repo root.
  if(CMAKE_VERSION VERSION_GREATER 3.8.0)
    set_target_properties(${BUILD_TARGET}
                          PROPERTIES VS_DEBUGGER_WORKING_DIRECTORY
                                     "${CMAKE_CURRENT_SOURCE_DIR}")
  endif()
endif()
