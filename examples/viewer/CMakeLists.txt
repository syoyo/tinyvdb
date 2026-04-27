cmake_minimum_required(VERSION 3.5)

set(BUILD_TARGET "tvdb_view")

project(${BUILD_TARGET} C CXX)

# options
option(TVDB_VIEWER_USE_CCACHE "Use ccache for faster recompile." ON)
option(TVDB_VIEWER_WITH_BLOSC "Enable BLOSC." ON)
option(TVDB_VIEWER_WITH_SYSTEM_ZLIB "Use system zlib." OFF)

if (TVDB_VIEWER_WITH_SYSTEM_ZLIB)
  find_package(ZLIB REQUIRED)
endif (TVDB_VIEWER_WITH_SYSTEM_ZLIB)

# cmake modules
list(APPEND CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/../common/cmake)
# list(APPEND CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake/sanitizers)
find_package(Sanitizers) # Address sanitizer (-DSANITIZE_ADDRESS=ON)
set(CMAKE_CXX_STANDARD 11)

# [ccache]
if(TVDB_VIEWER_USE_CCACHE)
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

find_package(OpenGL REQUIRED)

# [glfw3]
set(GLFW_BUILD_EXAMPLES OFF CACHE INTERNAL "" FORCE)
set(GLFW_BUILD_TESTS OFF CACHE INTERNAL "" FORCE)
set(GLFW_BUILD_DOCS OFF CACHE INTERNAL "" FORCE)
set(GLFW_INSTALL OFF CACHE INTERNAL "" FORCE)
add_subdirectory(${PROJECT_SOURCE_DIR}/../common/glfw-3.4 glfw)

if (SANITIZE_ADDRESS)
  set(EMBREE_ADDRESS_SANITIZER On CACHE INTERNAL "" FORCE)
  message(STATUS "Enable ASAN for Embree3")
endif ()

set(TVDB_VIEWER_SOURCES
    main.cc
    )

set(TVDB_VIEWER_DEP_SOURCES
    )

set(TVDB_VIEWER_GUI_SOURCES
    ../common/trackball.cc
    ../common/glad/src/glad.c
    ../common/imgui/imgui.cpp
    ../common/imgui/imgui_draw.cpp
    ../common/imgui/imgui_tables.cpp
    ../common/imgui/imgui_widgets.cpp
    ../common/imgui/imgui_impl_opengl3.cpp
    ../common/imgui/imgui_impl_glfw.cpp
  )

add_executable(${BUILD_TARGET} ${TVDB_VIEWER_SOURCES} ${TVDB_VIEWER_DEP_SOURCES} ${TVDB_VIEWER_GUI_SOURCES})
add_sanitizers(${BUILD_TARGET})

# [tinyvdb]
target_include_directories(${BUILD_TARGET} PRIVATE ${PROJECT_SOURCE_DIR}/../../)

target_include_directories(${BUILD_TARGET} PRIVATE ${PROJECT_SOURCE_DIR})

# [imgui]
target_include_directories(${BUILD_TARGET} PRIVATE "${PROJECT_SOURCE_DIR}/../common/")

# [glad]
add_definitions("-DIMGUI_IMPL_OPENGL_LOADER_GLAD")
target_include_directories(${BUILD_TARGET} PRIVATE "${PROJECT_SOURCE_DIR}/../common/glad/include")

target_include_directories(${BUILD_TARGET} PRIVATE ${glfw_INCLUDE_DIRS} ${BLOSC_INCDIR})
target_link_libraries(${BUILD_TARGET} ${TVDB_VIEWER_EXT_LIBRARIES} ${BLOSC_LIBRARY} glfw ${OPENGL_LIBRARIES} ${CMAKE_DL_LIBS})

if (TVDB_VIEWER_WITH_SYSTEM_ZLIB)
  target_compile_definitions(${BUILD_TARGET} PRIVATE TINYVDB_IO_USE_SYSTEM_ZLIB=1)
  target_link_libraries(${BUILD_TARGET} ${ZLIB_LIBRARIES})
else (TVDB_VIEWER_WITH_SYSTEM_ZLIB)
  # Assume miniz is available at ../../
  target_include_directories(${BUILD_TARGET} PRIVATE "${PROJECT_SOURCE_DIR}/../../")
  list(APPEND TVDB_VIEWER_DEP_SOURCES ../../miniz.c)

endif (TVDB_VIEWER_WITH_SYSTEM_ZLIB)

# Increase warning level for clang.
IF (CMAKE_CXX_COMPILER_ID MATCHES "Clang")
    set_source_files_properties(${TVDB_VIEWER_SOURCES} PROPERTIES COMPILE_FLAGS "-Weverything -Wno-system-headers -Werror -Wno-padded -Wno-c++98-compat-pedantic -Wno-documentation -Wno-documentation-unknown-command -Wno-reserved-id-macro -Wno-unused-variable -Wno-unused-function")
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
