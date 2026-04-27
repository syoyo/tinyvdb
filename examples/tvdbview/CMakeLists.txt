cmake_minimum_required(VERSION 3.10)

set(EXAMPLE_TARGET tvdbview)

project(${EXAMPLE_TARGET} C CXX)

option(TVDBVIEW_ENABLE_NFD "Enable native file dialog support" ON)

find_package(OpenGL REQUIRED)

set(GLFW_BUILD_EXAMPLES OFF CACHE BOOL "" FORCE)
set(GLFW_BUILD_TESTS OFF CACHE BOOL "" FORCE)
set(GLFW_BUILD_DOCS OFF CACHE BOOL "" FORCE)
set(GLFW_INSTALL OFF CACHE BOOL "" FORCE)
if(NOT TARGET glfw)
  add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/../common/glfw-3.4 glfw)
endif()

set(TVDBVIEW_SOURCES
  main.cc
  ../common/glad/src/glad.c)

add_executable(${EXAMPLE_TARGET} ${TVDBVIEW_SOURCES})
set_target_properties(${EXAMPLE_TARGET} PROPERTIES
  RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})

target_compile_definitions(${EXAMPLE_TARGET} PRIVATE GLFW_INCLUDE_NONE)
target_include_directories(${EXAMPLE_TARGET} PRIVATE
  ${CMAKE_CURRENT_SOURCE_DIR}/../common/glad/include)
target_link_libraries(${EXAMPLE_TARGET} PRIVATE
  tinyvdb
  glfw
  ${OPENGL_LIBRARIES}
  ${CMAKE_DL_LIBS})

if(TVDBVIEW_ENABLE_NFD)
  set(NFD_BUILD_TESTS OFF CACHE BOOL "" FORCE)
  set(NFD_BUILD_SDL2_TESTS OFF CACHE BOOL "" FORCE)
  set(NFD_BUILD_GLFW3_TESTS OFF CACHE BOOL "" FORCE)
  set(NFD_INSTALL OFF CACHE BOOL "" FORCE)
  set(NFD_PORTAL OFF CACHE BOOL "" FORCE)
  set(NFD_X11 ON CACHE BOOL "" FORCE)
  set(NFD_WAYLAND OFF CACHE BOOL "" FORCE)
  if(NOT TARGET nfd)
    add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/../common/nativefiledialog-extended nfd)
  endif()
  target_link_libraries(${EXAMPLE_TARGET} PRIVATE nfd)
  target_compile_definitions(${EXAMPLE_TARGET} PRIVATE TVDBVIEW_ENABLE_NFD=1)
endif()

if(MSVC)
  target_compile_options(${EXAMPLE_TARGET} PRIVATE /W3)
else()
  target_compile_options(${EXAMPLE_TARGET} PRIVATE -Wall -Wextra)
endif()
