cmake_minimum_required(VERSION 3.10)

set(EXAMPLE_TARGET tvdbview)

project(${EXAMPLE_TARGET} C CXX)

option(TVDBVIEW_ENABLE_NFD "Enable native file dialog support" ON)

find_package(OpenGL REQUIRED)
find_program(GLSLANG_VALIDATOR glslangValidator)
find_program(XXD_EXECUTABLE xxd)

set(GLFW_BUILD_EXAMPLES OFF CACHE BOOL "" FORCE)
set(GLFW_BUILD_TESTS OFF CACHE BOOL "" FORCE)
set(GLFW_BUILD_DOCS OFF CACHE BOOL "" FORCE)
set(GLFW_INSTALL OFF CACHE BOOL "" FORCE)
if(NOT TARGET glfw)
  add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/../common/glfw-3.4 glfw)
endif()

set(TVDBVIEW_SOURCES
  main.cc
  ../common/glad/src/glad.c
  ../common/imgui/imgui.cpp
  ../common/imgui/imgui_demo.cpp
  ../common/imgui/imgui_draw.cpp
  ../common/imgui/imgui_tables.cpp
  ../common/imgui/imgui_widgets.cpp
  ../common/imgui/imgui_impl_glfw.cpp
  ../common/imgui/imgui_impl_opengl3.cpp)

set(TVDBVIEW_VULKAN_SPV_INC
    ${CMAKE_CURRENT_BINARY_DIR}/generated_vulkan_pathtrace_spv.inc)
if(GLSLANG_VALIDATOR AND XXD_EXECUTABLE)
  add_custom_command(
    OUTPUT ${TVDBVIEW_VULKAN_SPV_INC}
    COMMAND ${GLSLANG_VALIDATOR} -V
            ${CMAKE_CURRENT_SOURCE_DIR}/vulkan_pathtrace.comp
            -o ${CMAKE_CURRENT_BINARY_DIR}/vulkan_pathtrace.spv
    COMMAND ${XXD_EXECUTABLE} -i
            ${CMAKE_CURRENT_BINARY_DIR}/vulkan_pathtrace.spv
            ${CMAKE_CURRENT_BINARY_DIR}/vulkan_pathtrace_spv.tmp
    COMMAND ${CMAKE_COMMAND}
            -DINPUT=${CMAKE_CURRENT_BINARY_DIR}/vulkan_pathtrace_spv.tmp
            -DOUTPUT=${TVDBVIEW_VULKAN_SPV_INC}
            -P ${CMAKE_CURRENT_SOURCE_DIR}/make_spv_include.cmake
    DEPENDS
      ${CMAKE_CURRENT_SOURCE_DIR}/vulkan_pathtrace.comp
      ${CMAKE_CURRENT_SOURCE_DIR}/make_spv_include.cmake
    VERBATIM)
else()
  configure_file(${CMAKE_CURRENT_SOURCE_DIR}/vulkan_pathtrace_spv.inc
                 ${TVDBVIEW_VULKAN_SPV_INC} COPYONLY)
endif()
set_source_files_properties(${TVDBVIEW_VULKAN_SPV_INC}
  PROPERTIES GENERATED TRUE HEADER_FILE_ONLY TRUE)
list(APPEND TVDBVIEW_SOURCES ${TVDBVIEW_VULKAN_SPV_INC})

add_executable(${EXAMPLE_TARGET} ${TVDBVIEW_SOURCES})
add_custom_target(tvdbview_vulkan_spv DEPENDS ${TVDBVIEW_VULKAN_SPV_INC})
add_dependencies(${EXAMPLE_TARGET} tvdbview_vulkan_spv)
set_target_properties(${EXAMPLE_TARGET} PROPERTIES
  RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})

target_compile_definitions(${EXAMPLE_TARGET} PRIVATE GLFW_INCLUDE_NONE)
target_include_directories(${EXAMPLE_TARGET} PRIVATE
  ${CMAKE_CURRENT_BINARY_DIR}
  ${CMAKE_CURRENT_SOURCE_DIR}/../common/glad/include
  ${CMAKE_CURRENT_SOURCE_DIR}/../common/glfw-3.4/deps
  ${CMAKE_CURRENT_SOURCE_DIR}/../common/imgui)
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
