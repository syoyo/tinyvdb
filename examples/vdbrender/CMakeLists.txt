set(EXAMPLE_TARGET "vdbrender")

add_executable(${EXAMPLE_TARGET} vdbrender.cc)

target_link_libraries(${EXAMPLE_TARGET} PRIVATE tinyvdb)

# tinyexr (header-only)
target_include_directories(${EXAMPLE_TARGET} PRIVATE
  ${PROJECT_SOURCE_DIR}/third_party/tinyexr)

# OpenMP (optional, for parallel rendering)
find_package(OpenMP QUIET)
if(OpenMP_CXX_FOUND)
  target_link_libraries(${EXAMPLE_TARGET} PRIVATE OpenMP::OpenMP_CXX)
endif()

set_target_properties(${EXAMPLE_TARGET} PROPERTIES
  RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")
