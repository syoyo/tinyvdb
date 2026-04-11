set(EXAMPLE_TARGET "vdbdump")

add_executable(${EXAMPLE_TARGET} vdbdump.cc)

target_link_libraries(${EXAMPLE_TARGET} PRIVATE tinyvdb)

set_target_properties(${EXAMPLE_TARGET} PROPERTIES
  RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")
