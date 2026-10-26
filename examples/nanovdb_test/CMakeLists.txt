cmake_minimum_required(VERSION 3.10)
project(nanovdb_test C)


add_executable(test_roundtrip test_roundtrip.c)

target_include_directories(test_roundtrip PRIVATE
    ${PROJECT_SOURCE_DIR}/../src
)

target_link_libraries(test_roundtrip tinyvdb_nanovdb tinyvdb_mesh_ops m)
