cmake_minimum_required(VERSION 3.10)
project(nanovdb_test CXX)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_executable(test_roundtrip test_roundtrip.cc)

target_include_directories(test_roundtrip PRIVATE
    ${PROJECT_SOURCE_DIR}/../src
)

target_link_libraries(test_roundtrip tinyvdb_nanovdb)
