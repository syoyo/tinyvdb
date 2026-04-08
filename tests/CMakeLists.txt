# Unit test: open + read VDB files using the C11 API
add_executable(test_read_vdb test_read_vdb.c)
target_link_libraries(test_read_vdb PRIVATE tinyvdbio)

# Register one CTest per data file
file(GLOB VDB_DATA_FILES "${PROJECT_SOURCE_DIR}/data/*.vdb")
foreach(vdb ${VDB_DATA_FILES})
  get_filename_component(vdb_name ${vdb} NAME_WE)
  add_test(NAME read_${vdb_name} COMMAND test_read_vdb "${vdb}")
endforeach()
