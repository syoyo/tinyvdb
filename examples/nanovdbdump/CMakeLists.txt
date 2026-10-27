add_executable(nanovdbdump nanovdbdump.c)
# libm is explicit now: this is a C target, and the C++ driver used to supply
# it implicitly (tinyvdb_nanovdb.c calls fmax/fmin).
target_link_libraries(nanovdbdump PRIVATE tinyvdb_nanovdb m)
