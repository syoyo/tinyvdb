add_executable(nanovdbdump nanovdbdump.c)
# Keep the math runtime dependency platform-aware: Unix uses libm, while
# Windows provides these functions through the C runtime.
target_link_libraries(nanovdbdump PRIVATE tinyvdb_nanovdb tinyvdb_math)
