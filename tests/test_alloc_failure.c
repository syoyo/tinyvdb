/* Compile private implementations with failing allocators; no production hooks. */
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
static int allocation_count, fail_at, live_allocations;
static void *failing_malloc(size_t n) {
    int call;
    #pragma omp atomic capture
    call = ++allocation_count;
    void *ptr = call == fail_at ? NULL : malloc(n);
    if (ptr) {
        #pragma omp atomic update
        ++live_allocations;
    }
    return ptr;
}
static void *failing_calloc(size_t n, size_t size) {
    int call;
    #pragma omp atomic capture
    call = ++allocation_count;
    void *ptr = call == fail_at ? NULL : calloc(n, size);
    if (ptr) {
        #pragma omp atomic update
        ++live_allocations;
    }
    return ptr;
}
static void tracking_free(void *ptr) {
    if (ptr) {
        #pragma omp atomic update
        --live_allocations;
    }
    free(ptr);
}
#define free tracking_free
#define malloc failing_malloc
#define calloc failing_calloc
#include "../src/tinyvdb_sparse.c"
#include "../src/tinyvdb_ops.c"
#undef malloc
#undef calloc
#undef free

int main(void) {
    int failed = 0;
    tvdb_sparse_grid g; tvdb_sparse_grid_init(&g);
    fail_at = 0;
    if (!tvdb_sparse_grid_reserve(&g, 1)) return 1;
    g.count = 1; g.coords[0] = (tvdb_vec3i){1,2,3}; g.values[0] = 42;
    for (int at = 1; at <= 2; ++at) {
        allocation_count = 0; fail_at = at;
        tvdb_vec3i *coords = g.coords; float *values = g.values;
        if (tvdb_sparse_grid_reserve(&g, 2) || g.coords != coords || g.values != values ||
            g.capacity != 1 || g.count != 1 || g.values[0] != 42 || live_allocations != 2) failed = 1;
    }
    tvdb_sparse_grid_free(&g);
    if (live_allocations != 0) failed = 1;
    float data[8] = {7,6,5,4,3,2,1,0}, saved[8]; memcpy(saved, data, sizeof(data));
    tvdb_dense_grid dense = {0}; dense.nx = dense.ny = dense.nz = 2; dense.data = data;
    for (int at = 1; at <= 2; ++at) {
        allocation_count = 0; fail_at = at;
        tvdb_median_filter(&dense, 1, 3);
        if (memcmp(data, saved, sizeof(data)) != 0 || live_allocations != 0) failed = 1;
    }
    if (failed) fprintf(stderr, "allocation failure changed grid state\n");
    return failed;
}
