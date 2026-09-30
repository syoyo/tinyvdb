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
#include "../src/tinyvdb_poisson.c"
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
    tvdb_dense_grid dense = {0}; dense.nx = dense.ny = dense.nz = 2; dense.data = data; dense.voxel_size=1;
    for (int at = 1; at <= 2; ++at) {
        allocation_count = 0; fail_at = at;
        tvdb_median_filter(&dense, 1, 3);
        if (memcmp(data, saved, sizeof(data)) != 0 || live_allocations != 0) failed = 1;
    }
    /* The projected solver allocates before touching the caller's solution. */
    float rhsdata[8]={1,-1,0,0,0,0,0,0}; tvdb_dense_grid rhs=dense; rhs.data=rhsdata;
    tvdb_poisson_result_t info; tvdb_error_t err;
    allocation_count=0; fail_at=1;
    if(tvdb_solve_poisson_ex(&rhs,&dense,10,1e-4f,&info,&err)!=TVDB_ERROR_OUT_OF_MEMORY ||
       memcmp(data,saved,sizeof(data)) || live_allocations) failed=1;
    allocation_count=0; fail_at=1;
    tvdb_dense_grid_d converted;
    tvdb_dense_grid_f_to_d(&dense,&converted);
    if(converted.data || converted.nx || converted.ny || converted.nz || live_allocations) failed=1;
    allocation_count=0; fail_at=1; tvdb_laplacian(&dense,&dense);
    if(memcmp(data,saved,sizeof(data)) || live_allocations) failed=1;
    /* In-place sparse convolution must also be transactional on every allocation. */
    fail_at=0; allocation_count=0; tvdb_sparse_grid_init(&g);
    if(!tvdb_sparse_grid_reserve(&g,1)) return 1;
    g.count=1; g.coords[0]=(tvdb_vec3i){0,0,0}; g.values[0]=42;
    float kernel=1;
    tvdb_sparse_grid probe; tvdb_sparse_grid_init(&probe);
    allocation_count=0;
    if(!tvdb_sparse_conv3d(&g,&kernel,1,1,1,0,&probe)) return 1;
    int conv_allocations=allocation_count; tvdb_sparse_grid_free(&probe);
    for(int at=1;at<=conv_allocations;++at) {
      fail_at=at; allocation_count=0; tvdb_vec3i* coords=g.coords; float* values=g.values;
      if(tvdb_sparse_conv3d(&g,&kernel,1,1,1,0,&g) || g.coords!=coords || g.values!=values ||
         g.count!=1 || g.values[0]!=42 || live_allocations!=2) failed=1;
    }
    fail_at=0; tvdb_sparse_grid_free(&g);
    if (failed) fprintf(stderr, "allocation failure changed grid state\n");
    return failed;
}
