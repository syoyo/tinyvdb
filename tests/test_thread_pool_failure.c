/* Real native workers plus deterministic creation/allocation failures. */
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <threads.h>
static size_t allocation_calls, fail_allocation, live, create_calls, fail_create;
static void *fault_calloc(size_t n, size_t size) {
    if (++allocation_calls == fail_allocation)
        return NULL;
    void *p = calloc(n, size);
    if (p)
        ++live;
    return p;
}
static void fault_free(void *p) {
    if (p) {
        --live;
        free(p);
    }
}
static int fault_create(thrd_t *t, thrd_start_t fn, void *arg) {
    if (++create_calls == fail_create)
        return thrd_error;
    return thrd_create(t, fn, arg);
}
#define calloc fault_calloc
#define free fault_free
#define thrd_create fault_create
#include "../src/tinyvdb_thread.c"
#undef calloc
#undef free
#undef thrd_create
static void count(size_t a, size_t b, void *user) {
    atomic_fetch_add((atomic_size_t *)user, b - a);
}
int main(void) {
    for (size_t fail = 1; fail <= 7; ++fail) {
        tvdb_thread_pool_t *pool = (void *)1;
        create_calls = 0;
        fail_create = fail;
        if (tvdb_thread_pool_create(8, &pool, NULL) != TVDB_ERROR_IO || pool || live) {
            fprintf(stderr, "worker failure cleanup failed: %zu\n", fail);
            return 1;
        }
    }
    fail_create = 0;
    for (size_t fail = 1; fail <= 2; ++fail) {
        tvdb_thread_pool_t *pool = (void *)1;
        allocation_calls = 0;
        fail_allocation = fail;
        if (tvdb_thread_pool_create(8, &pool, NULL) != TVDB_ERROR_OUT_OF_MEMORY || pool || live) {
            fprintf(stderr, "allocation cleanup failed\n");
            return 1;
        }
    }
    fail_allocation = 0;
    tvdb_thread_pool_t *pool = NULL;
    atomic_size_t visits;
    atomic_init(&visits, 0);
    if (tvdb_thread_pool_create(8, &pool, NULL) != TVDB_OK)
        return 1;
    if (tvdb_thread_pool_for(pool, 0, 10000, 13, count, &visits, NULL) != TVDB_OK ||
        atomic_load(&visits) != 10000)
        return 1;
    tvdb_thread_pool_destroy(pool);
    return live ? 1 : 0;
}
