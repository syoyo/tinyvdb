#include "tinyvdb_thread.h"
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#if defined(TINYVDB_THREAD_C11)
#include <threads.h>
#elif defined(TINYVDB_THREAD_PTHREAD)
#include <pthread.h>
#endif
static int failures;
#define CHECK(c)                                                                                   \
    do {                                                                                           \
        if (!(c)) {                                                                                \
            fprintf(stderr, "FAIL %d: %s\n", __LINE__, #c);                                        \
            ++failures;                                                                            \
        }                                                                                          \
    } while (0)
typedef struct {
    atomic_uint count[1003];
    size_t origin;
    tvdb_thread_pool_t *pool;
    int nested;
} task;
static void visit(size_t begin, size_t end, void *user) {
    task *t = user;
    for (size_t i = begin; i < end; ++i)
        atomic_fetch_add(&t->count[i - t->origin], 1);
}
static void nested(size_t begin, size_t end, void *user) {
    task *t = user;
    for (size_t i = begin; i < end; ++i)
        CHECK(tvdb_thread_pool_for(t->pool, i, i + 1, 1, visit, t, NULL) == TVDB_OK);
}
static void run(task *t) {
    for (unsigned pass = 0; pass < 30; ++pass)
        CHECK(tvdb_thread_pool_for(t->pool, t->origin, t->origin + 1003, 7, visit, t, NULL) ==
              TVDB_OK);
}
#if defined(TINYVDB_THREAD_C11)
static int entry(void *arg) {
    run(arg);
    return 0;
}
#elif defined(TINYVDB_THREAD_PTHREAD)
static void *entry(void *arg) {
    run(arg);
    return NULL;
}
#endif
static void barrier_visit(size_t begin, size_t end, void *user) {
    (void)begin;
    (void)end;
    atomic_uint *entered = user;
    atomic_fetch_add(entered, 1);
    while (atomic_load(entered) < 2) {
    }
}
int main(void) {
    printf("task backend=%s\n", tvdb_thread_backend_name());
    tvdb_thread_pool_t *pool = (void *)1;
    CHECK(tvdb_thread_pool_create(257, &pool, NULL) == TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(!pool);
    CHECK(tvdb_thread_pool_create(1, NULL, NULL) == TVDB_ERROR_INVALID_ARGUMENT);
    for (size_t threads = 1; threads <= 8; threads *= 2) {
        CHECK(tvdb_thread_pool_create(threads, &pool, NULL) == TVDB_OK);
        if (!pool)
            return 1;
        if (threads > 1 && strcmp(tvdb_thread_backend_name(), "none")) {
            atomic_uint entered;
            atomic_init(&entered, 0);
            CHECK(tvdb_thread_pool_for(pool, 0, 2, 1, barrier_visit, &entered, NULL) == TVDB_OK);
            CHECK(atomic_load(&entered) == 2);
        }
        task t;
        memset(&t, 0, sizeof(t));
        for (int i = 0; i < 1003; ++i)
            atomic_init(&t.count[i], 0);
        t.pool = pool;
        t.origin = SIZE_MAX - 1003;
        CHECK(tvdb_thread_pool_for(pool, t.origin, SIZE_MAX, 31, visit, &t, NULL) == TVDB_OK);
        CHECK(tvdb_thread_pool_for(pool, t.origin, SIZE_MAX, 11, nested, &t, NULL) == TVDB_OK);
        run(&t);
        for (int i = 0; i < 1003; ++i)
            CHECK(atomic_load(&t.count[i]) == 32);
        CHECK(tvdb_thread_pool_for(pool, 0, 0, 1, visit, &t, NULL) == TVDB_OK);
        CHECK(tvdb_thread_pool_for(pool, 2, 1, 1, visit, &t, NULL) == TVDB_ERROR_INVALID_ARGUMENT);
        CHECK(tvdb_thread_pool_for(pool, 0, 1, 0, visit, &t, NULL) == TVDB_ERROR_INVALID_ARGUMENT);
        CHECK(tvdb_thread_pool_for(pool, 0, 1, 1, NULL, &t, NULL) == TVDB_ERROR_INVALID_ARGUMENT);
#if defined(TINYVDB_THREAD_C11) || defined(TINYVDB_THREAD_PTHREAD)
        task other;
        memset(&other, 0, sizeof(other));
        for (int i = 0; i < 1003; ++i)
            atomic_init(&other.count[i], 0);
        other.pool = pool;
#if defined(TINYVDB_THREAD_C11)
        thrd_t caller;
        CHECK(thrd_create(&caller, entry, &other) == thrd_success);
        run(&t);
        thrd_join(caller, NULL);
#else
        pthread_t caller;
        CHECK(!pthread_create(&caller, NULL, entry, &other));
        run(&t);
        pthread_join(caller, NULL);
#endif
        for (int i = 0; i < 1003; ++i) {
            CHECK(atomic_load(&other.count[i]) == 30);
            CHECK(atomic_load(&t.count[i]) == 62);
        }
#endif
        tvdb_thread_pool_destroy(pool);
    }
    return failures ? 1 : 0;
}
