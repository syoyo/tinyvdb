/* Override only maintenance-owned heap allocation, including clone callbacks.
 * The sanitizer run checks leaks from failed partial clones. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static size_t calls, fail_at;
static void *fault_malloc(size_t n) { return ++calls == fail_at ? NULL : malloc(n); }
static void *fault_calloc(size_t n, size_t s) { return ++calls == fail_at ? NULL : calloc(n, s); }
static void *fault_realloc(void *p, size_t n) { return ++calls == fail_at ? NULL : realloc(p, n); }
#define malloc fault_malloc
#define calloc fault_calloc
#define realloc fault_realloc
#include "../src/tinyvdb_tree.c"
#undef malloc
#undef calloc
#undef realloc
#define CHECK(x)                                                                                   \
    do {                                                                                           \
        if (!(x)) {                                                                                \
            fprintf(stderr, "line %d fail_at=%zu: %s\n", __LINE__, fail_at, #x);                   \
            return 1;                                                                              \
        }                                                                                          \
    } while (0)
int main(int argc, char **argv) {
    tvdb_file_t f = {0};
    tvdb_error_t err = {0};
    CHECK(tvdb_file_open(&f, argv[1], NULL, &err) == TVDB_OK);
    CHECK(tvdb_read_all_grids(&f, &err) == TVDB_OK);
    tvdb_sparse_grid sg = {0};
    CHECK(tvdb_sparse_grid_reserve(&sg, 513));
    for (int x = 0; x < 8; ++x)
        for (int y = 0; y < 8; ++y)
            for (int z = 0; z < 8; ++z) {
                sg.coords[sg.count] = (tvdb_vec3i){x, y, z};
                sg.values[sg.count++] = 1;
            }
    sg.coords[sg.count] = (tvdb_vec3i){8, 0, 0};
    sg.values[sg.count++] = 2;
    tvdb_grid_t compact_source = {0};
    CHECK(tvdb_grid_from_sparse_using_template(f.grids, &sg, "compact", 0, &compact_source));
    tvdb_sparse_grid_free(&sg);
    for (int op = 0; op < 3; ++op) {
        const tvdb_grid_t *source = op == 2 ? &compact_source : f.grids;
        tvdb_grid_t out = {0};
        calls = 0;
        fail_at = 0;
        tvdb_status_t st = op == 1 ? tvdb_grid_signed_flood_fill(source, 3, -3, &out, &err)
                                   : tvdb_grid_prune(source, &out, &err);
        CHECK(st == TVDB_OK);
        size_t total = calls;
        tvdb_grid_destroy_owned(&out);
        for (size_t n = 1; n <= total; ++n) {
            /* A live destination must survive every failed allocation. */
            tvdb_vec3i c = {0, 0, 0};
            float v = 123;
            tvdb_sparse_grid sg = {&c, &v, 1, 0, 1, 0, 0, 0};
            CHECK(tvdb_grid_from_sparse_using_template(f.grids, &sg, "keep", 10, &out));
            tvdb_grid_t before = out;
            calls = 0;
            fail_at = n;
            st = op == 1 ? tvdb_grid_signed_flood_fill(source, 3, -3, &out, &err)
                         : tvdb_grid_prune(source, &out, &err);
            CHECK(st == TVDB_ERROR_OUT_OF_MEMORY);
            CHECK(!memcmp(&before, &out, sizeof(out)));
            fail_at = 0;
            tvdb_grid_destroy_owned(&out);
        }
        printf("%s: %zu allocation failures checked\n",
               op == 1   ? "flood fill"
               : op == 2 ? "prune compaction"
                         : "prune",
               total);
    }
    fail_at = 0;
    tvdb_grid_destroy_owned(&compact_source);
    tvdb_file_close(&f);
    (void)argc;
    return 0;
}
