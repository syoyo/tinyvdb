/* Exercise metadata ownership independently of the system leak detector. */
#define _POSIX_C_SOURCE 200809L
#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_io.h"
#include "tinyvdb_sparse_tree.h"
#include <stdio.h>
#include <stdlib.h>

typedef struct { size_t live; int calls, fail; } tracker;
static void *tracked_alloc(size_t n, void *ctx) {
    tracker *t = ctx;
    if (++t->calls == t->fail) return NULL;
    void *p = malloc(n);
    if (p) ++t->live;
    return p;
}
static void *tracked_realloc(void *p, size_t old, size_t n, void *ctx) {
    tracker *t = ctx; (void)old;
    if (++t->calls == t->fail) return NULL;
    int was_null = p == NULL;
    void *q = realloc(p, n);
    if (q && was_null) ++t->live;
    return q;
}
static void tracked_free(void *p, size_t n, void *ctx) {
    tracker *t = ctx; (void)n;
    if (p) { --t->live; free(p); }
}

int main(int argc, char **argv) {
    /* One string-valued metadata entry: name="n", type="string", value="v". */
    static const uint8_t bytes[] = {
        1,0,0,0, 1,0,0,0,'n', 6,0,0,0,'s','t','r','i','n','g',
        1,0,0,0,'v'
    };
    int failures = 0;
    for (size_t len = 0; len <= sizeof(bytes); ++len) {
        for (int fail = 0; fail <= 4; ++fail) {
            tracker t = {0}; t.fail = fail;
            tvdb_allocator_t a = {tracked_alloc, tracked_realloc, tracked_free, &t};
            tvdb_metadata_t meta; tvdb__metadata_init(&meta, &a);
            tvdb__sr_t sr; tvdb__sr_init(&sr, bytes, len, 0);
            tvdb_error_t err = {0};
            tvdb_status_t st = tvdb__read_meta(&sr, &meta, &a, &err);
            if ((len < sizeof(bytes) || fail) && st == TVDB_OK) ++failures;
            if (len == sizeof(bytes) && !fail &&
                (st != TVDB_OK || meta.count != 1 || strcmp(meta.entries[0].value.u.s.str,"v"))) ++failures;
            tvdb__metadata_destroy(&meta);
            if (t.live) { fprintf(stderr,"metadata leak: length=%zu failure=%d live=%zu\n",len,fail,t.live); ++failures; }
        }
    }
    /* The malloc-owned wrapper must also release attached, allocator-owned metadata. */
    tracker t = {0};
    tvdb_allocator_t a = {tracked_alloc, tracked_realloc, tracked_free, &t};
    tvdb_grid_t grid = {0};
    tvdb__metadata_init(&grid.metadata, &a);
    tvdb__sr_t sr; tvdb__sr_init(&sr, bytes, sizeof(bytes), 0);
    tvdb_error_t err = {0};
    if (tvdb__read_meta(&sr, &grid.metadata, &a, &err) != TVDB_OK) return 1;
    tvdb_grid_destroy_owned(&grid);
    tvdb_grid_destroy_owned(&grid);
    if (t.live) { fprintf(stderr,"owned grid leaked %zu metadata allocations\n",t.live); ++failures; }
    /* Repeated reads replace independent payloads; a failed reload preserves
       existing grids, and frees every partially loaded allocation. */
    if (argc > 1) {
        tracker rt = {0};
        tvdb_allocator_t ra = {tracked_alloc, tracked_realloc, tracked_free, &rt};
        tvdb_file_t file = {0};
        if (tvdb_file_open(&file, argv[1], &ra, &err) != TVDB_OK ||
            tvdb_read_all_grids(&file, &err) != TVDB_OK) return 1;
        size_t loaded_live = rt.live;
        for (int pass = 0; pass < 3; ++pass) {
            tvdb_tree_node_t *prior = file.grids[0].tree.nodes;
            if (tvdb_read_all_grids(&file, &err) != TVDB_OK ||
                file.grids[0].tree.nodes == prior || rt.live != loaded_live) ++failures;
        }
        tvdb_tree_node_t *prior = file.grids[0].tree.nodes;
        rt.fail = rt.calls + 1;
        if (tvdb_read_all_grids(&file, &err) == TVDB_OK ||
            file.grids[0].tree.nodes != prior || rt.live != loaded_live) ++failures;
        rt.fail = 0;
        tvdb_file_close(&file);
        if (rt.live) { fprintf(stderr,"reload leaked %zu allocations\n",rt.live); ++failures; }
    }
    return failures ? 1 : 0;
}
