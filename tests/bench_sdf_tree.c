#define _POSIX_C_SOURCE 200809L
#include "sdf_tree_fixture.h"
#include "tinyvdb_ops.h"
#include <stdio.h>
#include <time.h>
static double seconds(void) {
    struct timespec t;
    timespec_get(&t, TIME_UTC);
    return t.tv_sec + t.tv_nsec * 1e-9;
}
static void restore(tvdb_grid_t *g, const float *saved) {
    size_t at = 0;
    for (size_t i = 0; i < g->tree.num_nodes; ++i)
        if (g->tree.nodes[i].type == TVDB_NODE_LEAF) {
            memcpy(g->tree.nodes[i].u.leaf.data, saved + at, 512 * 4);
            at += 512;
        }
}
static int run(int n, int narrow, size_t threads) {
    tvdb_grid_t g = {0};
    if (!sdf_fixture_cube(&g, n, 1, narrow))
        return 1;
    size_t leaves = 0;
    for (size_t i = 0; i < g.tree.num_nodes; ++i)
        leaves += g.tree.nodes[i].type == TVDB_NODE_LEAF;
    float *saved = malloc(leaves * 512 * 4);
    size_t at = 0;
    if (!saved)
        return 1;
    for (size_t i = 0; i < g.tree.num_nodes; ++i)
        if (g.tree.nodes[i].type == TVDB_NODE_LEAF) {
            memcpy(saved + at, g.tree.nodes[i].u.leaf.data, 512 * 4);
            at += 512;
        }
    tvdb_thread_pool_t *pool = NULL;
    tvdb_sdf_tree_t *w = NULL;
    tvdb_error_t err = {0};
    if ((threads && tvdb_thread_pool_create(threads, &pool, &err) != TVDB_OK) ||
        tvdb_sdf_tree_create(&g, pool, NULL, &w, &err) != TVDB_OK) {
        fprintf(stderr, "%s\n", err.message);
        return 1;
    }
    tvdb_sdf_sweep_result_t r = {0};
    tvdb_sdf_tree_info_t sweep_info = {0};
    double sweep = 1e20, filter = 1e20;
    for (int pass = 0; pass < 4; ++pass) {
        restore(&g, saved);
        double t = seconds();
        if (tvdb_sdf_tree_fast_sweep(w, 1.5f, 8, 1e-5f, &r, &err) != TVDB_OK)
            return 1;
        t = seconds() - t;
        if (!pass)
            tvdb_sdf_tree_info(w, &sweep_info);
        if (pass && t < sweep)
            sweep = t;
        restore(&g, saved);
        t = seconds();
        if (tvdb_sdf_tree_filter(w, TVDB_SDF_FILTER_GAUSSIAN, 4, &err) != TVDB_OK)
            return 1;
        t = seconds() - t;
        if (pass && t < filter)
            filter = t;
    }
    tvdb_sdf_tree_info_t info;
    tvdb_sdf_tree_info(w, &info);
    printf("backend=%s n=%d narrow=%d workers=%zu leaves=%zu active=%zu sweep_ms=%.3f "
           "gaussian4_ms=%.3f iter=%d metadata=%zu scratch=%zu sweep_scratch=%zu "
           "dense_sweep_scratch=%zu\n",
           tvdb_thread_backend_name(), n, narrow, info.workers, info.leaves, info.active_voxels,
           sweep * 1e3, filter * 1e3, r.iterations, info.metadata_bytes, info.scratch_bytes,
           sweep_info.scratch_bytes, (size_t)n * n * n * 6);
    free(saved);
    tvdb_sdf_tree_destroy(w);
    tvdb_thread_pool_destroy(pool);
    tvdb_grid_destroy_owned(&g);
    return 0;
}
int main(int argc, char **argv) {
    int n = argc > 1 ? atoi(argv[1]) : 64;
    if (n < 8 || n > 256 || n % 8)
        return 1;
    if (argc > 2)
        return run(n, 0, (size_t)atoi(argv[2])) || run(n, 1, (size_t)atoi(argv[2]));
    return run(n, 0, 1) || run(n, 0, 8) || run(n, 1, 1) || run(n, 1, 8);
}
