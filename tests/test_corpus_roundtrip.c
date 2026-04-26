// Round-trip every .vdb in the corpus through our reader+writer and verify:
//   - active voxel count matches
//   - leaf count matches
//   - sum of all leaf voxel values matches (within fp tolerance)
//
// This is the "do we regress on real .vdb files?" guard. Files exercised:
//   - sphere.vdb         (v224, BLOSC + ACTIVE_MASK)
//   - bunny.vdb          (v222, half-precision FLOAT)
//   - cube.vdb           (v222, half-precision FLOAT)
//   - smoke.vdb          (v222, half-precision FLOAT, with translation)
//   - data/sphere-div1.vdb, data/sphere-div2.vdb (v224, BLOSC)
//
// The half-precision files are particularly important: they exercise the
// pre-v225 path where the half flag is per-grid and the value buffer is
// promoted from fp16 -> fp32 on read, demoted on write.

#include "tinyvdb_io.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int fails = 0;
#define EXPECT(cond, msg) do { \
    if (!(cond)) { fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, msg); ++fails; } \
} while (0)

typedef struct {
    size_t leaf_count;
    size_t active_count;
    double value_sum;
} grid_stats_t;

static void compute_stats(const tvdb_grid_t *g, grid_stats_t *s) {
    s->leaf_count = 0;
    s->active_count = 0;
    s->value_sum = 0.0;
    int leaf_lv = g->tree.layout.num_levels - 1;
    if (leaf_lv < 0) return;
    int leaf_log2dim = g->tree.layout.levels[leaf_lv].log2dim;
    int leaf_bitsize = 1 << (3 * leaf_log2dim);
    tvdb_value_type_t vt = g->tree.layout.levels[leaf_lv].value_type;
    for (size_t n = 0; n < g->tree.num_nodes; ++n) {
        const tvdb_tree_node_t *nd = &g->tree.nodes[n];
        if (nd->type != TVDB_NODE_LEAF) continue;
        const tvdb_leaf_node_t *leaf = &nd->u.leaf;
        ++s->leaf_count;
        for (int b = 0; b < leaf_bitsize; ++b) {
            if (tvdb_nodemask_is_on((tvdb_nodemask_t *)&leaf->value_mask, b)) {
                ++s->active_count;
                if (vt == TVDB_VALUE_FLOAT) {
                    float v;
                    memcpy(&v, leaf->data + (size_t)b * 4, 4);
                    s->value_sum += (double)v;
                } else if (vt == TVDB_VALUE_DOUBLE) {
                    double v;
                    memcpy(&v, leaf->data + (size_t)b * 8, 8);
                    s->value_sum += v;
                }
            }
        }
    }
}

static int roundtrip_one(const char *in_path, const char *out_path) {
    tvdb_file_t f1; memset(&f1, 0, sizeof(f1));
    tvdb_error_t err = {0};
    if (tvdb_file_open(&f1, in_path, NULL, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL: open %s: %s\n", in_path, err.message);
        return 1;
    }
    if (tvdb_read_all_grids(&f1, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL: read %s: %s\n", in_path, err.message);
        tvdb_file_close(&f1);
        return 1;
    }
    if (f1.num_grids == 0) {
        fprintf(stderr, "FAIL: %s has no grids\n", in_path);
        tvdb_file_close(&f1);
        return 1;
    }

    grid_stats_t before;
    compute_stats(&f1.grids[0], &before);

    // Save with no compression to keep the test simple.
    if (tvdb_file_save(&f1, out_path, TVDB_COMPRESS_NONE, 0, 0, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL: save %s: %s\n", in_path, err.message);
        tvdb_file_close(&f1);
        return 1;
    }
    tvdb_file_close(&f1);

    tvdb_file_t f2; memset(&f2, 0, sizeof(f2));
    if (tvdb_file_open(&f2, out_path, NULL, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL: reopen %s: %s\n", out_path, err.message);
        return 1;
    }
    if (tvdb_read_all_grids(&f2, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL: re-read %s: %s\n", out_path, err.message);
        tvdb_file_close(&f2);
        return 1;
    }

    grid_stats_t after;
    compute_stats(&f2.grids[0], &after);
    tvdb_file_close(&f2);

    int local_fail = 0;
    if (before.leaf_count != after.leaf_count) {
        fprintf(stderr, "FAIL [%s]: leaf count %zu -> %zu\n",
                in_path, before.leaf_count, after.leaf_count);
        local_fail = 1;
    }
    if (before.active_count != after.active_count) {
        fprintf(stderr, "FAIL [%s]: active count %zu -> %zu\n",
                in_path, before.active_count, after.active_count);
        local_fail = 1;
    }
    // For half-precision files the demote -> promote round-trip introduces
    // ~ulp-level drift per voxel, so use a relative tolerance.
    double abs_diff = fabs(before.value_sum - after.value_sum);
    double rel = abs_diff / (fabs(before.value_sum) + 1e-9);
    if (rel > 1e-3) {  // half-precision is ~3 decimal digits per voxel
        fprintf(stderr, "FAIL [%s]: value sum drift |%.6g - %.6g| = %.4e (rel %.2e)\n",
                in_path, before.value_sum, after.value_sum, abs_diff, rel);
        local_fail = 1;
    }
    if (!local_fail) {
        printf("[ok] %s: %zu leaves, %zu active, sum=%.6g (drift %.2e)\n",
               in_path, before.leaf_count, before.active_count,
               before.value_sum, rel);
    }
    return local_fail;
}

int main(int argc, char **argv) {
    const char *root = argc > 1 ? argv[1] : "..";
    const char *out_dir = argc > 2 ? argv[2] : "/tmp";

    const char *files[] = {
        "sphere.vdb",
        "bunny.vdb",
        "cube.vdb",
        "smoke.vdb",
        "data/sphere-div1.vdb",
        "data/sphere-div2.vdb",
    };
    const int n = (int)(sizeof(files) / sizeof(files[0]));

    for (int i = 0; i < n; ++i) {
        char in_path[512], out_path[512];
        snprintf(in_path, sizeof(in_path), "%s/%s", root, files[i]);
        // Out filename: replace '/' with '_'.
        char fn[256]; strncpy(fn, files[i], sizeof(fn) - 1); fn[sizeof(fn)-1] = 0;
        for (char *p = fn; *p; ++p) if (*p == '/') *p = '_';
        snprintf(out_path, sizeof(out_path), "%s/rt_%s", out_dir, fn);
        if (roundtrip_one(in_path, out_path)) ++fails;
    }

    if (fails) { fprintf(stderr, "%d FAILURES\n", fails); return 1; }
    printf("All corpus round-trips passed.\n");
    return 0;
}
