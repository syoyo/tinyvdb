// Round-trip the libopenvdb-generated reference corpus through tinyvdb.
//
// Each reference file holds a 4x4x4 = 64-active-voxel grid produced by
// scripts/gen_openvdb_reference.cc (linked against libopenvdb). This test
// reads each reference file with tinyvdb, writes it back uncompressed, then
// re-reads the output and verifies the active-voxel count is preserved
// across all six core OpenVDB value types: bool, float, double, int32,
// int64, vec3s.
//
// Reference files are gitignored (*.vdb); regenerate them via
// scripts/gen_openvdb_reference.cc. If data/reference/ is missing the test
// reports "skipped" with exit 0 — there's nothing to validate, but absence
// alone isn't a regression.
//
// This is the "do we agree with the canonical OpenVDB byte format?" guard.

#include "tinyvdb_io.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

static size_t count_active(const tvdb_grid_t *g) {
    size_t active = 0;
    int leaf_lv = g->tree.layout.num_levels - 1;
    if (leaf_lv < 0) return 0;
    int log2dim = g->tree.layout.levels[leaf_lv].log2dim;
    int bs = 1 << (3 * log2dim);
    for (size_t n = 0; n < g->tree.num_nodes; ++n) {
        const tvdb_tree_node_t *nd = &g->tree.nodes[n];
        if (nd->type != TVDB_NODE_LEAF) continue;
        for (int b = 0; b < bs; ++b) {
            if (tvdb_nodemask_is_on((tvdb_nodemask_t *)&nd->u.leaf.value_mask, b)) {
                ++active;
            }
        }
    }
    return active;
}

static int rt(const char *root, const char *out_dir, const char *name) {
    char in[512], out[512];
    snprintf(in, sizeof(in), "%s/data/reference/%s.vdb", root, name);
    snprintf(out, sizeof(out), "%s/rt_%s.vdb", out_dir, name);

    tvdb_file_t f1; memset(&f1, 0, sizeof(f1));
    tvdb_error_t err = {0};
    if (tvdb_file_open(&f1, in, NULL, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL [%s]: open %s: %s\n", name, in, err.message);
        return 1;
    }
    if (tvdb_read_all_grids(&f1, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL [%s]: read: %s\n", name, err.message);
        tvdb_file_close(&f1);
        return 1;
    }
    if (f1.num_grids == 0) {
        fprintf(stderr, "FAIL [%s]: no grids\n", name);
        tvdb_file_close(&f1);
        return 1;
    }
    size_t before = count_active(&f1.grids[0]);

    if (tvdb_file_save(&f1, out, TVDB_COMPRESS_NONE, 0, 0, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL [%s]: save: %s\n", name, err.message);
        tvdb_file_close(&f1);
        return 1;
    }
    tvdb_file_close(&f1);

    tvdb_file_t f2; memset(&f2, 0, sizeof(f2));
    if (tvdb_file_open(&f2, out, NULL, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL [%s]: reopen: %s\n", name, err.message);
        return 1;
    }
    if (tvdb_read_all_grids(&f2, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL [%s]: re-read: %s\n", name, err.message);
        tvdb_file_close(&f2);
        return 1;
    }
    size_t after = count_active(&f2.grids[0]);
    tvdb_file_close(&f2);

    if (before != 64 || after != 64) {
        fprintf(stderr, "FAIL [%s]: expected 64 active, got before=%zu after=%zu\n",
                name, before, after);
        return 1;
    }
    printf("[ok] %s: 64 active voxels\n", name);
    return 0;
}

int main(int argc, char **argv) {
    const char *root = argc > 1 ? argv[1] : "..";
    const char *out_dir = argc > 2 ? argv[2] : "/tmp";

    char probe[512];
    snprintf(probe, sizeof(probe), "%s/data/reference/ref_bool.vdb", root);
    struct stat st;
    if (stat(probe, &st) != 0) {
        printf("[skip] reference corpus not present at %s/data/reference/\n", root);
        printf("       regenerate via scripts/gen_openvdb_reference.cc\n");
        return 0;
    }

    const char *names[] = {
        "ref_bool", "ref_float", "ref_double",
        "ref_int32", "ref_int64", "ref_vec3s",
    };
    int fails = 0;
    for (size_t i = 0; i < sizeof(names) / sizeof(names[0]); ++i) {
        fails += rt(root, out_dir, names[i]);
    }
    if (fails) {
        fprintf(stderr, "%d FAILURES\n", fails);
        return 1;
    }
    printf("All reference round-trips passed.\n");
    return 0;
}
