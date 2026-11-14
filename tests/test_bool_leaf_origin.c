// Finding F7: bool-leaf writer must emit the true leaf origin.
//
// Why: the reader never populates tvdb_tree_node_t.origin (internal/leaf
// origins are implicit in child-mask slot positions and root child_origins),
// so a load -> save cycle used to write {0,0,0} as a bool leaf's "origin"
// bytes. This test builds a bool grid whose only leaf sits at voxel origin
// (1000,1000,1000), round-trips it through memory twice (once from the
// in-memory builder, where origins are known, and once from the reader-
// produced tree, where they are lost), and checks the bool-leaf origin
// bytes in the output.

#include "tinyvdb_io.h"
#include "tinyvdb_sparse.h"
#include "tinyvdb_sparse_tree.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int g_failures = 0;
#define EXPECT(cond) do { if (!(cond)) { \
    fprintf(stderr, "FAIL [%s:%d]: %s\n", __FILE__, __LINE__, #cond); \
    ++g_failures; } } while (0)

// The 12-byte little-endian triple (origin_x, origin_y, origin_z) as the
// bool-leaf buffer stores it (1000 = 0x000003e8).
static const uint8_t LEAF_ORIGIN_1000[12] = {
    0xe8, 0x03, 0x00, 0x00,
    0xe8, 0x03, 0x00, 0x00,
    0xe8, 0x03, 0x00, 0x00,
};

static int find_bytes(const uint8_t *hay, size_t hay_sz, const uint8_t *needle,
                      size_t needle_sz) {
    if (needle_sz > hay_sz) return 0;
    for (size_t i = 0; i + needle_sz <= hay_sz; ++i)
        if (!memcmp(hay + i, needle, needle_sz)) return 1;
    return 0;
}

int main(int argc, char **argv) {
    const char *path = argc > 1 ? argv[1] : "../sphere.vdb";
    tvdb_error_t err;

    tvdb_file_t file;
    memset(&file, 0, sizeof(file));
    if (tvdb_file_open(&file, path, NULL, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL: open %s: %s\n", path, err.message);
        return 1;
    }
    if (tvdb_read_all_grids(&file, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL: read grids: %s\n", err.message);
        tvdb_file_close(&file);
        return 1;
    }
    if (file.num_grids == 0) {
        fprintf(stderr, "FAIL: empty fixture\n");
        tvdb_file_close(&file);
        return 1;
    }
    tvdb_grid_t *tmpl = &file.grids[0];

    /* Retype the template's layout to BOOL (same trick as
       test_scalar_writer_audit). */
    tvdb_grid_t retyped = *tmpl;
    for (int i = 0; i < retyped.tree.layout.num_levels; ++i)
        retyped.tree.layout.levels[i].value_type = TVDB_VALUE_BOOL;

    /* 4x4x4 = 64 active voxels at coords 1000..1003 on each axis.
       Leaf log2dim is 3, so the leaf origin is exactly (1000,1000,1000). */
    tvdb_vec3i coords[64];
    uint8_t values[64];
    int k = 0;
    for (int z = 1000; z < 1004; ++z)
        for (int y = 1000; y < 1004; ++y)
            for (int x = 1000; x < 1004; ++x) {
                coords[k].x = x; coords[k].y = y; coords[k].z = z;
                values[k] = 1; ++k;
            }
    const uint8_t background = 0;

    tvdb_grid_t built;
    memset(&built, 0, sizeof(built));
    if (!tvdb_grid_from_sparse_typed_using_template(&retyped, coords, values,
                                                    (size_t)k, TVDB_VALUE_BOOL,
                                                    &background, "boolleaf",
                                                    &built)) {
        fprintf(stderr, "FAIL: bool grid build\n");
        tvdb_file_close(&file);
        return 1;
    }

    /* Replace the template grid with the bool grid (same pattern as
       test_scalar_writer_audit). */
    tvdb_grid_destroy(tmpl, &file.alloc);
    *tmpl = built;

    uint8_t *data1 = NULL;
    size_t size1 = 0;
    if (tvdb_write_to_memory(&file, TVDB_COMPRESS_NONE, 5, &data1, &size1,
                             &err) != TVDB_OK) {
        fprintf(stderr, "FAIL: write to memory (builder tree): %s\n",
                err.message);
        tvdb_file_close(&file);
        return 1;
    }
    EXPECT(find_bytes(data1, size1, LEAF_ORIGIN_1000, sizeof(LEAF_ORIGIN_1000)));

    /* Round-trip through the reader: the reader-produced tree has zeroed
       node->origin fields (it keeps origins in child_origins + slot
       positions only). Writing THAT tree is what used to emit {0,0,0}. */
    tvdb_file_t file2;
    memset(&file2, 0, sizeof(file2));
    if (tvdb_file_open_memory(&file2, data1, size1, NULL, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL: reopen: %s\n", err.message);
        free(data1);
        tvdb_file_close(&file);
        return 1;
    }
    if (tvdb_read_all_grids(&file2, &err) != TVDB_OK) {
        fprintf(stderr, "FAIL: read reopened: %s\n", err.message);
        free(data1);
        tvdb_file_close(&file2);
        tvdb_file_close(&file);
        return 1;
    }
    /* (Deliberately no precondition assert here: the test must not break
       if a future reader starts populating node origins.) */

    uint8_t *data2 = NULL;
    size_t size2 = 0;
    if (tvdb_write_to_memory(&file2, TVDB_COMPRESS_NONE, 5, &data2, &size2,
                             &err) != TVDB_OK) {
        fprintf(stderr, "FAIL: write to memory (reader-produced tree): %s\n",
                err.message);
        free(data1);
        tvdb_file_close(&file2);
        tvdb_file_close(&file);
        return 1;
    }
    EXPECT(find_bytes(data2, size2, LEAF_ORIGIN_1000, sizeof(LEAF_ORIGIN_1000)));

    free(data1);
    free(data2);
    tvdb_file_close(&file2);
    tvdb_file_close(&file);

    /* Also verify the reader tolerates the newly written file (it skips
       the bool-leaf origin) by round-tripping the voxel data through the
       success path exercised above. */

    if (g_failures) {
        fprintf(stderr, "failures=%d\n", g_failures);
        return 1;
    }
    printf("test_bool_leaf_origin: ok\n");
    return 0;
}
