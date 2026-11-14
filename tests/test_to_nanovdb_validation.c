// Finding F9: tvdb_grid_to_nanovdb must not trust child_indices or node
// types from a caller-supplied tree. The reader and the from-sparse builder
// maintain the invariants; a damaged tree must be rejected with
// TVDB_ERROR_INVALID_DATA rather than indexed out of bounds or silently
// produce a partial NanoVDB grid.
//
// Method: read the fixture grid, then corrupt one upper-level child slot at
// a time (out-of-bounds index; wrong child node type; duplicated child;
// inflated num_children; self-referential root child), checking that
// conversion fails each time, and that it succeeds again once restored.

#include "tinyvdb_io.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* tvdb_grid_to_nanovdb lives in tinyvdb_to_nanovdb.c; tinyvdb_nanovdb.h
 * would redefine the shared io types, so declare what this test needs. */
tvdb_status_t tvdb_grid_to_nanovdb(const tvdb_grid_t *grid, uint8_t **out_data,
                                   size_t *out_size, tvdb_error_t *err);

static int g_failures = 0;
#define EXPECT(cond) do { if (!(cond)) { \
    fprintf(stderr, "FAIL [%s:%d]: %s\n", __FILE__, __LINE__, #cond); \
    ++g_failures; } } while (0)

/* Convert and release; returns the status. */
static tvdb_status_t convert(const tvdb_grid_t *g, tvdb_error_t *err) {
    uint8_t *data = NULL;
    size_t size = 0;
    tvdb_status_t st = tvdb_grid_to_nanovdb(g, &data, &size, err);
    free(data);
    return st;
}

int main(int argc, char **argv) {
    const char *path = argc > 1 ? argv[1] : "../sphere.vdb";

    tvdb_file_t file;
    memset(&file, 0, sizeof(file));
    tvdb_error_t err;
    memset(&err, 0, sizeof(err));
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
    tvdb_grid_t *g = &file.grids[0];
    if (!g->tree.nodes || g->tree.num_nodes == 0) {
        fprintf(stderr, "FAIL: instance fixture?\n");
        tvdb_file_close(&file);
        return 1;
    }

    /* Sanity: the untouched grid converts. */
    EXPECT(convert(g, &err) == TVDB_OK);

    /* Locate a level-1 internal node with children. */
    tvdb_tree_node_t *upper = NULL;
    size_t upper_idx = (size_t)-1;
    for (size_t n = 0; n < g->tree.num_nodes; ++n) {
        tvdb_tree_node_t *node = &g->tree.nodes[n];
        if (node->type == TVDB_NODE_INTERNAL && node->level == 1 &&
            node->u.internal.num_children > 0) {
            upper = node;
            upper_idx = n;
            break;
        }
    }
    if (!upper) {
        fprintf(stderr, "FAIL: fixture has no upper internal node with children\n");
        tvdb_file_close(&file);
        return 1;
    }
    tvdb_internal_node_t *ui = &upper->u.internal;
    tvdb_tree_t *tree = &g->tree;

    /* 1) Child index out of bounds. */
    size_t saved0 = ui->child_indices[0];
    ui->child_indices[0] = tree->num_nodes + 1000u;
    EXPECT(convert(g, &err) == TVDB_ERROR_INVALID_DATA);
    ui->child_indices[0] = saved0;

    /* 2) Child node has the wrong type/level. */
    size_t child0 = ui->child_indices[0];
    tvdb_node_type_t saved_type = tree->nodes[child0].type;
    int saved_level = tree->nodes[child0].level;
    tree->nodes[child0].type = TVDB_NODE_LEAF;
    tree->nodes[child0].level = 3;
    EXPECT(convert(g, &err) == TVDB_ERROR_INVALID_DATA);
    tree->nodes[child0].type = saved_type;
    tree->nodes[child0].level = saved_level;

    /* 3) Duplicated child (shared nodes are invalid in this tree). */
    if (ui->num_children > 1) {
        size_t saved1 = ui->child_indices[1];
        ui->child_indices[1] = ui->child_indices[0];
        EXPECT(convert(g, &err) == TVDB_ERROR_INVALID_DATA);
        ui->child_indices[1] = saved1;
    }

    /* 4) num_children inflated past the mask rank. */
    uint32_t saved_nc = ui->num_children;
    ui->num_children = saved_nc + 1u;
    EXPECT(convert(g, &err) == TVDB_ERROR_INVALID_DATA);
    ui->num_children = saved_nc;

    /* 5) Root child pointing back at the root (cycle). */
    {
        tvdb_root_node_t *root = &tree->nodes[0].u.root;
        if (root->num_children > 0) {
            size_t saved_rc = root->child_indices[0];
            root->child_indices[0] = 0;
            EXPECT(convert(g, &err) == TVDB_ERROR_INVALID_DATA);
            root->child_indices[0] = saved_rc;
        }
    }

    /* 6) Root child index out of bounds. */
    {
        tvdb_root_node_t *root = &tree->nodes[0].u.root;
        if (root->num_children > 0) {
            size_t saved_rc = root->child_indices[0];
            root->child_indices[0] = tree->num_nodes + 1000u;
            EXPECT(convert(g, &err) == TVDB_ERROR_INVALID_DATA);
            root->child_indices[0] = saved_rc;
        }
    }

    /* 7) Leaf value mask destroyed (the walk must reject before touching it). */
    for (size_t n = 0; n < tree->num_nodes; ++n) {
        if (tree->nodes[n].type != TVDB_NODE_LEAF) continue;
        tvdb_leaf_node_t *lf = &tree->nodes[n].u.leaf;
        uint8_t *saved_data = lf->data;
        if (!saved_data) break;
        lf->data = NULL;
        EXPECT(convert(g, &err) == TVDB_ERROR_INVALID_DATA);
        lf->data = saved_data;
        break;
    }

    /* Restored grid converts again (no state leaked through the corruptions). */
    EXPECT(convert(g, &err) == TVDB_OK);

    tvdb_file_close(&file);

    if (g_failures) {
        fprintf(stderr, "failures=%d\n", g_failures);
        return 1;
    }
    printf("test_to_nanovdb_validation: ok\n");
    return 0;
}
