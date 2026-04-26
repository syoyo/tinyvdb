// Test vec3 tree builder and topology-extending update.
//
// vec3 builder: requires a Tree_vec3s_5_4_3 template. We synthesize a
// minimal vec3 grid by deep-copying a Tree_float_5_4_3 layout and
// retyping its leaf level to VEC3F. Then build a vec3 grid from a small
// sparse coord+value array and walk the tree to verify leaf count and
// per-voxel values. (We don't round-trip via tvdb_file_save here — the
// io path's vec3 writer is exercised separately.)
//
// extend_from_sparse: load sphere.vdb, extract a small set of off-leaf
// coords, call extend, verify the new grid's active count = original +
// number of new coords.

#include "tinyvdb_io.h"
#include "tinyvdb_sparse.h"
#include "tinyvdb_sparse_tree.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int g_failures = 0;
#define EXPECT(cond) do { if (!(cond)) { \
    fprintf(stderr, "FAIL [%s:%d]: %s\n", __FILE__, __LINE__, #cond); \
    ++g_failures; } } while (0)

static int noop_leaf_cb(const tvdb_leaf_view_t *leaf, void *user) {
    (void)leaf; (void)user; return 0;
}

// Walk all leaves of a vec3-typed grid; return total active voxels and
// (optionally) collected per-voxel values.
typedef struct {
    size_t   total_active;
    size_t   leaf_count;
} vec3_walk_t;

static void walk_vec3(const tvdb_grid_t *g, vec3_walk_t *out) {
    out->total_active = 0;
    out->leaf_count = 0;
    int leaf_lv = g->tree.layout.num_levels - 1;
    int leaf_bitsize = 1 << (3 * g->tree.layout.levels[leaf_lv].log2dim);
    for (size_t n = 0; n < g->tree.num_nodes; ++n) {
        const tvdb_tree_node_t *nd = &g->tree.nodes[n];
        if (nd->type != TVDB_NODE_LEAF) continue;
        const tvdb_leaf_node_t *leaf = &nd->u.leaf;
        ++out->leaf_count;
        for (int b = 0; b < leaf_bitsize; ++b) {
            if (tvdb_nodemask_is_on((tvdb_nodemask_t *)&leaf->value_mask, b)) {
                ++out->total_active;
            }
        }
    }
}

int main(int argc, char **argv) {
    const char *path = argc > 1 ? argv[1] : "../sphere.vdb";

    // ---- Test 1: vec3 builder using a synthetically-retyped template. ----
    {
        tvdb_file_t f; memset(&f, 0, sizeof(f));
        tvdb_error_t err = {0};
        EXPECT(tvdb_file_open(&f, path, NULL, &err) == TVDB_OK);
        EXPECT(tvdb_read_all_grids(&f, &err) == TVDB_OK);
        EXPECT(f.num_grids > 0);
        tvdb_grid_t tmpl = f.grids[0];   // shallow copy is fine; we only read layout
        // Retype layout to vec3.
        for (int i = 0; i < tmpl.tree.layout.num_levels; ++i) {
            // Internal/leaf levels store their value type in this field.
            tmpl.tree.layout.levels[i].value_type = TVDB_VALUE_VEC3F;
        }

        // Build a 2x2x2 = 8-coord sparse grid spanning a single leaf.
        tvdb_vec3i coords[8];
        float values[24]; // 8 * 3
        size_t k = 0;
        for (int z = 0; z < 2; ++z)
        for (int y = 0; y < 2; ++y)
        for (int x = 0; x < 2; ++x) {
            coords[k].x = x; coords[k].y = y; coords[k].z = z;
            values[3 * k + 0] = (float)x;
            values[3 * k + 1] = (float)y;
            values[3 * k + 2] = (float)z;
            ++k;
        }
        float bg[3] = {0.0f, 0.0f, 0.0f};
        tvdb_grid_t built; memset(&built, 0, sizeof(built));
        EXPECT(tvdb_grid_from_sparse_vec3_using_template(&tmpl, coords, values,
                                                         8, "vel", bg, &built));

        vec3_walk_t w; walk_vec3(&built, &w);
        printf("[vec3] leaves=%zu active=%zu (expect 1 / 8)\n",
               w.leaf_count, w.total_active);
        EXPECT(w.leaf_count == 1);
        EXPECT(w.total_active == 8);

        // Spot-check a voxel's value (slot for coord (1,1,1) in an 8^3 leaf is
        // (1<<6)|(1<<3)|1 = 73; data is 12 bytes per slot).
        if (built.tree.num_nodes > 0) {
            // Find the leaf node.
            for (size_t n = 0; n < built.tree.num_nodes; ++n) {
                if (built.tree.nodes[n].type != TVDB_NODE_LEAF) continue;
                const tvdb_leaf_node_t *lf = &built.tree.nodes[n].u.leaf;
                int slot = (1 << 6) | (1 << 3) | 1;
                float v[3];
                memcpy(v, lf->data + (size_t)slot * 12, 12);
                printf("  voxel(1,1,1) = (%.1f, %.1f, %.1f)\n", v[0], v[1], v[2]);
                EXPECT(v[0] == 1.0f && v[1] == 1.0f && v[2] == 1.0f);
                break;
            }
        }

        // Confirm root background got set as VEC3F (not FLOAT).
        size_t root_idx = (size_t)-1;
        for (size_t n = 0; n < built.tree.num_nodes; ++n) {
            if (built.tree.nodes[n].type == TVDB_NODE_ROOT) { root_idx = n; break; }
        }
        EXPECT(root_idx != (size_t)-1);
        if (root_idx != (size_t)-1) {
            EXPECT(built.tree.nodes[root_idx].u.root.background.type == TVDB_VALUE_VEC3F);
        }

        tvdb_grid_destroy_owned(&built);
        tvdb_file_close(&f);
    }

    // ---- Test 2: topology-extending update_from_sparse. ----
    {
        tvdb_file_t f; memset(&f, 0, sizeof(f));
        tvdb_error_t err = {0};
        EXPECT(tvdb_file_open(&f, path, NULL, &err) == TVDB_OK);
        EXPECT(tvdb_read_all_grids(&f, &err) == TVDB_OK);
        const tvdb_grid_t *tmpl = &f.grids[0];

        size_t orig_count = tvdb_grid_active_voxel_count(tmpl);
        size_t orig_leaves = tvdb_grid_visit_leaves_float(tmpl, noop_leaf_cb, NULL);

        // Pick coords WAY outside any existing leaf (large origin offsets).
        tvdb_sparse_grid sg; tvdb_sparse_grid_init(&sg);
        EXPECT(tvdb_sparse_grid_reserve(&sg, 4));
        // Sphere data lives near origin; place new coords far away so they
        // certainly land in new leaves.
        sg.coords[0].x = 1000; sg.coords[0].y =    0; sg.coords[0].z =    0; sg.values[0] = 1.0f;
        sg.coords[1].x = 1001; sg.coords[1].y =    0; sg.coords[1].z =    0; sg.values[1] = 2.0f;
        sg.coords[2].x =    0; sg.coords[2].y = 1000; sg.coords[2].z =    0; sg.values[2] = 3.0f;
        sg.coords[3].x =    0; sg.coords[3].y =    0; sg.coords[3].z = 1000; sg.values[3] = 4.0f;
        sg.count = 4;

        tvdb_grid_t extended; memset(&extended, 0, sizeof(extended));
        EXPECT(tvdb_grid_extend_from_sparse(tmpl, &sg, "extended", 0.0f, &extended));

        size_t new_count = tvdb_grid_active_voxel_count(&extended);
        size_t new_leaves = tvdb_grid_visit_leaves_float(&extended, noop_leaf_cb, NULL);
        printf("[extend] orig active=%zu leaves=%zu  ->  new active=%zu leaves=%zu\n",
               orig_count, orig_leaves, new_count, new_leaves);
        // 4 new coords; coords[0]=(1000,0,0) and coords[1]=(1001,0,0) share a
        // leaf (origin 1000 in 8^3 leaves), so 3 distinct new leaves.
        EXPECT(new_count == orig_count + 4);
        EXPECT(new_leaves == orig_leaves + 3);

        tvdb_sparse_grid_free(&sg);
        tvdb_grid_destroy_owned(&extended);
        tvdb_file_close(&f);
    }

    if (g_failures == 0) {
        printf("All vec3 / extend tests passed.\n");
        return 0;
    }
    printf("%d failures.\n", g_failures);
    return 1;
}
