/* Procedural tests intentionally include inactive values that differ from
 * background. Sample through the checked tree lookup, not flat extraction. */
#include "tinyvdb_sdf_tree.h"
#include "tinyvdb_tree_internal.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define CHECK(x)                                                                                   \
    do {                                                                                           \
        if (!(x)) {                                                                                \
            fprintf(stderr, "line %d: %s (%s)\n", __LINE__, #x, err.message);                      \
            return 1;                                                                              \
        }                                                                                          \
    } while (0)
static float sample(const tvdb_grid_t *g, int x, int y, int z, int *active) {
    tvdb_tree_index p;
    int32_t c[3] = {x, y, z};
    if (tvdb_tree_index_create(g, 1, &p, NULL) != TVDB_OK)
        return NAN;
    float v = tvdb_tree_get(&p, c, active);
    tvdb_tree_index_destroy(&p);
    return v;
}
int main(int argc, char **argv) {
    tvdb_error_t err = {0};
    tvdb_file_t f = {0};
    CHECK(tvdb_file_open(&f, argv[1], NULL, &err) == TVDB_OK);
    CHECK(tvdb_read_all_grids(&f, &err) == TVDB_OK);
    tvdb_grid_t *tmpl = f.grids;
    tvdb_vec3i c = {3, 3, 3};
    float v = 5;
    tvdb_sparse_grid s = {&c, &v, 1, 0, 1, 0, 0, 0}, filtered = {0};
    tvdb_grid_t g = {0}, p = {0}, filled = {0};
    CHECK(tvdb_grid_from_sparse_using_template(tmpl, &s, "inactive", 10, &g));
    size_t leaf = 0;
    for (size_t i = 1; i < g.tree.num_nodes; ++i)
        if (g.tree.nodes[i].type == TVDB_NODE_LEAF)
            leaf = i;
    CHECK(leaf);
    float *data = (float *)g.tree.nodes[leaf].u.leaf.data;
    for (size_t i = 0; i < 512; ++i)
        if (i != 219)
            data[i] = 0;
    CHECK(tvdb_grid_erode_active(&g, 2, &filtered));
    CHECK(filtered.count == 1 && filtered.values[0] == 5);
    tvdb_sparse_grid_free(&filtered);
    CHECK(tvdb_grid_erode_active(&g, 0, &filtered));
    CHECK(filtered.values[0] == 5);
    CHECK(sample(&g, 2, 3, 3, NULL) == 0);
    tvdb_sparse_grid_free(&filtered);
    tvdb_sdf_tree_t *workspace = NULL;
    CHECK(tvdb_sdf_tree_create(&g, NULL, NULL, &workspace, &err) == TVDB_OK);
    CHECK(tvdb_grid_prune(&g, &p, &err) == TVDB_OK);
    CHECK(sample(&p, 2, 3, 3, NULL) == 0 && sample(&p, 3, 3, 3, NULL) == 5);
    tvdb_sdf_tree_info_t stats;
    tvdb_sdf_tree_info(workspace, &stats);
    CHECK(stats.active_voxels == 1);
    tvdb_sdf_tree_destroy(workspace);
    CHECK(tvdb_grid_prune(&g, &g, &err) == TVDB_ERROR_INVALID_ARGUMENT);
    tvdb_grid_destroy_owned(&p);
    /* An entire active leaf collapses to a tile with the same exact bounds. */
    memset(g.tree.nodes[leaf].u.leaf.value_mask.bits.data, 255, 64);
    for (size_t i = 0; i < 512; ++i)
        data[i] = 3;
    CHECK(tvdb_grid_prune(&g, &p, &err) == TVDB_OK);
    CHECK(p.tree.num_nodes == g.tree.num_nodes - 1);
    tvdb_tree_diagnostics_t d = {0};
    CHECK(tvdb_grid_diagnose(&p, TVDB_TREE_DIAG_GENERIC, 0, 0, &d, &err) == TVDB_OK);
    CHECK(d.valid && d.active_voxels == 512 && d.active_tiles == 1);
    CHECK(d.active_min[0] == 0 && d.active_max[0] == 8);
    CHECK(tvdb_grid_to_sparse_ex(&p, &filtered, &err) == TVDB_ERROR_UNIMPLEMENTED);
    int32_t lo[3] = {1, 1, 1}, hi[3] = {2, 2, 2};
    tvdb_dense_grid dense = {0};
    CHECK(tvdb_grid_materialize_dense_ex(&p, lo, hi, 99, &dense, &err) == TVDB_OK);
    CHECK(dense.data[0] == 3);
    float *old = dense.data;
    lo[0] = INT32_MIN;
    hi[0] = INT32_MAX;
    CHECK(tvdb_grid_materialize_dense_ex(&p, lo, hi, 0, &dense, &err) != TVDB_OK &&
          dense.data == old);
    tvdb_dense_grid_free(&dense);
    int active = 0;
    CHECK(sample(&p, 7, 7, 7, &active) == 3 && active);
    CHECK(tvdb_grid_signed_flood_fill(&p, 2, -2, &filled, &err) == TVDB_ERROR_INVALID_DATA);
    tvdb_file_t single = {0}, reloaded = {0};
    single.header = f.header;
    single.alloc = f.alloc;
    single.grids = &p;
    single.num_grids = 1;
    uint8_t *serialized = NULL;
    size_t serialized_size = 0;
    CHECK(tvdb_write_to_memory(&single, 0, 0, &serialized, &serialized_size, &err) == TVDB_OK);
    CHECK(tvdb_file_open_memory(&reloaded, serialized, serialized_size, NULL, &err) == TVDB_OK);
    CHECK(tvdb_read_all_grids(&reloaded, &err) == TVDB_OK);
    CHECK(tvdb_grid_diagnose(reloaded.grids, 0, 0, 0, &d, &err) == TVDB_OK && d.active_tiles == 1 &&
          d.active_voxels == 512);
    CHECK(sample(reloaded.grids, 7, 7, 7, &active) == 3 && active);
    tvdb_file_close(&reloaded);
    free(serialized);
    /* Structural failure preserves a previously initialized diagnostic. */
    size_t original = g.tree.nodes[0].u.root.child_indices[0];
    g.tree.nodes[0].u.root.child_indices[0] = 0;
    d.flags = 123;
    CHECK(tvdb_grid_diagnose(&g, 0, 0, 0, &d, &err) != TVDB_OK && d.flags == 123);
    g.tree.nodes[0].u.root.child_indices[0] = original;
    data[0] = NAN;
    CHECK(tvdb_grid_diagnose(&g, 0, 0, 0, &d, &err) == TVDB_OK && !d.valid &&
          d.nonfinite_values == 1);
    data[0] = 3;
    tvdb_grid_destroy_owned(&p);
    tvdb_grid_destroy_owned(&g);
    /* A closed sphere whose inactive interior has not yet been populated. */
    tvdb_sparse_grid sphere = {0};
    CHECK(tvdb_sparse_grid_reserve(&sphere, 5000));
    for (int x = -9; x <= 9; ++x)
        for (int y = -9; y <= 9; ++y)
            for (int z = -9; z <= 9; ++z) {
                float dist = sqrtf((float)(x * x + y * y + z * z)) - 6;
                if (fabsf(dist) < 2) {
                    size_t k = sphere.count++;
                    sphere.coords[k] = (tvdb_vec3i){x, y, z};
                    sphere.values[k] = dist;
                }
            }
    CHECK(tvdb_grid_from_sparse_using_template(tmpl, &sphere, "sphere", 2, &g));
    CHECK(sample(&g, 0, 0, 0, NULL) == 2);
    CHECK(tvdb_grid_signed_flood_fill(&g, 2, -3, &filled, &err) == TVDB_OK);
    CHECK(sample(&filled, 0, 0, 0, NULL) == -3 && sample(&filled, 20, 0, 0, NULL) == 2);
    CHECK(sample(&g, 0, 0, 0, NULL) == 2);
    tvdb_tree_index filled_index;
    CHECK(tvdb_tree_index_create(&filled, 1, &filled_index, &err) == TVDB_OK);
    for (size_t i = 0; i < sphere.count; ++i) {
        tvdb_vec3i q = sphere.coords[i];
        int32_t xyz[3] = {q.x, q.y, q.z};
        CHECK(tvdb_tree_get(&filled_index, xyz, &active) == sphere.values[i] && active);
    }
    tvdb_tree_index_destroy(&filled_index);
    CHECK(tvdb_grid_prune(&filled, &p, &err) == TVDB_OK);
    CHECK(sample(&p, 0, 0, 0, NULL) == -3);
    tvdb_grid_destroy_owned(&p);
    tvdb_grid_destroy_owned(&filled);
    tvdb_grid_destroy_owned(&g);
    tvdb_sparse_grid_free(&sphere);
    /* CSG uses each input's stored inactive values and full transform. */
    CHECK(tvdb_grid_from_sparse_using_template(tmpl, &s, "a", 10, &g));
    c.x = 20;
    CHECK(tvdb_grid_from_sparse_using_template(tmpl, &s, "b", -10, &p));
    CHECK(tvdb_grid_csg_union(&g, &p, &filtered));
    for (size_t i = 0; i < filtered.count; ++i)
        if (filtered.coords[i].x == 3)
            CHECK(filtered.values[i] == -10);
    tvdb_sparse_grid_free(&filtered);
    CHECK(tvdb_tree_matrix(&p.transform, p.transform.matrix));
    p.transform.type = TVDB_TRANSFORM_AFFINE;
    p.transform.matrix[0][1] = .25;
    CHECK(!tvdb_grid_csg_union(&g, &p, &filtered));
    tvdb_grid_destroy_owned(&p);
    tvdb_grid_destroy_owned(&g);
    /* Root z-scanlines can overwrite an existing inactive exterior tile. */
    tvdb_vec3i gap_coords[2] = {{0, 0, 0}, {0, 0, 8192}};
    float gap_values[2] = {-1, -1};
    tvdb_sparse_grid gap = {gap_coords, gap_values, 2, 0, 1, 0, 0, 0};
    CHECK(tvdb_grid_from_sparse_using_template(tmpl, &gap, "root gap", 2, &g));
    for (size_t ni = 1; ni < g.tree.num_nodes; ++ni) {
        tvdb_tree_node_t *node = g.tree.nodes + ni;
        int L = g.tree.layout.levels[node->level].log2dim;
        size_t slots = (size_t)1 << (3 * L);
        int leaf_node = node->type == TVDB_NODE_LEAF;
        float *values = (float *)(leaf_node ? node->u.leaf.data : node->u.internal.values);
        const tvdb_nodemask_t *mask =
            leaf_node ? &node->u.leaf.value_mask : &node->u.internal.child_mask;
        for (size_t k = 0; k < slots; ++k)
            if (!tvdb_nodemask_is_on(mask, (int32_t)k))
                values[k] = -2;
    }
    tvdb_root_node_t *root = &g.tree.nodes[0].u.root;
    root->tile_origins = malloc(3 * sizeof(int32_t));
    root->tile_values = calloc(1, sizeof(tvdb_value_t));
    root->tile_active = calloc(1, sizeof(int));
    CHECK(root->tile_origins && root->tile_values && root->tile_active);
    root->num_tiles = 1;
    root->tile_origins[0] = root->tile_origins[1] = 0;
    root->tile_origins[2] = 4096;
    root->tile_values[0].type = TVDB_VALUE_FLOAT;
    root->tile_values[0].u.f = 2;
    CHECK(tvdb_grid_signed_flood_fill(&g, 2, -3, &filled, &err) == TVDB_OK);
    CHECK(sample(&g, 1, 1, 4096, NULL) == 2 && sample(&filled, 1, 1, 4096, &active) == -3 &&
          !active);
    CHECK(filled.tree.nodes[0].u.root.num_tiles == 1);
    tvdb_grid_destroy_owned(&filled);
    tvdb_grid_destroy_owned(&g);
    /* int32 exclusive bounds cannot represent a voxel at INT32_MAX. */
    c = (tvdb_vec3i){INT32_MAX, 0, 0};
    CHECK(tvdb_grid_from_sparse_using_template(tmpl, &s, "edge", 1, &g));
    CHECK(tvdb_grid_diagnose(&g, 0, 0, 0, &d, &err) == TVDB_OK);
    CHECK(d.active_max[0] == (int64_t)INT32_MAX + 1);
    int32_t min[3] = {7, 7, 7}, max[3] = {7, 7, 7};
    CHECK(!tvdb_grid_active_bbox(&g, min, max) && min[0] == 7);
    tvdb_grid_destroy_owned(&g);
    /* Empty trees and the bit distinction between signed zero values. */
    tvdb_sparse_grid empty = {0};
    CHECK(tvdb_grid_from_sparse_using_template(tmpl, &empty, "empty", 2, &g));
    CHECK(tvdb_grid_prune(&g, &p, &err) == TVDB_OK && p.tree.num_nodes == 1);
    CHECK(tvdb_grid_signed_flood_fill(&g, 4, -4, &filled, &err) == TVDB_OK &&
          sample(&filled, 0, 0, 0, NULL) == 4);
    CHECK(tvdb_grid_diagnose(&p, 0, 0, 0, &d, &err) == TVDB_OK && !d.has_active_bbox &&
          d.active_voxels == 0);
    tvdb_grid_destroy_owned(&filled);
    tvdb_grid_destroy_owned(&p);
    tvdb_grid_destroy_owned(&g);
    c = (tvdb_vec3i){0, 0, 0};
    v = 0;
    CHECK(tvdb_grid_from_sparse_using_template(tmpl, &s, "zero", 0, &g));
    for (size_t i = 1; i < g.tree.num_nodes; ++i)
        if (g.tree.nodes[i].type == TVDB_NODE_LEAF)
            leaf = i;
    memset(g.tree.nodes[leaf].u.leaf.value_mask.bits.data, 0, 64);
    ((float *)g.tree.nodes[leaf].u.leaf.data)[1] = -0.f;
    CHECK(tvdb_grid_prune(&g, &p, &err) == TVDB_OK && p.tree.num_nodes == g.tree.num_nodes);
    CHECK(signbit(sample(&p, 0, 0, 1, NULL)));
    tvdb_grid_destroy_owned(&p);
    tvdb_grid_destroy_owned(&g);
    c = (tvdb_vec3i){0, 0, 0};
    v = .5f;
    CHECK(tvdb_grid_from_sparse_using_template(tmpl, &s, "fog", 0, &g));
    tvdb_meta_entry_t class_entry = {0};
    class_entry.name = (char *)"class";
    class_entry.value.type = TVDB_VALUE_STRING;
    class_entry.value.u.s.str = (char *)"fog volume";
    class_entry.value.u.s.len = 10;
    g.metadata.entries = &class_entry;
    g.metadata.count = g.metadata.capacity = 1;
    CHECK(tvdb_grid_diagnose(&g, TVDB_TREE_DIAG_FOG, 0, 0, &d, &err) == TVDB_OK && d.valid);
    CHECK(tvdb_grid_diagnose(&g, TVDB_TREE_DIAG_LEVEL_SET, 0, 0, &d, &err) == TVDB_OK && !d.valid);
    CHECK((d.flags & (TVDB_TREE_DIAG_CLASS | TVDB_TREE_DIAG_BACKGROUND)) ==
          (TVDB_TREE_DIAG_CLASS | TVDB_TREE_DIAG_BACKGROUND));
    g.metadata.entries = NULL;
    g.metadata.count = g.metadata.capacity = 0;
    tvdb_grid_destroy_owned(&g);
    tvdb_file_close(&f);
    puts("tree maintenance contracts passed");
    (void)argc;
    return 0;
}
