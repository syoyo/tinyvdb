#pragma once
#include "tinyvdb_sdf_tree.h"
#include <math.h>
#include <stdlib.h>
#include <string.h>

static void sdf_fixture_template(tvdb_grid_t *g) {
    memset(g, 0, sizeof(*g));
    g->descriptor.grid_type = (char *)"Tree_float_5_4_3";
    g->transform.type = TVDB_TRANSFORM_UNIFORM_SCALE;
    g->transform.voxel_size[0] = 1;
    g->tree.layout.num_levels = 4;
    const int dims[4] = {0, 5, 4, 3};
    for (int i = 0; i < 4; ++i) {
        g->tree.layout.levels[i].log2dim = dims[i];
        g->tree.layout.levels[i].value_type = TVDB_VALUE_FLOAT;
        g->tree.layout.levels[i].node_type = i == 0   ? TVDB_NODE_ROOT
                                             : i == 3 ? TVDB_NODE_LEAF
                                                      : TVDB_NODE_INTERNAL;
    }
}
static int sdf_fixture_cube(tvdb_grid_t *grid, int n, int sphere, int narrow) {
    tvdb_grid_t tmpl;
    sdf_fixture_template(&tmpl);
    tvdb_sparse_grid sparse = {0};
    size_t count = (size_t)n * n * n;
    if (!tvdb_sparse_grid_reserve(&sparse, count))
        return 0;
    for (int x = 0; x < n; ++x)
        for (int y = 0; y < n; ++y)
            for (int z = 0; z < n; ++z) {
                float dx = x + 0.5f - n * 0.5f, dy = y + 0.5f - n * 0.5f, dz = z + 0.5f - n * 0.5f;
                float exact = sphere ? sqrtf(dx * dx + dy * dy + dz * dz) - n * 0.28f : dx;
                if (narrow && fabsf(exact) > 4)
                    continue;
                size_t i = sparse.count++;
                sparse.coords[i] = (tvdb_vec3i){x, y, z};
                sparse.values[i] = fabsf(exact) <= 1.5f ? exact : exact >= 0 ? 100 : -100;
            }
    int ok = tvdb_grid_from_sparse_using_template(&tmpl, &sparse, "procedural", 100, grid);
    tvdb_sparse_grid_free(&sparse);
    /* Represent the negative interior in inactive voxels and constant tiles,
     * as a narrow-band level set does after signed flood fill. */
    if (ok && narrow) {
        for (size_t ni = 0; ni < grid->tree.num_nodes; ++ni) {
            tvdb_tree_node_t *node = grid->tree.nodes + ni;
            if (node->type == TVDB_NODE_ROOT)
                continue;
            int L = grid->tree.layout.levels[node->level].log2dim;
            int dim = 1 << L;
            int span = node->type == TVDB_NODE_LEAF ? 1 : node->level == 1 ? 128 : 8;
            const tvdb_nodemask_t *mask = node->type == TVDB_NODE_LEAF
                                              ? &node->u.leaf.value_mask
                                              : &node->u.internal.child_mask;
            float *data = (float *)(node->type == TVDB_NODE_LEAF ? node->u.leaf.data
                                                                 : node->u.internal.values);
            for (int slot = 0; slot < dim * dim * dim; ++slot) {
                if (tvdb_nodemask_is_on(mask, slot))
                    continue;
                float d[3];
                for (int a = 0; a < 3; ++a)
                    d[a] = node->origin[a] + (((slot >> ((2 - a) * L)) & (dim - 1)) + 0.5f) * span -
                           n * 0.5f;
                float phi =
                    sphere ? sqrtf(d[0] * d[0] + d[1] * d[1] + d[2] * d[2]) - n * 0.28f : d[0];
                data[slot] = phi < 0 ? -100 : 100;
            }
        }
    }
    return ok;
}
static float *sdf_fixture_at(tvdb_grid_t *grid, int32_t x, int32_t y, int32_t z) {
    /* Tests use this independent (slow) traversal only for assertions. */
    tvdb_tree_t *t = &grid->tree;
    tvdb_root_node_t *r = &t->nodes[0].u.root;
    int32_t origin[3] = {x, y, z};
    for (int a = 0; a < 3; ++a)
        origin[a] = (int32_t)(origin[a] >= 0 ? (int64_t)origin[a] / 4096 * 4096
                                             : (-1 - ((-1 - (int64_t)origin[a]) / 4096)) * 4096);
    size_t node = SIZE_MAX;
    for (size_t i = 0; i < r->num_children; ++i)
        if (!memcmp(origin, r->child_origins + 3 * i, sizeof(origin))) {
            node = r->child_indices[i];
            break;
        }
    if (node == SIZE_MAX)
        return NULL;
    int coord[3] = {x, y, z};
    for (int level = 1; level < 3; ++level) {
        tvdb_internal_node_t *in = &t->nodes[node].u.internal;
        int L = t->layout.levels[level].log2dim, shift = level == 1 ? 7 : 3;
        int slot = 0;
        for (int a = 0; a < 3; ++a)
            slot = (slot << L) | ((int)(((int64_t)coord[a] - origin[a]) >> shift) & ((1 << L) - 1));
        if (!tvdb_nodemask_is_on(&in->child_mask, slot))
            return NULL;
        size_t rank = 0;
        for (int b = 0; b < slot; ++b)
            rank += tvdb_nodemask_is_on(&in->child_mask, b);
        node = in->child_indices[rank];
        for (int a = 0; a < 3; ++a)
            origin[a] = (int32_t)((int64_t)origin[a] +
                                  (((slot >> ((2 - a) * L)) & ((1 << L) - 1)) << shift));
    }
    size_t slot =
        ((size_t)(x - origin[0]) << 6) | ((size_t)(y - origin[1]) << 3) | (size_t)(z - origin[2]);
    return (float *)t->nodes[node].u.leaf.data + slot;
}
