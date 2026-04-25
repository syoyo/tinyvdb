#include "tinyvdb_sparse_tree.h"

#include <stdlib.h>
#include <string.h>

// ----- internals -----

static int leaf_level_of(const tvdb_grid_t *grid) {
    return grid->tree.layout.num_levels - 1;
}

static bool grid_is_float(const tvdb_grid_t *grid) {
    int leaf_lv = leaf_level_of(grid);
    if (leaf_lv < 0) return false;
    return grid->tree.layout.levels[leaf_lv].value_type == TVDB_VALUE_FLOAT;
}

static int leaf_log2dim_of(const tvdb_grid_t *grid) {
    int leaf_lv = leaf_level_of(grid);
    if (leaf_lv < 0) return 0;
    return grid->tree.layout.levels[leaf_lv].log2dim;
}

// Walk the tree depth-first from a starting node index. Origins are computed
// on the fly: roots have explicit child_origins[]; internal-node children
// derive their origin from the parent's origin + (slot_index * child_dim),
// where slot_index is the position of the c-th set bit in the parent's
// child_mask (OpenVDB layout: ix is innermost-major bits, iy middle, iz innermost).
typedef struct {
    size_t  node_idx;
    int32_t origin[3];
} stack_entry_t;

static void leaf_log2dim_for_index(const tvdb_tree_t *tree, int *out) {
    *out = tree->layout.levels[tree->layout.num_levels - 1].log2dim;
}

// Find the position (slot index 0..(1<<3*L)-1) of the c-th set bit in mask.
static int32_t nth_set_bit_pos(const tvdb_nodemask_t *m, size_t c) {
    int32_t total = 1 << (3 * m->log2dim);
    size_t seen = 0;
    for (int32_t i = 0; i < total; ++i) {
        if (m->bits.data[i >> 3] & (1 << (i & 7))) {
            if (seen == c) return i;
            ++seen;
        }
    }
    return -1;
}

static void visit_subtree(const tvdb_tree_t *tree, size_t root_idx,
                          tvdb_leaf_visit_fn cb, void *user, size_t *count, int *stop) {
    enum { MAX_DEPTH = 64 };
    stack_entry_t stack[MAX_DEPTH];
    int sp = 0;
    stack[sp].node_idx = root_idx;
    stack[sp].origin[0] = stack[sp].origin[1] = stack[sp].origin[2] = 0;
    sp++;

    while (sp > 0 && !*stop) {
        --sp;
        size_t idx = stack[sp].node_idx;
        int32_t parent_origin[3] = { stack[sp].origin[0], stack[sp].origin[1], stack[sp].origin[2] };
        const tvdb_tree_node_t *node = &tree->nodes[idx];

        if (node->type == TVDB_NODE_ROOT) {
            const tvdb_root_node_t *r = &node->u.root;
            for (uint32_t c = 0; c < r->num_children && !*stop; ++c) {
                if (sp < MAX_DEPTH) {
                    stack[sp].node_idx = r->child_indices[c];
                    // Root provides explicit child origins.
                    stack[sp].origin[0] = r->child_origins[3 * c + 0];
                    stack[sp].origin[1] = r->child_origins[3 * c + 1];
                    stack[sp].origin[2] = r->child_origins[3 * c + 2];
                    ++sp;
                }
            }
        } else if (node->type == TVDB_NODE_INTERNAL) {
            const tvdb_internal_node_t *in = &node->u.internal;
            int parent_log2dim = (int)in->child_mask.log2dim;
            // Child's voxel-extent per slot = 2^(sum of log2dims of all
            // descendant levels below this internal node, INCLUDING the leaf).
            // E.g. for Tree_float_5_4_3: L1 child covers 2^(4+3)=128 voxels,
            // L2 child covers 2^3=8 voxels (each leaf is 8 voxels per axis).
            int child_dim = 1;
            int my_level = -1;
            for (int lv = 0; lv < tree->layout.num_levels; ++lv) {
                if (tree->layout.levels[lv].log2dim == parent_log2dim &&
                    tree->layout.levels[lv].node_type == TVDB_NODE_INTERNAL) {
                    my_level = lv;
                    break;
                }
            }
            if (my_level >= 0) {
                int sum = 0;
                for (int lv = my_level + 1; lv < tree->layout.num_levels; ++lv) {
                    sum += tree->layout.levels[lv].log2dim;
                }
                child_dim = 1 << sum;
            }
            int32_t total = 1 << (3 * parent_log2dim);
            // Walk the child_mask in linear order; pair the c-th set bit with
            // child_indices[c].
            size_t c_idx = 0;
            int parent_dim_mask = (1 << parent_log2dim) - 1;
            for (int32_t s = 0; s < total && c_idx < in->num_children; ++s) {
                if (!(in->child_mask.bits.data[s >> 3] & (1 << (s & 7)))) continue;
                // Decompose s into (ix, iy, iz) per OpenVDB convention.
                int32_t ix = (s >> (2 * parent_log2dim)) & parent_dim_mask;
                int32_t iy = (s >> parent_log2dim)       & parent_dim_mask;
                int32_t iz = s & parent_dim_mask;
                if (sp < MAX_DEPTH) {
                    stack[sp].node_idx = in->child_indices[c_idx];
                    stack[sp].origin[0] = parent_origin[0] + ix * child_dim;
                    stack[sp].origin[1] = parent_origin[1] + iy * child_dim;
                    stack[sp].origin[2] = parent_origin[2] + iz * child_dim;
                    ++sp;
                }
                ++c_idx;
            }
        } else if (node->type == TVDB_NODE_LEAF) {
            tvdb_leaf_view_t v;
            v.origin[0] = parent_origin[0];
            v.origin[1] = parent_origin[1];
            v.origin[2] = parent_origin[2];
            v.log2dim = (int32_t)node->u.leaf.value_mask.log2dim;
            v.data = (const float *)node->u.leaf.data;
            v.value_mask = &node->u.leaf.value_mask;
            ++*count;
            if (cb(&v, user)) *stop = 1;
        }
    }
    (void)leaf_log2dim_for_index;
}

size_t tvdb_grid_visit_leaves_float(const tvdb_grid_t *grid,
                                    tvdb_leaf_visit_fn cb, void *user) {
    if (!grid || !cb || !grid_is_float(grid)) return 0;
    if (grid->tree.num_nodes == 0) return 0;
    size_t count = 0;
    int stop = 0;
    visit_subtree(&grid->tree, /*root_idx=*/0, cb, user, &count, &stop);
    return count;
}

// ----- count -----

static int count_visit(const tvdb_leaf_view_t *leaf, void *user) {
    size_t *acc = (size_t *)user;
    *acc += tvdb_nodemask_count_on(leaf->value_mask);
    return 0;
}

size_t tvdb_grid_active_voxel_count(const tvdb_grid_t *grid) {
    size_t acc = 0;
    tvdb_grid_visit_leaves_float(grid, count_visit, &acc);
    return acc;
}

// ----- bbox -----

typedef struct {
    int32_t bb_min[3], bb_max[3];
    int has_any;
} bbox_acc_t;

static int bbox_visit(const tvdb_leaf_view_t *leaf, void *user) {
    bbox_acc_t *a = (bbox_acc_t *)user;
    int32_t dim = 1 << leaf->log2dim;
    int32_t lo[3] = { leaf->origin[0], leaf->origin[1], leaf->origin[2] };
    int32_t hi[3] = { lo[0] + dim, lo[1] + dim, lo[2] + dim };
    if (!a->has_any) {
        a->bb_min[0] = lo[0]; a->bb_min[1] = lo[1]; a->bb_min[2] = lo[2];
        a->bb_max[0] = hi[0]; a->bb_max[1] = hi[1]; a->bb_max[2] = hi[2];
        a->has_any = 1;
    } else {
        for (int i = 0; i < 3; ++i) {
            if (lo[i] < a->bb_min[i]) a->bb_min[i] = lo[i];
            if (hi[i] > a->bb_max[i]) a->bb_max[i] = hi[i];
        }
    }
    return 0;
}

bool tvdb_grid_active_bbox(const tvdb_grid_t *grid,
                           int32_t out_min[3], int32_t out_max[3]) {
    bbox_acc_t a;
    a.has_any = 0;
    tvdb_grid_visit_leaves_float(grid, bbox_visit, &a);
    if (!a.has_any) return false;
    out_min[0] = a.bb_min[0]; out_min[1] = a.bb_min[1]; out_min[2] = a.bb_min[2];
    out_max[0] = a.bb_max[0]; out_max[1] = a.bb_max[1]; out_max[2] = a.bb_max[2];
    return true;
}

// ----- transform helpers -----

static void grid_voxel_size_origin(const tvdb_grid_t *grid,
                                   float *vs, float origin[3]) {
    // tvdb_transform_t carries scale_values/voxel_size/translation/matrix as
    // flat fields. Pull voxel_size and translation from whichever fields are
    // populated based on the transform type; fall back to the affine matrix
    // diagonal otherwise.
    *vs = 1.0f;
    origin[0] = origin[1] = origin[2] = 0.0f;
    const tvdb_transform_t *t = &grid->transform;
    switch (t->type) {
        case TVDB_TRANSFORM_UNIFORM_SCALE:
            *vs = (float)t->voxel_size[0]; break;
        case TVDB_TRANSFORM_UNIFORM_SCALE_TRANSLATE:
            *vs = (float)t->voxel_size[0];
            origin[0] = (float)t->translation[0];
            origin[1] = (float)t->translation[1];
            origin[2] = (float)t->translation[2];
            break;
        case TVDB_TRANSFORM_SCALE:
            *vs = (float)t->voxel_size[0];
            break;
        case TVDB_TRANSFORM_SCALE_TRANSLATE:
            *vs = (float)t->voxel_size[0];
            origin[0] = (float)t->translation[0];
            origin[1] = (float)t->translation[1];
            origin[2] = (float)t->translation[2];
            break;
        case TVDB_TRANSFORM_TRANSLATION:
            origin[0] = (float)t->translation[0];
            origin[1] = (float)t->translation[1];
            origin[2] = (float)t->translation[2];
            break;
        case TVDB_TRANSFORM_AFFINE:
            // Use diagonal of 4x4 affine matrix (row-major) for voxel size,
            // last column for translation.
            *vs = (float)t->matrix[0][0];
            origin[0] = (float)t->matrix[0][3];
            origin[1] = (float)t->matrix[1][3];
            origin[2] = (float)t->matrix[2][3];
            break;
        default: break;
    }
}

// ----- to_sparse -----

typedef struct {
    tvdb_sparse_grid *out;
    int               failed;
} sparse_acc_t;

static int sparse_visit(const tvdb_leaf_view_t *leaf, void *user) {
    sparse_acc_t *a = (sparse_acc_t *)user;
    int L = leaf->log2dim;
    int32_t dim = 1 << L;
    // grow
    size_t need = a->out->count + (size_t)tvdb_nodemask_count_on(leaf->value_mask);
    if (need > a->out->capacity) {
        size_t cap = a->out->capacity ? a->out->capacity : 1024;
        while (cap < need) cap *= 2;
        if (!tvdb_sparse_grid_reserve(a->out, cap)) { a->failed = 1; return 1; }
    }
    int32_t lin = 0;
    for (int32_t i = 0; i < dim; ++i) {
        for (int32_t j = 0; j < dim; ++j) {
            for (int32_t k = 0; k < dim; ++k, ++lin) {
                if (tvdb_nodemask_is_on(leaf->value_mask, lin)) {
                    int32_t x = leaf->origin[0] + i;
                    int32_t y = leaf->origin[1] + j;
                    int32_t z = leaf->origin[2] + k;
                    a->out->coords[a->out->count].x = x;
                    a->out->coords[a->out->count].y = y;
                    a->out->coords[a->out->count].z = z;
                    a->out->values[a->out->count]   = leaf->data[lin];
                    a->out->count++;
                }
            }
        }
    }
    return 0;
}

bool tvdb_grid_to_sparse(const tvdb_grid_t *grid, tvdb_sparse_grid *out) {
    if (!grid || !out) return false;
    if (!grid_is_float(grid)) return false;
    out->count = 0;
    float origin[3];
    grid_voxel_size_origin(grid, &out->voxel_size, origin);
    out->ox = origin[0]; out->oy = origin[1]; out->oz = origin[2];
    sparse_acc_t a;
    a.out = out; a.failed = 0;
    tvdb_grid_visit_leaves_float(grid, sparse_visit, &a);
    return !a.failed;
}

// ----- materialize_dense -----

typedef struct {
    tvdb_dense_grid *out;
    int32_t bb_min[3], bb_max[3];
} mat_ctx_t;

static int materialize_visit(const tvdb_leaf_view_t *leaf, void *user) {
    mat_ctx_t *c = (mat_ctx_t *)user;
    int L = leaf->log2dim;
    int32_t dim = 1 << L;
    // Quick AABB cull
    if (leaf->origin[0] + dim <= c->bb_min[0] || leaf->origin[0] >= c->bb_max[0] ||
        leaf->origin[1] + dim <= c->bb_min[1] || leaf->origin[1] >= c->bb_max[1] ||
        leaf->origin[2] + dim <= c->bb_min[2] || leaf->origin[2] >= c->bb_max[2]) return 0;

    tvdb_dense_grid *o = c->out;
    int32_t lin = 0;
    for (int32_t i = 0; i < dim; ++i) {
        int32_t wx = leaf->origin[0] + i;
        for (int32_t j = 0; j < dim; ++j) {
            int32_t wy = leaf->origin[1] + j;
            for (int32_t k = 0; k < dim; ++k, ++lin) {
                int32_t wz = leaf->origin[2] + k;
                if (wx < c->bb_min[0] || wx >= c->bb_max[0]) continue;
                if (wy < c->bb_min[1] || wy >= c->bb_max[1]) continue;
                if (wz < c->bb_min[2] || wz >= c->bb_max[2]) continue;
                if (!tvdb_nodemask_is_on(leaf->value_mask, lin)) continue;
                int32_t ox_ = wx - c->bb_min[0];
                int32_t oy_ = wy - c->bb_min[1];
                int32_t oz_ = wz - c->bb_min[2];
                size_t idx = (size_t)((oz_ * o->ny + oy_) * o->nx + ox_);
                o->data[idx] = leaf->data[lin];
            }
        }
    }
    return 0;
}

float tvdb_grid_float_background(const tvdb_grid_t *grid) {
    if (!grid || grid->tree.num_nodes == 0) return 0.0f;
    if (!grid_is_float(grid)) return 0.0f;
    const tvdb_value_t *bg = &grid->tree.nodes[0].u.root.background;
    return bg->type == TVDB_VALUE_FLOAT ? bg->u.f : 0.0f;
}

bool tvdb_grid_materialize_dense(const tvdb_grid_t *grid,
                                 const int32_t bbox_min[3],
                                 const int32_t bbox_max[3],
                                 float background,
                                 tvdb_dense_grid *out) {
    if (!grid || !out || !bbox_min || !bbox_max) return false;
    if (!grid_is_float(grid)) return false;
    int32_t nx = bbox_max[0] - bbox_min[0];
    int32_t ny = bbox_max[1] - bbox_min[1];
    int32_t nz = bbox_max[2] - bbox_min[2];
    if (nx <= 0 || ny <= 0 || nz <= 0) return false;

    out->nx = nx; out->ny = ny; out->nz = nz;
    float vs; float go[3];
    grid_voxel_size_origin(grid, &vs, go);
    out->voxel_size = vs;
    out->ox = go[0] + (float)bbox_min[0] * vs;
    out->oy = go[1] + (float)bbox_min[1] * vs;
    out->oz = go[2] + (float)bbox_min[2] * vs;
    size_t total = (size_t)nx * (size_t)ny * (size_t)nz;
    out->data = (float *)malloc(total * sizeof(float));
    if (!out->data) return false;
    for (size_t i = 0; i < total; ++i) out->data[i] = background;

    mat_ctx_t c;
    c.out = out;
    c.bb_min[0] = bbox_min[0]; c.bb_min[1] = bbox_min[1]; c.bb_min[2] = bbox_min[2];
    c.bb_max[0] = bbox_max[0]; c.bb_max[1] = bbox_max[1]; c.bb_max[2] = bbox_max[2];
    tvdb_grid_visit_leaves_float(grid, materialize_visit, &c);
    return true;
}

// ----- leaf-stamp dilate / erode -----

typedef struct {
    int32_t lcoord[3];     // leaf coord (origin >> log2dim)
    const float *data;
    const tvdb_nodemask_t *value_mask;
    int log2dim;
} leaf_entry_t;

typedef struct {
    leaf_entry_t *entries;
    size_t        count;
    size_t        capacity;
    int           log2dim;  // shared across all leaves in a single-grid type
} leaf_collect_t;

typedef struct {
    uint64_t lkey;
    uint32_t idx_plus_one;  // 0 = empty
} leaf_hash_entry_t;

static uint64_t pack_leaf_key(int32_t lx, int32_t ly, int32_t lz) {
    uint64_t ux = (uint64_t)((int64_t)lx + (1LL << 20)) & ((1ULL << 21) - 1);
    uint64_t uy = (uint64_t)((int64_t)ly + (1LL << 20)) & ((1ULL << 21) - 1);
    uint64_t uz = (uint64_t)((int64_t)lz + (1LL << 20)) & ((1ULL << 21) - 1);
    return (ux << 42) | (uy << 21) | uz;
}

static uint64_t mix64_(uint64_t k) {
    k ^= k >> 33; k *= 0xff51afd7ed558ccdULL;
    k ^= k >> 33; k *= 0xc4ceb9fe1a85ec53ULL;
    k ^= k >> 33; return k;
}

static size_t pow2_(size_t v) { size_t p = 1; while (p < v) p <<= 1; return p; }

static int collect_visit(const tvdb_leaf_view_t *leaf, void *user) {
    leaf_collect_t *c = (leaf_collect_t *)user;
    if (c->count == c->capacity) {
        size_t cap = c->capacity ? c->capacity * 2 : 64;
        leaf_entry_t *ne = (leaf_entry_t *)realloc(c->entries, cap * sizeof(leaf_entry_t));
        if (!ne) return 1;
        c->entries = ne;
        c->capacity = cap;
    }
    c->log2dim = leaf->log2dim;
    leaf_entry_t *e = &c->entries[c->count++];
    e->lcoord[0] = leaf->origin[0] >> leaf->log2dim;
    e->lcoord[1] = leaf->origin[1] >> leaf->log2dim;
    e->lcoord[2] = leaf->origin[2] >> leaf->log2dim;
    e->data = leaf->data;
    e->value_mask = leaf->value_mask;
    e->log2dim = leaf->log2dim;
    return 0;
}

static int leaf_hash_lookup(const leaf_hash_entry_t *tbl, size_t mask,
                            const leaf_entry_t *entries,
                            int32_t lx, int32_t ly, int32_t lz) {
    uint64_t key = pack_leaf_key(lx, ly, lz);
    size_t h = (size_t)(mix64_(key) & mask);
    while (tbl[h].idx_plus_one) {
        size_t idx = tbl[h].idx_plus_one - 1;
        if (entries[idx].lcoord[0] == lx &&
            entries[idx].lcoord[1] == ly &&
            entries[idx].lcoord[2] == lz) return (int)idx;
        h = (h + 1) & mask;
    }
    return -1;
}

// Apply a single dilate (is_dilate=1) / erode (is_dilate=0) step.
// Reads from `cur` (a leaf_collect_t whose values come from `cur_values`
// or directly from leaf->data on the first step), writes voxel coord+value
// pairs into `out`.
static bool dilate_step(const leaf_collect_t *leaves,
                        const float *current_values, // NULL on first step (use leaf->data)
                        float background, int is_dilate,
                        tvdb_sparse_grid *out, float voxel_size,
                        float ox, float oy, float oz) {
    out->count = 0;
    out->voxel_size = voxel_size;
    out->ox = ox; out->oy = oy; out->oz = oz;

    // Build leaf hash for fast neighbor leaf lookup.
    size_t cap = pow2_(leaves->count * 2 + 16);
    leaf_hash_entry_t *htbl = (leaf_hash_entry_t *)calloc(cap, sizeof(leaf_hash_entry_t));
    if (!htbl) return false;
    size_t mask = cap - 1;
    for (size_t i = 0; i < leaves->count; ++i) {
        uint64_t key = pack_leaf_key(leaves->entries[i].lcoord[0],
                                     leaves->entries[i].lcoord[1],
                                     leaves->entries[i].lcoord[2]);
        size_t h = (size_t)(mix64_(key) & mask);
        while (htbl[h].idx_plus_one) h = (h + 1) & mask;
        htbl[h].lkey = key;
        htbl[h].idx_plus_one = (uint32_t)(i + 1);
    }

    int L = leaves->log2dim;
    int32_t dim = 1 << L;
    int32_t dim_mask = dim - 1;
    size_t leaf_voxels = (size_t)dim * dim * dim;
    // OpenVDB leaf layout: linear = (i << 2L) | (j << L) | k.

    // Per-leaf offset into current_values (if provided): leaves are stored in
    // the same order as `leaves->entries`; values are flat dim^3 per leaf.
    const float *(get_data)(const leaf_collect_t *, size_t, const float *);
    (void)get_data;

    for (size_t li = 0; li < leaves->count; ++li) {
        const leaf_entry_t *leaf = &leaves->entries[li];
        const float *self_data = current_values
            ? current_values + li * leaf_voxels
            : leaf->data;

        // Pre-resolve 6 neighbor leaf data pointers (NULL if absent).
        int neighbors[6];
        for (int i = 0; i < 6; ++i) neighbors[i] = -1;
        // order: -x, +x, -y, +y, -z, +z
        neighbors[0] = leaf_hash_lookup(htbl, mask, leaves->entries,
                                        leaf->lcoord[0]-1, leaf->lcoord[1], leaf->lcoord[2]);
        neighbors[1] = leaf_hash_lookup(htbl, mask, leaves->entries,
                                        leaf->lcoord[0]+1, leaf->lcoord[1], leaf->lcoord[2]);
        neighbors[2] = leaf_hash_lookup(htbl, mask, leaves->entries,
                                        leaf->lcoord[0], leaf->lcoord[1]-1, leaf->lcoord[2]);
        neighbors[3] = leaf_hash_lookup(htbl, mask, leaves->entries,
                                        leaf->lcoord[0], leaf->lcoord[1]+1, leaf->lcoord[2]);
        neighbors[4] = leaf_hash_lookup(htbl, mask, leaves->entries,
                                        leaf->lcoord[0], leaf->lcoord[1], leaf->lcoord[2]-1);
        neighbors[5] = leaf_hash_lookup(htbl, mask, leaves->entries,
                                        leaf->lcoord[0], leaf->lcoord[1], leaf->lcoord[2]+1);

        const float *nb_data[6] = {0};
        for (int n = 0; n < 6; ++n) {
            if (neighbors[n] >= 0) {
                nb_data[n] = current_values
                    ? current_values + (size_t)neighbors[n] * leaf_voxels
                    : leaves->entries[neighbors[n]].data;
            }
        }

        int32_t origin_x = leaf->lcoord[0] << L;
        int32_t origin_y = leaf->lcoord[1] << L;
        int32_t origin_z = leaf->lcoord[2] << L;

        for (int32_t i = 0; i < dim; ++i) {
            for (int32_t j = 0; j < dim; ++j) {
                for (int32_t k = 0; k < dim; ++k) {
                    int32_t lin = (i << (2*L)) | (j << L) | k;
                    if (!tvdb_nodemask_is_on(leaf->value_mask, lin)) continue;
                    float c = self_data[lin];
                    float nb_vals[6];
                    // -x (i-1)
                    if (i > 0) nb_vals[0] = self_data[((i-1) << (2*L)) | (j << L) | k];
                    else if (nb_data[0]) nb_vals[0] = nb_data[0][((dim-1) << (2*L)) | (j << L) | k];
                    else nb_vals[0] = background;
                    // +x
                    if (i < dim-1) nb_vals[1] = self_data[((i+1) << (2*L)) | (j << L) | k];
                    else if (nb_data[1]) nb_vals[1] = nb_data[1][(0 << (2*L)) | (j << L) | k];
                    else nb_vals[1] = background;
                    // -y
                    if (j > 0) nb_vals[2] = self_data[(i << (2*L)) | ((j-1) << L) | k];
                    else if (nb_data[2]) nb_vals[2] = nb_data[2][(i << (2*L)) | ((dim-1) << L) | k];
                    else nb_vals[2] = background;
                    // +y
                    if (j < dim-1) nb_vals[3] = self_data[(i << (2*L)) | ((j+1) << L) | k];
                    else if (nb_data[3]) nb_vals[3] = nb_data[3][(i << (2*L)) | (0 << L) | k];
                    else nb_vals[3] = background;
                    // -z
                    if (k > 0) nb_vals[4] = self_data[(i << (2*L)) | (j << L) | (k-1)];
                    else if (nb_data[4]) nb_vals[4] = nb_data[4][(i << (2*L)) | (j << L) | (dim-1)];
                    else nb_vals[4] = background;
                    // +z
                    if (k < dim-1) nb_vals[5] = self_data[(i << (2*L)) | (j << L) | (k+1)];
                    else if (nb_data[5]) nb_vals[5] = nb_data[5][(i << (2*L)) | (j << L) | 0];
                    else nb_vals[5] = background;

                    float r = c;
                    if (is_dilate) {
                        for (int n = 0; n < 6; ++n) if (nb_vals[n] < r) r = nb_vals[n];
                    } else {
                        for (int n = 0; n < 6; ++n) if (nb_vals[n] > r) r = nb_vals[n];
                    }

                    int32_t wx = origin_x + i;
                    int32_t wy = origin_y + j;
                    int32_t wz = origin_z + k;
                    if (out->count == out->capacity) {
                        size_t newcap = out->capacity ? out->capacity * 2 : 1024;
                        if (!tvdb_sparse_grid_reserve(out, newcap)) {
                            free(htbl); return false;
                        }
                    }
                    out->coords[out->count].x = wx;
                    out->coords[out->count].y = wy;
                    out->coords[out->count].z = wz;
                    out->values[out->count] = r;
                    ++out->count;
                }
            }
        }
    }
    free(htbl);
    return true;
}

static bool grid_dilate_erode_active(const tvdb_grid_t *grid, int iterations,
                                     int is_dilate, tvdb_sparse_grid *out) {
    if (!grid || !out || iterations <= 0 || !grid_is_float(grid)) return false;

    leaf_collect_t leaves = { NULL, 0, 0, 0 };
    tvdb_grid_visit_leaves_float(grid, collect_visit, &leaves);
    if (leaves.count == 0) { free(leaves.entries); return false; }

    float background = tvdb_grid_float_background(grid);
    float vs; float go[3];
    grid_voxel_size_origin(grid, &vs, go);

    int L = leaves.log2dim;
    size_t leaf_voxels = (size_t)1 << (3 * L);
    size_t total_voxels = leaves.count * leaf_voxels;

    // We need a per-leaf flat buffer of values to ping-pong between iterations.
    // First step reads from leaf->data (sparse but indexed via OpenVDB layout);
    // subsequent steps read from a packed buffer of size total_voxels.
    float *buf_a = NULL, *buf_b = NULL;
    if (iterations > 1) {
        buf_a = (float *)malloc(total_voxels * sizeof(float));
        buf_b = (float *)malloc(total_voxels * sizeof(float));
        if (!buf_a || !buf_b) { free(buf_a); free(buf_b); free(leaves.entries); return false; }
    }

    tvdb_sparse_grid scratch; tvdb_sparse_grid_init(&scratch);
    out->count = 0;
    out->voxel_size = vs;
    out->ox = go[0]; out->oy = go[1]; out->oz = go[2];

    const float *cur_values = NULL;
    for (int it = 0; it < iterations; ++it) {
        tvdb_sparse_grid *target = (it & 1) ? &scratch : out;
        if (!dilate_step(&leaves, cur_values, background, is_dilate,
                         target, vs, go[0], go[1], go[2])) {
            free(buf_a); free(buf_b); free(leaves.entries);
            tvdb_sparse_grid_free(&scratch);
            return false;
        }
        if (it + 1 < iterations) {
            // Pack target's values back into a flat per-leaf buffer for next iteration.
            // Since target was produced by walking leaves in `leaves` order with full
            // dim^3 emission per leaf (active voxels only), but the OUTPUT is
            // *only active voxels*, the packing into a dense per-leaf buffer is
            // approximate. For correctness across iterations we instead expand
            // the active set's worth of values into a buffer initialized to
            // background, then index into it.
            float *dst = (it & 1) ? buf_a : buf_b;
            for (size_t i = 0; i < total_voxels; ++i) dst[i] = background;
            for (size_t k = 0; k < target->count; ++k) {
                int32_t wx = target->coords[k].x;
                int32_t wy = target->coords[k].y;
                int32_t wz = target->coords[k].z;
                int32_t lx = wx >> L, ly = wy >> L, lz = wz >> L;
                // Find the leaf in `leaves` matching (lx, ly, lz).
                // Linear scan is fine for small leaf counts; for large trees,
                // build a hash once outside the loop.
                size_t li = (size_t)-1;
                for (size_t s = 0; s < leaves.count; ++s) {
                    if (leaves.entries[s].lcoord[0] == lx &&
                        leaves.entries[s].lcoord[1] == ly &&
                        leaves.entries[s].lcoord[2] == lz) { li = s; break; }
                }
                if (li == (size_t)-1) continue;
                int32_t i_ = wx & ((1<<L)-1);
                int32_t j_ = wy & ((1<<L)-1);
                int32_t k_ = wz & ((1<<L)-1);
                int32_t lin = (i_ << (2*L)) | (j_ << L) | k_;
                dst[li * leaf_voxels + (size_t)lin] = target->values[k];
            }
            cur_values = dst;
        }
    }

    // After iteration `it=iterations-1`: target = (it & 1) ? &scratch : out.
    // So scratch holds the final result iff (iterations-1) is odd, i.e.
    // iterations is even (and >= 2). Move it into `out` in that case.
    if (iterations >= 2 && ((iterations & 1) == 0)) {
        tvdb_sparse_grid_free(out);
        *out = scratch;
        scratch.coords = NULL; scratch.values = NULL;
        scratch.count = 0; scratch.capacity = 0;
    }

    tvdb_sparse_grid_free(&scratch);
    free(buf_a); free(buf_b);
    free(leaves.entries);
    return true;
}

bool tvdb_grid_dilate_active(const tvdb_grid_t *grid, int iterations,
                             tvdb_sparse_grid *out) {
    return grid_dilate_erode_active(grid, iterations, /*is_dilate=*/1, out);
}

bool tvdb_grid_erode_active(const tvdb_grid_t *grid, int iterations,
                            tvdb_sparse_grid *out) {
    return grid_dilate_erode_active(grid, iterations, /*is_dilate=*/0, out);
}

// ----- topology-growing dilate + tree-aware CSG -----

bool tvdb_grid_dilate_topology(const tvdb_grid_t *grid, int iterations,
                               tvdb_sparse_grid *out) {
    if (!grid || !out) return false;
    tvdb_sparse_grid sg; tvdb_sparse_grid_init(&sg);
    if (!tvdb_grid_to_sparse(grid, &sg)) {
        tvdb_sparse_grid_free(&sg);
        return false;
    }
    float bg = tvdb_grid_float_background(grid);
    bool ok = tvdb_dilate_sparse(&sg, bg, iterations, out);
    tvdb_sparse_grid_free(&sg);
    return ok;
}

bool tvdb_grid_erode_topology(const tvdb_grid_t *grid, int iterations,
                              tvdb_sparse_grid *out) {
    if (!grid || !out) return false;
    tvdb_sparse_grid sg; tvdb_sparse_grid_init(&sg);
    if (!tvdb_grid_to_sparse(grid, &sg)) {
        tvdb_sparse_grid_free(&sg);
        return false;
    }
    bool ok = tvdb_erode_sparse(&sg, iterations, out);
    tvdb_sparse_grid_free(&sg);
    return ok;
}

static bool tree_csg_dispatch(const tvdb_grid_t *a, const tvdb_grid_t *b,
                              tvdb_sparse_grid *out,
                              int op /*0:U 1:I 2:D*/) {
    if (!a || !b || !out) return false;
    tvdb_sparse_grid sa; tvdb_sparse_grid_init(&sa);
    tvdb_sparse_grid sb; tvdb_sparse_grid_init(&sb);
    bool ok = tvdb_grid_to_sparse(a, &sa) && tvdb_grid_to_sparse(b, &sb);
    if (!ok) {
        tvdb_sparse_grid_free(&sa);
        tvdb_sparse_grid_free(&sb);
        return false;
    }
    float bg = tvdb_grid_float_background(a);
    bool r = false;
    if (op == 0) r = tvdb_csg_union_sparse(&sa, &sb, bg, out);
    else if (op == 1) r = tvdb_csg_intersection_sparse(&sa, &sb, bg, out);
    else if (op == 2) r = tvdb_csg_difference_sparse(&sa, &sb, bg, out);
    tvdb_sparse_grid_free(&sa);
    tvdb_sparse_grid_free(&sb);
    return r;
}

bool tvdb_grid_csg_union(const tvdb_grid_t *a, const tvdb_grid_t *b,
                         tvdb_sparse_grid *out) {
    return tree_csg_dispatch(a, b, out, 0);
}
bool tvdb_grid_csg_intersection(const tvdb_grid_t *a, const tvdb_grid_t *b,
                                tvdb_sparse_grid *out) {
    return tree_csg_dispatch(a, b, out, 1);
}
bool tvdb_grid_csg_difference(const tvdb_grid_t *a, const tvdb_grid_t *b,
                              tvdb_sparse_grid *out) {
    return tree_csg_dispatch(a, b, out, 2);
}

// ----- update_from_sparse: topology-preserving voxel-value write -----

typedef struct mutable_leaf {
    int32_t  lcoord[3];   // leaf-coord (origin >> log2dim)
    int32_t  log2dim;
    float   *data;        // dim^3 floats (writable)
    tvdb_nodemask_t *value_mask; // writable
} mutable_leaf_t;

typedef struct mutable_leaf_collect {
    mutable_leaf_t *entries;
    size_t          count;
    size_t          capacity;
    int             log2dim;
} mutable_leaf_collect_t;

static void collect_mutable_leaves(tvdb_tree_t *tree, size_t node_idx,
                                   const int32_t parent_origin[3],
                                   mutable_leaf_collect_t *out) {
    if (!tree || node_idx >= tree->num_nodes) return;
    tvdb_tree_node_t *node = &tree->nodes[node_idx];
    if (node->type == TVDB_NODE_LEAF) {
        if (out->count == out->capacity) {
            size_t cap = out->capacity ? out->capacity * 2 : 64;
            mutable_leaf_t *ne = (mutable_leaf_t *)realloc(out->entries, cap * sizeof(mutable_leaf_t));
            if (!ne) return;
            out->entries = ne;
            out->capacity = cap;
        }
        mutable_leaf_t *e = &out->entries[out->count++];
        int32_t L = (int32_t)node->u.leaf.value_mask.log2dim;
        e->log2dim = L;
        e->lcoord[0] = parent_origin[0] >> L;
        e->lcoord[1] = parent_origin[1] >> L;
        e->lcoord[2] = parent_origin[2] >> L;
        e->data = (float *)node->u.leaf.data;
        e->value_mask = &node->u.leaf.value_mask;
        out->log2dim = L;
        return;
    }
    if (node->type == TVDB_NODE_ROOT) {
        const tvdb_root_node_t *root = &node->u.root;
        for (size_t c = 0; c < root->num_children; ++c) {
            int32_t co[3] = {
                root->child_origins[3*c+0],
                root->child_origins[3*c+1],
                root->child_origins[3*c+2]
            };
            collect_mutable_leaves(tree, root->child_indices[c], co, out);
        }
        return;
    }
    // Internal node: same descent as visit_subtree, but mutable.
    const tvdb_internal_node_t *in = &node->u.internal;
    int my_level = node->level;
    int my_log2dim = tree->layout.levels[my_level].log2dim;
    int sum = 0;
    for (int lv = my_level + 1; lv < tree->layout.num_levels; ++lv) {
        sum += tree->layout.levels[lv].log2dim;
    }
    int32_t child_dim = 1 << sum;
    int32_t total = 1 << (3 * my_log2dim);
    size_t c_idx = 0;
    int parent_dim_mask = (1 << my_log2dim) - 1;
    for (int32_t s = 0; s < total && c_idx < in->num_children; ++s) {
        if (!(in->child_mask.bits.data[s >> 3] & (1 << (s & 7)))) continue;
        int32_t ix = (s >> (2 * my_log2dim)) & parent_dim_mask;
        int32_t iy = (s >> my_log2dim)       & parent_dim_mask;
        int32_t iz = s & parent_dim_mask;
        int32_t co[3] = {
            parent_origin[0] + ix * child_dim,
            parent_origin[1] + iy * child_dim,
            parent_origin[2] + iz * child_dim
        };
        collect_mutable_leaves(tree, in->child_indices[c_idx], co, out);
        ++c_idx;
    }
}

size_t tvdb_grid_update_from_sparse(tvdb_grid_t *grid,
                                    const tvdb_sparse_grid *sg,
                                    size_t *out_skipped) {
    if (out_skipped) *out_skipped = 0;
    if (!grid || !sg || sg->count == 0) return 0;
    if (!grid_is_float(grid)) return 0;
    if (grid->tree.num_nodes == 0) return 0;

    mutable_leaf_collect_t leaves; memset(&leaves, 0, sizeof(leaves));
    int32_t zero_origin[3] = {0,0,0};
    collect_mutable_leaves(&grid->tree, 0, zero_origin, &leaves);
    if (leaves.count == 0) {
        free(leaves.entries);
        if (out_skipped) *out_skipped = sg->count;
        return 0;
    }

    int L = leaves.log2dim;
    int32_t dim_mask = (1 << L) - 1;

    // Build hash table on leaf-coords.
    size_t cap = pow2_(leaves.count * 2 + 16);
    leaf_hash_entry_t *htbl = (leaf_hash_entry_t *)calloc(cap, sizeof(leaf_hash_entry_t));
    if (!htbl) { free(leaves.entries); return 0; }
    size_t mask = cap - 1;
    for (size_t i = 0; i < leaves.count; ++i) {
        uint64_t key = pack_leaf_key(leaves.entries[i].lcoord[0],
                                     leaves.entries[i].lcoord[1],
                                     leaves.entries[i].lcoord[2]);
        size_t h = (size_t)(mix64_(key) & mask);
        while (htbl[h].idx_plus_one) h = (h + 1) & mask;
        htbl[h].lkey = key;
        htbl[h].idx_plus_one = (uint32_t)(i + 1);
    }

    size_t updated = 0, skipped = 0;
    for (size_t i = 0; i < sg->count; ++i) {
        int32_t cx = sg->coords[i].x, cy = sg->coords[i].y, cz = sg->coords[i].z;
        int32_t lcx = cx >> L, lcy = cy >> L, lcz = cz >> L;
        // Hash lookup: linear-probe until idx matches or empty.
        uint64_t key = pack_leaf_key(lcx, lcy, lcz);
        size_t h = (size_t)(mix64_(key) & mask);
        int found = -1;
        while (htbl[h].idx_plus_one) {
            size_t idx = htbl[h].idx_plus_one - 1;
            if (leaves.entries[idx].lcoord[0] == lcx &&
                leaves.entries[idx].lcoord[1] == lcy &&
                leaves.entries[idx].lcoord[2] == lcz) {
                found = (int)idx;
                break;
            }
            h = (h + 1) & mask;
        }
        if (found < 0) { ++skipped; continue; }
        int32_t lx = cx & dim_mask;
        int32_t ly = cy & dim_mask;
        int32_t lz = cz & dim_mask;
        int32_t slot = (lx << (2 * L)) | (ly << L) | lz;
        leaves.entries[found].data[slot] = sg->values[i];
        tvdb_nodemask_set_on(leaves.entries[found].value_mask, slot);
        ++updated;
    }

    free(htbl);
    free(leaves.entries);
    if (out_skipped) *out_skipped = skipped;
    return updated;
}
