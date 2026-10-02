#include "sdf_tree_fixture.h"
#include "tinyvdb_ops.h"
#include <float.h>
#include <stdio.h>
static int failures;
#define CHECK(c)                                                                                   \
    do {                                                                                           \
        if (!(c)) {                                                                                \
            fprintf(stderr, "FAIL %d: %s\n", __LINE__, #c);                                        \
            ++failures;                                                                            \
        }                                                                                          \
    } while (0)
#define OK(call)                                                                                   \
    do {                                                                                           \
        tvdb_status_t st = (call);                                                                 \
        if (st != TVDB_OK) {                                                                       \
            fprintf(stderr, "FAIL %d: status %d: %s\n", __LINE__, st, err.message);                \
            ++failures;                                                                            \
            return;                                                                                \
        }                                                                                          \
    } while (0)
static void check_sweep(tvdb_thread_pool_t *one, tvdb_thread_pool_t *many, int sphere, int narrow) {
    tvdb_error_t err = {0};
    tvdb_grid_t a = {0}, b = {0}, ref = {0};
    CHECK(sdf_fixture_cube(&a, 24, sphere, narrow));
    CHECK(sdf_fixture_cube(&b, 24, sphere, narrow));
    CHECK(sdf_fixture_cube(&ref, 24, sphere, narrow));
    tvdb_sdf_tree_t *wa = NULL, *wb = NULL;
    OK(tvdb_sdf_tree_create(&a, one, NULL, &wa, &err));
    OK(tvdb_sdf_tree_create(&b, many, NULL, &wb, &err));
    tvdb_dense_grid dense = {0};
    if (!narrow) {
        tvdb_dense_grid_init(&dense, 24, 24, 24);
        for (int x = 0; x < 24; ++x)
            for (int y = 0; y < 24; ++y)
                for (int z = 0; z < 24; ++z)
                    dense.data[(z * 24 + y) * 24 + x] = *sdf_fixture_at(&a, x, y, z);
        CHECK(tvdb_fast_sweeping(&dense, 1.5f, 12, 1e-5f) > 0);
    }
    tvdb_sdf_sweep_result_t ra, rb;
    OK(tvdb_sdf_tree_fast_sweep(wa, 1.5f, 12, 1e-5f, &ra, &err));
    OK(tvdb_sdf_tree_fast_sweep(wb, 1.5f, 12, 1e-5f, &rb, &err));
    CHECK(ra.converged && rb.converged);
    CHECK(!ra.unreached_voxels);
    CHECK(ra.iterations == rb.iterations);
    CHECK(ra.max_change == rb.max_change);
    tvdb_sparse_grid sa = {0}, sb = {0}, sref = {0};
    CHECK(tvdb_grid_to_sparse(&a, &sa));
    CHECK(tvdb_grid_to_sparse(&b, &sb));
    CHECK(tvdb_grid_to_sparse(&ref, &sref));
    CHECK(sa.count == sb.count);
    CHECK(sa.count == sref.count);
    CHECK(!memcmp(sa.coords, sref.coords, sa.count * sizeof(tvdb_vec3i)));
    CHECK(!memcmp(sa.values, sb.values, sa.count * sizeof(float)));
    float worst = 0;
    for (size_t i = 0; i < sa.count; ++i) {
        float x = sa.coords[i].x + 0.5f - 12, y = sa.coords[i].y + 0.5f - 12,
              z = sa.coords[i].z + 0.5f - 12;
        float exact = sphere ? sqrtf(x * x + y * y + z * z) - 24 * 0.28f : x;
        if (!narrow)
            CHECK(fabsf(sa.values[i] -
                        dense.data[(sa.coords[i].z * 24 + sa.coords[i].y) * 24 + sa.coords[i].x]) <
                  1e-4f);
        float error = fabsf(sa.values[i] - exact);
        if (error > worst)
            worst = error;
        CHECK((sa.values[i] >= 0) == (exact >= 0));
        /* Seeded boundary voxels are fixed; compare with the unswept input
         * rather than recomputing it, since FMA contraction may differ. */
        if (fabsf(sref.values[i]) <= 1.5f)
            CHECK(sa.values[i] == sref.values[i]);
    }
    CHECK(worst < (sphere ? 3.0f : 1e-6f));
    printf("tree sweep sphere=%d narrow=%d active=%zu iter=%d max_error=%g\n", sphere, narrow,
           sa.count, ra.iterations, worst);
    tvdb_sdf_tree_info_t info;
    tvdb_sdf_tree_info(wa, &info);
    CHECK(info.scratch_bytes == 4 * info.active_voxels + (info.active_voxels + 3) / 4);
    tvdb_dense_grid_free(&dense);
    tvdb_sparse_grid_free(&sa);
    tvdb_sparse_grid_free(&sb);
    tvdb_sparse_grid_free(&sref);
    tvdb_sdf_tree_destroy(wa);
    tvdb_sdf_tree_destroy(wb);
    tvdb_grid_destroy_owned(&a);
    tvdb_grid_destroy_owned(&b);
    tvdb_grid_destroy_owned(&ref);
}
static float reference_neighbor(const float *values, int n, int x, int y, int z) {
    if (x < 0 || x >= n || y < 0 || y >= n || z < 0 || z >= n)
        return 100;
    return values[((size_t)x * n + y) * n + z];
}
static void reference_filter(float *a, float *b, int n, tvdb_sdf_filter_t kind, int iterations) {
    int passes = kind <= TVDB_SDF_FILTER_GAUSSIAN ? 3 : 1;
    for (int iter = 0; iter < iterations; ++iter)
        for (int axis = 0; axis < passes; ++axis) {
            for (int x = 0; x < n; ++x)
                for (int y = 0; y < n; ++y)
                    for (int z = 0; z < n; ++z) {
                        size_t i = ((size_t)x * n + y) * n + z;
                        double v = a[i], sum = 0;
                        if (passes == 3) {
                            int dx = axis == 0, dy = axis == 1, dz = axis == 2;
                            double low = reference_neighbor(a, n, x - dx, y - dy, z - dz),
                                   high = reference_neighbor(a, n, x + dx, y + dy, z + dz);
                            v = kind == TVDB_SDF_FILTER_MEAN ? (low + v + high) / 3
                                                             : (low + 2 * v + high) / 4;
                        } else {
                            const int delta[6][3] = {{-1, 0, 0}, {1, 0, 0},  {0, -1, 0},
                                                     {0, 1, 0},  {0, 0, -1}, {0, 0, 1}};
                            for (int d = 0; d < 6; ++d) {
                                float w = reference_neighbor(a, n, x + delta[d][0], y + delta[d][1],
                                                             z + delta[d][2]);
                                sum += w;
                                if (kind == TVDB_SDF_FILTER_DILATE && w < v)
                                    v = w;
                                if (kind == TVDB_SDF_FILTER_ERODE && w > v)
                                    v = w;
                            }
                            if (kind == TVDB_SDF_FILTER_LAPLACIAN)
                                v = sum / 6;
                        }
                        b[i] = (float)v;
                    }
            memcpy(a, b, (size_t)n * n * n * sizeof(float));
        }
}
static void check_filters(tvdb_thread_pool_t *one, tvdb_thread_pool_t *many) {
    tvdb_error_t err = {0};
    const int n = 16;
    size_t count = (size_t)n * n * n;
    float *ref = malloc(count * 4), *temp = malloc(count * 4);
    CHECK(ref && temp);
    if (!ref || !temp)
        return;
    for (int kind = TVDB_SDF_FILTER_MEAN; kind <= TVDB_SDF_FILTER_ERODE; ++kind) {
        tvdb_grid_t a = {0}, b = {0};
        CHECK(sdf_fixture_cube(&a, n, 1, 0));
        CHECK(sdf_fixture_cube(&b, n, 1, 0));
        tvdb_sdf_tree_t *wa = NULL, *wb = NULL;
        OK(tvdb_sdf_tree_create(&a, one, NULL, &wa, &err));
        OK(tvdb_sdf_tree_create(&b, many, NULL, &wb, &err));
        for (int x = 0; x < n; ++x)
            for (int y = 0; y < n; ++y)
                for (int z = 0; z < n; ++z)
                    ref[((size_t)x * n + y) * n + z] = *sdf_fixture_at(&a, x, y, z);
        reference_filter(ref, temp, n, (tvdb_sdf_filter_t)kind, 3);
        OK(tvdb_sdf_tree_filter(wa, (tvdb_sdf_filter_t)kind, 3, &err));
        OK(tvdb_sdf_tree_filter(wb, (tvdb_sdf_filter_t)kind, 3, &err));
        for (int x = 0; x < n; ++x)
            for (int y = 0; y < n; ++y)
                for (int z = 0; z < n; ++z) {
                    float av = *sdf_fixture_at(&a, x, y, z), bv = *sdf_fixture_at(&b, x, y, z);
                    CHECK(av == bv);
                    CHECK(av == ref[((size_t)x * n + y) * n + z]);
                }
        OK(tvdb_sdf_tree_offset(wa, 0.75f, &err));
        for (int x = 0; x < n; ++x)
            for (int y = 0; y < n; ++y)
                for (int z = 0; z < n; ++z)
                    CHECK(*sdf_fixture_at(&a, x, y, z) ==
                          (float)((double)ref[((size_t)x * n + y) * n + z] + 0.75));
        tvdb_sdf_tree_info_t info;
        tvdb_sdf_tree_info(wa, &info);
        CHECK(info.scratch_bytes == 8 * count);
        tvdb_sdf_tree_destroy(wa);
        tvdb_sdf_tree_destroy(wb);
        tvdb_grid_destroy_owned(&a);
        tvdb_grid_destroy_owned(&b);
    }
    free(ref);
    free(temp);
}
/* Custom allocation records make every failing constructor/lazy allocation
 * observable, including the exact byte size passed back to free. */
typedef union {
    max_align_t alignment;
    size_t bytes;
} header;
typedef struct {
    size_t calls, fail, live, bytes, peak;
} tracking;
static void *allocate(size_t n, void *user) {
    tracking *t = user;
    if (++t->calls == t->fail)
        return NULL;
    header *h = malloc(sizeof(*h) + n);
    if (!h)
        return NULL;
    h->bytes = n;
    ++t->live;
    t->bytes += n;
    if (t->bytes > t->peak)
        t->peak = t->bytes;
    return h + 1;
}
static void release(void *v, size_t n, void *user) {
    if (!v)
        return;
    tracking *t = user;
    header *h = (header *)v - 1;
    CHECK(h->bytes == n);
    --t->live;
    t->bytes -= n;
    free(h);
}
static void check_contracts(tvdb_thread_pool_t *pool) {
    tvdb_error_t err = {0};
    tvdb_grid_t g = {0};
    CHECK(sdf_fixture_cube(&g, 8, 0, 0));
    for (size_t fail = 1; fail < 40; ++fail) {
        tracking t = {0};
        t.fail = fail;
        tvdb_allocator_t alloc = {allocate, NULL, release, &t};
        tvdb_sdf_tree_t *w = (void *)1;
        tvdb_status_t st = tvdb_sdf_tree_create(&g, pool, &alloc, &w, &err);
        if (st == TVDB_OK) {
            tvdb_sdf_tree_destroy(w);
            CHECK(!t.live && !t.bytes);
            break;
        }
        CHECK(st == TVDB_ERROR_OUT_OF_MEMORY);
        CHECK(!w);
        CHECK(!t.live && !t.bytes);
    }
    for (int operation = 0; operation < 2; ++operation)
        for (size_t fail = 1; fail <= 10; ++fail) {
            tracking t = {0};
            tvdb_allocator_t alloc = {allocate, NULL, release, &t};
            tvdb_sdf_tree_t *w = NULL;
            OK(tvdb_sdf_tree_create(&g, pool, &alloc, &w, &err));
            t.fail = t.calls + fail;
            float before[512];
            memcpy(before, sdf_fixture_at(&g, 0, 0, 0), sizeof(before));
            tvdb_status_t st = operation
                                   ? tvdb_sdf_tree_fast_sweep(w, 1.5f, 8, 1e-5f, NULL, &err)
                                   : tvdb_sdf_tree_filter(w, TVDB_SDF_FILTER_GAUSSIAN, 2, &err);
            if (st == TVDB_ERROR_OUT_OF_MEMORY) {
                CHECK(!memcmp(before, sdf_fixture_at(&g, 0, 0, 0), sizeof(before)));
                t.fail = 0;
                OK(tvdb_sdf_tree_fast_sweep(w, 1.5f, 8, 1e-5f, NULL, &err));
            } else
                CHECK(st == TVDB_OK);
            memcpy(sdf_fixture_at(&g, 0, 0, 0), before, sizeof(before));
            tvdb_sdf_tree_destroy(w);
            CHECK(!t.live && !t.bytes);
        }
    tvdb_sdf_tree_t *w = NULL;
    OK(tvdb_sdf_tree_create(&g, pool, NULL, &w, &err));
    float before[512];
    float *data = sdf_fixture_at(&g, 0, 0, 0);
    memcpy(before, data, sizeof(before));
    CHECK(tvdb_sdf_tree_filter(w, (tvdb_sdf_filter_t)99, 1, &err) == TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(tvdb_sdf_tree_filter(w, TVDB_SDF_FILTER_MEAN, -1, &err) == TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(tvdb_sdf_tree_offset(w, NAN, &err) == TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(tvdb_sdf_tree_fast_sweep(w, -1, 4, 0, NULL, &err) == TVDB_ERROR_INVALID_ARGUMENT);
    OK(tvdb_sdf_tree_filter(w, TVDB_SDF_FILTER_MEAN, 0, &err));
    OK(tvdb_sdf_tree_fast_sweep(w, 1.5f, 0, 0, NULL, &err));
    CHECK(!memcmp(before, data, sizeof(before)));
    data[200] = NAN;
    float saved[512];
    memcpy(saved, data, sizeof(saved));
    CHECK(tvdb_sdf_tree_offset(w, 1, &err) == TVDB_ERROR_INVALID_DATA);
    CHECK(!memcmp(saved, data, sizeof(saved)));
    memcpy(data, before, sizeof(before));
    for (int i = 0; i < 512; ++i)
        data[i] = FLT_MAX;
    CHECK(tvdb_sdf_tree_offset(w, FLT_MAX, &err) == TVDB_ERROR_INVALID_DATA);
    for (int i = 0; i < 512; ++i)
        CHECK(data[i] == FLT_MAX);
    tvdb_sdf_sweep_result_t r;
    OK(tvdb_sdf_tree_fast_sweep(w, 0, 8, 0, &r, &err));
    CHECK(!r.converged && r.unreached_voxels == 512 && !r.iterations);
    memcpy(data, before, sizeof(before));
    tvdb_sdf_tree_destroy(w);
    g.transform.type = TVDB_TRANSFORM_SCALE;
    g.transform.voxel_size[1] = 2;
    g.transform.voxel_size[2] = 1;
    CHECK(tvdb_sdf_tree_create(&g, pool, NULL, &w, &err) == TVDB_ERROR_UNSUPPORTED_TRANSFORM);
    CHECK(!w);
    /* A rotated, translated uniform affine map keeps world-distance spacing. */
    g.transform.type = TVDB_TRANSFORM_AFFINE;
    memset(g.transform.matrix, 0, sizeof(g.transform.matrix));
    g.transform.matrix[0][1] = -2;
    g.transform.matrix[1][0] = 2;
    g.transform.matrix[2][2] = 2;
    g.transform.matrix[3][3] = 1;
    g.transform.matrix[0][3] = 25;
    for (int i = 0; i < 512; ++i) {
        float exact = ((i >> 6) + 0.5f - 4) * 2;
        data[i] = fabsf(exact) <= 1 ? exact : exact < 0 ? -100 : 100;
    }
    OK(tvdb_sdf_tree_create(&g, pool, NULL, &w, &err));
    OK(tvdb_sdf_tree_fast_sweep(w, 1, 8, 0, &r, &err));
    CHECK(r.converged);
    for (int i = 0; i < 512; ++i)
        CHECK(data[i] == ((i >> 6) + 0.5f - 4) * 2);
    tvdb_sdf_tree_destroy(w);
    g.transform.matrix[0][2] = 2;
    g.transform.matrix[2][2] = 0;
    CHECK(tvdb_sdf_tree_create(&g, pool, NULL, &w, &err) == TVDB_ERROR_UNSUPPORTED_TRANSFORM);
    CHECK(!w);
    memcpy(data, before, sizeof(before));
    g.transform.type = TVDB_TRANSFORM_UNIFORM_SCALE;
    size_t child = g.tree.nodes[0].u.root.child_indices[0];
    g.tree.nodes[0].u.root.child_indices[0] = 0;
    CHECK(tvdb_sdf_tree_create(&g, pool, NULL, &w, &err) == TVDB_ERROR_INVALID_DATA);
    CHECK(!w);
    g.tree.nodes[0].u.root.child_indices[0] = child;
    tvdb_internal_node_t *internal = &g.tree.nodes[child].u.internal;
    ++internal->num_children;
    CHECK(tvdb_sdf_tree_create(&g, pool, NULL, &w, &err) == TVDB_ERROR_INVALID_DATA);
    CHECK(!w);
    --internal->num_children;
    g.transform.voxel_size[0] = FLT_MAX;
    data[0] = FLT_MAX / 2;
    for (int i = 1; i < 512; ++i)
        data[i] = FLT_MAX;
    memcpy(saved, data, sizeof(saved));
    OK(tvdb_sdf_tree_create(&g, pool, NULL, &w, &err));
    CHECK(tvdb_sdf_tree_fast_sweep(w, FLT_MAX / 2, 8, 0, NULL, &err) == TVDB_ERROR_INVALID_DATA);
    CHECK(!memcmp(saved, data, sizeof(saved)));
    tvdb_sdf_tree_destroy(w);
    tvdb_grid_destroy_owned(&g);
}
static void check_sparse_tiles(tvdb_thread_pool_t *pool) {
    tvdb_error_t err = {0};
    tvdb_grid_t tmpl, g = {0};
    sdf_fixture_template(&tmpl);
    tvdb_vec3i coords[4] = {{0, 0, 0}, {7, 0, 0}, {8, 0, 0}, {1000000000, 0, 0}};
    float v[4] = {0, 12, 12, 12};
    tvdb_sparse_grid s = {0};
    s.coords = coords;
    s.values = v;
    s.count = 4;
    CHECK(tvdb_grid_from_sparse_using_template(&tmpl, &s, "islands", 100, &g));
    /* The adjacent missing leaf is a signed internal tile, not root fill. */
    tvdb_root_node_t *root = &g.tree.nodes[0].u.root;
    tvdb_internal_node_t *upper = NULL, *lower = NULL;
    for (size_t i = 0; i < root->num_children; ++i)
        if (root->child_origins[3 * i] == 0)
            upper = &g.tree.nodes[root->child_indices[i]].u.internal;
    CHECK(upper);
    lower = &g.tree.nodes[upper->child_indices[0]].u.internal;
    float negative = -30;
    memcpy(lower->values + 512 * sizeof(float), &negative, sizeof(negative)); /* origin (16,0,0) */
    tvdb_sdf_tree_t *w = NULL;
    tracking t = {0};
    tvdb_allocator_t alloc = {allocate, NULL, release, &t};
    OK(tvdb_sdf_tree_create(&g, pool, &alloc, &w, &err));
    tvdb_sdf_tree_info_t info;
    tvdb_sdf_tree_info(w, &info);
    CHECK(info.active_voxels == 4);
    CHECK(info.scratch_bytes == 16);
    CHECK(info.metadata_bytes < 5000);
    CHECK(t.peak < 10000);
    tvdb_sdf_sweep_result_t r;
    OK(tvdb_sdf_tree_fast_sweep(w, 0, 8, 0, &r, &err));
    CHECK(r.unreached_voxels == 3 && !r.converged);
    CHECK(*sdf_fixture_at(&g, 1000000000, 0, 0) == 12);
    /* Add an active boundary voxel before creating a new mask snapshot. */
    tvdb_sdf_tree_destroy(w);
    CHECK(!t.live);
    tvdb_vec3i extra = {15, 0, 0};
    float value = 20;
    tvdb_sparse_grid update = {0};
    update.coords = &extra;
    update.values = &value;
    update.count = 1;
    CHECK(tvdb_grid_update_from_sparse(&g, &update, NULL) == 1);
    OK(tvdb_sdf_tree_create(&g, pool, NULL, &w, &err));
    float inactive = *sdf_fixture_at(&g, 14, 0, 0);
    *sdf_fixture_at(&g, 14, 0, 0) = NAN;
    CHECK(tvdb_sdf_tree_filter(w, TVDB_SDF_FILTER_DILATE, 1, &err) == TVDB_ERROR_INVALID_DATA);
    CHECK(*sdf_fixture_at(&g, 15, 0, 0) == 20);
    *sdf_fixture_at(&g, 14, 0, 0) = inactive;
    OK(tvdb_sdf_tree_filter(w, TVDB_SDF_FILTER_DILATE, 1, &err));
    CHECK(*sdf_fixture_at(&g, 15, 0, 0) == -30);
    CHECK(*sdf_fixture_at(&g, 14, 0, 0) == inactive);
    tvdb_sdf_tree_destroy(w);
    tvdb_grid_destroy_owned(&g);
    /* Empty hierarchy: no dense region or voxel workspace. */
    memset(&g, 0, sizeof(g));
    s.count = 0;
    CHECK(tvdb_grid_from_sparse_using_template(&tmpl, &s, "empty", 100, &g));
    OK(tvdb_sdf_tree_create(&g, pool, NULL, &w, &err));
    OK(tvdb_sdf_tree_fast_sweep(w, 0, 8, 0, &r, &err));
    CHECK(r.converged && !r.unreached_voxels);
    tvdb_sdf_tree_info(w, &info);
    CHECK(!info.scratch_bytes);
    tvdb_sdf_tree_destroy(w);
    tvdb_grid_destroy_owned(&g);
}
static void check_leaf_dimensions(tvdb_thread_pool_t *pool) {
    tvdb_error_t err = {0};
    for (int L = 0; L <= 5; ++L) {
        int dim = 1 << L;
        size_t count = (size_t)1 << (3 * L), bytes = (count + 7) / 8;
        tvdb_grid_t g = {0};
        tvdb_tree_node_t nodes[2] = {0};
        size_t child = 1;
        int32_t origin[3] = {INT32_MIN, INT32_MAX - dim + 1, 0};
        int32_t tile_origin[3] = {INT32_MIN + dim, INT32_MAX - dim + 1, 0};
        tvdb_value_t tile = {0};
        tile.type = TVDB_VALUE_FLOAT;
        tile.u.f = -7;
        int tile_active = 1;
        g.transform.type = TVDB_TRANSFORM_UNIFORM_SCALE;
        g.transform.voxel_size[0] = 0.5;
        g.tree.nodes = nodes;
        g.tree.num_nodes = 2;
        g.tree.layout.num_levels = 2;
        g.tree.layout.levels[0] = (tvdb_node_info_t){TVDB_NODE_ROOT, TVDB_VALUE_FLOAT, 0};
        g.tree.layout.levels[1] = (tvdb_node_info_t){TVDB_NODE_LEAF, TVDB_VALUE_FLOAT, L};
        nodes[0].type = TVDB_NODE_ROOT;
        tvdb_root_node_t *r = &nodes[0].u.root;
        r->background.type = TVDB_VALUE_FLOAT;
        r->background.u.f = 100;
        r->num_children = 1;
        r->child_indices = &child;
        r->child_origins = origin;
        r->num_tiles = 1;
        r->tile_origins = tile_origin;
        r->tile_values = &tile;
        r->tile_active = &tile_active;
        nodes[1].type = TVDB_NODE_LEAF;
        tvdb_leaf_node_t *leaf = &nodes[1].u.leaf;
        leaf->data = malloc(count * sizeof(float));
        leaf->data_size = count * sizeof(float);
        leaf->num_voxels = (uint32_t)count;
        leaf->value_mask.log2dim = L;
        leaf->value_mask.bitsize = (int32_t)count;
        leaf->value_mask.bits.num_bits = count;
        leaf->value_mask.bits.num_bytes = bytes;
        leaf->value_mask.bits.data = malloc(bytes);
        memset(leaf->value_mask.bits.data, 255, bytes);
        if (count < 8)
            leaf->value_mask.bits.data[0] = (uint8_t)((1u << count) - 1);
        float *data = (float *)leaf->data;
        for (size_t i = 0; i < count; ++i)
            data[i] = (i >> (2 * L)) == 0 ? 0 : 100;
        tvdb_sdf_tree_t *w = NULL;
        OK(tvdb_sdf_tree_create(&g, pool, NULL, &w, &err));
        tvdb_sdf_sweep_result_t result;
        OK(tvdb_sdf_tree_fast_sweep(w, 0, 8, 0, &result, &err));
        CHECK(result.converged);
        for (size_t i = 0; i < count; ++i)
            CHECK(data[i] == (float)(i >> (2 * L)) * 0.5f);
        OK(tvdb_sdf_tree_filter(w, TVDB_SDF_FILTER_DILATE, 1, &err));
        for (size_t i = count - (size_t)dim * dim; i < count; ++i)
            CHECK(data[i] == -7);
        CHECK(tile.u.f == -7 && tile_active == 1);
        tvdb_sdf_tree_destroy(w);
        free(leaf->data);
        free(leaf->value_mask.bits.data);
    }
}
static void check_loaded(const char *path) {
    tvdb_error_t err = {0};
    tvdb_file_t file = {0};
    OK(tvdb_file_open(&file, path, NULL, &err));
    OK(tvdb_read_all_grids(&file, &err));
    CHECK(file.num_grids);
    tvdb_sdf_tree_t *w = NULL;
    OK(tvdb_sdf_tree_create(&file.grids[0], NULL, NULL, &w, &err));
    OK(tvdb_sdf_tree_offset(w, 0.25f, &err));
    OK(tvdb_sdf_tree_filter(w, TVDB_SDF_FILTER_GAUSSIAN, 1, &err));
    tvdb_sdf_tree_info_t info;
    tvdb_sdf_tree_info(w, &info);
    CHECK(info.active_voxels > 0);
    CHECK(info.workers >= 1 && info.workers <= 8 && info.workers <= info.leaves);
    tvdb_sdf_tree_destroy(w);
    tvdb_file_close(&file);
}
int main(int argc, char **argv) {
    tvdb_thread_pool_t *one = NULL, *many = NULL;
    CHECK(tvdb_thread_pool_create(1, &one, NULL) == TVDB_OK);
    CHECK(tvdb_thread_pool_create(8, &many, NULL) == TVDB_OK);
    check_sweep(one, many, 0, 0);
    check_sweep(one, many, 1, 0);
    check_sweep(one, many, 1, 1);
    check_leaf_dimensions(many);
    check_filters(one, many);
    check_contracts(many);
    check_sparse_tiles(many);
    if (argc > 1)
        check_loaded(argv[1]);
    tvdb_thread_pool_destroy(one);
    tvdb_thread_pool_destroy(many);
    printf("SDF tree failures=%d\n", failures);
    return failures ? 1 : 0;
}
