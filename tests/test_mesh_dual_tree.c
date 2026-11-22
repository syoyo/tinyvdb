/* Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
   SPDX-License-Identifier: Apache-2.0 */

/* Regression test for the sparse-tree dual marching cubes first slice
 * (DMC-0 / naive surface nets). The field/tree is generated procedurally from
 * the same analytic sphere used by test_mesh_dual; independent oracles check
 * vertex/quad counts, watertightness, and byte-for-byte equality with the
 * landed dense DMC-0 result (the tree transform is the dense grid's inverse
 * origin mapping). */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tinyvdb_mesh_dual.h"
#include "tinyvdb_sparse.h"
#include "tinyvdb_tree.h"

#define CHECK(x)                                                                                   \
    do {                                                                                           \
        if (!(x)) {                                                                                \
            fprintf(stderr, "line %d: %s\n", __LINE__, #x);                                        \
            return 1;                                                                              \
        }                                                                                          \
    } while (0)

#define N 16
#define RADIUS 4.5f
#define ORIGIN (-N / 2.0f)
#define BG 100.0f

static size_t vidx(int x, int y, int z) {
    return (size_t)x + (size_t)y * N + (size_t)z * N * N;
}
static float world(int i) { return ORIGIN + (i + 0.5f); }
static float sphere(float *data, int x, int y, int z) {
    float px = world(x), py = world(y), pz = world(z);
    return data[vidx(x, y, z)] = sqrtf(px * px + py * py + pz * pz) - RADIUS;
}

static const int CORNER[8][3] = {{0, 0, 0}, {1, 0, 0}, {1, 1, 0}, {0, 1, 0},
                                 {0, 0, 1}, {1, 0, 1}, {1, 1, 1}, {0, 1, 1}};
static const int EDGE[12][2] = {{0, 1}, {1, 2}, {2, 3}, {3, 0},
                                {4, 5}, {5, 6}, {6, 7}, {7, 4},
                                {0, 4}, {1, 5}, {2, 6}, {3, 7}};

static int crossed_cell(const float *data, int x, int y, int z) {
    int below[8];
    for (int c = 0; c < 8; ++c)
        below[c] = data[vidx(x + CORNER[c][0], y + CORNER[c][1], z + CORNER[c][2])] < 0.0f;
    for (int e = 0; e < 12; ++e)
        if (below[EDGE[e][0]] != below[EDGE[e][1]])
            return 1;
    return 0;
}
static int cross_edge(const float *data, int x, int y, int z, int axis) {
    int q[3] = {x, y, z};
    int a = data[vidx(x, y, z)] < 0.0f;
    q[axis] += 1;
    return a != (data[vidx(q[0], q[1], q[2])] < 0.0f);
}
static void expected_counts(const float *data, size_t *nv, size_t *nq) {
    *nv = *nq = 0;
    for (int z = 0; z < N - 1; ++z)
        for (int y = 0; y < N - 1; ++y)
            for (int x = 0; x < N - 1; ++x)
                *nv += crossed_cell(data, x, y, z);
    for (int z = 1; z <= N - 3; ++z) {
        for (int y = 1; y <= N - 3; ++y)
            for (int x = 0; x <= N - 2; ++x)
                *nq += cross_edge(data, x, y, z, 0);
        for (int x = 1; x <= N - 3; ++x)
            for (int y = 0; y <= N - 2; ++y)
                *nq += cross_edge(data, x, y, z, 1);
    }
    for (int z = 0; z <= N - 2; ++z)
        for (int y = 1; y <= N - 3; ++y)
            for (int x = 1; x <= N - 3; ++x)
                *nq += cross_edge(data, x, y, z, 2);
}

typedef struct {
    uint32_t u, v;
} edge_t;
static int edge_cmp(const void *a, const void *b) {
    const edge_t *x = a, *y = b;
    if (x->u != y->u)
        return x->u < y->u ? -1 : 1;
    if (x->v != y->v)
        return x->v < y->v ? -1 : 1;
    return 0;
}
static size_t edge_count(const edge_t *edges, size_t n, uint32_t u, uint32_t v) {
    size_t lo = 0, hi = n;
    while (lo < hi) {
        size_t mid = (lo + hi) / 2;
        if (edges[mid].u < u || (edges[mid].u == u && edges[mid].v < v))
            lo = mid + 1;
        else
            hi = mid;
    }
    size_t count = 0;
    while (lo < n && edges[lo].u == u && edges[lo].v == v) {
        ++count;
        ++lo;
    }
    return count;
}
static int watertight(const tvdb_quad_mesh *m) {
    size_t ne = m->quad_count * 4;
    edge_t *edges = malloc(ne * sizeof(edge_t));
    if (!edges)
        return 0;
    for (size_t q = 0; q < m->quad_count; ++q) {
        const tvdb_quad *f = &m->quads[q];
        uint32_t v[4] = {f->v0, f->v1, f->v2, f->v3};
        for (int t = 0; t < 4; ++t)
            edges[4 * q + t] = (edge_t){v[t], v[(t + 1) & 3]};
    }
    qsort(edges, ne, sizeof(edge_t), edge_cmp);
    int ok = 1;
    for (size_t i = 0; i < ne && ok; ++i)
        ok = edge_count(edges, ne, edges[i].u, edges[i].v) ==
             edge_count(edges, ne, edges[i].v, edges[i].u);
    free(edges);
    return ok;
}
static double signed_volume(const tvdb_quad_mesh *m) {
    double vol = 0;
    for (size_t q = 0; q < m->quad_count; ++q) {
        tvdb_vec3f p[4] = {m->vertices[m->quads[q].v0], m->vertices[m->quads[q].v1],
                           m->vertices[m->quads[q].v2], m->vertices[m->quads[q].v3]};
        int tri[2][3] = {{0, 1, 2}, {0, 2, 3}};
        for (int t = 0; t < 2; ++t) {
            tvdb_vec3f a = p[tri[t][0]], b = p[tri[t][1]], c = p[tri[t][2]];
            vol += (a.x * (b.y * c.z - b.z * c.y) - a.y * (b.x * c.z - b.z * c.x) +
                    a.z * (b.x * c.y - b.y * c.x)) /
                   6.0;
        }
    }
    return vol;
}
static int same_mesh(const tvdb_quad_mesh *a, const tvdb_quad_mesh *b) {
    return a->vertex_count == b->vertex_count && a->quad_count == b->quad_count &&
           !memcmp(a->vertices, b->vertices, a->vertex_count * sizeof(tvdb_vec3f)) &&
           !memcmp(a->quads, b->quads, a->quad_count * sizeof(tvdb_quad));
}
static int quad_cmp(const void *pa, const void *pb) {
    const tvdb_quad *a = pa, *b = pb;
    const uint32_t x[4] = {a->v0, a->v1, a->v2, a->v3};
    const uint32_t y[4] = {b->v0, b->v1, b->v2, b->v3};
    for (int i = 0; i < 4; ++i)
        if (x[i] != y[i])
            return x[i] < y[i] ? -1 : 1;
    return 0;
}
static int same_mesh_unordered(const tvdb_quad_mesh *a, const tvdb_quad_mesh *b) {
    if (a->vertex_count != b->vertex_count || a->quad_count != b->quad_count)
        return 0;
    for (size_t i = 0; i < a->vertex_count; ++i) {
        tvdb_vec3f u = a->vertices[i], v = b->vertices[i];
        if (fabs(u.x - v.x) > 1e-5 || fabs(u.y - v.y) > 1e-5 || fabs(u.z - v.z) > 1e-5)
            return 0;
    }
    tvdb_quad *qa = malloc(a->quad_count * sizeof(tvdb_quad));
    tvdb_quad *qb = malloc(b->quad_count * sizeof(tvdb_quad));
    if (!qa || !qb) {
        free(qa);
        free(qb);
        return 0;
    }
    memcpy(qa, a->quads, a->quad_count * sizeof(tvdb_quad));
    memcpy(qb, b->quads, b->quad_count * sizeof(tvdb_quad));
    qsort(qa, a->quad_count, sizeof(tvdb_quad), quad_cmp);
    qsort(qb, b->quad_count, sizeof(tvdb_quad), quad_cmp);
    int ok = !memcmp(qa, qb, a->quad_count * sizeof(tvdb_quad));
    free(qa);
    free(qb);
    return ok;
}

static void fill_sphere(float *data) {
    for (int z = 0; z < N; ++z)
        for (int y = 0; y < N; ++y)
            for (int x = 0; x < N; ++x)
                sphere(data, x, y, z);
}

static void tree_template(tvdb_grid_t *tmpl) {
    memset(tmpl, 0, sizeof(*tmpl));
    tmpl->descriptor.grid_type = (char *)"Tree_float_5_4_3";
    tmpl->transform.type = TVDB_TRANSFORM_UNIFORM_SCALE_TRANSLATE;
    tmpl->transform.voxel_size[0] = 1.0;
    for (int a = 0; a < 3; ++a)
        tmpl->transform.translation[a] = ORIGIN + 0.5;
    tmpl->tree.layout.num_levels = 4;
    const int dims[4] = {0, 5, 4, 3};
    for (int i = 0; i < 4; ++i) {
        tmpl->tree.layout.levels[i].log2dim = dims[i];
        tmpl->tree.layout.levels[i].value_type = TVDB_VALUE_FLOAT;
        tmpl->tree.layout.levels[i].node_type =
            i == 0 ? TVDB_NODE_ROOT : i == 3 ? TVDB_NODE_LEAF : TVDB_NODE_INTERNAL;
    }
}

static int build_grid(const tvdb_dense_grid *dense, double sy, tvdb_grid_t *grid) {
    tvdb_grid_t tmpl;
    tree_template(&tmpl);
    if (sy != 1.0) {
        tmpl.transform.type = TVDB_TRANSFORM_SCALE_TRANSLATE;
        tmpl.transform.voxel_size[0] = 1.0;
        tmpl.transform.voxel_size[1] = sy;
        tmpl.transform.voxel_size[2] = 1.0;
    }
    tvdb_sparse_grid sg = {0};
    if (!tvdb_dense_to_sparse(dense, BG, 1e-3f, &sg))
        return 0;
    int ok = tvdb_grid_from_sparse_using_template(&tmpl, &sg, "sphere", BG, grid);
    tvdb_sparse_grid_free(&sg);
    return ok;
}

int main(void) {
    float *data = malloc((size_t)N * N * N * sizeof(float));
    CHECK(data);
    fill_sphere(data);
    size_t want_v, want_q;
    expected_counts(data, &want_v, &want_q);
    CHECK(want_v > 100 && want_q > 100);

    tvdb_dense_grid dense = {N, N, N, ORIGIN, ORIGIN, ORIGIN, 1.0f, data};
    tvdb_quad_mesh reference; /* dense DMC-0 oracle */
    tvdb_quad_mesh_init(&reference);
    CHECK(tvdb_sdf_to_mesh_dual_ex(&dense, 0.0f, NULL, &reference, NULL, NULL) == TVDB_OK);

    tvdb_grid_t grid;
    CHECK(build_grid(&dense, 1.0, &grid));

    tvdb_quad_mesh mesh;
    tvdb_quad_mesh_init(&mesh);
    tvdb_error_t err;
    CHECK(tvdb_grid_volume_to_mesh_dual_ex(&grid, 0.0f, 0, NULL, &mesh, NULL, &err) == TVDB_OK);
    CHECK(mesh.vertex_count == want_v && mesh.vertex_count == reference.vertex_count);
    CHECK(mesh.quad_count == want_q && mesh.quad_count == reference.quad_count);
    CHECK(watertight(&mesh));
    CHECK(signed_volume(&mesh) > 0.0); /* outward for a negative-inside SDF */
    /* Same surface as dense DMC-0: identical vertex positions and the same
     * quad set (emission order differs: tree walks cells, dense walks axes). */
    if (!same_mesh_unordered(&mesh, &reference))
        fprintf(stderr, "tree vs dense: %zu/%zu verts, %zu/%zu quads\n", mesh.vertex_count,
                reference.vertex_count, mesh.quad_count, reference.quad_count);
    CHECK(same_mesh_unordered(&mesh, &reference));
    for (size_t v = 0; v < mesh.vertex_count; ++v)
        CHECK(isfinite(mesh.vertices[v].x) && isfinite(mesh.vertices[v].y) &&
              isfinite(mesh.vertices[v].z));
    for (size_t q = 0; q < mesh.quad_count; ++q)
        CHECK(mesh.quads[q].v0 < mesh.vertex_count && mesh.quads[q].v1 < mesh.vertex_count &&
              mesh.quads[q].v2 < mesh.vertex_count && mesh.quads[q].v3 < mesh.vertex_count);

    /* Determinism across worker partitions. */
    tvdb_thread_pool_t *p1 = NULL, *p4 = NULL, *p8 = NULL;
    CHECK(tvdb_thread_pool_create(1, &p1, NULL) == TVDB_OK);
    CHECK(tvdb_thread_pool_create(4, &p4, NULL) == TVDB_OK);
    CHECK(tvdb_thread_pool_create(8, &p8, NULL) == TVDB_OK);
    tvdb_quad_mesh a, b, c;
    tvdb_quad_mesh_init(&a);
    tvdb_quad_mesh_init(&b);
    tvdb_quad_mesh_init(&c);
    CHECK(tvdb_grid_volume_to_mesh_dual_ex(&grid, 0.0f, 0, p1, &a, NULL, NULL) == TVDB_OK);
    CHECK(tvdb_grid_volume_to_mesh_dual_ex(&grid, 0.0f, 0, p4, &b, NULL, NULL) == TVDB_OK);
    CHECK(tvdb_grid_volume_to_mesh_dual_ex(&grid, 0.0f, 0, p8, &c, NULL, NULL) == TVDB_OK);
    CHECK(same_mesh(&a, &mesh) && same_mesh(&b, &mesh) && same_mesh(&c, &mesh));
    tvdb_thread_pool_destroy(p1);
    tvdb_thread_pool_destroy(p4);
    tvdb_thread_pool_destroy(p8);
    tvdb_quad_mesh_free(&a);
    tvdb_quad_mesh_free(&b);
    tvdb_quad_mesh_free(&c);

    /* Non-uniform transform: the same index-space topology, stretched in y,
     * must still produce a finite, watertight, outward mesh (a dense
     * materialization could not represent this). */
    tvdb_grid_t stretched;
    CHECK(build_grid(&dense, 2.0, &stretched));
    tvdb_quad_mesh sm;
    tvdb_quad_mesh_init(&sm);
    CHECK(tvdb_grid_volume_to_mesh_dual_ex(&stretched, 0.0f, 0, NULL, &sm, NULL, &err) == TVDB_OK);
    CHECK(sm.vertex_count == want_v && sm.quad_count == want_q);
    CHECK(watertight(&sm) && signed_volume(&sm) > 0.0);
    for (size_t v = 0; v < sm.vertex_count; ++v)
        CHECK(isfinite(sm.vertices[v].x) && isfinite(sm.vertices[v].y) &&
              isfinite(sm.vertices[v].z));
    /* y world = 2*index_y + translation, so it must differ from the unit case. */
    CHECK(fabs(sm.vertices[0].y - (2.0 * mesh.vertices[0].y - (ORIGIN + 0.5))) < 1e-4);
    tvdb_quad_mesh_free(&sm);
    tvdb_grid_destroy_owned(&stretched);

    /* Convenience wrapper. */
    tvdb_quad_mesh wrapped;
    tvdb_quad_mesh_init(&wrapped);
    CHECK(tvdb_grid_volume_to_mesh_dual(&grid, 0.0f, 0, &wrapped, NULL));
    CHECK(same_mesh(&wrapped, &mesh));
    tvdb_quad_mesh_free(&wrapped);

    /* Appending to a populated mesh keeps the prefix and bases new indices. */
    tvdb_quad_mesh append;
    tvdb_quad_mesh_init(&append);
    append.vertices = malloc(sizeof(tvdb_vec3f));
    append.quads = malloc(sizeof(tvdb_quad));
    CHECK(append.vertices && append.quads);
    append.vertex_count = append.vertex_capacity = append.quad_count = append.quad_capacity = 1;
    append.vertices[0] = (tvdb_vec3f){8, 9, 10};
    append.quads[0] = (tvdb_quad){0, 0, 0, 0};
    CHECK(tvdb_grid_volume_to_mesh_dual_ex(&grid, 0.0f, 0, NULL, &append, NULL, NULL) == TVDB_OK);
    CHECK(append.vertex_count == want_v + 1 && append.quad_count == want_q + 1);
    CHECK(append.vertices[0].y == 9 && append.quads[0].v0 == 0);
    for (size_t q = 1; q < append.quad_count; ++q) {
        const tvdb_quad *f = &append.quads[q];
        CHECK(f->v0 >= 1 && f->v1 >= 1 && f->v2 >= 1 && f->v3 >= 1 &&
              f->v0 < append.vertex_count && f->v1 < append.vertex_count &&
              f->v2 < append.vertex_count && f->v3 < append.vertex_count);
    }
    tvdb_quad_mesh_free(&append);

    /* Output preserved on argument failure (invalid isovalue). */
    tvdb_quad_mesh guard;
    tvdb_quad_mesh_init(&guard);
    guard.vertices = malloc(sizeof(tvdb_vec3f));
    guard.quads = malloc(sizeof(tvdb_quad));
    CHECK(guard.vertices && guard.quads);
    guard.vertex_count = guard.vertex_capacity = guard.quad_count = guard.quad_capacity = 1;
    guard.vertices[0] = (tvdb_vec3f){8, 9, 10};
    guard.quads[0] = (tvdb_quad){0, 0, 0, 0};
    tvdb_quad_mesh saved = guard;
    memset(&err, 0, sizeof(err));
    CHECK(tvdb_grid_volume_to_mesh_dual_ex(&grid, NAN, 0, NULL, &guard, NULL, &err) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(err.status == TVDB_ERROR_INVALID_ARGUMENT && err.message[0]);
    CHECK(!memcmp(&guard, &saved, sizeof(guard)) && guard.vertices[0].y == 9);

    /* Alias rejection: output storage overlapping tree node storage. */
    const tvdb_tree_node_t *node = grid.tree.nodes + 1;
    const void *node_data = node->type == TVDB_NODE_LEAF ? (const void *)node->u.leaf.data
                                                         : (const void *)node->u.internal.values;
    guard.vertices = (tvdb_vec3f *)(void *)node_data;
    CHECK(tvdb_grid_volume_to_mesh_dual_ex(&grid, 0.0f, 0, NULL, &guard, NULL, NULL) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    guard.vertices = saved.vertices;
    CHECK(!memcmp(&guard, &saved, sizeof(guard)));

    /* Nonfinite stored sample: data error, output preserved. */
    float *sample = NULL;
    for (size_t i = 1; i < grid.tree.num_nodes && !sample; ++i)
        if (grid.tree.nodes[i].type == TVDB_NODE_LEAF)
            sample = (float *)grid.tree.nodes[i].u.leaf.data;
    CHECK(sample);
    float saved_value = sample[0];
    sample[0] = NAN;
    CHECK(tvdb_grid_volume_to_mesh_dual_ex(&grid, 0.0f, 0, NULL, &guard, NULL, &err) ==
          TVDB_ERROR_INVALID_DATA);
    CHECK(!memcmp(&guard, &saved, sizeof(guard)));
    sample[0] = saved_value;

    /* Cell budget exhaustion is an explicit error and preserves output. */
    CHECK(tvdb_grid_volume_to_mesh_dual_ex(&grid, 0.0f, 1, NULL, &guard, NULL, &err) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(!memcmp(&guard, &saved, sizeof(guard)));

    /* Arena rollback: a too-small arena fails and restores the offset. */
    char tiny[64];
    tvdb_arena_allocator_t arena = {tiny, sizeof(tiny), 3};
    tvdb_quad_mesh empty;
    tvdb_quad_mesh_init(&empty);
    CHECK(tvdb_grid_volume_to_mesh_dual_ex(&grid, 0.0f, 0, NULL, &empty, &arena, &err) ==
          TVDB_ERROR_OUT_OF_MEMORY);
    CHECK(arena.current_offset == 3 && !empty.vertices && !empty.quads && !empty.vertex_count);
    /* A successful arena conversion retains exactly the output. */
    size_t need = mesh.vertex_count * sizeof(tvdb_vec3f) + mesh.quad_count * sizeof(tvdb_quad);
    void *storage = malloc(need + 16);
    CHECK(storage);
    arena = (tvdb_arena_allocator_t){storage, need + 16, 0};
    tvdb_quad_mesh from_arena;
    tvdb_quad_mesh_init(&from_arena);
    CHECK(tvdb_grid_volume_to_mesh_dual_ex(&grid, 0.0f, 0, NULL, &from_arena, &arena, NULL) ==
          TVDB_OK);
    CHECK(same_mesh(&from_arena, &mesh));
    CHECK(arena.current_offset <= need + 15);
    free(storage); /* arena-owned buffers must not be freed by tvdb_quad_mesh_free */

    free(guard.vertices);
    free(guard.quads);
    tvdb_quad_mesh_free(&mesh);
    tvdb_quad_mesh_free(&reference);
    tvdb_grid_destroy_owned(&grid);
    free(data);
    printf("test_mesh_dual_tree: %zu vertices, %zu quads, watertight, deterministic\n", want_v,
           want_q);
    return 0;
}
