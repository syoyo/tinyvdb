/* Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
    SPDX-License-Identifier: Apache-2.0 */

/* Sparse-tree DMC-1 (shell-pinned, index-space QEF), first slice.
 *
 * Independent oracles (no library DMC-1 internals):
 *   - expected vertices = sum over crossed cells of the MC soup component
 *     count, computed here by adjacency BFS over the shipped triangle table;
 *   - expected quads = crossed primal edges with four incident crossed cells,
 *     recomputed from the analytic field;
 *   - every quad has four distinct in-range corners, the directed-edge list
 *     is closed (watertight), and the signed volume is positive;
 *   - the result is byte-identical across worker counts and agrees with the
 *     dense DMC-1 padded API in vertex/quad count and watertightness for the
 *     same analytic field. Vertex positions are NOT required to match: tree
 *     DMC-1 solves its QEF in index space with a per-cell averaged gradient,
 *     while dense DMC-1 solves in world space with corner central differences.
 *   - a sphere reaching the boundary is open without pinning and closed by
 *     the always-on shell; contract failures preserve output/arena state.
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tinyvdb_mc_tri_table.h"
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
#define ORIGIN (-N / 2.0f)
#define BG 100.0f

typedef float (*field_fn)(float, float, float);

static float interior_sphere(float x, float y, float z) {
    return sqrtf(x * x + y * y + z * z) - 4.5f;
}
/* Reaches every domain face: face-centre samples are inside, so the crossing
 * surface meets the boundary and only the pinned shell can close it. */
static float boundary_sphere(float x, float y, float z) {
    return sqrtf(x * x + y * y + z * z) - 8.0f;
}

static size_t vidx(int x, int y, int z) {
    return (size_t)x + (size_t)y * N + (size_t)z * N * N;
}
static float world(int i) { return ORIGIN + (i + 0.5f); }
static void fill(field_fn f, float *data) {
    for (int z = 0; z < N; ++z)
        for (int y = 0; y < N; ++y)
            for (int x = 0; x < N; ++x)
                data[vidx(x, y, z)] = f(world(x), world(y), world(z));
}

static const int CORNER[8][3] = {{0, 0, 0}, {1, 0, 0}, {1, 1, 0}, {0, 1, 0},
                                 {0, 0, 1}, {1, 0, 1}, {1, 1, 1}, {0, 1, 1}};
static const int EDGE[12][2] = {{0, 1}, {1, 2}, {2, 3}, {3, 0},
                                {4, 5}, {5, 6}, {6, 7}, {7, 4},
                                {0, 4}, {1, 5}, {2, 6}, {3, 7}};

static unsigned case_id(const float *data, int x, int y, int z) {
    unsigned k = 0;
    for (int c = 0; c < 8; ++c)
        if (data[vidx(x + CORNER[c][0], y + CORNER[c][1], z + CORNER[c][2])] < 0.0f)
            k |= 1u << c;
    return k;
}
static int crossed_cell(const float *data, int x, int y, int z) {
    unsigned k = case_id(data, x, y, z);
    for (int e = 0; e < 12; ++e)
        if (((k >> EDGE[e][0]) & 1u) != ((k >> EDGE[e][1]) & 1u))
            return 1;
    return 0;
}
static int cross_edge(const float *data, int x, int y, int z, int axis) {
    int q[3] = {x, y, z};
    int a = data[vidx(x, y, z)] < 0.0f;
    q[axis] += 1;
    return a != (data[vidx(q[0], q[1], q[2])] < 0.0f);
}

/* Adjacency BFS over the MC soup: independent of the library union-find. */
static int ref_patch_count(unsigned k) {
    const int *row = MC_TRI_TABLE[k];
    int tris[5][3], nt = 0;
    for (int i = 0; i + 2 < 16 && nt < 5; i += 3) {
        if (row[i] < 0)
            break;
        tris[nt][0] = row[i];
        tris[nt][1] = row[i + 1];
        tris[nt][2] = row[i + 2];
        ++nt;
    }
    int adj[12][12] = {{0}}, used[12] = {0}, seen[12] = {0};
    for (int t = 0; t < nt; ++t) {
        const int *v = tris[t];
        used[v[0]] = used[v[1]] = used[v[2]] = 1;
        const int pairs[3][2] = {{0, 1}, {1, 2}, {0, 2}};
        for (int p = 0; p < 3; ++p) {
            int a = v[pairs[p][0]], b = v[pairs[p][1]];
            adj[a][b] = adj[b][a] = 1;
        }
    }
    int stack[12], comps = 0;
    for (int e = 0; e < 12; ++e) {
        if (!used[e] || seen[e])
            continue;
        ++comps;
        int top = 0;
        stack[top++] = e;
        seen[e] = 1;
        while (top) {
            int u = stack[--top];
            for (int w = 0; w < 12; ++w)
                if (adj[u][w] && !seen[w]) {
                    seen[w] = 1;
                    stack[top++] = w;
                }
        }
    }
    return comps;
}

/* Expected counts for a surface strictly inside the lattice (no pinned cell
 * is crossed, so the counts coincide with the DMC-0 crossed-edge count). */
static void expected_counts(const float *data, size_t *nv, size_t *nq) {
    *nv = *nq = 0;
    for (int z = 0; z < N - 1; ++z)
        for (int y = 0; y < N - 1; ++y)
            for (int x = 0; x < N - 1; ++x)
                if (crossed_cell(data, x, y, z))
                    *nv += (size_t)ref_patch_count(case_id(data, x, y, z));
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
static size_t edge_count(const edge_t *e, size_t n, uint32_t u, uint32_t v) {
    size_t lo = 0, hi = n;
    while (lo < hi) {
        size_t mid = (lo + hi) / 2;
        if (e[mid].u < u || (e[mid].u == u && e[mid].v < v))
            lo = mid + 1;
        else
            hi = mid;
    }
    size_t c = 0;
    while (lo < n && e[lo].u == u && e[lo].v == v) {
        ++c;
        ++lo;
    }
    return c;
}

/* Finite positions, four distinct in-range corners, watertight, outward. */
static int check_mesh(const tvdb_quad_mesh *m) {
    for (size_t v = 0; v < m->vertex_count; ++v)
        if (!isfinite(m->vertices[v].x) || !isfinite(m->vertices[v].y) ||
            !isfinite(m->vertices[v].z))
            return 0;
    size_t ne = m->quad_count * 4;
    edge_t *edges = malloc(ne * sizeof(edge_t));
    if (!edges)
        return 0;
    double vol = 0;
    for (size_t q = 0; q < m->quad_count; ++q) {
        const tvdb_quad *f = &m->quads[q];
        uint32_t v[4] = {f->v0, f->v1, f->v2, f->v3};
        for (int t = 0; t < 4; ++t) {
            for (int s = t + 1; s < 4; ++s)
                if (v[t] == v[s]) {
                    free(edges);
                    return 0; /* four distinct corners */
                }
            if (v[t] >= m->vertex_count) {
                free(edges);
                return 0;
            }
            edges[4 * q + t] = (edge_t){v[t], v[(t + 1) & 3]};
        }
        tvdb_vec3f p[4] = {m->vertices[f->v0], m->vertices[f->v1], m->vertices[f->v2],
                           m->vertices[f->v3]};
        const int tri[2][3] = {{0, 1, 2}, {0, 2, 3}};
        for (int t = 0; t < 2; ++t) {
            tvdb_vec3f a = p[tri[t][0]], b = p[tri[t][1]], c = p[tri[t][2]];
            vol += (a.x * (b.y * c.z - b.z * c.y) - a.y * (b.x * c.z - b.z * c.x) +
                    a.z * (b.x * c.y - b.y * c.x)) /
                   6.0;
        }
    }
    qsort(edges, ne, sizeof(edge_t), edge_cmp);
    int ok = 1;
    for (size_t i = 0; i < ne && ok; ++i)
        ok = edge_count(edges, ne, edges[i].u, edges[i].v) ==
             edge_count(edges, ne, edges[i].v, edges[i].u);
    if (!(vol > 0.0))
        ok = 0;
    free(edges);
    return ok;
}

static int same_mesh(const tvdb_quad_mesh *a, const tvdb_quad_mesh *b) {
    return a->vertex_count == b->vertex_count && a->quad_count == b->quad_count &&
           !memcmp(a->vertices, b->vertices, a->vertex_count * sizeof(tvdb_vec3f)) &&
           !memcmp(a->quads, b->quads, a->quad_count * sizeof(tvdb_quad));
}

static void tree_template(tvdb_grid_t *tmpl, double sy) {
    memset(tmpl, 0, sizeof(*tmpl));
    tmpl->descriptor.grid_type = (char *)"Tree_float_5_4_3";
    tmpl->transform.type = sy == 1.0 ? TVDB_TRANSFORM_UNIFORM_SCALE_TRANSLATE
                                     : TVDB_TRANSFORM_SCALE_TRANSLATE;
    tmpl->transform.voxel_size[0] = 1.0;
    tmpl->transform.voxel_size[1] = sy;
    tmpl->transform.voxel_size[2] = 1.0;
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
    tree_template(&tmpl, sy);
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
    fill(interior_sphere, data);
    size_t want_v, want_q;
    expected_counts(data, &want_v, &want_q);
    CHECK(want_v > 100 && want_q > 100);

    tvdb_dense_grid dense = {N, N, N, ORIGIN, ORIGIN, ORIGIN, 1.0f, data};
    tvdb_quad_mesh dense_closed; /* dense DMC-1 padded oracle */
    tvdb_quad_mesh_init(&dense_closed);
    CHECK(tvdb_sdf_to_mesh_dual_one_padded_ex(&dense, 0.0f, NULL, &dense_closed, NULL, NULL) ==
          TVDB_OK);
    CHECK(dense_closed.vertex_count == want_v && dense_closed.quad_count == want_q);

    tvdb_grid_t grid;
    CHECK(build_grid(&dense, 1.0, &grid));

    tvdb_quad_mesh mesh;
    tvdb_quad_mesh_init(&mesh);
    tvdb_error_t err;
    CHECK(tvdb_grid_volume_to_mesh_dual_one_ex(&grid, 0.0f, 0, NULL, &mesh, NULL, &err) == TVDB_OK);
    /* Independent count oracles + dense padded topology/count agreement. */
    CHECK(mesh.vertex_count == want_v && mesh.quad_count == want_q);
    CHECK(mesh.vertex_count == dense_closed.vertex_count &&
          mesh.quad_count == dense_closed.quad_count);
    CHECK(check_mesh(&mesh));
    CHECK(check_mesh(&dense_closed));
    printf("test_mesh_dual_tree_one [interior]: %zu vertices, %zu quads, watertight; "
           "dense padded %zu/%zu\n",
           mesh.vertex_count, mesh.quad_count, dense_closed.vertex_count,
           dense_closed.quad_count);

    /* Determinism across worker partitions (emission is serial). */
    tvdb_thread_pool_t *p1 = NULL, *p4 = NULL, *p8 = NULL;
    CHECK(tvdb_thread_pool_create(1, &p1, NULL) == TVDB_OK);
    CHECK(tvdb_thread_pool_create(4, &p4, NULL) == TVDB_OK);
    CHECK(tvdb_thread_pool_create(8, &p8, NULL) == TVDB_OK);
    tvdb_quad_mesh a, b, c;
    tvdb_quad_mesh_init(&a);
    tvdb_quad_mesh_init(&b);
    tvdb_quad_mesh_init(&c);
    CHECK(tvdb_grid_volume_to_mesh_dual_one_ex(&grid, 0.0f, 0, p1, &a, NULL, NULL) == TVDB_OK);
    CHECK(tvdb_grid_volume_to_mesh_dual_one_ex(&grid, 0.0f, 0, p4, &b, NULL, NULL) == TVDB_OK);
    CHECK(tvdb_grid_volume_to_mesh_dual_one_ex(&grid, 0.0f, 0, p8, &c, NULL, NULL) == TVDB_OK);
    CHECK(same_mesh(&a, &mesh) && same_mesh(&b, &mesh) && same_mesh(&c, &mesh));
    tvdb_thread_pool_destroy(p1);
    tvdb_thread_pool_destroy(p4);
    tvdb_thread_pool_destroy(p8);
    tvdb_quad_mesh_free(&a);
    tvdb_quad_mesh_free(&b);
    tvdb_quad_mesh_free(&c);

    /* Non-uniform transform: index-space QEF + affine still closes and winds. */
    tvdb_grid_t stretched;
    CHECK(build_grid(&dense, 2.0, &stretched));
    tvdb_quad_mesh sm;
    tvdb_quad_mesh_init(&sm);
    CHECK(tvdb_grid_volume_to_mesh_dual_one_ex(&stretched, 0.0f, 0, NULL, &sm, NULL, &err) ==
          TVDB_OK);
    CHECK(sm.vertex_count == want_v && sm.quad_count == want_q);
    CHECK(check_mesh(&sm));
    tvdb_quad_mesh_free(&sm);
    tvdb_grid_destroy_owned(&stretched);

    /* Convenience wrapper. */
    tvdb_quad_mesh wrapped;
    tvdb_quad_mesh_init(&wrapped);
    CHECK(tvdb_grid_volume_to_mesh_dual_one(&grid, 0.0f, 0, &wrapped, NULL));
    CHECK(same_mesh(&wrapped, &mesh));
    tvdb_quad_mesh_free(&wrapped);

    /* Appending preserves the prefix and bases new indices after it. */
    tvdb_quad_mesh append;
    tvdb_quad_mesh_init(&append);
    append.vertices = malloc(sizeof(tvdb_vec3f));
    append.quads = malloc(sizeof(tvdb_quad));
    CHECK(append.vertices && append.quads);
    append.vertex_count = append.vertex_capacity = append.quad_count = append.quad_capacity = 1;
    append.vertices[0] = (tvdb_vec3f){8, 9, 10};
    append.quads[0] = (tvdb_quad){0, 0, 0, 0};
    CHECK(tvdb_grid_volume_to_mesh_dual_one_ex(&grid, 0.0f, 0, NULL, &append, NULL, NULL) ==
          TVDB_OK);
    CHECK(append.vertex_count == want_v + 1 && append.quad_count == want_q + 1);
    CHECK(append.vertices[0].y == 9 && append.quads[0].v0 == 0);
    for (size_t q = 1; q < append.quad_count; ++q) {
        const tvdb_quad *f = &append.quads[q];
        CHECK(f->v0 >= 1 && f->v1 >= 1 && f->v2 >= 1 && f->v3 >= 1 &&
              f->v0 < append.vertex_count && f->v1 < append.vertex_count &&
              f->v2 < append.vertex_count && f->v3 < append.vertex_count);
    }
    tvdb_quad_mesh_free(&append);

    /* Failure preservation: invalid isovalue, alias, nonfinite sample, budget. */
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
    CHECK(tvdb_grid_volume_to_mesh_dual_one_ex(&grid, NAN, 0, NULL, &guard, NULL, &err) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(err.status == TVDB_ERROR_INVALID_ARGUMENT && err.message[0]);
    CHECK(!memcmp(&guard, &saved, sizeof(guard)) && guard.vertices[0].y == 9);

    const tvdb_tree_node_t *node = grid.tree.nodes + 1;
    const void *node_data = node->type == TVDB_NODE_LEAF ? (const void *)node->u.leaf.data
                                                         : (const void *)node->u.internal.values;
    guard.vertices = (tvdb_vec3f *)(void *)node_data;
    CHECK(tvdb_grid_volume_to_mesh_dual_one_ex(&grid, 0.0f, 0, NULL, &guard, NULL, NULL) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    guard.vertices = saved.vertices;
    CHECK(!memcmp(&guard, &saved, sizeof(guard)));

    float *sample = NULL;
    for (size_t i = 1; i < grid.tree.num_nodes && !sample; ++i)
        if (grid.tree.nodes[i].type == TVDB_NODE_LEAF)
            sample = (float *)grid.tree.nodes[i].u.leaf.data;
    CHECK(sample);
    float saved_value = sample[0];
    sample[0] = NAN;
    CHECK(tvdb_grid_volume_to_mesh_dual_one_ex(&grid, 0.0f, 0, NULL, &guard, NULL, &err) ==
          TVDB_ERROR_INVALID_DATA);
    CHECK(!memcmp(&guard, &saved, sizeof(guard)));
    sample[0] = saved_value;

    CHECK(tvdb_grid_volume_to_mesh_dual_one_ex(&grid, 0.0f, 1, NULL, &guard, NULL, &err) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(!memcmp(&guard, &saved, sizeof(guard)));

    /* Arena rollback on exhaustion; success retains exactly the output. */
    char tiny[64];
    tvdb_arena_allocator_t arena = {tiny, sizeof(tiny), 3};
    tvdb_quad_mesh empty;
    tvdb_quad_mesh_init(&empty);
    CHECK(tvdb_grid_volume_to_mesh_dual_one_ex(&grid, 0.0f, 0, NULL, &empty, &arena, &err) ==
          TVDB_ERROR_OUT_OF_MEMORY);
    CHECK(arena.current_offset == 3 && !empty.vertices && !empty.quads && !empty.vertex_count);
    size_t need = mesh.vertex_count * sizeof(tvdb_vec3f) + mesh.quad_count * sizeof(tvdb_quad) + 64;
    void *storage = malloc(need);
    CHECK(storage);
    arena = (tvdb_arena_allocator_t){storage, need, 0};
    tvdb_quad_mesh from_arena;
    tvdb_quad_mesh_init(&from_arena);
    CHECK(tvdb_grid_volume_to_mesh_dual_one_ex(&grid, 0.0f, 0, NULL, &from_arena, &arena, NULL) ==
          TVDB_OK);
    CHECK(same_mesh(&from_arena, &mesh));
    CHECK(arena.current_offset <= need);
    /* from_arena's buffers belong to the arena: release them via storage. */
    free(storage);

    free(guard.vertices);
    free(guard.quads);
    tvdb_quad_mesh_free(&dense_closed);
    tvdb_quad_mesh_free(&mesh);
    tvdb_grid_destroy_owned(&grid);

    /* Boundary-touching sphere: shell pinning closes the surface. */
    fill(boundary_sphere, data);
    tvdb_dense_grid bdense = {N, N, N, ORIGIN, ORIGIN, ORIGIN, 1.0f, data};
    tvdb_quad_mesh dense_padded;
    tvdb_quad_mesh_init(&dense_padded);
    CHECK(tvdb_sdf_to_mesh_dual_one_padded_ex(&bdense, 0.0f, NULL, &dense_padded, NULL, NULL) ==
          TVDB_OK);
    CHECK(check_mesh(&dense_padded));

    tvdb_grid_t bgrid;
    CHECK(build_grid(&bdense, 1.0, &bgrid));
    tvdb_quad_mesh bmesh;
    tvdb_quad_mesh_init(&bmesh);
    CHECK(tvdb_grid_volume_to_mesh_dual_one_ex(&bgrid, 0.0f, 0, NULL, &bmesh, NULL, &err) ==
          TVDB_OK);
    CHECK(check_mesh(&bmesh)); /* closed by the shell, outward */
    CHECK(bmesh.vertex_count == dense_padded.vertex_count &&
          bmesh.quad_count == dense_padded.quad_count);
    printf("test_mesh_dual_tree_one [boundary]: %zu vertices, %zu quads, shell-pinned closed\n",
           bmesh.vertex_count, bmesh.quad_count);

    tvdb_quad_mesh_free(&dense_padded);
    tvdb_quad_mesh_free(&bmesh);
    tvdb_grid_destroy_owned(&bgrid);
    free(data);
    puts("test_mesh_dual_tree_one: OK (counts, closure, winding, determinism, contract)");
    return 0;
}
