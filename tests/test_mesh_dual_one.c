/* Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
   SPDX-License-Identifier: Apache-2.0 */

/* Dense DMC-1 (Nielson dual marching cubes), first slice.
 *
 * Independent oracle (does not call any DMC-1 library code except the public
 * API under test):
 *   - the expected quad count is the number of crossed primal edges with four
 *     incident cells, recomputed from the analytic field;
 *   - the expected vertex count is the sum, over crossed cells, of the MC soup
 *     component count computed here by adjacency BFS over the shipped table
 *     (NOT the library's union-find);
 *   - each quad must have four distinct corners, the directed-edge list must
 *     be closed (watertight), and the signed volume positive;
 *   - the result is byte-identical across worker counts and equals DMC-0's
 *     quad count (same crossed edges) while having >= DMC-0's vertex count.
 * A tiny single-corner field also checks the documented QEF placement.
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "tinyvdb_mc_tri_table.h"
#include "tinyvdb_mesh_dual.h"

#define CHECK(x)                                                                                   \
    do {                                                                                           \
        if (!(x)) {                                                                                \
            fprintf(stderr, "line %d: %s\n", __LINE__, #x);                                        \
            return 1;                                                                              \
        }                                                                                          \
    } while (0)

#define N 24
#define ORIGIN (-N / 2.0f)

typedef float (*field_fn)(float, float, float);

static size_t vidx(int n, int x, int y, int z) {
    return (size_t)x + (size_t)y * n + (size_t)z * n * n;
}

static void fill(int n, float origin, float vs, field_fn f, float *data) {
    for (int z = 0; z < n; ++z)
        for (int y = 0; y < n; ++y)
            for (int x = 0; x < n; ++x) {
                float wx = origin + (x + 0.5f) * vs, wy = origin + (y + 0.5f) * vs,
                      wz = origin + (z + 0.5f) * vs;
                data[vidx(n, x, y, z)] = f(wx, wy, wz);
            }
}

static float sphere(float x, float y, float z) {
    return sqrtf(x * x + y * y + z * z) - 6.5f;
}
static float torus(float x, float y, float z) {
    float r = sqrtf(x * x + z * z) - 6.0f;
    return sqrtf(r * r + y * y) - 2.5f;
}
static float box(float x, float y, float z) {
    float a = fabsf(x), b = fabsf(y), c = fabsf(z);
    float m = a > b ? a : b;
    m = m > c ? m : c;
    return m - 6.5f;
}
/* Windowed oscillation: pins the boundary outside while producing many
 * ambiguous MC cases (multi-patch cells), the hardest DMC-1 stitching case. */
static float ripple(float x, float y, float z) {
    double r2 = (x * x + y * y + z * z) / (9.0 * 9.0);
    double w = r2 < 1.0 ? 1.0 - r2 : 0.0;
    return (float)(0.6 - 3.0 * w * sin(1.1 * x) * sin(1.1 * y) * sin(1.1 * z));
}

/* Same corner/edge convention as the MC table and the DMC-0 tests. */
static const int CORNER[8][3] = {{0, 0, 0}, {1, 0, 0}, {1, 1, 0}, {0, 1, 0},
                                 {0, 0, 1}, {1, 0, 1}, {1, 1, 1}, {0, 1, 1}};
static const int EDGE[12][2] = {{0, 1}, {1, 2}, {2, 3}, {3, 0},
                                {4, 5}, {5, 6}, {6, 7}, {7, 4},
                                {0, 4}, {1, 5}, {2, 6}, {3, 7}};

static unsigned case_id(const float *data, int n, int x, int y, int z) {
    unsigned k = 0;
    for (int c = 0; c < 8; ++c)
        if (data[vidx(n, x + CORNER[c][0], y + CORNER[c][1], z + CORNER[c][2])] < 0.0f)
            k |= 1u << c;
    return k;
}
static int crossed(const float *data, int n, int x, int y, int z) {
    unsigned k = case_id(data, n, x, y, z);
    for (int e = 0; e < 12; ++e)
        if (((k >> EDGE[e][0]) & 1u) != ((k >> EDGE[e][1]) & 1u))
            return 1;
    return 0;
}
static int cross_edge(const float *data, int n, int x, int y, int z, int axis) {
    int q[3] = {x, y, z};
    int a = data[vidx(n, x, y, z)] < 0.0f;
    q[axis] += 1;
    return a != (data[vidx(n, q[0], q[1], q[2])] < 0.0f);
}

/* Expected quads: crossed primal edges with 4 incident cells (same loops as
 * the DMC-0 oracle). */
static size_t expected_quads(const float *data, int n) {
    size_t nq = 0;
    for (int z = 1; z <= n - 3; ++z) {
        for (int y = 1; y <= n - 3; ++y)
            for (int x = 0; x <= n - 2; ++x)
                nq += cross_edge(data, n, x, y, z, 0);
        for (int x = 1; x <= n - 3; ++x)
            for (int y = 0; y <= n - 2; ++y)
                nq += cross_edge(data, n, x, y, z, 1);
    }
    for (int z = 0; z <= n - 2; ++z)
        for (int y = 1; y <= n - 3; ++y)
            for (int x = 1; x <= n - 3; ++x)
                nq += cross_edge(data, n, x, y, z, 2);
    return nq;
}

/* Independent soup component count by adjacency BFS (not the library's
 * union-find), mirroring the machine-checked distribution in Vdb.DmcOne. */
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

/* Expected DMC-1 vertices: one per patch of every crossed cell. */
static size_t expected_vertices(const float *data, int n) {
    size_t nv = 0;
    for (int z = 0; z < n - 1; ++z)
        for (int y = 0; y < n - 1; ++y)
            for (int x = 0; x < n - 1; ++x)
                if (crossed(data, n, x, y, z))
                    nv += (size_t)ref_patch_count(case_id(data, n, x, y, z));
    return nv;
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

static int check_mesh(const tvdb_quad_mesh *m, int want_watertight, int want_volume) {
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
                    return 0; /* four distinct corners required */
                }
            if (v[t] >= m->vertex_count) {
                free(edges);
                return 0; /* never emit invalid indices */
            }
            edges[4 * q + t] = (edge_t){v[t], v[(t + 1) & 3]};
        }
        tvdb_vec3f p[4] = {m->vertices[v[0]], m->vertices[v[1]], m->vertices[v[2]],
                           m->vertices[v[3]]};
        const int tri[2][3] = {{0, 1, 2}, {0, 2, 3}};
        for (int t = 0; t < 2; ++t) {
            tvdb_vec3f a = p[tri[t][0]], b = p[tri[t][1]], c = p[tri[t][2]];
            vol += (a.x * (b.y * c.z - b.z * c.y) - a.y * (b.x * c.z - b.z * c.x) +
                    a.z * (b.x * c.y - b.y * c.x)) /
                   6.0;
        }
    }
    int ok = 1;
    if (want_watertight) {
        qsort(edges, ne, sizeof(edge_t), edge_cmp);
        for (size_t i = 0; i < ne && ok; ++i)
            if (edge_count(edges, ne, edges[i].u, edges[i].v) !=
                edge_count(edges, ne, edges[i].v, edges[i].u))
                ok = 0;
    }
    if (want_volume && !(vol > 0.0))
        ok = 0;
    free(edges);
    return ok;
}

static int same_mesh(const tvdb_quad_mesh *a, const tvdb_quad_mesh *b) {
    return a->vertex_count == b->vertex_count && a->quad_count == b->quad_count &&
           !memcmp(a->vertices, b->vertices, a->vertex_count * sizeof(tvdb_vec3f)) &&
           !memcmp(a->quads, b->quads, a->quad_count * sizeof(tvdb_quad));
}

static int run_field(const char *name, int n, float origin, float vs, field_fn f) {
    float *data = malloc((size_t)n * n * n * sizeof(float));
    CHECK(data);
    fill(n, origin, vs, f, data);
    tvdb_dense_grid g = {n, n, n, origin, origin, origin, vs, data};

    size_t want_q = expected_quads(data, n);
    size_t want_v = expected_vertices(data, n);
    size_t want_cells = 0;
    for (int z = 0; z < n - 1; ++z)
        for (int y = 0; y < n - 1; ++y)
            for (int x = 0; x < n - 1; ++x)
                want_cells += crossed(data, n, x, y, z);
    CHECK(want_q > 100 && want_v >= want_cells);

    tvdb_quad_mesh one, zero;
    tvdb_quad_mesh_init(&one);
    tvdb_quad_mesh_init(&zero);
    CHECK(tvdb_sdf_to_mesh_dual_one_ex(&g, 0.0f, NULL, &one, NULL, NULL) == TVDB_OK);
    CHECK(tvdb_sdf_to_mesh_dual_ex(&g, 0.0f, NULL, &zero, NULL, NULL) == TVDB_OK);

    /* Independent count oracles. */
    CHECK(one.vertex_count == want_v);
    CHECK(one.quad_count == want_q);
    /* DMC-1 emits the same crossed edges (quad count) but splits ambiguous
     * cells into multiple patch vertices, so it never has fewer vertices. */
    CHECK(zero.quad_count == want_q);
    CHECK(zero.vertex_count == want_cells && one.vertex_count >= zero.vertex_count);
    CHECK(check_mesh(&one, 1, 1));

    /* Determinism across worker partitions (counting is parallel, emission serial). */
    tvdb_thread_pool_t *p1 = NULL, *p4 = NULL;
    CHECK(tvdb_thread_pool_create(1, &p1, NULL) == TVDB_OK);
    CHECK(tvdb_thread_pool_create(4, &p4, NULL) == TVDB_OK);
    tvdb_quad_mesh a, b;
    tvdb_quad_mesh_init(&a);
    tvdb_quad_mesh_init(&b);
    CHECK(tvdb_sdf_to_mesh_dual_one_ex(&g, 0.0f, p1, &a, NULL, NULL) == TVDB_OK);
    CHECK(tvdb_sdf_to_mesh_dual_one_ex(&g, 0.0f, p4, &b, NULL, NULL) == TVDB_OK);
    CHECK(same_mesh(&one, &a) && same_mesh(&one, &b));
    tvdb_thread_pool_destroy(p1);
    tvdb_thread_pool_destroy(p4);
    tvdb_quad_mesh_free(&a);
    tvdb_quad_mesh_free(&b);

    /* Convenience wrapper. */
    tvdb_quad_mesh wrapped;
    tvdb_quad_mesh_init(&wrapped);
    CHECK(tvdb_sdf_to_mesh_dual_one(&g, 0.0f, &wrapped, NULL));
    CHECK(same_mesh(&one, &wrapped));
    tvdb_quad_mesh_free(&wrapped);

    /* Appending: indices globally based, prefix preserved. */
    tvdb_quad_mesh append;
    tvdb_quad_mesh_init(&append);
    append.vertices = malloc(sizeof(tvdb_vec3f));
    append.quads = malloc(sizeof(tvdb_quad));
    CHECK(append.vertices && append.quads);
    append.vertex_count = append.vertex_capacity = append.quad_count = append.quad_capacity = 1;
    append.vertices[0] = (tvdb_vec3f){8, 9, 10};
    append.quads[0] = (tvdb_quad){0, 0, 0, 0};
    CHECK(tvdb_sdf_to_mesh_dual_one_ex(&g, 0.0f, NULL, &append, NULL, NULL) == TVDB_OK);
    CHECK(append.vertex_count == want_v + 1 && append.quad_count == want_q + 1);
    CHECK(append.vertices[0].y == 9 && append.quads[0].v0 == 0);
    for (size_t q = 1; q < append.quad_count; ++q) {
        const tvdb_quad *f = &append.quads[q];
        CHECK(f->v0 >= 1 && f->v1 >= 1 && f->v2 >= 1 && f->v3 >= 1 &&
              f->v0 < append.vertex_count && f->v1 < append.vertex_count &&
              f->v2 < append.vertex_count && f->v3 < append.vertex_count);
    }
    tvdb_quad_mesh_free(&append);

    printf("test_mesh_dual_one [%s]: %zu vertices, %zu quads, watertight, deterministic\n", name,
           one.vertex_count, one.quad_count);
    tvdb_quad_mesh_free(&one);
    tvdb_quad_mesh_free(&zero);
    free(data);
    return 0;
}

/* A sphere whose surface meets the domain boundary: N=24, origin -12, radius
 * 12, so the outer samples are inside while the pinned outside shell is not. */
static float boundary_sphere(float x, float y, float z) {
    return sqrtf(x * x + y * y + z * z) - 12.0f;
}

static int check_padded(void) {
    float *data = malloc((size_t)N * N * N * sizeof(float));
    CHECK(data);
    fill(N, ORIGIN, 1.0f, boundary_sphere, data);
    tvdb_dense_grid g = {N, N, N, ORIGIN, ORIGIN, ORIGIN, 1.0f, data};

    tvdb_quad_mesh open, closed, wrapped;
    tvdb_quad_mesh_init(&open);
    tvdb_quad_mesh_init(&closed);
    tvdb_quad_mesh_init(&wrapped);
    CHECK(tvdb_sdf_to_mesh_dual_one_ex(&g, 0.0f, NULL, &open, NULL, NULL) == TVDB_OK);
    CHECK(tvdb_sdf_to_mesh_dual_one_padded_ex(&g, 0.0f, NULL, &closed, NULL, NULL) == TVDB_OK);
    CHECK(open.quad_count > 0 && closed.quad_count > open.quad_count);
    CHECK(check_mesh(&open, 0, 0));
    CHECK(!check_mesh(&open, 1, 0)); /* unpadded: surface meets the boundary -> open */
    CHECK(check_mesh(&closed, 1, 1)); /* shell-pinned: closed, outward */

    CHECK(tvdb_sdf_to_mesh_dual_one_padded(&g, 0.0f, &wrapped, NULL));
    CHECK(same_mesh(&wrapped, &closed));

    /* Determinism across worker partitions. */
    tvdb_thread_pool_t *p1 = NULL, *p4 = NULL;
    CHECK(tvdb_thread_pool_create(1, &p1, NULL) == TVDB_OK);
    CHECK(tvdb_thread_pool_create(4, &p4, NULL) == TVDB_OK);
    tvdb_quad_mesh a, b;
    tvdb_quad_mesh_init(&a);
    tvdb_quad_mesh_init(&b);
    CHECK(tvdb_sdf_to_mesh_dual_one_padded_ex(&g, 0.0f, p1, &a, NULL, NULL) == TVDB_OK);
    CHECK(tvdb_sdf_to_mesh_dual_one_padded_ex(&g, 0.0f, p4, &b, NULL, NULL) == TVDB_OK);
    CHECK(same_mesh(&a, &closed) && same_mesh(&b, &closed));
    tvdb_thread_pool_destroy(p1);
    tvdb_thread_pool_destroy(p4);
    tvdb_quad_mesh_free(&a);
    tvdb_quad_mesh_free(&b);

    /* Failure preservation on a nonfinite sample. */
    size_t mid = vidx(N, N / 2, N / 2, N / 2);
    float saved = data[mid];
    data[mid] = NAN;
    tvdb_quad_mesh guard;
    tvdb_quad_mesh_init(&guard);
    guard.vertices = malloc(sizeof(tvdb_vec3f));
    guard.quads = malloc(sizeof(tvdb_quad));
    CHECK(guard.vertices && guard.quads);
    guard.vertex_count = guard.vertex_capacity = guard.quad_count = guard.quad_capacity = 1;
    guard.vertices[0] = (tvdb_vec3f){3, 4, 5};
    guard.quads[0] = (tvdb_quad){0, 0, 0, 0};
    tvdb_quad_mesh saved_guard = guard;
    CHECK(tvdb_sdf_to_mesh_dual_one_padded_ex(&g, 0.0f, NULL, &guard, NULL, NULL) != TVDB_OK);
    CHECK(!memcmp(&guard, &saved_guard, sizeof(guard)));
    data[mid] = saved;

    printf("test_mesh_dual_one [padded]: open=%zu quads -> shell-pinned closed=%zu quads, "
           "watertight, deterministic\n", open.quad_count, closed.quad_count);
    tvdb_quad_mesh_free(&open);
    tvdb_quad_mesh_free(&closed);
    tvdb_quad_mesh_free(&wrapped);
    free(guard.vertices);
    free(guard.quads);
    free(data);
    return 0;
}

/* One interior lattice corner is inside; verify the DMC-1 vertex at raster
 * index 0 (cell (0,0,0), case bit 6) minimises the QEF of its three crossing
 * planes. For this field the interpolated gradients at the outside endpoints
 * are axis-aligned, so the QEF solution is the component-wise crossing point
 * (-0.9,-0.9,-0.9), distinct from the crossing centroid (-0.633...). */
static float one_corner(float x, float y, float z) {
    float dx = x + 0.5f, dy = y + 0.5f, dz = z + 0.5f;
    return sqrtf(dx * dx + dy * dy + dz * dz) - 0.4f;
}

static int check_placement(void) {
    const int n = 4;
    const float origin = -2.0f;
    float *data = malloc((size_t)n * n * n * sizeof(float));
    CHECK(data);
    fill(n, origin, 1.0f, one_corner, data);
    tvdb_dense_grid g = {n, n, n, origin, origin, origin, 1.0f, data};
    tvdb_quad_mesh m;
    tvdb_quad_mesh_init(&m);
    CHECK(tvdb_sdf_to_mesh_dual_one_ex(&g, 0.0f, NULL, &m, NULL, NULL) == TVDB_OK);
    CHECK(m.vertex_count == 8); /* one patch in each of 8 incident cells */
    CHECK(check_mesh(&m, 1, 1));

    /* Crossings: corner (1,1,1) world -0.5, neighbours one step away, t=0.4.
     * The three interpolated normals are -x, -y, -z, so each plane fixes one
     * coordinate to -0.9; the centroid (-0.633...) must NOT be the answer. */
    const double c = -0.5, t = 0.4, nb = -1.5;
    const double cross = c + t * (nb - c);
    const double centroid = (cross + c + c) / 3.0;
    CHECK(fabs((double)m.vertices[0].x - cross) < 1e-4);
    CHECK(fabs((double)m.vertices[0].y - cross) < 1e-4);
    CHECK(fabs((double)m.vertices[0].z - cross) < 1e-4);
    CHECK(fabs((double)m.vertices[0].x - centroid) > 1e-2);
    CHECK((double)m.vertices[0].x >= -1.5 && (double)m.vertices[0].x <= -0.5); /* stays in cell */
    tvdb_quad_mesh_free(&m);
    free(data);
    puts("test_mesh_dual_one [placement]: QEF of patch crossings OK");
    return 0;
}

int main(void) {
    CHECK(run_field("sphere", N, ORIGIN, 1.0f, sphere) == 0);
    CHECK(run_field("torus", N, ORIGIN, 1.0f, torus) == 0);
    CHECK(run_field("box", N, ORIGIN, 1.0f, box) == 0);
    CHECK(run_field("ripple", N, ORIGIN, 1.0f, ripple) == 0);
    CHECK(check_padded() == 0);
    CHECK(check_placement() == 0);

    /* Contract: invalid isovalue / nonfinite sample / alias / arena rollback. */
    float *data = malloc((size_t)N * N * N * sizeof(float));
    CHECK(data);
    fill(N, ORIGIN, 1.0f, sphere, data);
    tvdb_dense_grid g = {N, N, N, ORIGIN, ORIGIN, ORIGIN, 1.0f, data};
    tvdb_quad_mesh guard;
    tvdb_quad_mesh_init(&guard);
    guard.vertices = malloc(sizeof(tvdb_vec3f));
    guard.quads = malloc(sizeof(tvdb_quad));
    CHECK(guard.vertices && guard.quads);
    guard.vertex_count = guard.vertex_capacity = guard.quad_count = guard.quad_capacity = 1;
    guard.vertices[0] = (tvdb_vec3f){8, 9, 10};
    guard.quads[0] = (tvdb_quad){0, 0, 0, 0};
    tvdb_quad_mesh saved = guard;
    tvdb_error_t err;

    CHECK(tvdb_sdf_to_mesh_dual_one_ex(&g, NAN, NULL, &guard, NULL, &err) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(err.status == TVDB_ERROR_INVALID_ARGUMENT && err.message[0]);
    CHECK(!memcmp(&guard, &saved, sizeof(guard)));

    guard.vertices = (tvdb_vec3f *)(void *)data; /* alias input grid */
    CHECK(tvdb_sdf_to_mesh_dual_one_ex(&g, 0.0f, NULL, &guard, NULL, NULL) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    guard.vertices = saved.vertices;
    CHECK(!memcmp(&guard, &saved, sizeof(guard)));

    float saved_sample = data[vidx(N, N / 2, N / 2, N / 2)];
    data[vidx(N, N / 2, N / 2, N / 2)] = NAN;
    CHECK(tvdb_sdf_to_mesh_dual_one_ex(&g, 0.0f, NULL, &guard, NULL, &err) ==
          TVDB_ERROR_INVALID_DATA);
    CHECK(!memcmp(&guard, &saved, sizeof(guard)));
    data[vidx(N, N / 2, N / 2, N / 2)] = saved_sample;

    char tiny[64];
    tvdb_arena_allocator_t arena = {tiny, sizeof(tiny), 3};
    tvdb_quad_mesh empty;
    tvdb_quad_mesh_init(&empty);
    CHECK(tvdb_sdf_to_mesh_dual_one_ex(&g, 0.0f, NULL, &empty, &arena, &err) ==
          TVDB_ERROR_OUT_OF_MEMORY);
    CHECK(arena.current_offset == 3 && !empty.vertices && !empty.quads);

    free(guard.vertices);
    free(guard.quads);
    free(data);
    puts("test_mesh_dual_one: OK (counts, closure, winding, determinism, contract)");
    return 0;
}
