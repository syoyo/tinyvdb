/* Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
   SPDX-License-Identifier: Apache-2.0 */

/* Dense dual marching cubes, first slice (DMC-0 / naive surface nets).
 * See tinyvdb_mesh_dual.h for the contract and the staged scope. */

#include "tinyvdb_mesh_dual.h"

#include "tinyvdb_checked.h"
#include "tinyvdb_mc_tri_table.h"  /* MC_TRI_TABLE (cube-local patch decomposition) */
#include "tinyvdb_tree.h"          /* tvdb_grid_diagnose */
#include "tinyvdb_tree_internal.h" /* tree index/accessor/matrix (library-local) */
#include <assert.h>
#include <float.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TVDB_DUAL_MAX_GRID_DIM 2048

/* MC cube corners and edge endpoints, in the canonical table order. */
static const int DUAL_CORNER[8][3] = {
    {0, 0, 0}, {1, 0, 0}, {1, 1, 0}, {0, 1, 0},
    {0, 0, 1}, {1, 0, 1}, {1, 1, 1}, {0, 1, 1}};
static const int DUAL_EDGE[12][2] = {
    {0, 1}, {1, 2}, {2, 3}, {3, 0},
    {4, 5}, {5, 6}, {6, 7}, {7, 4},
    {0, 4}, {1, 5}, {2, 6}, {3, 7}};

/* Cross axes in the right-handed counter-clockwise order of each primal axis:
 * rotate y->z about +x, z->x about +y, x->y about +z. */
static const int DUAL_CROSS_AXIS[3][2] = {{1, 2}, {2, 0}, {0, 1}};
/* The four cells around an edge, by (+/-0,+/-1) cross-axis lower-corner
 * offsets, in increasing CCW angle about the positive edge axis. */
static const int DUAL_CROSS_STEP[4][2] = {{1, 1}, {0, 1}, {0, 0}, {1, 0}};

/* ---- cube-local MC patch decomposition (DMC-1 first slice) --------------
 *
 * Union-find over the 12 cube edges, following Vdb.DmcOne exactly: each
 * triangle merges its first edge with its second, then its second with its
 * third (`ufStep`). The attach direction is "root of x becomes child of root
 * of y" with no rank and no path compression, so the roots (and hence the
 * patch ids) match the Lean oracle for every case. At 12 elements the find
 * chain is bounded; no cycles are possible. */

static int dual_uf_find(const int parent[12], int x) {
    while (parent[x] != x)
        x = parent[x];
    return x;
}

static void dual_uf_union(int parent[12], int x, int y) {
    int px = dual_uf_find(parent, x), py = dual_uf_find(parent, y);
    if (px != py)
        parent[px] = py;
}

static void dual_uf_step(int parent[12], const int tri[3]) {
    dual_uf_union(parent, tri[0], tri[1]);
    dual_uf_union(parent, tri[1], tri[2]);
}

bool tvdb_dual_patch_compute(unsigned case_id, tvdb_dual_patch_info *info) {
    if (!info || case_id > 255)
        return false;
    memset(info, 0, sizeof(*info));

    /* Parse the case's triangle soup, recording first occurrences of edges. */
    const int *row = MC_TRI_TABLE[case_id];
    int tris[TVDB_DUAL_PATCH_MAX_TRIS][3];
    int ntris = 0, used[12], nused = 0;
    bool seen[12] = {false, false, false, false, false, false,
                     false, false, false, false, false, false};
    for (int i = 0; i + 2 < 16; i += 3) {
        if (row[i] < 0)
            break;
        if (ntris == TVDB_DUAL_PATCH_MAX_TRIS)
            return false; /* shipped table is machine-checked to <= 5 triangles */
        int a = row[i], b = row[i + 1], c = row[i + 2];
        if (a < 0 || a > 11 || b < 0 || b > 11 || c < 0 || c > 11)
            return false; /* malformed table row: do not read past the soup */
        tris[ntris][0] = a;
        tris[ntris][1] = b;
        tris[ntris][2] = c;
        ++ntris;
        const int v[3] = {a, b, c};
        for (int j = 0; j < 3; ++j)
            if (!seen[v[j]]) {
                seen[v[j]] = true;
                used[nused++] = v[j];
            }
    }
    info->tri_count = (uint8_t)ntris;

    /* Sign-change mask from the case's corner bits (Bourke bit order).
     * DUAL_EDGE is the same edge->corner table as the C MC table and the
     * Lean `McTable.mcEdgeVerts`, so this equals the case's MC edge mask. */
    uint16_t cross = 0;
    for (int e = 0; e < 12; ++e) {
        unsigned a = (case_id >> DUAL_EDGE[e][0]) & 1u;
        unsigned b = (case_id >> DUAL_EDGE[e][1]) & 1u;
        if (a != b)
            cross |= (uint16_t)(1u << e);
    }
    info->cross_mask = cross;

    if (ntris == 0)
        return true; /* empty soup: zero patches (the two uniform cases) */

    int parent[12];
    for (int e = 0; e < 12; ++e)
        parent[e] = e;
    for (int t = 0; t < ntris; ++t)
        dual_uf_step(parent, tris[t]);

    /* Roots of the used edges, in first-occurrence order: patch ids are the
     * rank of a triangle's root in this list. */
    int roots[12], nroots = 0;
    for (int i = 0; i < nused; ++i)
        if (dual_uf_find(parent, used[i]) == used[i])
            roots[nroots++] = used[i];
    if (nroots > TVDB_DUAL_PATCH_MAX_PATCHES)
        return false; /* shipped table is machine-checked to <= 4 patches */
    info->patch_count = (uint8_t)nroots;

    for (int t = 0; t < ntris; ++t) {
        int r = dual_uf_find(parent, tris[t][0]);
        int p = 0;
        while (p < nroots && roots[p] != r)
            ++p;
        info->tri_patch[t] = (uint8_t)p; /* p < nroots: r is a root of a used edge */
    }

    /* Deduplicated patch ids owning each cube edge (`patchesUsing`). */
    for (int e = 0; e < 12; ++e) {
        uint8_t count = 0;
        for (int t = 0; t < ntris; ++t) {
            if (tris[t][0] != e && tris[t][1] != e && tris[t][2] != e)
                continue;
            uint8_t p = info->tri_patch[t];
            bool present = false;
            for (int j = 0; j < count; ++j)
                if (info->edge_patch[e][j] == p) {
                    present = true;
                    break;
                }
            if (!present)
                info->edge_patch[e][count++] = p;
        }
        info->edge_patch_count[e] = count;
    }
    return true;
}

static tvdb_status_t dual_error(tvdb_error_t *err, tvdb_status_t status, const char *message) {
    if (err) {
        memset(err, 0, sizeof(*err));
        err->status = status;
        snprintf(err->message, sizeof(err->message), "%s", message);
    }
    return status;
}

static void *dual_arena_destination(const tvdb_arena_allocator_t *arena, size_t *offset,
                                    size_t bytes) {
    if (!arena->buffer || *offset > SIZE_MAX - 7)
        return NULL;
    size_t aligned = (*offset + 7) & ~(size_t)7;
    if (aligned > arena->buffer_size || bytes > arena->buffer_size - aligned ||
        aligned > UINTPTR_MAX - (uintptr_t)arena->buffer)
        return NULL;
    *offset = aligned + bytes;
    return (void *)((uintptr_t)arena->buffer + aligned);
}

static void *dual_alloc(tvdb_arena_allocator_t *arena, size_t bytes) {
    return arena ? tvdb_arena_alloc(arena, bytes) : malloc(bytes);
}

static tvdb_status_t dual_pool(size_t work, size_t tasks, tvdb_thread_pool_t **pool,
                               tvdb_error_t *err) {
    size_t workers = work < 32768 ? 1 : tvdb_thread_default_count();
    if (workers > 8)
        workers = 8;
    if (workers > tasks)
        workers = tasks;
    if (!workers)
        workers = 1;
    return tvdb_thread_pool_create(workers, pool, err);
}

/* A source storage region the output must not overlap. */
typedef struct {
    const void *ptr;
    size_t bytes;
} dual_region;

/* Validate output buffers, check aliasing against every `inputs` region, and
 * grow `out` into `result` (copying the existing prefix). Emission is left to
 * the caller, which must set result.vertex_count/quad_count and commit. On
 * failure *result may hold newly allocated buffers that the caller frees;
 * the arena offset is left untouched for the caller to roll back. */
static tvdb_status_t dual_commit(tvdb_quad_mesh *out, size_t total_v, size_t total_q,
                                 const dual_region *inputs, size_t ninputs,
                                 tvdb_arena_allocator_t *arena, size_t mark,
                                 tvdb_quad_mesh *result, tvdb_error_t *err) {
    size_t ovb, oqb, vbytes, qbytes;
    if (!tvdb_size_mul(out->vertex_capacity, sizeof(tvdb_vec3f), &ovb) ||
        !tvdb_size_mul(out->quad_capacity, sizeof(tvdb_quad), &oqb) ||
        !tvdb_size_mul(total_v, sizeof(tvdb_vec3f), &vbytes) ||
        !tvdb_size_mul(total_q, sizeof(tvdb_quad), &qbytes))
        return dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                          "dual marching cubes size overflow");
    for (size_t i = 0; i < ninputs; ++i)
        if (tvdb_buffers_overlap(inputs[i].ptr, inputs[i].bytes, out->vertices, ovb) ||
            tvdb_buffers_overlap(inputs[i].ptr, inputs[i].bytes, out->quads, oqb))
            return dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                              "dual marching cubes storage overlaps");
    if (tvdb_buffers_overlap(out->vertices, ovb, out->quads, oqb))
        return dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                          "dual marching cubes storage overlaps");

    void *dest_v = out->vertices, *dest_q = out->quads;
    if (arena) {
        size_t offset = mark;
        if (total_v > out->vertex_capacity)
            dest_v = dual_arena_destination(arena, &offset, vbytes);
        if (total_q > out->quad_capacity)
            dest_q = dual_arena_destination(arena, &offset, qbytes);
        if (!dest_v || !dest_q)
            return dual_error(err, TVDB_ERROR_OUT_OF_MEMORY,
                              "dual marching cubes arena exhausted");
        for (size_t i = 0; i < ninputs; ++i)
            if (tvdb_buffers_overlap(inputs[i].ptr, inputs[i].bytes, dest_v, vbytes) ||
                tvdb_buffers_overlap(inputs[i].ptr, inputs[i].bytes, dest_q, qbytes))
                return dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                                  "dual marching cubes arena storage overlaps");
        if (tvdb_buffers_overlap(dest_v, vbytes, dest_q, qbytes) ||
            (dest_v != out->vertices &&
             tvdb_buffers_overlap(dest_v, vbytes, out->vertices, ovb)) ||
            (dest_q != out->quads && tvdb_buffers_overlap(dest_q, qbytes, out->quads, oqb)) ||
            tvdb_buffers_overlap(dest_v, vbytes, out->quads, oqb) ||
            tvdb_buffers_overlap(dest_q, qbytes, out->vertices, ovb))
            return dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                              "dual marching cubes arena storage overlaps");
    }

    *result = *out;
    if (total_v > result->vertex_capacity) {
        result->vertices = dual_alloc(arena, vbytes);
        if (!result->vertices)
            return dual_error(err, TVDB_ERROR_OUT_OF_MEMORY,
                              "dual marching cubes allocation failed");
        result->vertex_capacity = total_v;
        if (out->vertex_count)
            memcpy(result->vertices, out->vertices, out->vertex_count * sizeof(tvdb_vec3f));
    }
    if (total_q > result->quad_capacity) {
        result->quads = dual_alloc(arena, qbytes);
        if (!result->quads)
            return dual_error(err, TVDB_ERROR_OUT_OF_MEMORY,
                              "dual marching cubes allocation failed");
        result->quad_capacity = total_q;
        if (out->quad_count)
            memcpy(result->quads, out->quads, out->quad_count * sizeof(tvdb_quad));
    }
    return TVDB_OK;
}

static size_t dual_voxel_index(const tvdb_dense_grid *g, int x, int y, int z) {
    return (size_t)x + (size_t)y * (size_t)g->nx + (size_t)z * (size_t)g->nx * (size_t)g->ny;
}

static int dual_grid_frame(const tvdb_dense_grid *g, size_t *bytes) {
    if (!g || !tvdb_grid_valid(g->nx, g->ny, g->nz, g->voxel_size, g->data, sizeof(float)) ||
        g->nx > TVDB_DUAL_MAX_GRID_DIM || g->ny > TVDB_DUAL_MAX_GRID_DIM ||
        g->nz > TVDB_DUAL_MAX_GRID_DIM ||
        !tvdb_grid_bytes(g->nx, g->ny, g->nz, sizeof(float), bytes))
        return 0;
    const float origin[3] = {g->ox, g->oy, g->oz};
    const int dim[3] = {g->nx, g->ny, g->nz};
    for (int a = 0; a < 3; ++a) {
        double lo = (double)origin[a] + 0.5 * g->voxel_size,
               hi = (double)origin[a] + (dim[a] - 0.5) * g->voxel_size;
        if (!isfinite(origin[a]) || !isfinite(lo) || !isfinite(hi) || fabs(lo) > FLT_MAX ||
            fabs(hi) > FLT_MAX)
            return 0;
    }
    return 1;
}

/* 12-bit sign-change mask of an MC cube; also flags nonfinite corner samples. */
static int dual_cross_mask(const tvdb_dense_grid *g, int x, int y, int z, float iso, int *bad) {
    int below[8];
    for (int c = 0; c < 8; ++c) {
        int cx = x + DUAL_CORNER[c][0], cy = y + DUAL_CORNER[c][1],
            cz = z + DUAL_CORNER[c][2];
        float v = g->data[dual_voxel_index(g, cx, cy, cz)];
        if (!isfinite(v)) {
            *bad = 1;
            return 0;
        }
        below[c] = v < iso;
    }
    int mask = 0;
    for (int e = 0; e < 12; ++e)
        if (below[DUAL_EDGE[e][0]] != below[DUAL_EDGE[e][1]])
            mask |= 1 << e;
    return mask;
}

static int dual_edge_cross(const tvdb_dense_grid *g, int x, int y, int z, int axis, float iso) {
    int q[3] = {x, y, z};
    int a = g->data[dual_voxel_index(g, x, y, z)] < iso;
    q[axis] += 1;
    int b = g->data[dual_voxel_index(g, q[0], q[1], q[2])] < iso;
    return a != b;
}

/* ---- per-plane counting (parallel, order-independent) -------------------- */

typedef struct {
    size_t vertices, quads;
    int bad;
} dual_count;

typedef struct {
    const tvdb_dense_grid *g;
    float iso;
    dual_count *counts;
} dual_count_job;

static void dual_count_plane(size_t begin, size_t end, void *user) {
    dual_count_job *job = user;
    const tvdb_dense_grid *g = job->g;
    for (size_t z = begin; z < end; ++z) {
        dual_count c = {0, 0, 0};
        for (int y = 0; y < g->ny - 1; ++y)
            for (int x = 0; x < g->nx - 1; ++x)
                if (dual_cross_mask(g, x, y, (int)z, job->iso, &c.bad))
                    ++c.vertices;
        /* x-edges and y-edges need 1 <= z <= nz-2 for four incident cells. */
        if (z >= 1 && z <= (size_t)g->nz - 2) {
            for (int y = 1; y <= g->ny - 2; ++y)
                for (int x = 0; x <= g->nx - 2; ++x)
                    if (dual_edge_cross(g, x, y, (int)z, 0, job->iso))
                        ++c.quads;
            for (int x = 1; x <= g->nx - 2; ++x)
                for (int y = 0; y <= g->ny - 2; ++y)
                    if (dual_edge_cross(g, x, y, (int)z, 1, job->iso))
                        ++c.quads;
        }
        /* z-edges need x,y in [1,dim-2] and z <= nz-2. */
        if (z <= (size_t)g->nz - 2)
            for (int y = 1; y <= g->ny - 2; ++y)
                for (int x = 1; x <= g->nx - 2; ++x)
                    if (dual_edge_cross(g, x, y, (int)z, 2, job->iso))
                        ++c.quads;
        job->counts[z] = c;
    }
}

/* ---- deterministic serial emission -------------------------------------- */

static float dual_axis_pos(const tvdb_dense_grid *g, int index, int axis) {
    float o = axis == 0 ? g->ox : axis == 1 ? g->oy : g->oz;
    float p = o + (index + 0.5f) * g->voxel_size;
    if (!isfinite(p))
        p = (float)((double)o + (index + 0.5) * g->voxel_size);
    return p;
}

static tvdb_vec3f dual_interpolate(const tvdb_dense_grid *g, float iso,
                                   const int a[3], const int b[3]) {
    double va = g->data[dual_voxel_index(g, a[0], a[1], a[2])],
           vb = g->data[dual_voxel_index(g, b[0], b[1], b[2])];
    double t = ((double)iso - va) / (vb - va);
    if (t < 0)
        t = 0;
    if (t > 1)
        t = 1;
    float pa[3], pb[3], p[3];
    for (int d = 0; d < 3; ++d) {
        pa[d] = dual_axis_pos(g, a[d], d);
        pb[d] = dual_axis_pos(g, b[d], d);
        p[d] = (float)((1 - t) * pa[d] + t * pb[d]);
    }
    return (tvdb_vec3f){p[0], p[1], p[2]};
}

typedef struct {
    uint64_t key;
    uint32_t value;
} dual_hash_entry;

static uint64_t dual_hash(uint64_t x) {
    x ^= x >> 33;
    x *= UINT64_C(0xff51afd7ed558ccd);
    x ^= x >> 33;
    x *= UINT64_C(0xc4ceb9fe1a85ec53);
    return x ^ (x >> 33);
}

static uint32_t *dual_hash_slot(dual_hash_entry *table, size_t mask, uint64_t key) {
    size_t at = (size_t)dual_hash(key) & mask;
    while (table[at].key && table[at].key != key)
        at = (at + 1) & mask;
    if (!table[at].key) {
        table[at].key = key;
        table[at].value = UINT32_MAX;
    }
    return &table[at].value;
}

static void dual_cell_of_edge(const int p[3], int axis, int s0, int s1, int cell[3]) {
    int c0 = DUAL_CROSS_AXIS[axis][0], c1 = DUAL_CROSS_AXIS[axis][1];
    cell[0] = p[0];
    cell[1] = p[1];
    cell[2] = p[2];
    cell[c0] = p[c0] - (s0 ? 0 : 1);
    cell[c1] = p[c1] - (s1 ? 0 : 1);
}

static void dual_emit(const tvdb_dense_grid *g, float iso, size_t base_v, size_t base_q,
                      dual_hash_entry *table, size_t mask, tvdb_quad_mesh *out) {
    size_t vi = 0, qi = 0;
    /* Pass 1: one centroid vertex per crossed cell, in raster order. */
    for (int z = 0; z < g->nz - 1; ++z)
        for (int y = 0; y < g->ny - 1; ++y)
            for (int x = 0; x < g->nx - 1; ++x) {
                int bad = 0;
                int cross = dual_cross_mask(g, x, y, z, iso, &bad);
                if (!cross)
                    continue;
                double sum[3] = {0, 0, 0};
                int n = 0;
                for (int e = 0; e < 12; ++e)
                    if (cross & (1 << e)) {
                        int a = DUAL_EDGE[e][0], b = DUAL_EDGE[e][1];
                        int ca[3] = {x + DUAL_CORNER[a][0], y + DUAL_CORNER[a][1],
                                     z + DUAL_CORNER[a][2]};
                        int cb[3] = {x + DUAL_CORNER[b][0], y + DUAL_CORNER[b][1],
                                     z + DUAL_CORNER[b][2]};
                        tvdb_vec3f p = dual_interpolate(g, iso, ca, cb);
                        sum[0] += p.x;
                        sum[1] += p.y;
                        sum[2] += p.z;
                        ++n;
                    }
                tvdb_vec3f v = {(float)(sum[0] / n), (float)(sum[1] / n), (float)(sum[2] / n)};
                out->vertices[base_v + vi] = v;
                size_t cell = (size_t)(z * (g->ny - 1) + y) * (g->nx - 1) + (size_t)x;
                *dual_hash_slot(table, mask, (uint64_t)cell + 1) = (uint32_t)vi;
                ++vi;
            }
    /* Pass 2: one quad per sign-changing primal edge with four incident cells. */
    for (int axis = 0; axis < 3; ++axis) {
        int lim[3] = {g->nx - 1, g->ny - 1, g->nz - 1};
        int lo[3] = {0, 0, 0}, hi[3] = {lim[0], lim[1], lim[2]};
        for (int d = 0; d < 3; ++d)
            if (d != axis) {
                lo[d] = 1;
                hi[d] = lim[d] - 1; /* dim-2 */
            }
        /* axis itself: lower lattice point in [0, dim-2]. */
        hi[axis] = lim[axis] - 1;
        for (int z = lo[2]; z <= hi[2]; ++z)
            for (int y = lo[1]; y <= hi[1]; ++y)
                for (int x = lo[0]; x <= hi[0]; ++x) {
                    int p[3] = {x, y, z};
                    if (!dual_edge_cross(g, x, y, z, axis, iso))
                        continue;
                    uint32_t quad[4];
                    for (int t = 0; t < 4; ++t) {
                        int cell[3];
                        dual_cell_of_edge(p, axis, DUAL_CROSS_STEP[t][0], DUAL_CROSS_STEP[t][1], cell);
                        size_t key = (size_t)(cell[2] * (g->ny - 1) + cell[1]) * (g->nx - 1) +
                                     (size_t)cell[0];
                        uint32_t local = *dual_hash_slot(table, mask, (uint64_t)key + 1);
                        assert(local != UINT32_MAX); /* counted and emitted identically */
                        quad[t] = (uint32_t)base_v + local;
                    }
                    /* Outward winding: reverse when the sample decreases
                     * along the positive edge axis (gradient points -axis). */
                    int q[3] = {x, y, z};
                    q[axis] += 1;
                    if (g->data[dual_voxel_index(g, q[0], q[1], q[2])] <
                        g->data[dual_voxel_index(g, x, y, z)]) {
                        uint32_t tmp = quad[1];
                        quad[1] = quad[3];
                        quad[3] = tmp;
                    }
                    out->quads[base_q + qi++] =
                        (tvdb_quad){quad[0], quad[1], quad[2], quad[3]};
                }
    }
    (void)vi;
    (void)qi;
}

void tvdb_quad_mesh_init(tvdb_quad_mesh *mesh) {
    if (!mesh)
        return;
    mesh->vertices = NULL;
    mesh->vertex_count = mesh->vertex_capacity = 0;
    mesh->quads = NULL;
    mesh->quad_count = mesh->quad_capacity = 0;
}

void tvdb_quad_mesh_free(tvdb_quad_mesh *mesh) {
    if (!mesh)
        return;
    free(mesh->vertices);
    free(mesh->quads);
    tvdb_quad_mesh_init(mesh);
}

void tvdb_quad_mesh_init_arena(tvdb_quad_mesh *mesh, tvdb_arena_allocator_t *arena) {
    (void)arena;
    tvdb_quad_mesh_init(mesh);
}

tvdb_status_t tvdb_sdf_to_mesh_dual_ex(const tvdb_dense_grid *g, float iso,
                                       tvdb_thread_pool_t *pool, tvdb_quad_mesh *out,
                                       tvdb_arena_allocator_t *arena, tvdb_error_t *err) {
    size_t grid_bytes;
    if (!out || !isfinite(iso) || !dual_grid_frame(g, &grid_bytes) || g->nx < 2 || g->ny < 2 ||
        g->nz < 2 || out->vertex_count > out->vertex_capacity ||
        out->quad_count > out->quad_capacity || out->vertex_count > UINT32_MAX ||
        (out->vertex_capacity && !out->vertices) || (out->quad_capacity && !out->quads))
        return dual_error(err, TVDB_ERROR_INVALID_ARGUMENT, "invalid dual marching cubes grid or output");

    tvdb_thread_pool_t *owned = NULL;
    dual_count *counts = NULL;
    dual_hash_entry *table = NULL;
    tvdb_quad_mesh result = *out;
    tvdb_status_t st = TVDB_OK;
    size_t mark = arena ? arena->current_offset : 0, count_bytes;

    if (!tvdb_size_mul((size_t)g->nz, sizeof(dual_count), &count_bytes))
        return dual_error(err, TVDB_ERROR_INVALID_ARGUMENT, "dual marching cubes count overflow");
    counts = malloc(count_bytes);
    if (!counts)
        goto oom;
    memset(counts, 0, count_bytes);
    if (!pool) {
        st = dual_pool(grid_bytes / sizeof(float), (size_t)g->nz - 1, &owned, err);
        if (st != TVDB_OK)
            goto done;
        pool = owned;
    }
    dual_count_job job = {g, iso, counts};
    st = tvdb_thread_pool_for(pool, 0, (size_t)g->nz - 1, 1, dual_count_plane, &job, err);
    if (st != TVDB_OK)
        goto done;

    size_t nv = 0, nq = 0;
    for (int z = 0; z < g->nz; ++z) {
        if (counts[z].bad) {
            st = dual_error(err, TVDB_ERROR_INVALID_DATA, "nonfinite dual marching cubes sample");
            goto done;
        }
        if (counts[z].vertices > SIZE_MAX - nv || counts[z].quads > SIZE_MAX - nq)
            goto overflow;
        nv += counts[z].vertices;
        nq += counts[z].quads;
    }
    if (nv > UINT32_MAX - out->vertex_count || nq > SIZE_MAX - out->quad_count)
        goto overflow;
    dual_region input = {g->data, grid_bytes};
    if (!nv && !nq) {
        /* Still validate output storage/aliasing, as the original path did. */
        st = dual_commit(out, out->vertex_count, out->quad_count, &input, 1, arena, mark,
                         &result, err);
        goto done;
    }
    size_t total_v = out->vertex_count + nv, total_q = out->quad_count + nq;
    st = dual_commit(out, total_v, total_q, &input, 1, arena, mark, &result, err);
    if (st != TVDB_OK)
        goto done;

    size_t capacity = 0;
    if (!tvdb_hash_capacity(nv, 2, &capacity))
        goto overflow;
    table = calloc(capacity, sizeof(dual_hash_entry));
    if (!table)
        goto oom;
    dual_emit(g, iso, out->vertex_count, out->quad_count, table, capacity - 1, &result);
    result.vertex_count = total_v;
    result.quad_count = total_q;
    if (!arena) {
        if (result.vertices != out->vertices)
            free(out->vertices);
        if (result.quads != out->quads)
            free(out->quads);
    }
    *out = result;
    goto done;
overflow:
    st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                    "dual marching cubes size exceeds index or allocation limits");
    goto done;
oom:
    st = dual_error(err, TVDB_ERROR_OUT_OF_MEMORY, "dual marching cubes allocation failed");
done:
    if (st != TVDB_OK) {
        if (arena)
            arena->current_offset = mark;
        else {
            if (result.vertices != out->vertices)
                free(result.vertices);
            if (result.quads != out->quads)
                free(result.quads);
        }
    }
    free(counts);
    free(table);
    tvdb_thread_pool_destroy(owned);
    return st;
}

bool tvdb_sdf_to_mesh_dual(const tvdb_dense_grid *g, float iso, tvdb_quad_mesh *out,
                           tvdb_arena_allocator_t *arena) {
    return tvdb_sdf_to_mesh_dual_ex(g, iso, NULL, out, arena, NULL) == TVDB_OK;
}

/* ---- dense DMC-1 (Nielson dual marching cubes) ---------------------------
 *
 * Reuses the DMC-0 counting / emission / commit machinery. The vertex key is
 * (cell, patch) instead of cell, and each patch vertex minimises the quadratic
 * error function of its owned edge-crossing planes (QEF): for crossing point
 * p_i with unit normal n_i, minimise sum_i (n_i . (x - p_i))^2. Normals come
 * from the interpolated central-difference gradient at the two edge ends.
 * A singular system falls back to the centroid of the crossings, and the final
 * point is clamped to the owning cell. See tinyvdb_mesh_dual.h for scope:
 * dense only, no padding, no C<->Lean index-vector claim.
 */

/* Clamped central-difference gradient at a lattice point, in world units. */
static void dual_gradient_at(const tvdb_dense_grid *g, int x, int y, int z, double out[3]) {
    int c[3] = {x, y, z};
    int dim[3] = {g->nx, g->ny, g->nz};
    for (int d = 0; d < 3; ++d) {
        int lo[3] = {x, y, z}, hi[3] = {x, y, z};
        lo[d] = c[d] > 0 ? c[d] - 1 : c[d];
        hi[d] = c[d] < dim[d] - 1 ? c[d] + 1 : c[d];
        double vl = g->data[dual_voxel_index(g, lo[0], lo[1], lo[2])];
        double vh = g->data[dual_voxel_index(g, hi[0], hi[1], hi[2])];
        double h = (double)(hi[d] - lo[d]) * (double)g->voxel_size;
        out[d] = h > 0 ? (vh - vl) / h : 0.0;
    }
}

/* Solve A x = b for a symmetric 3x3 A by Cramer's rule. Returns false when
 * the determinant is too small relative to A's scale (singular QEF). */
static bool dual_solve3(double A[3][3], double b[3], double x[3]) {
    double det = A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1]) -
                 A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0]) +
                 A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]);
    double scale = (A[0][0] + A[1][1] + A[2][2]) / 3.0;
    if (!isfinite(det) || !isfinite(scale) || scale <= 0 ||
        fabs(det) <= 1e-12 * scale * scale * scale)
        return false;
    for (int col = 0; col < 3; ++col) {
        double M[3][3];
        for (int i = 0; i < 3; ++i)
            for (int j = 0; j < 3; ++j)
                M[i][j] = (j == col) ? b[i] : A[i][j];
        double dc = M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) -
                    M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) +
                    M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]);
        x[col] = dc / det;
    }
    return isfinite(x[0]) && isfinite(x[1]) && isfinite(x[2]);
}

/* QEF vertex of one (cell, patch): minimise sum (n.(x-p))^2 over the patch's
 * owned edge crossings, clamped to the cell. Falls back to the centroid when
 * the normal equations are singular. */
static tvdb_vec3f dual_qef_vertex(const tvdb_dense_grid *g, float iso, int x, int y, int z,
                                  const tvdb_dual_patch_info *info, unsigned p) {
    double A[3][3] = {{0, 0, 0}, {0, 0, 0}, {0, 0, 0}};
    double b[3] = {0, 0, 0};
    double sum[3] = {0, 0, 0};
    int n = 0;
    for (int e = 0; e < 12; ++e) {
        if (info->edge_patch_count[e] != 1 || info->edge_patch[e][0] != (uint8_t)p)
            continue;
        int a = DUAL_EDGE[e][0], bb = DUAL_EDGE[e][1];
        int ca[3] = {x + DUAL_CORNER[a][0], y + DUAL_CORNER[a][1], z + DUAL_CORNER[a][2]};
        int cb[3] = {x + DUAL_CORNER[bb][0], y + DUAL_CORNER[bb][1], z + DUAL_CORNER[bb][2]};
        double va = g->data[dual_voxel_index(g, ca[0], ca[1], ca[2])];
        double vb = g->data[dual_voxel_index(g, cb[0], cb[1], cb[2])];
        if (va == vb)
            continue;
        double t = ((double)iso - va) / (vb - va);
        if (t < 0) t = 0;
        if (t > 1) t = 1;
        double pos[3], ga[3], gb[3], nv[3];
        for (int d = 0; d < 3; ++d)
            pos[d] = (1 - t) * dual_axis_pos(g, ca[d], d) + t * dual_axis_pos(g, cb[d], d);
        dual_gradient_at(g, ca[0], ca[1], ca[2], ga);
        dual_gradient_at(g, cb[0], cb[1], cb[2], gb);
        for (int d = 0; d < 3; ++d)
            nv[d] = (1 - t) * ga[d] + t * gb[d];
        double len = sqrt(nv[0] * nv[0] + nv[1] * nv[1] + nv[2] * nv[2]);
        if (!isfinite(len) || len < 1e-12)
            continue; /* degenerate gradient: omit this plane */
        for (int d = 0; d < 3; ++d)
            nv[d] /= len;
        double np = nv[0] * pos[0] + nv[1] * pos[1] + nv[2] * pos[2];
        for (int i = 0; i < 3; ++i) {
            for (int j = 0; j < 3; ++j)
                A[i][j] += nv[i] * nv[j];
            b[i] += np * nv[i];
        }
        for (int d = 0; d < 3; ++d)
            sum[d] += pos[d];
        ++n;
    }
    double sol[3];
    if (!n)
        return (tvdb_vec3f){0, 0, 0}; /* defensive: a patch owns >= 1 edge */
    if (!dual_solve3(A, b, sol))
        for (int d = 0; d < 3; ++d)
            sol[d] = sum[d] / n;
    /* The dual vertex must remain inside its cell. */
    int c[3] = {x, y, z};
    double origin[3] = {g->ox, g->oy, g->oz};
    for (int d = 0; d < 3; ++d) {
        /* An MC cell's corners are the voxel centres at indices c and c+1. */
        double lo = origin[d] + ((double)c[d] + 0.5) * (double)g->voxel_size;
        double hi = lo + (double)g->voxel_size;
        if (sol[d] < lo) sol[d] = lo;
        if (sol[d] > hi) sol[d] = hi;
    }
    return (tvdb_vec3f){(float)sol[0], (float)sol[1], (float)sol[2]};
}

/* Local MC edge id of the crossed cube edge in each incident cell, indexed by
 * the primal edge's axis and the cross-step t in DUAL_CROSS_STEP. Derived from
 * DUAL_CORNER/DUAL_EDGE (corner index c = position in DUAL_CORNER, not a
 * coordinate bit pattern). Kept as a table so emission cannot mis-map an
 * incident cell back to its own local cube edge. */
static const int DUAL_STEP_LOCAL_EDGE[3][4] = {
    {0, 2, 6, 4},   /* axis x: cross axes (y,z) -> edges 0,2,6,4 */
    {3, 7, 5, 1},   /* axis y: cross axes (z,x) -> edges 3,7,5,1 */
    {8, 9, 10, 11}, /* axis z: cross axes (x,y) -> edges 8,9,10,11 */
};

/* 8-bit case id of a cell: bit c set when corner c is below isovalue. This is
 * the Bourke corner order shipped in MC_TRI_TABLE. Corners are already known
 * finite by the counting pass. */
static unsigned dual_case_id(const tvdb_dense_grid *g, int x, int y, int z, float iso) {
    unsigned k = 0;
    for (int c = 0; c < 8; ++c) {
        int cx = x + DUAL_CORNER[c][0], cy = y + DUAL_CORNER[c][1],
            cz = z + DUAL_CORNER[c][2];
        if (g->data[dual_voxel_index(g, cx, cy, cz)] < iso)
            k |= 1u << c;
    }
    return k;
}

/* Hash key for a (cell, patch) vertex; +1 so 0 stays the empty-slot sentinel.
 * cell < 2048^3 (< 2^34) and patch < 4 (2 bits), so the 64-bit key cannot
 * overflow. */
static uint64_t dual_one_key(size_t cell, unsigned patch) {
    return (((uint64_t)cell << 2) | (uint64_t)patch) + 1;
}

/* ---- per-plane counting for DMC-1 (parallel, order-independent) ---------- */

typedef struct {
    const tvdb_dense_grid *g;
    float iso;
    dual_count *counts;
} dual_count_job_one;

static void dual_count_plane_one(size_t begin, size_t end, void *user) {
    dual_count_job_one *job = user;
    const tvdb_dense_grid *g = job->g;
    for (size_t z = begin; z < end; ++z) {
        dual_count c = {0, 0, 0};
        /* Vertices: one per (crossed cell, MC patch). */
        for (int y = 0; y < g->ny - 1; ++y)
            for (int x = 0; x < g->nx - 1; ++x) {
                int bad = 0;
                int cross = dual_cross_mask(g, x, y, (int)z, job->iso, &bad);
                if (bad)
                    c.bad = 1;
                if (!cross)
                    continue;
                tvdb_dual_patch_info info;
                if (!tvdb_dual_patch_compute(dual_case_id(g, x, y, (int)z, job->iso), &info))
                    continue; /* unreachable for the machine-checked shipped table */
                c.vertices += info.patch_count;
            }
        /* Quads: exactly the DMC-0 edge enumeration (one per crossed primal
         * edge with four incident cells). */
        if (z >= 1 && z <= (size_t)g->nz - 2) {
            for (int y = 1; y <= g->ny - 2; ++y)
                for (int x = 0; x <= g->nx - 2; ++x)
                    if (dual_edge_cross(g, x, y, (int)z, 0, job->iso))
                        ++c.quads;
            for (int x = 1; x <= g->nx - 2; ++x)
                for (int y = 0; y <= g->ny - 2; ++y)
                    if (dual_edge_cross(g, x, y, (int)z, 1, job->iso))
                        ++c.quads;
        }
        if (z <= (size_t)g->nz - 2)
            for (int y = 1; y <= g->ny - 2; ++y)
                for (int x = 1; x <= g->nx - 2; ++x)
                    if (dual_edge_cross(g, x, y, (int)z, 2, job->iso))
                        ++c.quads;
        job->counts[z] = c;
    }
}

/* ---- deterministic serial emission for DMC-1 ---------------------------- */

static void dual_emit_one(const tvdb_dense_grid *g, float iso, size_t base_v, size_t base_q,
                          dual_hash_entry *table, size_t mask, tvdb_quad_mesh *out) {
    size_t vi = 0, qi = 0;
    /* Pass 1: one QEF vertex per (cell, patch), in raster order. */
    for (int z = 0; z < g->nz - 1; ++z)
        for (int y = 0; y < g->ny - 1; ++y)
            for (int x = 0; x < g->nx - 1; ++x) {
                unsigned case_id = dual_case_id(g, x, y, z, iso);
                tvdb_dual_patch_info info;
                if (!tvdb_dual_patch_compute(case_id, &info))
                    continue; /* unreachable for the shipped table */
                for (unsigned p = 0; p < info.patch_count; ++p) {
                    tvdb_vec3f v = dual_qef_vertex(g, iso, x, y, z, &info, p);
                    out->vertices[base_v + vi] = v;
                    size_t cell = (size_t)(z * (g->ny - 1) + y) * (g->nx - 1) + (size_t)x;
                    *dual_hash_slot(table, mask, dual_one_key(cell, p)) = (uint32_t)vi;
                    ++vi;
                }
            }

    /* Pass 2: one quad per crossed primal edge with four incident cells, using
     * the same edge enumeration and winding rule as DMC-0. */
    for (int axis = 0; axis < 3; ++axis) {
        int lim[3] = {g->nx - 1, g->ny - 1, g->nz - 1};
        int lo[3] = {0, 0, 0}, hi[3] = {lim[0], lim[1], lim[2]};
        for (int d = 0; d < 3; ++d)
            if (d != axis) {
                lo[d] = 1;
                hi[d] = lim[d] - 1; /* dim-2 */
            }
        hi[axis] = lim[axis] - 1;
        for (int z = lo[2]; z <= hi[2]; ++z)
            for (int y = lo[1]; y <= hi[1]; ++y)
                for (int x = lo[0]; x <= hi[0]; ++x) {
                    int p[3] = {x, y, z};
                    if (!dual_edge_cross(g, x, y, z, axis, iso))
                        continue;
                    uint32_t quad[4];
                    for (int t = 0; t < 4; ++t) {
                        int cell[3];
                        dual_cell_of_edge(p, axis, DUAL_CROSS_STEP[t][0], DUAL_CROSS_STEP[t][1],
                                          cell);
                        size_t ckey = (size_t)(cell[2] * (g->ny - 1) + cell[1]) * (g->nx - 1) +
                                      (size_t)cell[0];
                        unsigned case_id = dual_case_id(g, cell[0], cell[1], cell[2], iso);
                        tvdb_dual_patch_info info;
                        int owner = 0; /* fallback patch is always in range */
                        if (tvdb_dual_patch_compute(case_id, &info) &&
                            info.edge_patch_count[DUAL_STEP_LOCAL_EDGE[axis][t]] == 1)
                            owner = info.edge_patch[DUAL_STEP_LOCAL_EDGE[axis][t]][0];
                        uint32_t local = *dual_hash_slot(table, mask, dual_one_key(ckey, (unsigned)owner));
                        /* Unreachable for an interior crossed edge; clamp so a
                         * degenerate lookup can never emit an invalid index. */
                        if (local == UINT32_MAX)
                            local = 0;
                        quad[t] = (uint32_t)base_v + local;
                    }
                    int q[3] = {x, y, z};
                    q[axis] += 1;
                    if (g->data[dual_voxel_index(g, q[0], q[1], q[2])] <
                        g->data[dual_voxel_index(g, x, y, z)]) {
                        uint32_t tmp = quad[1];
                        quad[1] = quad[3];
                        quad[3] = tmp;
                    }
                    out->quads[base_q + qi++] = (tvdb_quad){quad[0], quad[1], quad[2], quad[3]};
                }
    }
    (void)vi;
    (void)qi;
}

tvdb_status_t tvdb_sdf_to_mesh_dual_one_ex(const tvdb_dense_grid *g, float iso,
                                            tvdb_thread_pool_t *pool, tvdb_quad_mesh *out,
                                            tvdb_arena_allocator_t *arena, tvdb_error_t *err) {
    size_t grid_bytes;
    if (!out || !isfinite(iso) || !dual_grid_frame(g, &grid_bytes) || g->nx < 2 || g->ny < 2 ||
        g->nz < 2 || out->vertex_count > out->vertex_capacity ||
        out->quad_count > out->quad_capacity || out->vertex_count > UINT32_MAX ||
        (out->vertex_capacity && !out->vertices) || (out->quad_capacity && !out->quads))
        return dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                          "invalid dual marching cubes one grid or output");

    tvdb_thread_pool_t *owned = NULL;
    dual_count *counts = NULL;
    dual_hash_entry *table = NULL;
    tvdb_quad_mesh result = *out;
    tvdb_status_t st = TVDB_OK;
    size_t mark = arena ? arena->current_offset : 0, count_bytes;

    if (!tvdb_size_mul((size_t)g->nz, sizeof(dual_count), &count_bytes))
        return dual_error(err, TVDB_ERROR_INVALID_ARGUMENT, "dual marching cubes one count overflow");
    counts = malloc(count_bytes);
    if (!counts)
        goto oom;
    memset(counts, 0, count_bytes);
    if (!pool) {
        st = dual_pool(grid_bytes / sizeof(float), (size_t)g->nz - 1, &owned, err);
        if (st != TVDB_OK)
            goto done;
        pool = owned;
    }
    dual_count_job_one job = {g, iso, counts};
    st = tvdb_thread_pool_for(pool, 0, (size_t)g->nz - 1, 1, dual_count_plane_one, &job, err);
    if (st != TVDB_OK)
        goto done;

    size_t nv = 0, nq = 0;
    for (int z = 0; z < g->nz; ++z) {
        if (counts[z].bad) {
            st = dual_error(err, TVDB_ERROR_INVALID_DATA, "nonfinite dual marching cubes one sample");
            goto done;
        }
        if (counts[z].vertices > SIZE_MAX - nv || counts[z].quads > SIZE_MAX - nq)
            goto overflow;
        nv += counts[z].vertices;
        nq += counts[z].quads;
    }
    if (nv > UINT32_MAX - out->vertex_count || nq > SIZE_MAX - out->quad_count)
        goto overflow;
    dual_region input = {g->data, grid_bytes};
    if (!nv && !nq) {
        st = dual_commit(out, out->vertex_count, out->quad_count, &input, 1, arena, mark,
                         &result, err);
        goto done;
    }
    size_t total_v = out->vertex_count + nv, total_q = out->quad_count + nq;
    st = dual_commit(out, total_v, total_q, &input, 1, arena, mark, &result, err);
    if (st != TVDB_OK)
        goto done;

    size_t capacity = 0;
    if (!tvdb_hash_capacity(nv, 2, &capacity))
        goto overflow;
    table = calloc(capacity, sizeof(dual_hash_entry));
    if (!table)
        goto oom;
    dual_emit_one(g, iso, out->vertex_count, out->quad_count, table, capacity - 1, &result);
    result.vertex_count = total_v;
    result.quad_count = total_q;
    if (!arena) {
        if (result.vertices != out->vertices)
            free(out->vertices);
        if (result.quads != out->quads)
            free(out->quads);
    }
    *out = result;
    goto done;
overflow:
    st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                    "dual marching cubes one size exceeds index or allocation limits");
    goto done;
oom:
    st = dual_error(err, TVDB_ERROR_OUT_OF_MEMORY, "dual marching cubes one allocation failed");
done:
    if (st != TVDB_OK) {
        if (arena)
            arena->current_offset = mark;
        else {
            if (result.vertices != out->vertices)
                free(result.vertices);
            if (result.quads != out->quads)
                free(result.quads);
        }
    }
    free(counts);
    free(table);
    tvdb_thread_pool_destroy(owned);
    return st;
}

bool tvdb_sdf_to_mesh_dual_one(const tvdb_dense_grid *g, float iso, tvdb_quad_mesh *out,
                               tvdb_arena_allocator_t *arena) {
    return tvdb_sdf_to_mesh_dual_one_ex(g, iso, NULL, out, arena, NULL) == TVDB_OK;
}

/* ---- dense DMC-1 with a shell-pinned boundary -----------------------------
 * Materialise one extra voxel of outside samples on every face, shift the
 * origin by -h so the original voxel centres keep their world positions, and
 * reuse the proven dense DMC-1 emitter unchanged. The shell makes every
 * sign-changing edge on the original boundary have four incident cells. */

tvdb_status_t tvdb_sdf_to_mesh_dual_one_padded_ex(const tvdb_dense_grid *g, float iso,
                                                   tvdb_thread_pool_t *pool, tvdb_quad_mesh *out,
                                                   tvdb_arena_allocator_t *arena, tvdb_error_t *err) {
    size_t grid_bytes, vbytes, qbytes;
    if (!out || !isfinite(iso) || !dual_grid_frame(g, &grid_bytes) || g->nx < 2 || g->ny < 2 ||
        g->nz < 2 || g->nx > 2046 || g->ny > 2046 || g->nz > 2046 ||
        out->vertex_count > out->vertex_capacity || out->quad_count > out->quad_capacity ||
        out->vertex_count > UINT32_MAX || (out->vertex_capacity && !out->vertices) ||
        (out->quad_capacity && !out->quads) ||
        !tvdb_size_mul(out->vertex_capacity, sizeof(tvdb_vec3f), &vbytes) ||
        !tvdb_size_mul(out->quad_capacity, sizeof(tvdb_quad), &qbytes))
        return dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                          "invalid padded dual marching cubes grid or output");
    if (tvdb_buffers_overlap(g->data, grid_bytes, out->vertices, vbytes) ||
        tvdb_buffers_overlap(g->data, grid_bytes, out->quads, qbytes) ||
        tvdb_buffers_overlap(out->vertices, vbytes, out->quads, qbytes))
        return dual_error(err, TVDB_ERROR_INVALID_ARGUMENT, "padded dual marching cubes storage overlaps");

    int px = g->nx + 2, py = g->ny + 2, pz = g->nz + 2;
    size_t bytes;
    if (!tvdb_grid_bytes(px, py, pz, sizeof(float), &bytes))
        return dual_error(err, TVDB_ERROR_INVALID_ARGUMENT, "padded grid size overflow");
    float *data = malloc(bytes);
    if (!data)
        return dual_error(err, TVDB_ERROR_OUT_OF_MEMORY, "padded dual marching cubes allocation failed");

    float outside = isfinite(iso + 1.0f) ? iso + 1.0f : FLT_MAX;
    for (int z = 0; z < pz; ++z)
        for (int y = 0; y < py; ++y)
            for (int x = 0; x < px; ++x) {
                size_t at = (size_t)x + (size_t)y * (size_t)px + (size_t)z * (size_t)px * (size_t)py;
                bool shell = x == 0 || x == px - 1 || y == 0 || y == py - 1 || z == 0 || z == pz - 1;
                data[at] = shell ? outside
                                 : g->data[dual_voxel_index(g, x - 1, y - 1, z - 1)];
            }

    tvdb_dense_grid padded = {px, py, pz,
                              g->ox - g->voxel_size, g->oy - g->voxel_size,
                              g->oz - g->voxel_size, g->voxel_size, data};
    tvdb_status_t st = tvdb_sdf_to_mesh_dual_one_ex(&padded, iso, pool, out, arena, err);
    free(data);
    return st;
}

bool tvdb_sdf_to_mesh_dual_one_padded(const tvdb_dense_grid *g, float iso,
                                      tvdb_quad_mesh *out, tvdb_arena_allocator_t *arena) {
    return tvdb_sdf_to_mesh_dual_one_padded_ex(g, iso, NULL, out, arena, NULL) == TVDB_OK;
}

/* ---- sparse tree traversal (DMC-0 / naive surface nets) ------------------
 *
 * The tree is walked over the active index box (plus a one-voxel margin) with
 * a cached accessor; every crossed cell is kept with its eight stored corner
 * values. Emission then reuses the dense DMC-0 tables and quad rule, with the
 * grid's complete affine transform placing vertices in world space. Only the
 * surface list is O(surface); no dense nx*ny*nz array is built.
 */

typedef struct {
    int32_t c[3];              /* cell lower corner, index coordinates */
    float corners[8];          /* values in DUAL_CORNER order */
    uint16_t mask;             /* 12-bit sign-change mask */
} dual_tree_cell;

typedef struct {
    int32_t c[3];
    uint32_t value;            /* local vertex index + 1; 0 means empty */
} dual_tree_slot;

static uint64_t dual_tree_hash(const int32_t c[3]) {
    uint64_t h = (uint32_t)c[0] * UINT64_C(73856093) ^
                 (uint32_t)c[1] * UINT64_C(19349663) ^
                 (uint32_t)c[2] * UINT64_C(83492791);
    h ^= h >> 33;
    h *= UINT64_C(0xff51afd7ed558ccd);
    return h ^ (h >> 33);
}

static uint32_t *dual_tree_find(dual_tree_slot *table, size_t mask, const int32_t c[3]) {
    size_t at = (size_t)dual_tree_hash(c) & mask;
    while (table[at].value) {
        if (table[at].c[0] == c[0] && table[at].c[1] == c[1] && table[at].c[2] == c[2])
            return &table[at].value;
        at = (at + 1) & mask;
    }
    return NULL;
}

static uint32_t *dual_tree_insert(dual_tree_slot *table, size_t mask, const int32_t c[3]) {
    size_t at = (size_t)dual_tree_hash(c) & mask;
    while (table[at].value) {
        if (table[at].c[0] == c[0] && table[at].c[1] == c[1] && table[at].c[2] == c[2])
            return &table[at].value;
        at = (at + 1) & mask;
    }
    memcpy(table[at].c, c, sizeof(table[at].c));
    return &table[at].value;
}

static tvdb_status_t dual_tree_collect(tvdb_tree_accessor *acc, float iso,
                                       const int64_t lo[3], const int64_t hi[3],
                                       size_t limit, size_t scan_limit,
                                       dual_tree_cell **out, size_t *count, tvdb_error_t *err) {
    dual_tree_cell *cells = NULL;
    size_t n = 0, cap = 0, scans = 0;
    tvdb_status_t st = TVDB_OK;
    for (int64_t z = lo[2]; z <= hi[2]; ++z)
        for (int64_t y = lo[1]; y <= hi[1]; ++y)
            for (int64_t x = lo[0]; x <= hi[0]; ++x) {
                if (++scans > scan_limit) {
                    st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                                    "sparse dual marching cubes scan budget exceeded");
                    goto done;
                }
                int64_t base[3] = {x, y, z};
                float corners[8];
                int mask = 0, bad = 0;
                for (int c = 0; c < 8; ++c) {
                    int32_t q[3];
                    for (int d = 0; d < 3; ++d) {
                        int64_t v = base[d] + DUAL_CORNER[c][d];
                        if (v < INT32_MIN || v > INT32_MAX) {
                            bad = 1;
                            break;
                        }
                        q[d] = (int32_t)v;
                    }
                    if (bad)
                        break;
                    corners[c] = tvdb_tree_accessor_get(acc, q, NULL);
                    if (!isfinite(corners[c])) {
                        bad = 1;
                        break;
                    }
                }
                if (bad) {
                    st = dual_error(err, TVDB_ERROR_INVALID_DATA,
                                    "nonfinite sparse dual marching cubes sample");
                    goto done;
                }
                for (int e = 0; e < 12; ++e)
                    if ((corners[DUAL_EDGE[e][0]] < iso) != (corners[DUAL_EDGE[e][1]] < iso))
                        mask |= 1 << e;
                if (!mask)
                    continue;
                if (n == cap) {
                    if (n >= limit) {
                        st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                                        "sparse dual marching cubes cell budget exceeded");
                        goto done;
                    }
                    size_t next = cap ? cap * 2 : 64, bytes;
                    if (next > limit)
                        next = limit;
                    if (next <= cap || !tvdb_size_mul(next, sizeof(dual_tree_cell), &bytes)) {
                        st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                                        "sparse dual marching cubes cell overflow");
                        goto done;
                    }
                    dual_tree_cell *p = realloc(cells, bytes);
                    if (!p) {
                        st = dual_error(err, TVDB_ERROR_OUT_OF_MEMORY,
                                        "sparse dual marching cubes allocation failed");
                        goto done;
                    }
                    cells = p;
                    cap = next;
                }
                dual_tree_cell *cell = &cells[n++];
                for (int d = 0; d < 3; ++d)
                    cell->c[d] = (int32_t)base[d];
                memcpy(cell->corners, corners, sizeof(corners));
                cell->mask = (uint16_t)mask;
            }
    *out = cells;
    *count = n;
    cells = NULL;
done:
    free(cells);
    return st;
}

static int dual_tree_world(double m[4][4], const double q[3], float w[3]) {
    for (int d = 0; d < 3; ++d) {
        double v = m[d][0] * q[0] + m[d][1] * q[1] + m[d][2] * q[2] + m[d][3];
        if (!isfinite(v) || fabs(v) > FLT_MAX)
            return 0;
        w[d] = (float)v;
    }
    return 1;
}

/* Pass 1: register every crossed cell in the hash (cell coord -> local vertex
 * index) and, when `vertices` is non-NULL, write its centroid vertex. */
static void dual_tree_index(const dual_tree_cell *cells, size_t ncells,
                            dual_tree_slot *table, size_t mask) {
    for (size_t i = 0; i < ncells; ++i)
        *dual_tree_insert(table, mask, cells[i].c) = (uint32_t)i + 1;
}

static tvdb_status_t dual_tree_vertices(double matrix[4][4], float iso,
                                        const dual_tree_cell *cells, size_t ncells,
                                        size_t base_v, tvdb_vec3f *vertices, tvdb_error_t *err) {
    for (size_t i = 0; i < ncells; ++i) {
        const dual_tree_cell *cell = &cells[i];
        double sum[3] = {0, 0, 0};
        int n = 0;
        for (int e = 0; e < 12; ++e)
            if (cell->mask & (1u << e)) {
                int a = DUAL_EDGE[e][0], b = DUAL_EDGE[e][1];
                double va = cell->corners[a], vb = cell->corners[b];
                double t = ((double)iso - va) / (vb - va);
                if (t < 0)
                    t = 0;
                if (t > 1)
                    t = 1;
                double q[3];
                for (int d = 0; d < 3; ++d)
                    q[d] = (double)cell->c[d] + DUAL_CORNER[a][d] +
                           t * (DUAL_CORNER[b][d] - DUAL_CORNER[a][d]);
                float w[3];
                if (!dual_tree_world(matrix, q, w))
                    return dual_error(err, TVDB_ERROR_INVALID_DATA,
                                      "sparse dual marching cubes world coordinate overflow");
                sum[0] += w[0];
                sum[1] += w[1];
                sum[2] += w[2];
                ++n;
            }
        if (vertices)
            vertices[base_v + i] =
                (tvdb_vec3f){(float)(sum[0] / n), (float)(sum[1] / n), (float)(sum[2] / n)};
    }
    return TVDB_OK;
}

/* Pass 2: one quad per sign-changing primal edge with four incident crossed
 * cells. Only the lowest cell around an edge (both cross-axis offsets zero)
 * emits, so each edge yields exactly one quad regardless of traversal order.
 * `quads` may be NULL to count the quads first. */
static size_t dual_tree_quads(const dual_tree_cell *cells, size_t ncells,
                              dual_tree_slot *table, size_t mask, size_t base_v,
                              tvdb_quad *quads) {
    size_t qi = 0;
    for (size_t i = 0; i < ncells; ++i) {
        const dual_tree_cell *cell = &cells[i];
        for (int e = 0; e < 12; ++e)
            if (cell->mask & (1u << e)) {
                int a = DUAL_EDGE[e][0], b = DUAL_EDGE[e][1], axis = 0;
                for (int d = 0; d < 3; ++d)
                    if (DUAL_CORNER[a][d] != DUAL_CORNER[b][d])
                        axis = d;
                int64_t p[3];
                for (int d = 0; d < 3; ++d)
                    p[d] = (int64_t)cell->c[d] +
                           (DUAL_CORNER[a][d] < DUAL_CORNER[b][d] ? DUAL_CORNER[a][d]
                                                                  : DUAL_CORNER[b][d]);
                int c0 = DUAL_CROSS_AXIS[axis][0], c1 = DUAL_CROSS_AXIS[axis][1];
                /* Canonical emitting cell is cross step {0,0} (index 2). */
                int64_t canon[3] = {p[0], p[1], p[2]};
                canon[c0] = p[c0] - 1;
                canon[c1] = p[c1] - 1;
                if (canon[0] != cell->c[0] || canon[1] != cell->c[1] ||
                    canon[2] != cell->c[2])
                    continue;
                uint32_t quad[4];
                int ok = 1;
                for (int t = 0; t < 4; ++t) {
                    int64_t q[3] = {p[0], p[1], p[2]};
                    q[c0] = p[c0] - (DUAL_CROSS_STEP[t][0] ? 0 : 1);
                    q[c1] = p[c1] - (DUAL_CROSS_STEP[t][1] ? 0 : 1);
                    int32_t key[3];
                    for (int d = 0; d < 3; ++d) {
                        if (q[d] < INT32_MIN || q[d] > INT32_MAX) {
                            ok = 0;
                            break;
                        }
                        key[d] = (int32_t)q[d];
                    }
                    if (!ok)
                        break;
                    uint32_t *slot = dual_tree_find(table, mask, key);
                    if (!slot || !*slot) {
                        ok = 0;
                        break;
                    }
                    quad[t] = (uint32_t)base_v + *slot - 1;
                }
                if (!ok)
                    continue; /* edge on the scanned boundary: fewer than 4 cells */
                int lo = DUAL_CORNER[a][axis] == 0 ? a : b;
                int hi = DUAL_CORNER[a][axis] == 0 ? b : a;
                if (cell->corners[hi] < cell->corners[lo]) {
                    uint32_t tmp = quad[1];
                    quad[1] = quad[3];
                    quad[3] = tmp;
                }
                if (quads)
                    quads[qi++] = (tvdb_quad){quad[0], quad[1], quad[2], quad[3]};
                else
                    ++qi;
            }
    }
    return qi;
}

tvdb_status_t tvdb_grid_volume_to_mesh_dual_ex(const tvdb_grid_t *grid, float iso,
                                               size_t max_cells, tvdb_thread_pool_t *pool,
                                               tvdb_quad_mesh *out,
                                               tvdb_arena_allocator_t *arena, tvdb_error_t *err) {
    (void)pool; /* emission is serial in raster order: identical for any worker count */
    if (!out || !isfinite(iso) || out->vertex_count > out->vertex_capacity ||
        out->quad_count > out->quad_capacity || out->vertex_count > UINT32_MAX ||
        (out->vertex_capacity && !out->vertices) || (out->quad_capacity && !out->quads))
        return dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                          "invalid sparse dual marching cubes output");

    tvdb_tree_diagnostics_t d;
    tvdb_status_t st = tvdb_grid_diagnose(grid, TVDB_TREE_DIAG_GENERIC, 0, 0, &d, err);
    if (st != TVDB_OK)
        return st;
    if (!d.valid)
        return dual_error(err, TVDB_ERROR_INVALID_DATA, "invalid sparse dual marching cubes grid");

    tvdb_tree_index index = {0};
    st = tvdb_tree_index_create(grid, 1, &index, err);
    if (st != TVDB_OK)
        return st;

    dual_tree_cell *cells = NULL;
    dual_tree_slot *table = NULL;
    dual_region *inputs = NULL;
    size_t ncells = 0, ninputs = 0, nq = 0, capacity = 0;
    size_t mark = arena ? arena->current_offset : 0;
    tvdb_quad_mesh result = *out;

    if (!d.has_active_bbox) {
        st = TVDB_OK;
        goto done;
    }

    double matrix[4][4];
    if (!tvdb_tree_matrix(&grid->transform, matrix)) {
        st = dual_error(err, TVDB_ERROR_UNSUPPORTED_TRANSFORM,
                        "invalid sparse dual marching cubes transform");
        goto done;
    }

    int64_t lo[3], hi[3];
    uint64_t span = 1;
    for (int a = 0; a < 3; ++a) {
        if (d.active_min[a] < (int64_t)INT32_MIN + 2 || d.active_max[a] > INT32_MAX) {
            st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                            "sparse dual marching cubes box overflow");
            goto done;
        }
        int64_t l = d.active_min[a] - 2; /* one-cell margin each side */
        int64_t h = d.active_max[a];     /* active_max is exclusive */
        if (l < INT32_MIN || h + 1 > INT32_MAX || h < l) {
            st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                            "sparse dual marching cubes box overflow");
            goto done;
        }
        lo[a] = l;
        hi[a] = h;
        uint64_t n = (uint64_t)(h - l + 1);
        if (n > UINT64_MAX / span) {
            st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                            "sparse dual marching cubes scan overflow");
            goto done;
        }
        span *= n;
    }
    size_t limit = max_cells ? max_cells : 1000000;
    size_t scan_limit;
    if (limit > (SIZE_MAX - 4096) / 32) {
        st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                        "sparse dual marching cubes budget overflow");
        goto done;
    }
    scan_limit = limit * 32 + 4096;
    if (span > (uint64_t)scan_limit) {
        st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                        "sparse dual marching cubes scan budget exceeded");
        goto done;
    }

    /* Alias check every stored node buffer, as the classic sparse mesher does. */
    if (grid->tree.num_nodes > 1) {
        inputs = malloc((grid->tree.num_nodes - 1) * sizeof(dual_region));
        if (!inputs) {
            st = dual_error(err, TVDB_ERROR_OUT_OF_MEMORY,
                            "sparse dual marching cubes allocation failed");
            goto done;
        }
        for (size_t i = 1; i < grid->tree.num_nodes; ++i) {
            const tvdb_tree_node_t *n = grid->tree.nodes + i;
            inputs[ninputs].ptr = n->type == TVDB_NODE_LEAF ? (const void *)n->u.leaf.data
                                                            : (const void *)n->u.internal.values;
            inputs[ninputs].bytes = n->type == TVDB_NODE_LEAF ? n->u.leaf.data_size
                                                             : n->u.internal.values_size;
            ++ninputs;
        }
    }

    tvdb_tree_accessor acc;
    tvdb_tree_accessor_init(&acc, &index);
    st = dual_tree_collect(&acc, iso, lo, hi, limit, scan_limit, &cells, &ncells, err);
    if (st != TVDB_OK)
        goto done;
    if (ncells > UINT32_MAX - out->vertex_count) {
        st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                        "sparse dual marching cubes index overflow");
        goto done;
    }
    if (!ncells) {
        /* No surface: preserve out, but still validate storage/aliasing. */
        st = dual_commit(out, out->vertex_count, out->quad_count, inputs, ninputs, arena,
                         mark, &result, err);
        goto done;
    }

    if (!tvdb_hash_capacity(ncells, 2, &capacity)) {
        st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                        "sparse dual marching cubes hash overflow");
        goto done;
    }
    table = calloc(capacity, sizeof(dual_tree_slot));
    if (!table) {
        st = dual_error(err, TVDB_ERROR_OUT_OF_MEMORY,
                        "sparse dual marching cubes allocation failed");
        goto done;
    }
    dual_tree_index(cells, ncells, table, capacity - 1);
    nq = dual_tree_quads(cells, ncells, table, capacity - 1, out->vertex_count, NULL);
    if (nq > SIZE_MAX - out->quad_count) {
        st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                        "sparse dual marching cubes size overflow");
        goto done;
    }
    size_t total_v = out->vertex_count + ncells, total_q = out->quad_count + nq;
    st = dual_commit(out, total_v, total_q, inputs, ninputs, arena, mark, &result, err);
    if (st != TVDB_OK)
        goto done;

    st = dual_tree_vertices(matrix, iso, cells, ncells, out->vertex_count, result.vertices, err);
    if (st != TVDB_OK)
        goto done;
    size_t emitted = dual_tree_quads(cells, ncells, table, capacity - 1, out->vertex_count,
                                     result.quads + out->quad_count);
    assert(emitted == nq);
    (void)emitted;
    result.vertex_count = total_v;
    result.quad_count = total_q;
    if (!arena) {
        if (result.vertices != out->vertices)
            free(out->vertices);
        if (result.quads != out->quads)
            free(out->quads);
    }
    *out = result;
    goto done;
done:
    if (st != TVDB_OK) {
        if (arena)
            arena->current_offset = mark;
        else {
            if (result.vertices != out->vertices)
                free(result.vertices);
            if (result.quads != out->quads)
                free(result.quads);
        }
    }
    free(cells);
    free(table);
    free(inputs);
    tvdb_tree_index_destroy(&index);
    return st;
}

bool tvdb_grid_volume_to_mesh_dual(const tvdb_grid_t *grid, float iso, size_t max_cells,
                                   tvdb_quad_mesh *out, tvdb_arena_allocator_t *arena) {
    return tvdb_grid_volume_to_mesh_dual_ex(grid, iso, max_cells, NULL, out, arena, NULL) == TVDB_OK;
}

/* ---- sparse-tree DMC-1 (shell-pinned, index-space QEF) --------------------
 *
 * Pure addition: the DMC-0 tree section above is untouched. The tree is
 * scanned over the DMC-0 cell box extended by one cell on every side, with
 * corner samples outside the original DMC-0 sample domain pinned to the
 * outside phase, so a crossing surface that reaches the domain boundary is
 * closed by the shell. One vertex is placed per (cell, MC patch) by an
 * index-space QEF solve; one quad is emitted per crossed primal edge with four
 * incident crossed cells, using the same canonical-emitter and winding rule
 * as tree DMC-0. See tinyvdb_mesh_dual.h for the full contract and scope.
 */

typedef struct {
    int32_t c[3];
    uint32_t cell;       /* index into the collected cells array */
    uint32_t first;      /* absolute first vertex index of this cell */
    uint8_t patch_count; /* number of MC patches (vertices) in this cell */
    uint8_t occupied;    /* 1 once the slot is filled */
} dual_tree_slot_one;

/* Open-addressing lookup; when `insert` is 0 a missing slot yields NULL. */
static dual_tree_slot_one *dual_tree_slot_one_lookup(dual_tree_slot_one *table, size_t mask,
                                                     const int32_t c[3], int insert) {
    size_t at = (size_t)dual_tree_hash(c) & mask;
    while (table[at].occupied) {
        if (table[at].c[0] == c[0] && table[at].c[1] == c[1] && table[at].c[2] == c[2])
            return &table[at];
        at = (at + 1) & mask;
    }
    if (!insert)
        return NULL;
    memcpy(table[at].c, c, sizeof(table[at].c));
    table[at].occupied = 1;
    return &table[at];
}

/* Copy of dual_tree_collect with shell pinning: a corner whose index lies
 * outside [pin_lo, pin_hi] on any axis is set to `outside` without touching
 * the accessor. The scanned cell box is already the extended one. */
static tvdb_status_t dual_tree_collect_one(tvdb_tree_accessor *acc, float iso,
                                           const int64_t lo[3], const int64_t hi[3],
                                           const int64_t pin_lo[3], const int64_t pin_hi[3],
                                           float outside, size_t limit, size_t scan_limit,
                                           dual_tree_cell **out, size_t *count, tvdb_error_t *err) {
    dual_tree_cell *cells = NULL;
    size_t n = 0, cap = 0, scans = 0;
    tvdb_status_t st = TVDB_OK;
    for (int64_t z = lo[2]; z <= hi[2]; ++z)
        for (int64_t y = lo[1]; y <= hi[1]; ++y)
            for (int64_t x = lo[0]; x <= hi[0]; ++x) {
                if (++scans > scan_limit) {
                    st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                                    "sparse dual marching cubes one scan budget exceeded");
                    goto done;
                }
                int64_t base[3] = {x, y, z};
                float corners[8];
                int mask = 0, bad = 0;
                for (int c = 0; c < 8; ++c) {
                    int32_t q[3] = {0, 0, 0};
                    int pinned = 0;
                    for (int d = 0; d < 3; ++d) {
                        int64_t v = base[d] + DUAL_CORNER[c][d];
                        if (v < pin_lo[d] || v > pin_hi[d]) {
                            pinned = 1; /* outside the original DMC-0 sample domain */
                            break;
                        }
                        if (v < INT32_MIN || v > INT32_MAX) {
                            bad = 1;
                            break;
                        }
                        q[d] = (int32_t)v;
                    }
                    if (bad)
                        break;
                    corners[c] = pinned ? outside : tvdb_tree_accessor_get(acc, q, NULL);
                    if (!isfinite(corners[c])) {
                        bad = 1;
                        break;
                    }
                }
                if (bad) {
                    st = dual_error(err, TVDB_ERROR_INVALID_DATA,
                                    "nonfinite sparse dual marching cubes one sample");
                    goto done;
                }
                for (int e = 0; e < 12; ++e)
                    if ((corners[DUAL_EDGE[e][0]] < iso) != (corners[DUAL_EDGE[e][1]] < iso))
                        mask |= 1 << e;
                if (!mask)
                    continue;
                if (n == cap) {
                    if (n >= limit) {
                        st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                                        "sparse dual marching cubes one cell budget exceeded");
                        goto done;
                    }
                    size_t next = cap ? cap * 2 : 64, bytes;
                    if (next > limit)
                        next = limit;
                    if (next <= cap || !tvdb_size_mul(next, sizeof(dual_tree_cell), &bytes)) {
                        st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                                        "sparse dual marching cubes one cell overflow");
                        goto done;
                    }
                    dual_tree_cell *p = realloc(cells, bytes);
                    if (!p) {
                        st = dual_error(err, TVDB_ERROR_OUT_OF_MEMORY,
                                        "sparse dual marching cubes one allocation failed");
                        goto done;
                    }
                    cells = p;
                    cap = next;
                }
                dual_tree_cell *cell = &cells[n++];
                for (int d = 0; d < 3; ++d)
                    cell->c[d] = (int32_t)base[d];
                memcpy(cell->corners, corners, sizeof(corners));
                cell->mask = (uint16_t)mask;
            }
    *out = cells;
    *count = n;
    cells = NULL;
done:
    free(cells);
    return st;
}

/* 8-bit case id of a cell from its already-known corner values (DUAL_CORNER
 * order), fed to tvdb_dual_patch_compute whenever patch info is needed. */
static unsigned dual_tree_case(const float corners[8], float iso) {
    unsigned k = 0;
    for (int c = 0; c < 8; ++c)
        if (corners[c] < iso)
            k |= 1u << c;
    return k;
}

/* Index-space central-difference gradient of a cell: the mean of the four
 * axis-parallel edge differences per axis (unit index step). */
static void dual_tree_gradient(const float corners[8], double g[3]) {
    static const int AXIS_EDGES[3][4] = {{0, 2, 4, 6}, {1, 3, 5, 7}, {8, 9, 10, 11}};
    for (int d = 0; d < 3; ++d) {
        double sum = 0;
        for (int k = 0; k < 4; ++k) {
            int e = AXIS_EDGES[d][k];
            int a = DUAL_EDGE[e][0], b = DUAL_EDGE[e][1];
            int lo_corner = DUAL_CORNER[a][d] < DUAL_CORNER[b][d] ? a : b;
            int hi_corner = DUAL_CORNER[a][d] < DUAL_CORNER[b][d] ? b : a;
            sum += (double)corners[hi_corner] - (double)corners[lo_corner];
        }
        g[d] = sum * 0.25;
    }
}

/* Place one patch vertex by minimising sum (n.(x-q))^2 in index space. Each
 * owned crossed edge contributes its interpolated index-space crossing q and
 * the per-cell gradient normal; the 3x3 normal equations use dual_solve3 with
 * the crossing centroid as the singular fallback. The result is clamped to
 * the cell's index box [c, c+1] and mapped to world with dual_tree_world. */
static tvdb_status_t dual_tree_qef_vertex(const int32_t c[3], const float corners[8], float iso,
                                          const tvdb_dual_patch_info *info, unsigned p,
                                          double matrix[4][4], tvdb_vec3f *out, tvdb_error_t *err) {
    double g[3];
    dual_tree_gradient(corners, g);
    double A[3][3] = {{0, 0, 0}, {0, 0, 0}, {0, 0, 0}};
    double b[3] = {0, 0, 0};
    double sum[3] = {0, 0, 0};
    int nplanes = 0;
    for (int e = 0; e < 12; ++e) {
        if (info->edge_patch_count[e] != 1 || info->edge_patch[e][0] != (uint8_t)p)
            continue;
        int a = DUAL_EDGE[e][0], bb = DUAL_EDGE[e][1];
        double va = corners[a], vb = corners[bb];
        if (va == vb)
            continue;
        double t = ((double)iso - va) / (vb - va);
        if (t < 0)
            t = 0;
        if (t > 1)
            t = 1;
        double q[3];
        for (int d = 0; d < 3; ++d)
            q[d] = (double)c[d] + DUAL_CORNER[a][d] +
                   t * (DUAL_CORNER[bb][d] - DUAL_CORNER[a][d]);
        double len = sqrt(g[0] * g[0] + g[1] * g[1] + g[2] * g[2]);
        if (!isfinite(len) || len < 1e-12)
            continue; /* degenerate gradient: omit this plane */
        double nv[3] = {g[0] / len, g[1] / len, g[2] / len};
        double np = nv[0] * q[0] + nv[1] * q[1] + nv[2] * q[2];
        for (int i = 0; i < 3; ++i) {
            for (int j = 0; j < 3; ++j)
                A[i][j] += nv[i] * nv[j];
            b[i] += np * nv[i];
        }
        for (int d = 0; d < 3; ++d)
            sum[d] += q[d];
        ++nplanes;
    }
    double sol[3];
    if (!nplanes) {
        /* Defensive: a patch owns at least one crossed edge. */
        for (int d = 0; d < 3; ++d)
            sol[d] = (double)c[d] + 0.5;
    } else if (!dual_solve3(A, b, sol)) {
        for (int d = 0; d < 3; ++d)
            sol[d] = sum[d] / nplanes;
    }
    for (int d = 0; d < 3; ++d) {
        double lo = (double)c[d], hi = lo + 1.0;
        if (sol[d] < lo)
            sol[d] = lo;
        if (sol[d] > hi)
            sol[d] = hi;
    }
    float w[3];
    if (!dual_tree_world(matrix, sol, w))
        return dual_error(err, TVDB_ERROR_INVALID_DATA,
                          "sparse dual marching cubes one world coordinate overflow");
    *out = (tvdb_vec3f){w[0], w[1], w[2]};
    return TVDB_OK;
}

/* Pass 1: register one slot per crossed cell (cell index, absolute first
 * vertex index, patch count) and count vertices. When `vertices` is non-NULL
 * also place each patch vertex with the index-space QEF solver. */
static tvdb_status_t dual_tree_vertices_one(const dual_tree_cell *cells, size_t ncells,
                                            double matrix[4][4], float iso, size_t base_v,
                                            dual_tree_slot_one *table, size_t mask, size_t *nv_out,
                                            tvdb_vec3f *vertices, tvdb_error_t *err) {
    size_t nv = 0;
    for (size_t i = 0; i < ncells; ++i) {
        const dual_tree_cell *cell = &cells[i];
        tvdb_dual_patch_info info;
        unsigned patches = 1;
        if (tvdb_dual_patch_compute(dual_tree_case(cell->corners, iso), &info))
            patches = info.patch_count;
        dual_tree_slot_one *slot = dual_tree_slot_one_lookup(table, mask, cell->c, 1);
        slot->cell = (uint32_t)i;
        slot->first = (uint32_t)(base_v + nv);
        slot->patch_count = (uint8_t)patches;
        if (vertices) {
            for (unsigned p = 0; p < patches; ++p) {
                tvdb_vec3f w;
                tvdb_status_t st = dual_tree_qef_vertex(cell->c, cell->corners, iso, &info, p,
                                                        matrix, &w, err);
                if (st != TVDB_OK)
                    return st;
                vertices[slot->first + p] = w;
            }
        }
        nv += patches;
    }
    *nv_out = nv;
    return TVDB_OK;
}

/* Pass 2: one quad per crossed primal edge with four incident crossed cells.
 * Only the canonical cell (cross step {0,0}) emits, exactly as tree DMC-0;
 * each of the four incident cells contributes the vertex of the patch owning
 * its local crossed edge (DUAL_STEP_LOCAL_EDGE). `quads` may be NULL to count. */
static size_t dual_tree_quads_one(const dual_tree_cell *cells, size_t ncells,
                                  dual_tree_slot_one *table, size_t mask, float iso,
                                  tvdb_quad *quads) {
    size_t qi = 0;
    for (size_t i = 0; i < ncells; ++i) {
        const dual_tree_cell *cell = &cells[i];
        for (int e = 0; e < 12; ++e)
            if (cell->mask & (1u << e)) {
                int a = DUAL_EDGE[e][0], b = DUAL_EDGE[e][1], axis = 0;
                for (int d = 0; d < 3; ++d)
                    if (DUAL_CORNER[a][d] != DUAL_CORNER[b][d])
                        axis = d;
                int64_t p[3];
                for (int d = 0; d < 3; ++d)
                    p[d] = (int64_t)cell->c[d] +
                           (DUAL_CORNER[a][d] < DUAL_CORNER[b][d] ? DUAL_CORNER[a][d]
                                                                  : DUAL_CORNER[b][d]);
                int c0 = DUAL_CROSS_AXIS[axis][0], c1 = DUAL_CROSS_AXIS[axis][1];
                /* Canonical emitting cell is cross step {0,0} (index 2). */
                int64_t canon[3] = {p[0], p[1], p[2]};
                canon[c0] = p[c0] - 1;
                canon[c1] = p[c1] - 1;
                if (canon[0] != cell->c[0] || canon[1] != cell->c[1] || canon[2] != cell->c[2])
                    continue;
                uint32_t quad[4];
                int ok = 1;
                for (int t = 0; t < 4; ++t) {
                    int64_t q[3] = {p[0], p[1], p[2]};
                    q[c0] = p[c0] - (DUAL_CROSS_STEP[t][0] ? 0 : 1);
                    q[c1] = p[c1] - (DUAL_CROSS_STEP[t][1] ? 0 : 1);
                    int32_t key[3];
                    for (int d = 0; d < 3; ++d) {
                        if (q[d] < INT32_MIN || q[d] > INT32_MAX) {
                            ok = 0;
                            break;
                        }
                        key[d] = (int32_t)q[d];
                    }
                    if (!ok)
                        break;
                    const dual_tree_slot_one *slot =
                        dual_tree_slot_one_lookup(table, mask, key, 0);
                    if (!slot) {
                        ok = 0; /* edge on the scanned boundary: fewer than 4 cells */
                        break;
                    }
                    const dual_tree_cell *inc = &cells[slot->cell];
                    tvdb_dual_patch_info info;
                    int owner = 0; /* fallback patch is always in range */
                    int local = DUAL_STEP_LOCAL_EDGE[axis][t];
                    if (tvdb_dual_patch_compute(dual_tree_case(inc->corners, iso), &info) &&
                        info.edge_patch_count[local] == 1)
                        owner = info.edge_patch[local][0];
                    quad[t] = slot->first + (uint32_t)owner;
                }
                if (!ok)
                    continue;
                int lo = DUAL_CORNER[a][axis] == 0 ? a : b;
                int hi = DUAL_CORNER[a][axis] == 0 ? b : a;
                if (cell->corners[hi] < cell->corners[lo]) {
                    uint32_t tmp = quad[1];
                    quad[1] = quad[3];
                    quad[3] = tmp;
                }
                if (quads)
                    quads[qi++] = (tvdb_quad){quad[0], quad[1], quad[2], quad[3]};
                else
                    ++qi;
            }
    }
    return qi;
}

tvdb_status_t tvdb_grid_volume_to_mesh_dual_one_ex(const tvdb_grid_t *grid, float iso,
                                                   size_t max_cells, tvdb_thread_pool_t *pool,
                                                   tvdb_quad_mesh *out,
                                                   tvdb_arena_allocator_t *arena, tvdb_error_t *err) {
    (void)pool; /* emission is serial in raster order: identical for any worker count */
    if (!out || !isfinite(iso) || out->vertex_count > out->vertex_capacity ||
        out->quad_count > out->quad_capacity || out->vertex_count > UINT32_MAX ||
        (out->vertex_capacity && !out->vertices) || (out->quad_capacity && !out->quads))
        return dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                          "invalid sparse dual marching cubes one output");

    tvdb_tree_diagnostics_t d;
    tvdb_status_t st = tvdb_grid_diagnose(grid, TVDB_TREE_DIAG_GENERIC, 0, 0, &d, err);
    if (st != TVDB_OK)
        return st;
    if (!d.valid)
        return dual_error(err, TVDB_ERROR_INVALID_DATA,
                          "invalid sparse dual marching cubes one grid");

    tvdb_tree_index index = {0};
    st = tvdb_tree_index_create(grid, 1, &index, err);
    if (st != TVDB_OK)
        return st;

    dual_tree_cell *cells = NULL;
    dual_tree_slot_one *table = NULL;
    dual_region *inputs = NULL;
    size_t ncells = 0, ninputs = 0, nq = 0, nv = 0, capacity = 0;
    size_t mark = arena ? arena->current_offset : 0;
    tvdb_quad_mesh result = *out;

    if (!d.has_active_bbox)
        goto done; /* no surface: preserve out */

    double matrix[4][4];
    if (!tvdb_tree_matrix(&grid->transform, matrix)) {
        st = dual_error(err, TVDB_ERROR_UNSUPPORTED_TRANSFORM,
                        "invalid sparse dual marching cubes one transform");
        goto done;
    }

    int64_t lo[3], hi[3], pin_lo[3], pin_hi[3];
    uint64_t span = 1;
    for (int a = 0; a < 3; ++a) {
        /* DMC-0 uses sample domain [active_min-2, active_max+1]. The extended
         * cell box [active_min-3, active_max+1] must still fit in int32. */
        if (d.active_min[a] <= (int64_t)INT32_MIN + 2 ||
            d.active_max[a] >= (int64_t)INT32_MAX - 1 ||
            d.active_max[a] < d.active_min[a]) {
            st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                            "sparse dual marching cubes one box overflow");
            goto done;
        }
        int64_t l0 = d.active_min[a] - 2; /* DMC-0 sample-domain low */
        int64_t h0 = d.active_max[a];     /* DMC-0 cell high (active_max exclusive) */
        lo[a] = l0 - 1;                   /* shell-pinned cell box, one cell larger */
        hi[a] = h0 + 1;
        pin_lo[a] = l0;                   /* original DMC-0 sample domain [l0, h0+1] */
        pin_hi[a] = h0 + 1;
        uint64_t n = (uint64_t)(hi[a] - lo[a] + 1);
        if (n > UINT64_MAX / span) {
            st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                            "sparse dual marching cubes one scan overflow");
            goto done;
        }
        span *= n;
    }
    size_t limit = max_cells ? max_cells : 1000000;
    size_t scan_limit;
    if (limit > (SIZE_MAX - 4096) / 32) {
        st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                        "sparse dual marching cubes one budget overflow");
        goto done;
    }
    scan_limit = limit * 32 + 4096;
    if (span > (uint64_t)scan_limit) {
        st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                        "sparse dual marching cubes one scan budget exceeded");
        goto done;
    }

    /* Alias check every stored node buffer, as the DMC-0 tree path does. */
    if (grid->tree.num_nodes > 1) {
        inputs = malloc((grid->tree.num_nodes - 1) * sizeof(dual_region));
        if (!inputs) {
            st = dual_error(err, TVDB_ERROR_OUT_OF_MEMORY,
                            "sparse dual marching cubes one allocation failed");
            goto done;
        }
        for (size_t i = 1; i < grid->tree.num_nodes; ++i) {
            const tvdb_tree_node_t *n = grid->tree.nodes + i;
            inputs[ninputs].ptr = n->type == TVDB_NODE_LEAF ? (const void *)n->u.leaf.data
                                                            : (const void *)n->u.internal.values;
            inputs[ninputs].bytes = n->type == TVDB_NODE_LEAF ? n->u.leaf.data_size
                                                             : n->u.internal.values_size;
            ++ninputs;
        }
    }

    tvdb_tree_accessor acc;
    tvdb_tree_accessor_init(&acc, &index);
    float outside = isfinite(iso + 1.0f) ? iso + 1.0f : FLT_MAX;
    st = dual_tree_collect_one(&acc, iso, lo, hi, pin_lo, pin_hi, outside, limit, scan_limit,
                               &cells, &ncells, err);
    if (st != TVDB_OK)
        goto done;
    if (ncells > UINT32_MAX - out->vertex_count) {
        st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                        "sparse dual marching cubes one index overflow");
        goto done;
    }
    if (!ncells) {
        /* No surface: still validate storage/aliasing. */
        st = dual_commit(out, out->vertex_count, out->quad_count, inputs, ninputs, arena, mark,
                         &result, err);
        goto done;
    }

    if (!tvdb_hash_capacity(ncells, 2, &capacity)) {
        st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                        "sparse dual marching cubes one hash overflow");
        goto done;
    }
    table = calloc(capacity, sizeof(dual_tree_slot_one));
    if (!table) {
        st = dual_error(err, TVDB_ERROR_OUT_OF_MEMORY,
                        "sparse dual marching cubes one allocation failed");
        goto done;
    }

    /* Pass 1: fill slots and count vertices (no placement before commit). */
    st = dual_tree_vertices_one(cells, ncells, matrix, iso, out->vertex_count, table, capacity - 1,
                                &nv, NULL, err);
    if (st != TVDB_OK)
        goto done;
    if (nv > UINT32_MAX - out->vertex_count) {
        st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                        "sparse dual marching cubes one index overflow");
        goto done;
    }

    nq = dual_tree_quads_one(cells, ncells, table, capacity - 1, iso, NULL);
    if (nq > SIZE_MAX - out->quad_count) {
        st = dual_error(err, TVDB_ERROR_INVALID_ARGUMENT,
                        "sparse dual marching cubes one size overflow");
        goto done;
    }
    size_t total_v = out->vertex_count + nv, total_q = out->quad_count + nq;
    st = dual_commit(out, total_v, total_q, inputs, ninputs, arena, mark, &result, err);
    if (st != TVDB_OK)
        goto done;

    st = dual_tree_vertices_one(cells, ncells, matrix, iso, out->vertex_count, table, capacity - 1,
                                &nv, result.vertices, err);
    if (st != TVDB_OK)
        goto done;
    size_t emitted = dual_tree_quads_one(cells, ncells, table, capacity - 1, iso,
                                         result.quads + out->quad_count);
    assert(emitted == nq);
    (void)emitted;
    result.vertex_count = total_v;
    result.quad_count = total_q;
    if (!arena) {
        if (result.vertices != out->vertices)
            free(out->vertices);
        if (result.quads != out->quads)
            free(out->quads);
    }
    *out = result;
    goto done;
done:
    if (st != TVDB_OK) {
        if (arena)
            arena->current_offset = mark;
        else {
            if (result.vertices != out->vertices)
                free(result.vertices);
            if (result.quads != out->quads)
                free(result.quads);
        }
    }
    free(cells);
    free(table);
    free(inputs);
    tvdb_tree_index_destroy(&index);
    return st;
}

bool tvdb_grid_volume_to_mesh_dual_one(const tvdb_grid_t *grid, float iso, size_t max_cells,
                                       tvdb_quad_mesh *out, tvdb_arena_allocator_t *arena) {
    return tvdb_grid_volume_to_mesh_dual_one_ex(grid, iso, max_cells, NULL, out, arena, NULL) ==
           TVDB_OK;
}
