/* Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
   SPDX-License-Identifier: Apache-2.0 */

/* Differential harness: SPARSE/TREE marching-cubes TOPOLOGY (C half).
 *
 * Calls the REAL `tvdb_grid_volume_to_mesh` (src/tinyvdb_sparse_tools.c:
 * tool_surface_cells + tool_mesh + tool_adapt) on a deterministic procedural
 * sphere tree built with the same helpers as tests/test_mesh_dual_tree.c, and
 * dumps, as text:
 *
 *   fields <N>
 *   case <id> n <n> iso <f32hex> s0 <f64hex> s1 <f64hex> s2 <f64hex>
 *             t0 <f64hex> t1 <f64hex> t2 <f64hex> flip <0|1>
 *   voxel <id> <x> <y> <z> act <0|1> val <f32hex>      (every lattice sample)
 *   mesh <id> nv <n> nf <n>
 *   vertex <id> <j> <xb> <yb> <zb> <kx> <ky> <kz> <axis>
 *   face <id> <j> <v0> <v1> <v2>
 *
 * The samples are read back with `tvdb_tree_get`, so the dump contains the
 * values the real tool_mesh sees (stored leaves plus background tiles).
 *
 * The welded edge key of each emitted vertex is recovered GEOMETRICALLY from
 * the C's own output position, not from the internal hash map: a marching-
 * cubes crossing point lies on an axis-aligned lattice edge, so after the
 * inverse transform exactly two index coordinates are integers and the third
 * is a fraction in (0,1). The two integers plus floor(fraction) are the edge's
 * lower corner and the fractional axis is the edge axis -- exactly the key
 * the C weld map uses. This keeps the harness independent of src/ internals.
 *
 * The Lean twin (Vdb.McSparseTopologyCheck) recomputes the case masks, used
 * edges, triangles, welded keys and crossing positions from the shipped MC
 * tables (Vdb.McTable) and the weld model (Vdb.McWeld) over the same samples,
 * and compares counts, key-index multisets and positions with a tolerance.
 *
 * No secrets, no generated binaries. Build (see check_mc_sparse_topology.sh):
 *   cc -O2 -std=c11 -I<repo>/src mc_sparse_topology_c.c <sources> -lm -o X
 */
#if !defined(_WIN32) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200809L
#endif
#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_sparse_tools.h"
#include "tinyvdb_sparse.h"
#include "tinyvdb_tree.h"
#include "tinyvdb_tree_internal.h"
#include "tinyvdb_mesh.h"

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MC_SPARSE_N 16
#define MC_SPARSE_RADIUS 4.5f
#define MC_SPARSE_ORIGIN (-MC_SPARSE_N / 2.0f)
#define MC_SPARSE_BG 100.0f
#define MC_SPARSE_ISO 0.0f
#define MC_SPARSE_NFIELDS 2

static unsigned f32bits(float v) {
    unsigned w;
    memcpy(&w, &v, 4);
    return w;
}
static uint64_t f64bits(double v) {
    uint64_t w;
    memcpy(&w, &v, 8);
    return w;
}
static size_t vidx(int x, int y, int z) {
    return (size_t)x + (size_t)y * MC_SPARSE_N + (size_t)z * MC_SPARSE_N * MC_SPARSE_N;
}
static float world(int i) { return MC_SPARSE_ORIGIN + (i + 0.5f); }

static void fill_sphere(float *data) {
    for (int z = 0; z < MC_SPARSE_N; ++z)
        for (int y = 0; y < MC_SPARSE_N; ++y)
            for (int x = 0; x < MC_SPARSE_N; ++x) {
                float px = world(x), py = world(y), pz = world(z);
                data[vidx(x, y, z)] = sqrtf(px * px + py * py + pz * pz) - MC_SPARSE_RADIUS;
            }
}

static void tree_template(tvdb_grid_t *tmpl, int case_id) {
    memset(tmpl, 0, sizeof(*tmpl));
    tmpl->descriptor.grid_type = (char *)"Tree_float_5_4_3";
    tmpl->transform.type = case_id == 0 ? TVDB_TRANSFORM_UNIFORM_SCALE_TRANSLATE
                                        : TVDB_TRANSFORM_SCALE_TRANSLATE;
    tmpl->transform.voxel_size[0] = 1.0;
    tmpl->transform.voxel_size[1] = case_id == 0 ? 1.0 : 2.0;
    tmpl->transform.voxel_size[2] = 1.0;
    for (int a = 0; a < 3; ++a)
        tmpl->transform.translation[a] = MC_SPARSE_ORIGIN + 0.5;
    tmpl->tree.layout.num_levels = 4;
    const int dims[4] = {0, 5, 4, 3};
    for (int i = 0; i < 4; ++i) {
        tmpl->tree.layout.levels[i].log2dim = dims[i];
        tmpl->tree.layout.levels[i].value_type = TVDB_VALUE_FLOAT;
        tmpl->tree.layout.levels[i].node_type =
            i == 0 ? TVDB_NODE_ROOT : i == 3 ? TVDB_NODE_LEAF : TVDB_NODE_INTERNAL;
    }
}

static int build_grid(const tvdb_dense_grid *dense, int case_id, tvdb_grid_t *grid) {
    tvdb_grid_t tmpl;
    tree_template(&tmpl, case_id);
    tvdb_sparse_grid sg = {0};
    if (!tvdb_dense_to_sparse(dense, MC_SPARSE_BG, 1e-3f, &sg)) return 0;
    int ok = tvdb_grid_from_sparse_using_template(&tmpl, &sg, "sphere", MC_SPARSE_BG, grid);
    tvdb_sparse_grid_free(&sg);
    return ok;
}

/* Recover the welded edge key from an emitted world-space crossing point. */
static int recover_key(const double m[4][4], float x, float y, float z,
                       int32_t key[3], int *axis) {
    const double eps = 1e-4;
    double q[3] = {(double)x, (double)y, (double)z};
    int nfrac = 0, frac_axis = -1;
    for (int a = 0; a < 3; ++a) {
        double u = (q[a] - m[a][3]) / m[a][a];
        double fl = floor(u);
        double r = u - fl;
        if (r > 0.5) r = 1.0 - r;
        if (r < eps) {
            key[a] = (int32_t)llround(u);
        } else {
            key[a] = (int32_t)llround(fl);
            ++nfrac;
            frac_axis = a;
        }
    }
    if (nfrac != 1) return 0;
    *axis = frac_axis;
    return 1;
}

static int run_case(int id, const float *data) {
    tvdb_dense_grid dense = {MC_SPARSE_N, MC_SPARSE_N, MC_SPARSE_N,
                             MC_SPARSE_ORIGIN, MC_SPARSE_ORIGIN, MC_SPARSE_ORIGIN,
                             1.0f, (float *)data};
    tvdb_grid_t grid;
    if (!build_grid(&dense, id, &grid)) {
        fprintf(stderr, "build_grid failed: case=%d\n", id);
        return 2;
    }

    double matrix[4][4];
    if (!tvdb_tree_matrix(&grid.transform, matrix)) {
        fprintf(stderr, "tvdb_tree_matrix failed: case=%d\n", id);
        return 2;
    }
    double det = matrix[0][0] *
                     (matrix[1][1] * matrix[2][2] - matrix[1][2] * matrix[2][1]) -
                 matrix[0][1] *
                     (matrix[1][0] * matrix[2][2] - matrix[1][2] * matrix[2][0]) +
                 matrix[0][2] *
                     (matrix[1][0] * matrix[2][1] - matrix[1][1] * matrix[2][0]);
    int flip = det > 0;

    printf("case %d n %d iso %08x s0 %016llx s1 %016llx s2 %016llx "
           "t0 %016llx t1 %016llx t2 %016llx flip %d\n",
           id, MC_SPARSE_N, f32bits(MC_SPARSE_ISO),
           (unsigned long long)f64bits(matrix[0][0]),
           (unsigned long long)f64bits(matrix[1][1]),
           (unsigned long long)f64bits(matrix[2][2]),
           (unsigned long long)f64bits(matrix[0][3]),
           (unsigned long long)f64bits(matrix[1][3]),
           (unsigned long long)f64bits(matrix[2][3]), flip);

    /* Dump every lattice sample as the tree reports it. */
    tvdb_tree_index idx;
    tvdb_error_t err;
    memset(&idx, 0, sizeof(idx));
    memset(&err, 0, sizeof(err));
    if (tvdb_tree_index_create(&grid, 1, &idx, &err) != TVDB_OK) {
        fprintf(stderr, "tvdb_tree_index_create failed: case=%d\n", id);
        return 2;
    }
    for (int z = 0; z < MC_SPARSE_N; ++z)
        for (int y = 0; y < MC_SPARSE_N; ++y)
            for (int x = 0; x < MC_SPARSE_N; ++x) {
                int32_t c[3] = {x, y, z};
                int active = 0;
                float v = tvdb_tree_get(&idx, c, &active);
                printf("voxel %d %d %d %d act %d val %08x\n", id, x, y, z, active, f32bits(v));
            }
    tvdb_tree_index_destroy(&idx);

    /* The real sparse/tree marching cubes. */
    tvdb_triangle_mesh mesh = {0};
    memset(&err, 0, sizeof(err));
    tvdb_status_t st = tvdb_grid_volume_to_mesh(&grid, MC_SPARSE_ISO, 0.0, 0, &mesh, &err);
    if (st != TVDB_OK) {
        fprintf(stderr, "tvdb_grid_volume_to_mesh failed: case=%d status=%d msg=%s\n",
                id, (int)st, err.message);
        tvdb_triangle_mesh_free(&mesh);
        tvdb_grid_destroy_owned(&grid);
        return 3;
    }
    printf("mesh %d nv %zu nf %zu\n", id, mesh.vertex_count, mesh.face_count);
    for (size_t j = 0; j < mesh.vertex_count; ++j) {
        tvdb_vec3f p = mesh.vertices[j];
        int32_t key[3];
        int axis = -1;
        if (!recover_key(matrix, p.x, p.y, p.z, key, &axis)) {
            fprintf(stderr, "key recovery failed: case=%d vertex=%zu\n", id, j);
            tvdb_triangle_mesh_free(&mesh);
            tvdb_grid_destroy_owned(&grid);
            return 4;
        }
        printf("vertex %d %zu %08x %08x %08x %d %d %d %d\n", id, j,
               f32bits(p.x), f32bits(p.y), f32bits(p.z),
               key[0], key[1], key[2], axis);
    }
    for (size_t j = 0; j < mesh.face_count; ++j)
        printf("face %d %zu %u %u %u\n", id, j, mesh.faces[j].v0,
               mesh.faces[j].v1, mesh.faces[j].v2);

    tvdb_triangle_mesh_free(&mesh);
    tvdb_grid_destroy_owned(&grid);
    return 0;
}

int main(void) {
    float *data = malloc((size_t)MC_SPARSE_N * MC_SPARSE_N * MC_SPARSE_N * sizeof(float));
    if (!data) return 1;
    fill_sphere(data);
    printf("fields %d\n", MC_SPARSE_NFIELDS);
    for (int id = 0; id < MC_SPARSE_NFIELDS; ++id) {
        int rc = run_case(id, data);
        if (rc != 0) {
            free(data);
            return rc;
        }
    }
    free(data);
    return 0;
}
