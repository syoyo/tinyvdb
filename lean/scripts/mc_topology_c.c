/* Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
   SPDX-License-Identifier: Apache-2.0 */

/* Differential harness: dense marching-cubes TOPOLOGY (C half).
 *
 * Calls the REAL `tvdb_sdf_to_mesh_ex` (`src/tinyvdb_mesh_conversion.inl`,
 * reached through `src/tinyvdb_mesh.c`) on a deterministic corpus of dense
 * fields and dumps, as text:
 *
 *   fields <N>
 *   case <id> nx <n> ny <n> nz <n> ox <hex> oy <hex> oz <hex> vs <hex> iso <hex>
 *   sample <id> <linear-index> <hex>          (every input voxel, Float32 bits)
 *   mesh <id> <WINDING> nv <n> nf <n>
 *   vertex <id> <j> <xbits> <ybits> <zbits>   (output positions, Float32 bits)
 *   face <id> <WINDING> <j> <v0> <v1> <v2>    (REAL emitted triangle indices)
 *
 * Vertices are printed once per field (both windings allocate them in the
 * same order); faces are printed for both TVDB_MESH_WINDING_TABLE and
 * TVDB_MESH_WINDING_OUTWARD. The Lean twin (`Vdb/McTopologyCheck.lean`)
 * recomputes the welded edge keys, vertex ids and triangles independently
 * from `Vdb.McTable` / `Vdb.McWeld` and compares them.
 *
 * Corpus (258 fields):
 *   0..255 : one Bourke corner-case pattern embedded in the central cell
 *            (1,1,1) of a padded 4^3 lattice, background +1, iso 0.
 *   256    : analytic sphere  |p - (1,1,1)| - 0.7  on an 8^3 lattice.
 *   257    : analytic plane   px + py + pz - 3.1   on an 8^3 lattice.
 *
 * This driver #includes tinyvdb_mesh.c so the *real* static MC tables, edge
 * cache and emitter are exercised; nothing in src/ is modified. Link the
 * usual support sources but NOT tinyvdb_mesh.c itself.
 *
 * No secrets, no generated binaries. Build (see check_mc_topology.sh):
 *   cc -O2 -std=c11 -I<repo>/src mc_topology_c.c <support sources> -lm -o mc_topology_c
 */
#if !defined(_WIN32) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 199309L
#endif
#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_mesh.c"

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MC_TOPO_NFIELDS 258
#define MC_TOPO_PATTERNS 256
#define MC_TOPO_PAD_N 4
#define MC_TOPO_ANA_N 8
#define MC_TOPO_CELL_X 1
#define MC_TOPO_CELL_Y 1
#define MC_TOPO_CELL_Z 1

static const float MC_TOPO_ORIGIN = 0.0f;
static const float MC_TOPO_VS = 0.25f;
static const float MC_TOPO_ISO = 0.0f;

/* Bourke corner numbering, verbatim from MC_CORNER_OFFSETS in tinyvdb_mesh.c. */
static const int CORNER[8][3] = {
    {0, 0, 0}, {1, 0, 0}, {1, 1, 0}, {0, 1, 0},
    {0, 0, 1}, {1, 0, 1}, {1, 1, 1}, {0, 1, 1}};

static unsigned bits_of(float v) {
    unsigned w;
    memcpy(&w, &v, 4);
    return w;
}

static int dims_of(int id) { return id < MC_TOPO_PATTERNS ? MC_TOPO_PAD_N : MC_TOPO_ANA_N; }

static float field_value(int id, int x, int y, int z) {
    float px = MC_TOPO_ORIGIN + (x + 0.5f) * MC_TOPO_VS;
    float py = MC_TOPO_ORIGIN + (y + 0.5f) * MC_TOPO_VS;
    float pz = MC_TOPO_ORIGIN + (z + 0.5f) * MC_TOPO_VS;
    if (id < MC_TOPO_PATTERNS) {
        for (int c = 0; c < 8; ++c) {
            if (x == MC_TOPO_CELL_X + CORNER[c][0] && y == MC_TOPO_CELL_Y + CORNER[c][1] &&
                z == MC_TOPO_CELL_Z + CORNER[c][2]) {
                return ((id >> c) & 1) ? -1.0f : 1.0f;
            }
        }
        return 1.0f;
    }
    if (id == 256) {
        float dx = px - 1.0f, dy = py - 1.0f, dz = pz - 1.0f;
        return sqrtf(dx * dx + dy * dy + dz * dz) - 0.7f;
    }
    return px + py + pz - 3.1f;
}

static int run_case(int id, tvdb_dense_grid *g) {
    const int n = dims_of(id);
    size_t count = (size_t)n * n * n;
    g->nx = n;
    g->ny = n;
    g->nz = n;
    g->ox = g->oy = g->oz = MC_TOPO_ORIGIN;
    g->voxel_size = MC_TOPO_VS;
    g->data = (float *)malloc(count * sizeof(float));
    if (!g->data) return 2;
    for (int z = 0; z < n; ++z)
        for (int y = 0; y < n; ++y)
            for (int x = 0; x < n; ++x)
                g->data[((size_t)z * n + y) * n + x] = field_value(id, x, y, z);

    printf("case %d nx %d ny %d nz %d ox %08x oy %08x oz %08x vs %08x iso %08x\n", id, n, n, n,
           bits_of(g->ox), bits_of(g->oy), bits_of(g->oz), bits_of(g->voxel_size),
           bits_of(MC_TOPO_ISO));
    for (size_t i = 0; i < count; ++i)
        printf("sample %d %zu %08x\n", id, i, bits_of(g->data[i]));

    const tvdb_mesh_winding_t windings[2] = {TVDB_MESH_WINDING_TABLE, TVDB_MESH_WINDING_OUTWARD};
    const char *names[2] = {"TABLE", "OUTWARD"};
    for (int w = 0; w < 2; ++w) {
        tvdb_triangle_mesh mesh = {0};
        tvdb_error_t err = {0};
        tvdb_status_t st = tvdb_sdf_to_mesh_ex(g, MC_TOPO_ISO, windings[w], NULL, &mesh, NULL, &err);
        if (st != TVDB_OK) {
            fprintf(stderr, "tvdb_sdf_to_mesh_ex failed: case=%d winding=%s status=%d msg=%s\n",
                    id, names[w], (int)st, err.message);
            free(mesh.vertices);
            free(mesh.faces);
            free(g->data);
            g->data = NULL;
            return 3;
        }
        printf("mesh %d %s nv %zu nf %zu\n", id, names[w], mesh.vertex_count, mesh.face_count);
        if (w == 0) {
            for (size_t j = 0; j < mesh.vertex_count; ++j)
                printf("vertex %d %zu %08x %08x %08x\n", id, j, bits_of(mesh.vertices[j].x),
                       bits_of(mesh.vertices[j].y), bits_of(mesh.vertices[j].z));
        }
        for (size_t j = 0; j < mesh.face_count; ++j)
            printf("face %d %s %zu %u %u %u\n", id, names[w], j, mesh.faces[j].v0,
                   mesh.faces[j].v1, mesh.faces[j].v2);
        free(mesh.vertices);
        free(mesh.faces);
    }
    free(g->data);
    g->data = NULL;
    return 0;
}

int main(void) {
    printf("fields %d\n", MC_TOPO_NFIELDS);
    for (int id = 0; id < MC_TOPO_NFIELDS; ++id) {
        tvdb_dense_grid g = {0};
        int rc = run_case(id, &g);
        if (rc != 0) return rc;
    }
    return 0;
}
