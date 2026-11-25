/* Differential harness: sparse/tree mesh -> narrow-band level set
 * (tvdb_mesh_to_level_set, src/tinyvdb_sparse_tools.c), printed for
 * comparison against the Lean bounded twin (Vdb.TreeMeshSdfCheck).
 *
 * Two closed meshes are generated and processed through the real tree API:
 *   0  cube            8 verts,  12 faces (outward winding)
 *   1  octahedron      6 verts,   8 faces (outward winding)
 * Spacing h = 0.4f, exterior/interior width = 0.5f, winding sign EXACT.
 *
 * For each mesh the driver dumps
 *   - the generated input mesh (vertices/faces as Float32 bit patterns),
 *   - the options and the C result counters,
 *   - grid topology (background bits, active voxel count, index bounds)
 *     via tvdb_grid_get_info,
 *   - the stored (active, value bits) on a fixed 9^3 index lattice
 *     [-4,4]^3 via tvdb_tree_get / tvdb_tree_index_create.
 *
 * The lattice covers both meshes and their narrow band, so the dumped
 * active-voxel count equals the grid's reported active voxel count (the Lean
 * twin checks this). Values are read with tvdb_tree_get so the dump includes
 * the effect of seeding, dilation, band keep-rule, flood fill and prune; the
 * Lean twin deliberately does NOT mirror those stages (see its header).
 *
 * Output lines (the Lean parser consumes `params`, `vertex`, `face`, `topo`,
 * `voxel`; `result` is diagnostic evidence):
 *   mesh i params h <%08x> out <%08x> in <%08x>
 *   mesh i vertex j <%08x> <%08x> <%08x>
 *   mesh i face j <v0> <v1> <v2>
 *   mesh i face j steps <n>       (C seeding's barycentric sample count)
 *   mesh i seedcount <n>
 *   mesh i seed <x> <y> <z>       (unique snapped seed voxels)
 *   mesh i result seed <n> cand <n> active <n> maxd <%08x>
 *   mesh i topo bg <%08x> active_vox <n> imin <i> <j> <k> imax <i> <j> <k>
 *   mesh i voxel x y z act <0|1> val <%08x>
 *
 * Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
 * SPDX-License-Identifier: Apache-2.0
 */
#if !defined(_WIN32) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200809L
#endif
#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_sparse_tools.h"
#include "tinyvdb_volume.h"
#include "tinyvdb_tree_internal.h"

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned bits_of(float v) {
    unsigned w;
    memcpy(&w, &v, 4);
    return w;
}

static void dump_mesh(int id, const tvdb_triangle_mesh* m) {
    for (size_t j = 0; j < m->vertex_count; ++j)
        printf("mesh %d vertex %zu %08x %08x %08x\n", id, j, bits_of(m->vertices[j].x),
               bits_of(m->vertices[j].y), bits_of(m->vertices[j].z));
    for (size_t j = 0; j < m->face_count; ++j)
        printf("mesh %d face %zu %u %u %u\n", id, j, m->faces[j].v0, m->faces[j].v1,
               m->faces[j].v2);
}

/* Outward-orientation fix-up for a centred convex mesh: flip faces whose
 * geometric normal points toward the origin. */
static void fix_orientation(tvdb_vec3f* verts, const tvdb_triangle* faces, size_t n) {
    for (size_t f = 0; f < n; ++f) {
        tvdb_vec3f a = verts[faces[f].v0], b = verts[faces[f].v1], c = verts[faces[f].v2];
        double ab[3] = {(double)b.x - a.x, (double)b.y - a.y, (double)b.z - a.z},
               ac[3] = {(double)c.x - a.x, (double)c.y - a.y, (double)c.z - a.z};
        double nr[3] = {ab[1] * ac[2] - ab[2] * ac[1], ab[2] * ac[0] - ab[0] * ac[2],
                        ab[0] * ac[1] - ab[1] * ac[0]};
        double cx = (a.x + b.x + c.x) / 3.0, cy = (a.y + b.y + c.y) / 3.0,
               cz = (a.z + b.z + c.z) / 3.0;
        if (nr[0] * cx + nr[1] * cy + nr[2] * cz < 0.0) {
            tvdb_triangle* tf = (tvdb_triangle*)faces;
            uint32_t t = tf[f].v1;
            tf[f].v1 = tf[f].v2;
            tf[f].v2 = t;
        }
    }
}

/* Mirror of the barycentric seed loop of `tvdb_mesh_to_level_set`
 * (src/tinyvdb_sparse_tools.c, lines 1938-1992), exposing its intermediate
 * output: the unique snapped seed voxels. Every operation below is copied in
 * the same order as the C loop so the Lean native-Float twin can reproduce
 * the exact IEEE-754 double results. */
typedef struct { int32_t x, y, z; } seed_key;
static void dump_seeds(int id, const tvdb_triangle_mesh* m, float h) {
    const double inv_h = 1.0 / (double)h;
    seed_key* seeds = NULL;
    size_t cnt = 0, cap = 0;
    for (size_t f = 0; f < m->face_count; ++f) {
        const tvdb_vec3f* v[3] = {m->vertices + m->faces[f].v0,
                                  m->vertices + m->faces[f].v1,
                                  m->vertices + m->faces[f].v2};
        const double p0[3] = {v[0]->x, v[0]->y, v[0]->z};
        const double e1[3] = {(double)v[1]->x - p0[0], (double)v[1]->y - p0[1],
                              (double)v[1]->z - p0[2]};
        const double e2[3] = {(double)v[2]->x - p0[0], (double)v[2]->y - p0[1],
                              (double)v[2]->z - p0[2]};
        const double l = fmax(fmax(sqrt(e1[0] * e1[0] + e1[1] * e1[1] + e1[2] * e1[2]),
                                   sqrt(e2[0] * e2[0] + e2[1] * e2[1] + e2[2] * e2[2])),
                              sqrt((e1[0] - e2[0]) * (e1[0] - e2[0]) +
                                   (e1[1] - e2[1]) * (e1[1] - e2[1]) +
                                   (e1[2] - e2[2]) * (e1[2] - e2[2])));
        const double steps_d = ceil(2.0 * l * inv_h);
        printf("mesh %d face %zu steps %lld\n", id, f, (long long)steps_d);
        const size_t n = steps_d < 1 ? 1 : (size_t)steps_d;
        for (size_t i = 0; i <= n; ++i)
            for (size_t j = 0; i + j <= n; ++j) {
                const double a = (double)i / (double)n, b = (double)j / (double)n;
                const double p[3] = {p0[0] + a * e1[0] + b * e2[0],
                                     p0[1] + a * e1[1] + b * e2[1],
                                     p0[2] + a * e1[2] + b * e2[2]};
                int32_t c[3];
                for (int ax = 0; ax < 3; ++ax)
                    c[ax] = (int32_t)floor(p[ax] * inv_h + 0.5);
                int found = 0;
                for (size_t q = 0; q < cnt; ++q)
                    if (seeds[q].x == c[0] && seeds[q].y == c[1] && seeds[q].z == c[2]) {
                        found = 1;
                        break;
                    }
                if (found) continue;
                if (cnt == cap) {
                    cap = cap ? 2 * cap : 1024;
                    seed_key* t = realloc(seeds, cap * sizeof(*seeds));
                    if (!t) { free(seeds); exit(2); }
                    seeds = t;
                }
                seeds[cnt].x = c[0]; seeds[cnt].y = c[1]; seeds[cnt].z = c[2];
                ++cnt;
            }
    }
    printf("mesh %d seedcount %zu\n", id, cnt);
    for (size_t q = 0; q < cnt; ++q)
        printf("mesh %d seed %d %d %d\n", id, seeds[q].x, seeds[q].y, seeds[q].z);
    free(seeds);
}

static void run(int id, const tvdb_triangle_mesh* m, float h, float outside, float inside) {
    tvdb_mesh_level_set_options_t opt;
    memset(&opt, 0, sizeof(opt));
    opt.voxel_size = h;
    opt.exterior_width = outside;
    opt.interior_width = inside;
    opt.sign = TVDB_LEVEL_SET_SIGN_WINDING_EXACT;
    opt.max_voxels = 0; /* default 1,000,000 */
    opt.grid_name = "surface";

    tvdb_grid_t grid;
    memset(&grid, 0, sizeof(grid));
    tvdb_mesh_level_set_result_t res;
    memset(&res, 0, sizeof(res));
    tvdb_error_t err;
    memset(&err, 0, sizeof(err));
    tvdb_status_t st = tvdb_mesh_to_level_set(m, &opt, NULL, &grid, &res, &err);
    if (st != TVDB_OK) {
        fprintf(stderr, "mesh %d: tvdb_mesh_to_level_set failed (status %d)\n", id, (int)st);
        exit(2);
    }
    printf("mesh %d params h %08x out %08x in %08x\n", id, bits_of(h), bits_of(outside),
           bits_of(inside));
    dump_mesh(id, m);
    dump_seeds(id, m, h);
    printf("mesh %d result seed %zu cand %zu active %zu maxd %08x\n", id, res.seed_voxels,
           res.candidate_voxels, res.active_voxels, bits_of((float)res.max_distance));

    tvdb_grid_info_t info;
    memset(&info, 0, sizeof(info));
    st = tvdb_grid_get_info(&grid, &info, &err);
    if (st != TVDB_OK) {
        fprintf(stderr, "mesh %d: tvdb_grid_get_info failed (status %d)\n", id, (int)st);
        exit(2);
    }
    printf("mesh %d topo bg %08x active_vox %llu imin %d %d %d imax %d %d %d\n", id,
           bits_of(info.background[0]), (unsigned long long)info.active_voxels,
           info.index_min[0], info.index_min[1], info.index_min[2], info.index_max[0],
           info.index_max[1], info.index_max[2]);

    tvdb_tree_index idx;
    memset(&idx, 0, sizeof(idx));
    st = tvdb_tree_index_create(&grid, 1, &idx, &err);
    if (st != TVDB_OK) {
        fprintf(stderr, "mesh %d: tvdb_tree_index_create failed (status %d)\n", id, (int)st);
        exit(2);
    }
    for (int x = -4; x <= 4; ++x)
        for (int y = -4; y <= 4; ++y)
            for (int z = -4; z <= 4; ++z) {
                int32_t c[3] = {x, y, z};
                int active = 0;
                float v = tvdb_tree_get(&idx, c, &active);
                printf("mesh %d voxel %d %d %d act %d val %08x\n", id, x, y, z, active,
                       bits_of(v));
            }
    tvdb_tree_index_destroy(&idx);
    tvdb_grid_destroy_owned(&grid);
}

int main(void) {
    /* mesh 0: cube, outward winding. */
    {
        const tvdb_vec3f verts[8] = {
            {-1.0f, -1.0f, -1.0f}, {1.0f, -1.0f, -1.0f}, {1.0f, 1.0f, -1.0f}, {-1.0f, 1.0f, -1.0f},
            {-1.0f, -1.0f, 1.0f},  {1.0f, -1.0f, 1.0f},  {1.0f, 1.0f, 1.0f},  {-1.0f, 1.0f, 1.0f}};
        const tvdb_triangle faces[12] = {
            {0, 2, 1}, {0, 3, 2}, {4, 5, 6}, {4, 6, 7}, {0, 4, 7}, {0, 7, 3},
            {1, 2, 6}, {1, 6, 5}, {0, 1, 5}, {0, 5, 4}, {3, 7, 6}, {3, 6, 2}};
        tvdb_triangle_mesh m = {(tvdb_vec3f*)verts, 8, 8, (tvdb_triangle*)faces, 12, 12};
        run(0, &m, 0.4f, 0.5f, 0.5f);
    }
    /* mesh 1: octahedron, outward winding (a=1.3 is off-lattice for h=0.4,
     * so no sample lies exactly on the surface). */
    {
        const float a = 1.3f;
        tvdb_vec3f verts[6] = {{a, 0, 0}, {0, a, 0}, {-a, 0, 0}, {0, -a, 0}, {0, 0, a}, {0, 0, -a}};
        tvdb_triangle faces[8] = {
            {0, 1, 4}, {1, 2, 4}, {2, 3, 4}, {3, 0, 4},
            {1, 0, 5}, {2, 1, 5}, {3, 2, 5}, {0, 3, 5}};
        fix_orientation(verts, faces, 8);
        tvdb_triangle_mesh m = {verts, 6, 6, faces, 8, 8};
        run(1, &m, 0.4f, 0.5f, 0.5f);
    }
    return 0;
}
