/* Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
   SPDX-License-Identifier: Apache-2.0 */

/* Tie-explanation harness: per-face Float32 squared distances of the *real*
 * closest-point kernel used by tvdb_bvh_closest, for every cell-centre query.
 *
 * Companion to scripts/meshsdf_bvh_c.c. This driver #includes tinyvdb_mesh.c
 * so the *real* static routines (tri_closest_point_c, sub_c, dot_c,
 * tvdb_bvh_init / tvdb_bvh_build / tvdb_bvh_closest, mesh_position,
 * mesh_normal) are called -- not a reimplementation. Nothing in src/ changes.
 *
 * The cube + icosahedron, voxel size h, band, and row-major seed chain are
 * byte-for-byte the same as meshsdf_bvh_c.c, so the query set and the C winner
 * (`rf`) are the same corpus. Additionally, for EVERY query we compute the
 * squared distance of EVERY face with the identical expression used inside
 * tvdb_bvh_closest:
 *
 *     tvdb_vec3f cp = tri_closest_point_c(p, a, b, c, &feature);
 *     tvdb_vec3f d  = sub_c(p, cp);
 *     float     dsq = dot_c(d, d);
 *
 * and dump its 8-hex Float32 bits. The exact-ℚ Lean twin
 * (Vdb.MeshSdfBvhTieCheck) uses these bits to show that the 11 documented
 * Float32 tie faces are genuine exact ties whose C winner is selected by
 * Float32 rounding of the per-face squared distance.
 *
 * Output lines (all floats are 8 lowercase hex digits of IEEE-754 bits):
 *   # tie-dump v1 ...                              (comment, ignored by twin)
 *   mesh <id> vertex <j> <xbits> <ybits> <zbits>    (mesh geometry)
 *   mesh <id> face <j> <a> <b> <c>                  (mesh topology)
 *   tie <id> <qi> px <bits> py <bits> pz <bits> rd <bits> rf <face> \
 *       dsq <f0> <f1> ... <f_{nf-1}>               (one per query, all faces)
 *
 * No secrets, no generated binaries. Build (same flags as the C half of
 * check_meshsdf_bvh.sh):
 *   cc -O2 -std=c11 -I<repo>/src meshsdf_bvh_ties_c.c <support sources> -lm \
 *      -o meshsdf_bvh_ties_c
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

static unsigned bits_of(float v) {
    unsigned w;
    memcpy(&w, &v, 4);
    return w;
}

static void dump_geometry(int id, const tvdb_triangle_mesh* m) {
    for (size_t j = 0; j < m->vertex_count; ++j)
        printf("mesh %d vertex %zu %08x %08x %08x\n", id, j, bits_of(m->vertices[j].x),
               bits_of(m->vertices[j].y), bits_of(m->vertices[j].z));
    for (size_t j = 0; j < m->face_count; ++j)
        printf("mesh %d face %zu %u %u %u\n", id, j, m->faces[j].v0, m->faces[j].v1,
               m->faces[j].v2);
}

/* Squared distance of one face with exactly the expression tvdb_bvh_closest
 * uses at src/tinyvdb_mesh.c:650-652. */
static float face_dsq_c(const tvdb_triangle_mesh* m, const tvdb_triangle* t,
                        tvdb_vec3f p, int* feature) {
    tvdb_vec3f a = m->vertices[t->v0], b = m->vertices[t->v1], c = m->vertices[t->v2];
    tvdb_vec3f cp = tri_closest_point_c(p, a, b, c, feature);
    tvdb_vec3f d = sub_c(p, cp);
    return dot_c(d, d);
}

static int run_mesh(int id, const tvdb_triangle_mesh* m, float h, float band) {
    tvdb_dense_grid g = {0};
    tvdb_error_t err = {0};
    tvdb_status_t st = tvdb_mesh_to_sdf_ex(m, h, band, NULL, &g, NULL, &err);
    if (st != TVDB_OK) {
        fprintf(stderr, "tvdb_mesh_to_sdf_ex failed for mesh %d\n", id);
        return 2;
    }

    dump_geometry(id, m);

    tvdb_bvh_t bvh;
    if (tvdb_bvh_init(&bvh, m, m->face_count) != 0) {
        fprintf(stderr, "tvdb_bvh_init failed for mesh %d\n", id);
        free(g.data);
        return 2;
    }
    tvdb_vec3f* normals = (tvdb_vec3f*)malloc(m->face_count * sizeof(tvdb_vec3f));
    if (!normals) {
        tvdb_bvh_free(&bvh);
        free(g.data);
        return 2;
    }
    for (size_t f = 0; f < m->face_count; ++f) {
        const tvdb_triangle* t = &m->faces[f];
        normals[f] = mesh_normal(m->vertices[t->v0], m->vertices[t->v1], m->vertices[t->v2]);
    }

    long qi = 0;
    for (int z = 0; z < g.nz; ++z) {
        for (int y = 0; y < g.ny; ++y) {
            float seed = INFINITY;
            int32_t seed_face = -1;
            for (int x = 0; x < g.nx; ++x) {
                tvdb_vec3f p = mesh_position(&g, x, y, z);
                tvdb_vec3f cp, n;
                int32_t face = -1;
                int feature = 6;
                float dsq = tvdb_bvh_closest(&bvh, m, normals, p, seed, seed_face,
                                             &cp, &n, &face, &feature);
                if (face < 0 || !isfinite(dsq)) {
                    fprintf(stderr, "degenerate BVH query mesh %d voxel %d %d %d\n", id, x, y, z);
                    free(normals);
                    tvdb_bvh_free(&bvh);
                    free(g.data);
                    return 2;
                }

                printf("tie %d %ld px %08x py %08x pz %08x rd %08x rf %d dsq",
                       id, qi++, bits_of(p.x), bits_of(p.y), bits_of(p.z),
                       bits_of(dsq), (int)face);
                for (size_t f = 0; f < m->face_count; ++f) {
                    int feat = 6;
                    float fd = face_dsq_c(m, &m->faces[f], p, &feat);
                    printf(" %08x", bits_of(fd));
                }
                printf("\n");

                seed = dsq;
                seed_face = face;
            }
        }
    }

    free(normals);
    tvdb_bvh_free(&bvh);
    free(g.data);
    return 0;
}

/* Outward-orientation fix-up (centred meshes), identical to meshsdf_c.c. */
static void fix_orientation(tvdb_vec3f* verts, tvdb_triangle* faces, size_t n) {
    for (size_t f = 0; f < n; ++f) {
        tvdb_vec3f a = verts[faces[f].v0], b = verts[faces[f].v1], c = verts[faces[f].v2];
        double ab[3] = {(double)b.x - a.x, (double)b.y - a.y, (double)b.z - a.z},
               ac[3] = {(double)c.x - a.x, (double)c.y - a.y, (double)c.z - a.z};
        double nrm[3] = {ab[1] * ac[2] - ab[2] * ac[1], ab[2] * ac[0] - ab[0] * ac[2],
                         ab[0] * ac[1] - ab[1] * ac[0]};
        double cx = (a.x + b.x + c.x) / 3.0, cy = (a.y + b.y + c.y) / 3.0,
               cz = (a.z + b.z + c.z) / 3.0;
        double d = nrm[0] * cx + nrm[1] * cy + nrm[2] * cz;
        if (d < 0.0) {
            uint32_t t = faces[f].v1;
            faces[f].v1 = faces[f].v2;
            faces[f].v2 = t;
        }
    }
}

int main(void) {
    printf("# tie-dump v1: per-face Float32 squared distances from the real C kernel\n");
    printf("# mesh <id> vertex <j> <x> <y> <z> ; mesh <id> face <j> <a> <b> <c>\n");
    printf("# tie <id> <qi> px <p> py <p> pz <p> rd <bits> rf <face> dsq <f0> ... <fN-1>\n");

    /* mesh 0: cube, outward winding. 12 faces -> balanced test tree + ties. */
    {
        const tvdb_vec3f verts[8] = {
            {-1.0f, -1.0f, -1.0f}, {1.0f, -1.0f, -1.0f}, {1.0f, 1.0f, -1.0f}, {-1.0f, 1.0f, -1.0f},
            {-1.0f, -1.0f, 1.0f},  {1.0f, -1.0f, 1.0f},  {1.0f, 1.0f, 1.0f},  {-1.0f, 1.0f, 1.0f}};
        tvdb_triangle faces[12] = {
            {0, 2, 1}, {0, 3, 2}, {4, 5, 6}, {4, 6, 7}, {0, 4, 7}, {0, 7, 3},
            {1, 2, 6}, {1, 6, 5}, {0, 1, 5}, {0, 5, 4}, {3, 7, 6}, {3, 6, 2}};
        tvdb_triangle_mesh m = {(tvdb_vec3f*)verts, 8, 8, faces, 12, 12};
        if (run_mesh(0, &m, 0.7f, 0.4f) != 0) return 2;
    }

    /* mesh 1: icosahedron, outward winding (phi irrational). */
    {
        const float phi = 1.6180339887498949f;
        tvdb_vec3f verts[12] = {
            {-1.0f, phi, 0.0f}, {1.0f, phi, 0.0f},   {-1.0f, -phi, 0.0f}, {1.0f, -phi, 0.0f},
            {0.0f, -1.0f, phi}, {0.0f, 1.0f, phi},   {0.0f, -1.0f, -phi}, {0.0f, 1.0f, -phi},
            {phi, 0.0f, -1.0f}, {phi, 0.0f, 1.0f},   {-phi, 0.0f, -1.0f}, {-phi, 0.0f, 1.0f}};
        tvdb_triangle faces[20] = {
            {0, 11, 5},  {0, 5, 1},   {0, 1, 7},   {0, 7, 10}, {0, 10, 11},
            {1, 5, 9},   {5, 11, 4},  {11, 10, 2}, {10, 7, 6}, {7, 1, 8},
            {3, 9, 4},   {3, 4, 2},   {3, 2, 6},   {3, 6, 8},  {3, 8, 9},
            {4, 9, 5},   {2, 4, 11},  {6, 2, 10},  {8, 6, 7},  {9, 8, 1}};
        fix_orientation(verts, faces, 20);
        tvdb_triangle_mesh m = {verts, 12, 12, faces, 20, 20};
        if (run_mesh(1, &m, 0.8f, 0.4f) != 0) return 2;
    }
    return 0;
}
