/* Differential harness: dense mesh -> signed-distance field
 * (tvdb_mesh_to_sdf_ex, src/tinyvdb_mesh_conversion.inl), printed for
 * comparison against the Lean Float32 twin (Vdb.MeshSdfCheck).
 *
 * Three closed meshes are generated here and the generated dense grid is
 * dumped voxel by voxel as float bit patterns. The Lean twin recomputes the
 * grid from the dumped mesh alone (brute-force closest triangle, same
 * tie-break "lowest face index on exact tie", closest-feature pseudo-normal
 * sign, ±band clamp) and compares bits.
 *
 * Meshes:
 *   0  cube               8 verts,  12 faces (outward winding)
 *   1  icosahedron       12 verts,  20 faces (outward winding, phi irrational)
 *   2  jittered icosa.   12 verts,  20 faces (per-vertex radial LCG jitter
 *                        ±22%, orientation re-checked and fixed)
 *
 * Spacing h = 0.3f, band = 0.4f for all three grids.
 *
 * Output lines:
 *   mesh i params h <%08x> band <%08x> nx <d> ny <d> nz <d> ox <%08x> oy <%08x> oz <%08x>
 *   mesh i vertex j <%08x> <%08x> <%08x>
 *   mesh i face j <v0> <v1> <v2>
 *   mesh i voxel x y z <%08x>
 *
 * Build: cc -O2 -std=c11 -I<repo>/src meshsdf_c.c <sources...> -lm -o meshsdf_c
 */
#if !defined(_WIN32) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 199309L
#endif
#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_mesh.h"
#include "tinyvdb_mesh_conversion.h"

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint64_t g_state;
static uint64_t next_rand(void) {
    g_state = g_state * 6364136223846793005ULL + 1442695040888963407ULL;
    return g_state >> 33;
}

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

static void dump_grid(int id, const tvdb_dense_grid* g) {
    printf("mesh %d dims nx %d ny %d nz %d ox %08x oy %08x oz %08x\n", id,
           g->nx, g->ny, g->nz, bits_of(g->ox), bits_of(g->oy), bits_of(g->oz));
    for (int z = 0; z < g->nz; ++z)
        for (int y = 0; y < g->ny; ++y)
            for (int x = 0; x < g->nx; ++x)
                printf("mesh %d voxel %d %d %d %08x\n", id, x, y, z,
                       bits_of(g->data[(size_t)z * (size_t)g->ny * (size_t)g->nx +
                                           (size_t)y * (size_t)g->nx + (size_t)x]));
}

/* Outward-orientation fix-up: flip faces whose geometric normal disagrees
 * with their distance from the origin (centred meshes). */
static void fix_orientation(tvdb_vec3f* verts, const tvdb_triangle* faces, size_t n) {
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
            tvdb_triangle* tf = (tvdb_triangle*)faces;
            uint32_t t = tf[f].v1;
            tf[f].v1 = tf[f].v2;
            tf[f].v2 = t;
        }
    }
}

static void run_mesh(int id, tvdb_triangle_mesh* m, float h, float band) {
    tvdb_dense_grid out = {0};
    tvdb_error_t err;
    tvdb_status_t st = tvdb_mesh_to_sdf_ex(m, h, band, NULL, &out, NULL, &err);
    if (st != TVDB_OK) {
        fprintf(stderr, "tvdb_mesh_to_sdf_ex failed for mesh %d\n", id);
        exit(2);
    }
    /* h/band printed with the grid: the harness reads only the dump. */
    printf("mesh %d h %08x band %08x\n", id, bits_of(h), bits_of(band));
    dump_mesh(id, m);
    dump_grid(id, &out);
    free(out.data);
}

int main(void) {
    g_state = 0x9e3779b97f4a7c15ULL;

    /* mesh 0: cube, outward winding. */
    {
        const tvdb_vec3f verts[8] = {
            {-1.0f, -1.0f, -1.0f}, {1.0f, -1.0f, -1.0f}, {1.0f, 1.0f, -1.0f}, {-1.0f, 1.0f, -1.0f},
            {-1.0f, -1.0f, 1.0f},  {1.0f, -1.0f, 1.0f},  {1.0f, 1.0f, 1.0f},  {-1.0f, 1.0f, 1.0f}};
        const tvdb_triangle faces[12] = {
            {0, 2, 1}, {0, 3, 2}, {4, 5, 6}, {4, 6, 7}, {0, 4, 7}, {0, 7, 3},
            {1, 2, 6}, {1, 6, 5}, {0, 1, 5}, {0, 5, 4}, {3, 7, 6}, {3, 6, 2}};
        tvdb_triangle_mesh m = {(tvdb_vec3f*)verts, 8, 8, (tvdb_triangle*)faces, 12, 12};
        run_mesh(0, &m, 0.3f, 0.4f);
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
        run_mesh(1, &m, 0.3f, 0.4f);
    }

    /* mesh 2: jittered icosahedron (radial per-vertex LCG jitter ±22%). */
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
        for (int i = 0; i < 12; ++i) {
            double f = 1.0 + 0.22 * ((double)(next_rand() % 100000) / 100000.0 - 0.5);
            verts[i].x = (float)(verts[i].x * f);
            verts[i].y = (float)(verts[i].y * f);
            verts[i].z = (float)(verts[i].z * f);
        }
        fix_orientation(verts, faces, 20);
        tvdb_triangle_mesh m = {verts, 12, 12, faces, 20, 20};
        run_mesh(2, &m, 0.3f, 0.4f);
    }
    return 0;
}
