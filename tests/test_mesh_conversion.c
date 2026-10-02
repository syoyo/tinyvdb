/* Procedural inputs and independent triangle-soup/analytic references. */
#include "tinyvdb_mesh_conversion.h"
#include <float.h>
#include <math.h>
#include <stdio.h>
#include <string.h>
#define CHECK(x)                                                                                   \
    do {                                                                                           \
        if (!(x)) {                                                                                \
            fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #x);                                \
            return 1;                                                                              \
        }                                                                                          \
    } while (0)
static const int corners[8][3] = {{0, 0, 0}, {1, 0, 0}, {1, 1, 0}, {0, 1, 0},
                                  {0, 0, 1}, {1, 0, 1}, {1, 1, 1}, {0, 1, 1}};
static const int ends[12][2] = {{0, 1}, {1, 2}, {2, 3}, {3, 0}, {4, 5}, {5, 6},
                                {6, 7}, {7, 4}, {0, 4}, {1, 5}, {2, 6}, {3, 7}};
static size_t index3(const tvdb_dense_grid *g, int x, int y, int z) {
    return ((size_t)z * g->ny + y) * g->nx + x;
}
static tvdb_vec3f position(const tvdb_dense_grid *g, int x, int y, int z) {
    return (tvdb_vec3f){g->ox + (x + .5f) * g->voxel_size, g->oy + (y + .5f) * g->voxel_size,
                        g->oz + (z + .5f) * g->voxel_size};
}
static int same_mesh(const tvdb_triangle_mesh *a, const tvdb_triangle_mesh *b) {
    return a->vertex_count == b->vertex_count && a->face_count == b->face_count &&
           (!a->vertex_count ||
            !memcmp(a->vertices, b->vertices, a->vertex_count * sizeof(*a->vertices))) &&
           (!a->face_count || !memcmp(a->faces, b->faces, a->face_count * sizeof(*a->faces)));
}
static tvdb_vec3f cross(tvdb_vec3f a, tvdb_vec3f b, tvdb_vec3f c) {
    float x = b.x - a.x, y = b.y - a.y, z = b.z - a.z, u = c.x - a.x, v = c.y - a.y, w = c.z - a.z;
    return (tvdb_vec3f){y * w - z * v, z * u - x * w, x * v - y * u};
}
static int reference(const tvdb_dense_grid *g, const tvdb_triangle_mesh *m) {
    const int *table = tvdb_mc_tri_table_flat();
    size_t faces = 0, edges = 0;
    for (int z = 0; z < g->nz; ++z)
        for (int y = 0; y < g->ny; ++y)
            for (int x = 0; x < g->nx; ++x) {
                float v = g->data[index3(g, x, y, z)];
                if (x + 1 < g->nx)
                    edges += (v < 0) != (g->data[index3(g, x + 1, y, z)] < 0);
                if (y + 1 < g->ny)
                    edges += (v < 0) != (g->data[index3(g, x, y + 1, z)] < 0);
                if (z + 1 < g->nz)
                    edges += (v < 0) != (g->data[index3(g, x, y, z + 1)] < 0);
                if (x + 1 == g->nx || y + 1 == g->ny || z + 1 == g->nz)
                    continue;
                int cube = 0;
                float values[8];
                tvdb_vec3f points[8];
                for (int c = 0; c < 8; ++c) {
                    int a = x + corners[c][0], b = y + corners[c][1], d = z + corners[c][2];
                    values[c] = g->data[index3(g, a, b, d)];
                    points[c] = position(g, a, b, d);
                    cube |= (values[c] < 0) << c;
                }
                for (int t = 0; t < 16 && table[cube * 16 + t] >= 0; t += 3) {
                    CHECK(faces < m->face_count);
                    tvdb_triangle f = m->faces[faces++];
                    uint32_t ids[3] = {f.v0, f.v1, f.v2};
                    for (int k = 0; k < 3; ++k) {
                        int e = table[cube * 16 + t + k], a = ends[e][0], b = ends[e][1];
                        double mu = -(double)values[a] / ((double)values[b] - values[a]);
                        tvdb_vec3f p = {(float)((1 - mu) * points[a].x + mu * points[b].x),
                                        (float)((1 - mu) * points[a].y + mu * points[b].y),
                                        (float)((1 - mu) * points[a].z + mu * points[b].z)};
                        CHECK(ids[k] < m->vertex_count);
                        tvdb_vec3f q = m->vertices[ids[k]];
                        CHECK(fabsf(p.x - q.x) < 2e-6f && fabsf(p.y - q.y) < 2e-6f &&
                              fabsf(p.z - q.z) < 2e-6f);
                    }
                }
            }
    CHECK(faces == m->face_count && edges == m->vertex_count);
    return 0;
}
static int marching(tvdb_thread_pool_t *one, tvdb_thread_pool_t *many) {
    for (int pattern = 0; pattern < 264; ++pattern) {
        tvdb_dense_grid g = {0};
        int single = pattern < 256;
        tvdb_dense_grid_init(&g,
                             single           ? 2
                             : pattern == 263 ? 129
                                              : 17,
                             single           ? 2
                             : pattern == 263 ? 131
                                              : 9,
                             single           ? 2
                             : pattern == 263 ? 3
                                              : 7);
        CHECK(g.data);
        g.ox = -2;
        g.oy = .5f;
        g.oz = 3;
        g.voxel_size = .3f;
        unsigned seed = 11;
        size_t count = (size_t)g.nx * g.ny * g.nz;
        for (size_t i = 0; i < count; ++i) {
            int x = i % g.nx, y = (i / g.nx) % g.ny, z = i / (g.nx * g.ny);
            seed = 1664525u * seed + 1013904223u;
            if (single) {
                int map[8] = {0, 1, 3, 2, 4, 5, 7, 6};
                g.data[map[i]] = (pattern & (1u << i)) ? -.25f : .75f;
            } else if (pattern == 256)
                g.data[i] = 1;
            else if (pattern == 257)
                g.data[i] = x - 7.25f;
            else if (pattern == 258)
                g.data[i] =
                    sqrtf((x - 8.f) * (x - 8.f) + (y - 4.f) * (y - 4.f) + (z - 3.f) * (z - 3.f)) -
                    2.6f;
            else if (pattern == 259)
                g.data[i] = ((x + y + z) & 1) ? -1 : 1;
            else if (pattern == 261)
                g.data[i] = x < 8 ? -1e-30f : 1e-30f;
            else if (pattern == 262)
                g.data[i] = x < 8 ? -FLT_MAX : FLT_MAX;
            else if (pattern == 263)
                g.data[i] = x == 64 && y == 65 && z == 1 ? -1 : 1;
            else
                g.data[i] = (seed >> 8) / 8388608.f - 1;
        }
        tvdb_triangle_mesh a = {0}, b = {0}, outward = {0};
        CHECK(tvdb_sdf_to_mesh_ex(&g, 0, TVDB_MESH_WINDING_TABLE, one, &a, NULL, NULL) == TVDB_OK);
        CHECK(tvdb_sdf_to_mesh_ex(&g, 0, TVDB_MESH_WINDING_TABLE, many, &b, NULL, NULL) == TVDB_OK);
        CHECK(same_mesh(&a, &b));
        CHECK(!reference(&g, &a));
        CHECK(a.vertex_capacity == a.vertex_count && a.face_capacity == a.face_count);
        CHECK(tvdb_sdf_to_mesh_ex(&g, 0, TVDB_MESH_WINDING_OUTWARD, many, &outward, NULL, NULL) ==
              TVDB_OK);
        CHECK(outward.vertex_count == a.vertex_count && outward.face_count == a.face_count);
        for (size_t i = 0; i < a.face_count; ++i)
            CHECK(a.faces[i].v0 == outward.faces[i].v0 && a.faces[i].v1 == outward.faces[i].v2 &&
                  a.faces[i].v2 == outward.faces[i].v1);
        if (pattern == 257 || pattern == 261 || pattern == 262)
            for (size_t i = 0; i < outward.face_count; ++i) {
                tvdb_triangle f = outward.faces[i];
                CHECK(cross(outward.vertices[f.v0], outward.vertices[f.v1], outward.vertices[f.v2])
                          .x > 0);
            }
        size_t nv = a.vertex_count, nf = a.face_count;
        CHECK(tvdb_sdf_to_mesh(&g, 0, &a, NULL));
        CHECK(a.vertex_count == 2 * nv && a.face_count == 2 * nf);
        for (size_t i = 0; i < nf; ++i)
            CHECK(a.faces[nf + i].v0 == a.faces[i].v0 + nv &&
                  a.faces[nf + i].v1 == a.faces[i].v1 + nv &&
                  a.faces[nf + i].v2 == a.faces[i].v2 + nv);
        tvdb_triangle_mesh saved = a;
        if (count) {
            g.data[count - 1] = NAN;
            CHECK(tvdb_sdf_to_mesh_ex(&g, 0, TVDB_MESH_WINDING_TABLE, many, &a, NULL, NULL) ==
                  TVDB_ERROR_INVALID_DATA);
            CHECK(!memcmp(&a, &saved, sizeof(a)));
        }
        tvdb_triangle_mesh_free(&a);
        tvdb_triangle_mesh_free(&b);
        tvdb_triangle_mesh_free(&outward);
        tvdb_dense_grid_free(&g);
    }
    /* Reusing output capacity and failure after finite-frame validation. */
    float values[8] = {-1, 1, -1, 1, -1, 1, -1, 1};
    tvdb_dense_grid g = {2, 2, 2, 0, 0, 0, 1, values};
    tvdb_triangle_mesh m = {0};
    CHECK(tvdb_sdf_to_mesh(&g, 0, &m, NULL));
    tvdb_vec3f *v = m.vertices;
    tvdb_triangle *f = m.faces;
    m.vertex_count = m.face_count = 0;
    CHECK(tvdb_sdf_to_mesh_ex(&g, 0, TVDB_MESH_WINDING_OUTWARD, many, &m, NULL, NULL) == TVDB_OK);
    CHECK(m.vertices == v && m.faces == f);
    tvdb_triangle_mesh saved = m;
    CHECK(tvdb_sdf_to_mesh_ex(&g, INFINITY, TVDB_MESH_WINDING_TABLE, one, &m, NULL, NULL) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    g.ox = FLT_MAX;
    g.voxel_size = FLT_MAX;
    CHECK(tvdb_sdf_to_mesh_ex(&g, 0, TVDB_MESH_WINDING_TABLE, one, &m, NULL, NULL) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(!memcmp(&m, &saved, sizeof(m)));
    tvdb_triangle_mesh_free(&m);
    /* Predict the arena allocation before it zeroes an input grid. */
    float arena_values[64] = {-1, 1, -1, 1, -1, 1, -1, 1};
    g = (tvdb_dense_grid){2, 2, 2, 0, 0, 0, 1, arena_values};
    tvdb_arena_allocator_t arena = {arena_values, sizeof(arena_values), 0};
    CHECK(tvdb_sdf_to_mesh_ex(&g, 0, TVDB_MESH_WINDING_TABLE, one, &m, &arena, NULL) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(arena.current_offset == 0 && arena_values[0] == -1 && arena_values[1] == 1 &&
          !m.vertices);
    /* Exact isovalue endpoints retain classic-table topology. */
    g.data = values;
    for (int i = 0; i < 8; ++i)
        values[i] = (i & 1) ? 0 : -1;
    CHECK(tvdb_sdf_to_mesh_ex(&g, 0, TVDB_MESH_WINDING_TABLE, one, &m, NULL, NULL) == TVDB_OK);
    CHECK(!reference(&g, &m));
    tvdb_triangle_mesh_free(&m);
    g = (tvdb_dense_grid){2, 2, 2, 0, 0, 0, 1, values};
    m = (tvdb_triangle_mesh){.vertices = (tvdb_vec3f *)values, .vertex_capacity = 1};
    CHECK(tvdb_sdf_to_mesh_ex(&g, 0, TVDB_MESH_WINDING_TABLE, one, &m, NULL, NULL) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    return 0;
}
static tvdb_vec3f box_vertices[8] = {{-1, -1, -1}, {1, -1, -1}, {1, 1, -1}, {-1, 1, -1},
                                     {-1, -1, 1},  {1, -1, 1},  {1, 1, 1},  {-1, 1, 1}};
static tvdb_triangle box_faces[12] = {{0, 2, 1}, {0, 3, 2}, {4, 5, 6}, {4, 6, 7},
                                      {0, 1, 5}, {0, 5, 4}, {3, 7, 6}, {3, 6, 2},
                                      {0, 4, 7}, {0, 7, 3}, {1, 2, 6}, {1, 6, 5}};
static int analytic_box(const tvdb_dense_grid *g, float band) {
    for (int z = 0; z < g->nz; ++z)
        for (int y = 0; y < g->ny; ++y)
            for (int x = 0; x < g->nx; ++x) {
                tvdb_vec3f p = position(g, x, y, z);
                float a = fabsf(p.x) - 1, b = fabsf(p.y) - 1, c = fabsf(p.z) - 1;
                float outside = sqrtf(fmaxf(a, 0) * fmaxf(a, 0) + fmaxf(b, 0) * fmaxf(b, 0) +
                                      fmaxf(c, 0) * fmaxf(c, 0));
                float d = outside + fminf(fmaxf(a, fmaxf(b, c)), 0),
                      v = g->data[index3(g, x, y, z)];
                CHECK(isfinite(v) && fabsf(fabsf(v) - fminf(fabsf(d), band)) < 2e-5f);
                /* Closest-face sign is ambiguous outside sharp corners. Interior is unambiguous. */
                if (a < -.01f && b < -.01f && c < -.01f)
                    CHECK(v < 0);
            }
    return 0;
}
static int voxelization(tvdb_thread_pool_t *one, tvdb_thread_pool_t *many) {
    tvdb_triangle_mesh box = {box_vertices, 8, 8, box_faces, 12, 12};
    tvdb_mesh_sdf_t *w = NULL;
    tvdb_mesh_sdf_info_t info;
    CHECK(tvdb_mesh_sdf_create(&box, &w, NULL) == TVDB_OK);
    tvdb_mesh_sdf_info(w, &info);
    CHECK(info.faces == 12 && info.acceleration_bytes >= 12 * 40);
    tvdb_dense_grid a = {0}, b = {0}, c = {0};
    for (int i = 0; i < 2; ++i) {
        float h = i ? .11f : .065f, band = .35f;
        CHECK(tvdb_mesh_sdf_generate(w, h, band, one, &a, NULL, NULL) == TVDB_OK);
        CHECK(tvdb_mesh_sdf_generate(w, h, band, many, &b, NULL, NULL) == TVDB_OK);
        size_t n = (size_t)a.nx * a.ny * a.nz;
        CHECK(a.nx == b.nx && a.ny == b.ny && a.nz == b.nz && !memcmp(a.data, b.data, n * 4));
        CHECK(!analytic_box(&a, band));
        CHECK(tvdb_mesh_to_sdf_ex(&box, h, band, NULL, &c, NULL, NULL) == TVDB_OK);
        CHECK(!memcmp(a.data, c.data, n * 4));
    }
    tvdb_dense_grid saved = a;
    float old = a.data[0];
    CHECK(tvdb_mesh_sdf_generate(w, NAN, .3f, many, &a, NULL, NULL) == TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(tvdb_mesh_sdf_generate(w, FLT_MIN, .3f, many, &a, NULL, NULL) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(!memcmp(&a, &saved, sizeof(a)) && a.data[0] == old);
    box.vertex_count--;
    CHECK(tvdb_mesh_sdf_generate(w, .1f, .3f, many, &a, NULL, NULL) == TVDB_ERROR_INVALID_ARGUMENT);
    box.vertex_count++;
    tvdb_dense_grid alias = {2, 2, 2, 0, 0, 0, 1, (float *)box_vertices};
    CHECK(tvdb_mesh_sdf_generate(w, .1f, .3f, many, &alias, NULL, NULL) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    /* A reset arena must not overwrite a retained output on replacement. */
    tvdb_arena_allocator_t arena = {a.data, (size_t)a.nx * a.ny * a.nz * 4, 0};
    CHECK(tvdb_mesh_sdf_generate(w, .11f, .35f, many, &a, &arena, NULL) ==
          TVDB_ERROR_INVALID_ARGUMENT);
    CHECK(!memcmp(&a, &saved, sizeof(a)) && a.data[0] == old && arena.current_offset == 0);
    tvdb_mesh_sdf_destroy(w);
    w = NULL;
    tvdb_triangle bad = {0, 1, 99};
    box.faces = &bad;
    box.face_count = 1;
    CHECK(tvdb_mesh_sdf_create(&box, &w, NULL) == TVDB_ERROR_INVALID_DATA && !w);
    tvdb_mesh_bvh_t *bvh = NULL;
    CHECK(!tvdb_mesh_bvh_build(&box, &bvh) && !bvh);
    box.faces = box_faces;
    box.face_count = 12;
    float original = box_vertices[0].x;
    box_vertices[0].x = INFINITY;
    CHECK(tvdb_mesh_sdf_create(&box, &w, NULL) == TVDB_ERROR_INVALID_DATA && !w);
    box_vertices[0].x = original;
    /* Degenerate repeated edge: distance must be to the segment, not clamped infinity. */
    tvdb_vec3f line[2] = {{0, 0, 0}, {2, 0, 0}};
    tvdb_triangle repeated = {0, 0, 1};
    tvdb_triangle_mesh deg = {line, 2, 2, &repeated, 1, 1};
    CHECK(tvdb_mesh_to_sdf_ex(&deg, .2f, .5f, many, &c, NULL, NULL) == TVDB_OK);
    for (int z = 0; z < c.nz; ++z)
        for (int y = 0; y < c.ny; ++y)
            for (int x = 0; x < c.nx; ++x) {
                tvdb_vec3f p = position(&c, x, y, z);
                float dx = p.x < 0   ? p.x
                           : p.x > 2 ? p.x - 2
                                     : 0,
                      d = fminf(.5f, sqrtf(dx * dx + p.y * p.y + p.z * p.z));
                CHECK(fabsf(c.data[index3(&c, x, y, z)] - d) < 2e-6f);
            }
    repeated = (tvdb_triangle){0, 0, 0};
    deg.vertex_count = 1;
    CHECK(tvdb_mesh_to_sdf_ex(&deg, .2f, .5f, many, &c, NULL, NULL) == TVDB_OK);
    for (int z = 0; z < c.nz; ++z)
        for (int y = 0; y < c.ny; ++y)
            for (int x = 0; x < c.nx; ++x) {
                tvdb_vec3f p = position(&c, x, y, z);
                CHECK(fabsf(c.data[index3(&c, x, y, z)] -
                            fminf(.5f, sqrtf(p.x * p.x + p.y * p.y + p.z * p.z))) < 2e-6f);
            }
    /* Outward reconstruction retains negative interior when voxelized again. */
    tvdb_triangle_mesh surface = {0};
    CHECK(tvdb_sdf_to_mesh_ex(&a, 0, TVDB_MESH_WINDING_OUTWARD, many, &surface, NULL, NULL) ==
          TVDB_OK);
    CHECK(surface.face_count > 0);
    CHECK(tvdb_mesh_to_sdf_ex(&surface, .12f, .4f, many, &c, NULL, NULL) == TVDB_OK);
    int centerx = (int)((0 - c.ox) / c.voxel_size), centery = (int)((0 - c.oy) / c.voxel_size),
        centerz = (int)((0 - c.oz) / c.voxel_size);
    CHECK(c.data[index3(&c, centerx, centery, centerz)] < 0);
    tvdb_triangle_mesh_free(&surface);
    CHECK(tvdb_make_manifold(&box, .12, 0, &surface, NULL));
    CHECK(tvdb_mesh_to_sdf_ex(&surface, .15f, .4f, many, &c, NULL, NULL) == TVDB_OK);
    centerx = (int)(-c.ox / c.voxel_size);
    centery = (int)(-c.oy / c.voxel_size);
    centerz = (int)(-c.oz / c.voxel_size);
    CHECK(c.data[index3(&c, centerx, centery, centerz)] < 0);
    CHECK(!tvdb_make_manifold(&box, NAN, 0, &surface, NULL));
    tvdb_triangle_mesh_free(&surface);
    tvdb_dense_grid_free(&a);
    tvdb_dense_grid_free(&b);
    tvdb_dense_grid_free(&c);
    return 0;
}
int main(void) {
    tvdb_thread_pool_t *one = NULL, *many = NULL;
    CHECK(tvdb_thread_pool_create(1, &one, NULL) == TVDB_OK);
    CHECK(tvdb_thread_pool_create(8, &many, NULL) == TVDB_OK);
    int bad = marching(one, many) || voxelization(one, many);
    tvdb_thread_pool_destroy(one);
    tvdb_thread_pool_destroy(many);
    return bad;
}
