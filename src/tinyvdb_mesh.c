#include "tinyvdb_mesh.h"
#include "tvdb_memory.h"
#include <string.h>
#include <stdio.h>
#include <math.h>
#include <stdlib.h>
#include <assert.h>
#include <stdint.h>

#define TVDB_MAX_GRID_DIM 2048

static const int MC_EDGE_TABLE[256] = {
  0x0  , 0x109, 0x203, 0x30a, 0x406, 0x50f, 0x605, 0x70c,
  0x80c, 0x905, 0xa0f, 0xb06, 0xc0a, 0xd03, 0xe09, 0xf00,
  0x190, 0x99 , 0x393, 0x29a, 0x596, 0x49f, 0x795, 0x69c,
  0x99c, 0x895, 0xb9f, 0xa96, 0xd9a, 0xc93, 0xf99, 0xe90,
  0x230, 0x339, 0x33 , 0x13a, 0x636, 0x73f, 0x435, 0x53c,
  0xa3c, 0xb35, 0x83f, 0x936, 0xe3a, 0xf33, 0xc39, 0xd30,
  0x3a0, 0x2a9, 0x1a3, 0xaa , 0x7a6, 0x6af, 0x5a5, 0x4ac,
  0xbac, 0xaa5, 0x9af, 0x8a6, 0xfaa, 0xea3, 0xda9, 0xca0,
  0x460, 0x569, 0x663, 0x76a, 0x66 , 0x16f, 0x265, 0x36c,
  0xc6c, 0xd65, 0xe6f, 0xf66, 0x86a, 0x963, 0xa69, 0xb60,
  0x5f0, 0x4f9, 0x7f3, 0x6fa, 0x1f6, 0xff , 0x3f5, 0x2fc,
  0xdfc, 0xcf5, 0xfff, 0xef6, 0x9fa, 0x8f3, 0xbf9, 0xaf0,
  0x650, 0x759, 0x453, 0x55a, 0x256, 0x35f, 0x55 , 0x15c,
  0xe5c, 0xf55, 0xc5f, 0xd56, 0xa5a, 0xb53, 0x859, 0x950,
  0x7c0, 0x6c9, 0x5c3, 0x4ca, 0x3c6, 0x2cf, 0x1c5, 0xcc ,
  0xfcc, 0xec5, 0xdcf, 0xcc6, 0xbca, 0xac3, 0x9c9, 0x8c0,
  0x8c0, 0x9c9, 0xac3, 0xbca, 0xcc6, 0xdcf, 0xec5, 0xfcc,
  0xcc , 0x1c5, 0x2cf, 0x3c6, 0x4ca, 0x5c3, 0x6c9, 0x7c0,
  0x950, 0x859, 0xb53, 0xa5a, 0xd56, 0xc5f, 0xf55, 0xe5c,
  0x15c, 0x55 , 0x35f, 0x256, 0x55a, 0x453, 0x759, 0x650,
  0xaf0, 0xbf9, 0x8f3, 0x9fa, 0xef6, 0xfff, 0xcf5, 0xdfc,
  0x2fc, 0x3f5, 0xff , 0x1f6, 0x6fa, 0x7f3, 0x4f9, 0x5f0,
  0xb60, 0xa69, 0x963, 0x86a, 0xf66, 0xe6f, 0xd65, 0xc6c,
  0x36c, 0x265, 0x16f, 0x66 , 0x76a, 0x663, 0x569, 0x460,
  0xca0, 0xda9, 0xea3, 0xfaa, 0x8a6, 0x9af, 0xaa5, 0xbac,
  0x4ac, 0x5a5, 0x6af, 0x7a6, 0xaa , 0x1a3, 0x2a9, 0x3a0,
  0xd30, 0xc39, 0xf33, 0xe3a, 0x936, 0x83f, 0xb35, 0xa3c,
  0x53c, 0x435, 0x73f, 0x636, 0x13a, 0x33 , 0x339, 0x230,
  0xe90, 0xf99, 0xc93, 0xd9a, 0xa96, 0xb9f, 0x895, 0x99c,
  0x69c, 0x795, 0x49f, 0x596, 0x29a, 0x393, 0x99 , 0x190,
  0xf00, 0xe09, 0xd03, 0xc0a, 0xb06, 0xa0f, 0x905, 0x80c,
  0x70c, 0x605, 0x50f, 0x406, 0x30a, 0x203, 0x109, 0x0
};

#include "tinyvdb_mc_tri_table.h"  // canonical 256-row MC triangle table

static void* arena_alloc_wrapper(tvdb_arena_allocator_t* arena, size_t size) {
    if (!arena) return malloc(size);
    return tvdb_arena_alloc(arena, size);
}

// C-compatible math helpers
static inline float dot_c(tvdb_vec3f a, tvdb_vec3f b) { return a.x * b.x + a.y * b.y + a.z * b.z; }
static inline tvdb_vec3f sub_c(tvdb_vec3f a, tvdb_vec3f b) { return (tvdb_vec3f){a.x - b.x, a.y - b.y, a.z - b.z}; }
static inline tvdb_vec3f add_c(tvdb_vec3f a, tvdb_vec3f b) { return (tvdb_vec3f){a.x + b.x, a.y + b.y, a.z + b.z}; }
static inline tvdb_vec3f mul_c(tvdb_vec3f a, float s) { return (tvdb_vec3f){a.x * s, a.y * s, a.z * s}; }
static float dist_sq_c(tvdb_vec3f a, tvdb_vec3f b) { tvdb_vec3f d = sub_c(a, b); return dot_c(d, d); }
static float point_triangle_dist_sq_c(tvdb_vec3f p, tvdb_vec3f a, tvdb_vec3f b, tvdb_vec3f c) {
  tvdb_vec3f ab = sub_c(b, a), ac = sub_c(c, a), ap = sub_c(p, a);
  float d1 = dot_c(ab, ap), d2 = dot_c(ac, ap);
  if (d1 <= 0.0f && d2 <= 0.0f) return dist_sq_c(p, a);
  tvdb_vec3f bp = sub_c(p, b);
  float d3 = dot_c(ab, bp), d4 = dot_c(ac, bp);
  if (d3 >= 0.0f && d4 <= d3) return dist_sq_c(p, b);
  float vc = d1 * d4 - d3 * d2;
  if (vc <= 0.0f && d1 >= 0.0f && d3 <= 0.0f) {
    float v = d1 / (d1 - d3);
    return dist_sq_c(p, add_c(a, mul_c(ab, v)));
  }
  tvdb_vec3f cp = sub_c(p, c);
  float d5 = dot_c(ab, cp), d6 = dot_c(ac, cp);
  if (d6 >= 0.0f && d5 <= d6) return dist_sq_c(p, c);
  float vb = d5 * d2 - d1 * d6;
  if (vb <= 0.0f && d2 >= 0.0f && d6 <= 0.0f) {
    float w = d2 / (d2 - d6);
    return dist_sq_c(p, add_c(a, mul_c(ac, w)));
  }
  float va = d3 * d6 - d5 * d4;
  if (va <= 0.0f && (d4 - d3) >= 0.0f && (d5 - d6) >= 0.0f) {
    float w = (d4 - d3) / ((d4 - d3) + (d5 - d6));
    return dist_sq_c(p, add_c(b, mul_c(sub_c(c, b), w)));
  }
  float denom = 1.0f / (va + vb + vc);
  return dist_sq_c(p, add_c(add_c(a, mul_c(ab, vb * denom)), mul_c(ac, vc * denom)));
}

// VoxelPos, VoxelIdx, EdgeKey
static tvdb_vec3f voxel_pos_c(const tvdb_dense_grid* grid, int ix, int iy, int iz) {
    return (tvdb_vec3f){grid->ox + (ix + 0.5f) * grid->voxel_size,
                        grid->oy + (iy + 0.5f) * grid->voxel_size,
                        grid->oz + (iz + 0.5f) * grid->voxel_size};
}

static uint64_t voxel_idx_c(int nx, int ny, int ix, int iy, int iz) {
    return (uint64_t)ix + (uint64_t)iy * nx + (uint64_t)iz * nx * ny;
}

static uint64_t edge_key_c(uint64_t v0, uint64_t v1) {
    if (v0 > v1) { uint64_t temp = v0; v0 = v1; v1 = temp; }
    return (v0 << 32) | v1;
}

// Edge Cache — open-addressing hash map keyed on the 64-bit edge key, mapping
// each shared cube edge to its (deduplicated) output-vertex index. Replaces a
// former linear scan that made meshing O(n^2); lookups are now O(1) amortized.
//
// edge_key_c packs two *distinct* voxel indices as (min << 32) | max with the
// larger in the low word, so a valid edge key is always >= 1 — we can use
// key == 0 as the empty-slot sentinel.
typedef struct {
    uint64_t key;
    uint32_t value;
} edge_cache_entry_t;

typedef struct {
    edge_cache_entry_t* entries;
    size_t count;
    size_t capacity;   // power of two
    size_t mask;       // capacity - 1
} edge_cache_t;

static inline uint64_t edge_hash_u64(uint64_t x) {
    x ^= x >> 33; x *= 0xff51afd7ed558ccdULL;
    x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL;
    x ^= x >> 33;
    return x;
}

static void edge_cache_init(edge_cache_t* cache, tvdb_arena_allocator_t* arena) {
    cache->count = 0;
    cache->capacity = 1024;
    cache->mask = cache->capacity - 1;
    cache->entries = (edge_cache_entry_t*)arena_alloc_wrapper(arena, cache->capacity * sizeof(edge_cache_entry_t));
    if (cache->entries) memset(cache->entries, 0, cache->capacity * sizeof(edge_cache_entry_t));
}

// Double the table and rehash all live entries. Returns 0 on alloc failure.
static int edge_cache_grow(edge_cache_t* cache, tvdb_arena_allocator_t* arena) {
    size_t new_cap = cache->capacity ? cache->capacity * 2 : 1024;
    size_t new_mask = new_cap - 1;
    edge_cache_entry_t* ne = (edge_cache_entry_t*)arena_alloc_wrapper(arena, new_cap * sizeof(edge_cache_entry_t));
    if (!ne) return 0;
    memset(ne, 0, new_cap * sizeof(edge_cache_entry_t));
    for (size_t k = 0; k < cache->capacity; ++k) {
        uint64_t key = cache->entries[k].key;
        if (key == 0) continue;
        size_t i = edge_hash_u64(key) & new_mask;
        while (ne[i].key != 0) i = (i + 1) & new_mask;
        ne[i] = cache->entries[k];
    }
    if (!arena && cache->entries) free(cache->entries);
    cache->entries = ne;
    cache->capacity = new_cap;
    cache->mask = new_mask;
    return 1;
}

// Vertex Interpolation
static tvdb_vec3f vertex_interp_c(float iso, tvdb_vec3f p1, tvdb_vec3f p2, float v1, float v2) {
  if (fabsf(v1 - v2) < 1e-10f) return p1;
  float mu = (iso - v1) / (v2 - v1);
  return (tvdb_vec3f){p1.x + mu * (p2.x - p1.x), p1.y + mu * (p2.y - p1.y), p1.z + mu * (p2.z - p1.z)};
}

// C-compatible Edge Vertex Creation
static uint32_t get_or_create_edge_vertex_c(edge_cache_t* cache, tvdb_arena_allocator_t* arena,
                                            const tvdb_dense_grid* grid, float isovalue,
                                            tvdb_triangle_mesh* mesh,
                                            int x0, int y0, int z0, int x1, int y1, int z1) {
    uint64_t v0_flat = voxel_idx_c(grid->nx, grid->ny, x0, y0, z0);
    uint64_t v1_flat = voxel_idx_c(grid->nx, grid->ny, x1, y1, z1);
    uint64_t edge_key = edge_key_c(v0_flat, v1_flat);

    // Keep the load factor under ~0.7. Grow before probing so the slot we
    // settle on below stays valid.
    if ((cache->count + 1) * 10 >= cache->capacity * 7)
        if (!edge_cache_grow(cache, arena)) return 0;

    size_t i = edge_hash_u64(edge_key) & cache->mask;
    while (cache->entries[i].key != 0) {
        if (cache->entries[i].key == edge_key) return cache->entries[i].value;
        i = (i + 1) & cache->mask;
    }

    // Not cached: interpolate the new vertex, append it, and record the slot.
    tvdb_vec3f p0 = voxel_pos_c(grid, x0, y0, z0);
    tvdb_vec3f p1 = voxel_pos_c(grid, x1, y1, z1);
    tvdb_vec3f p = vertex_interp_c(isovalue, p0, p1, grid->data[v0_flat], grid->data[v1_flat]);

    uint32_t idx = (uint32_t)mesh->vertex_count;
    if (mesh->vertex_count == mesh->vertex_capacity) {
        size_t new_cap = mesh->vertex_capacity ? mesh->vertex_capacity * 2 : 64;
        tvdb_vec3f* new_verts = (tvdb_vec3f*)arena_alloc_wrapper(arena, new_cap * sizeof(tvdb_vec3f));
        if (!new_verts) return 0;
        if (mesh->vertices) memcpy(new_verts, mesh->vertices, mesh->vertex_count * sizeof(tvdb_vec3f));
        if (!arena && mesh->vertices) free(mesh->vertices);
        mesh->vertices = new_verts;
        mesh->vertex_capacity = new_cap;
    }
    mesh->vertices[mesh->vertex_count++] = p;

    cache->entries[i].key = edge_key;
    cache->entries[i].value = idx;
    cache->count++;
    return idx;
}

// -------------------------------------------------------------------------
// SDF -> mesh (marching cubes)
// -------------------------------------------------------------------------

// Marching-cubes corner-of-cube offsets and edge endpoint table.
static const int MC_CORNER_OFFSETS[8][3] = {
    {0,0,0},{1,0,0},{1,1,0},{0,1,0},
    {0,0,1},{1,0,1},{1,1,1},{0,1,1}
};

// MC edge -> (corner_a, corner_b) using the canonical lookup-table indexing.
static const int MC_EDGE_VERTS[12][2] = {
    {0,1},{1,2},{2,3},{3,0},
    {4,5},{5,6},{6,7},{7,4},
    {0,4},{1,5},{2,6},{3,7}
};

static bool ensure_mesh_capacity(tvdb_triangle_mesh* mesh,
                                 tvdb_arena_allocator_t* arena,
                                 size_t need_verts, size_t need_faces) {
    if (mesh->vertex_capacity < need_verts) {
        size_t cap = mesh->vertex_capacity ? mesh->vertex_capacity : 64;
        while (cap < need_verts) cap *= 2;
        tvdb_vec3f* nv = (tvdb_vec3f*)arena_alloc_wrapper(arena, cap * sizeof(tvdb_vec3f));
        if (!nv) return false;
        if (mesh->vertices) memcpy(nv, mesh->vertices, mesh->vertex_count * sizeof(tvdb_vec3f));
        // arena-backed memory is not freed; for malloc fall back, leak the
        // old buffer if arena==NULL (callers using malloc should size up-front).
        if (!arena && mesh->vertices) free(mesh->vertices);
        mesh->vertices = nv;
        mesh->vertex_capacity = cap;
    }
    if (mesh->face_capacity < need_faces) {
        size_t cap = mesh->face_capacity ? mesh->face_capacity : 64;
        while (cap < need_faces) cap *= 2;
        tvdb_triangle* nf = (tvdb_triangle*)arena_alloc_wrapper(arena, cap * sizeof(tvdb_triangle));
        if (!nf) return false;
        if (mesh->faces) memcpy(nf, mesh->faces, mesh->face_count * sizeof(tvdb_triangle));
        if (!arena && mesh->faces) free(mesh->faces);
        mesh->faces = nf;
        mesh->face_capacity = cap;
    }
    return true;
}

const int* tvdb_mc_edge_table(void) { return MC_EDGE_TABLE; }
const int* tvdb_mc_tri_table_flat(void) { return (const int*)MC_TRI_TABLE; }

bool tvdb_sdf_to_mesh(const tvdb_dense_grid* grid, float isovalue,
                      tvdb_triangle_mesh* mesh, tvdb_arena_allocator_t* arena) {
    if (!grid || !grid->data || !mesh) return false;
    if (grid->nx < 2 || grid->ny < 2 || grid->nz < 2) return false;

    // The cache is keyed by edge-key (sorted pair of voxel flat indices); it
    // dedupes vertices that lie on shared cube edges.
    edge_cache_t cache;
    edge_cache_init(&cache, arena);

    // Pre-size the mesh buffers conservatively to avoid many reallocs.
    size_t init_verts = (size_t)grid->nx * grid->ny;
    size_t init_faces = init_verts * 2;
    if (mesh->vertex_capacity == 0) {
        if (!ensure_mesh_capacity(mesh, arena, init_verts, init_faces)) return false;
    }

    const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
    for (int z = 0; z < nz - 1; ++z) {
      for (int y = 0; y < ny - 1; ++y) {
        for (int x = 0; x < nx - 1; ++x) {
            float vals[8];
            int corner_xyz[8][3];
            int cube_idx = 0;
            for (int i = 0; i < 8; ++i) {
                int cx = x + MC_CORNER_OFFSETS[i][0];
                int cy = y + MC_CORNER_OFFSETS[i][1];
                int cz = z + MC_CORNER_OFFSETS[i][2];
                corner_xyz[i][0] = cx;
                corner_xyz[i][1] = cy;
                corner_xyz[i][2] = cz;
                vals[i] = grid->data[voxel_idx_c(nx, ny, cx, cy, cz)];
                if (vals[i] < isovalue) cube_idx |= (1 << i);
            }
            int edges = MC_EDGE_TABLE[cube_idx];
            if (edges == 0) continue;

            // Compute (or fetch from cache) one vertex per active edge.
            uint32_t edge_vert_idx[12] = {0};
            for (int e = 0; e < 12; ++e) {
                if (!(edges & (1 << e))) continue;
                int a = MC_EDGE_VERTS[e][0];
                int b = MC_EDGE_VERTS[e][1];
                edge_vert_idx[e] = get_or_create_edge_vertex_c(
                    &cache, arena, grid, isovalue, mesh,
                    corner_xyz[a][0], corner_xyz[a][1], corner_xyz[a][2],
                    corner_xyz[b][0], corner_xyz[b][1], corner_xyz[b][2]);
            }

            // Emit triangles for this cube.
            const int* tri = MC_TRI_TABLE[cube_idx];
            for (int i = 0; i < 16 && tri[i] != -1; i += 3) {
                if (tri[i+1] == -1 || tri[i+2] == -1) break;
                if (mesh->face_count == mesh->face_capacity) {
                    if (!ensure_mesh_capacity(mesh, arena,
                            mesh->vertex_capacity,
                            mesh->face_capacity ? mesh->face_capacity * 2 : 64))
                        return false;
                }
                tvdb_triangle t;
                t.v0 = edge_vert_idx[tri[i]];
                t.v1 = edge_vert_idx[tri[i+1]];
                t.v2 = edge_vert_idx[tri[i+2]];
                mesh->faces[mesh->face_count++] = t;
            }
        }
      }
    }
    return true;
}

// -------------------------------------------------------------------------
// Mesh -> SDF (closest-triangle, signed via face normal)
// -------------------------------------------------------------------------
//
// For each voxel, compute distance to nearest triangle; sign comes from
// dot((voxel - closest_point), triangle_normal). This is the classic
// "pseudo-normal-free" approach: simple, robust for moderately well-formed
// closed meshes, but can have sign artifacts at sharp edges/vertices.
//
// Distance is clamped to ±band_width.

static tvdb_vec3f tri_closest_point_c(tvdb_vec3f p, tvdb_vec3f a, tvdb_vec3f b, tvdb_vec3f c) {
    // Same case analysis as point_triangle_dist_sq_c, but returning the point.
    tvdb_vec3f ab = sub_c(b, a), ac = sub_c(c, a), ap = sub_c(p, a);
    float d1 = dot_c(ab, ap), d2 = dot_c(ac, ap);
    if (d1 <= 0.0f && d2 <= 0.0f) return a;
    tvdb_vec3f bp = sub_c(p, b);
    float d3 = dot_c(ab, bp), d4 = dot_c(ac, bp);
    if (d3 >= 0.0f && d4 <= d3) return b;
    float vc = d1 * d4 - d3 * d2;
    if (vc <= 0.0f && d1 >= 0.0f && d3 <= 0.0f) {
        float v = d1 / (d1 - d3);
        return add_c(a, mul_c(ab, v));
    }
    tvdb_vec3f cp = sub_c(p, c);
    float d5 = dot_c(ab, cp), d6 = dot_c(ac, cp);
    if (d6 >= 0.0f && d5 <= d6) return c;
    float vb = d5 * d2 - d1 * d6;
    if (vb <= 0.0f && d2 >= 0.0f && d6 <= 0.0f) {
        float w = d2 / (d2 - d6);
        return add_c(a, mul_c(ac, w));
    }
    float va = d3 * d6 - d5 * d4;
    if (va <= 0.0f && (d4 - d3) >= 0.0f && (d5 - d6) >= 0.0f) {
        float w = (d4 - d3) / ((d4 - d3) + (d5 - d6));
        return add_c(b, mul_c(sub_c(c, b), w));
    }
    float denom = 1.0f / (va + vb + vc);
    return add_c(add_c(a, mul_c(ab, vb * denom)), mul_c(ac, vc * denom));
}

static tvdb_vec3f cross_c(tvdb_vec3f a, tvdb_vec3f b) {
    return (tvdb_vec3f){a.y * b.z - a.z * b.y,
                        a.z * b.x - a.x * b.z,
                        a.x * b.y - a.y * b.x};
}

static tvdb_vec3f normalize_c(tvdb_vec3f v) {
    float L = sqrtf(dot_c(v, v));
    if (L < 1e-30f) return (tvdb_vec3f){0, 0, 0};
    return mul_c(v, 1.0f / L);
}

// -------------------------------------------------------------------------
// BVH over mesh triangles
// -------------------------------------------------------------------------
//
// tvdb_mesh_to_sdf evaluates every voxel against every triangle, which is
// O(voxels * faces): a 64^3 grid over a marching-cubes sphere took 63
// seconds. A bounding volume hierarchy over the triangle set makes the query
// near-O(log n) on average and is the single largest win available here.
//
// Two properties are preserved exactly so results stay bit-identical:
//
//  * The brute-force loop accepts a triangle only on a *strictly* smaller
//    squared distance (`dsq < best_dsq`), so when two faces are exactly
//    equidistant the lower face index wins. The traversal below uses the same
//    strict test plus an explicit tie-break on the lower face index, so the
//    chosen triangle -- and hence both the distance and the sign -- matches
//    the brute-force result exactly.
//  * Node bounds are only ever used to *prune*. A node is skipped solely when
//    its lower bound already exceeds the current best, so a loose bound can
//    cost time but can never change the answer.

/* The node type is public (tinyvdb_mesh.h) because the GPU backend uploads these
 * verbatim and walks them in a shader. One definition, so the two cannot drift. */
_Static_assert(sizeof(tvdb_mesh_bvh_node_t) == 40,
               "BVH node must stay 40 bytes: it is uploaded as a std430 struct");
typedef tvdb_mesh_bvh_node_t tvdb_bvh_node_t;

typedef struct {
    int32_t *prim;              /* face indices, partitioned by the build */
    int32_t prim_count;
    tvdb_bvh_node_t *nodes;
    int32_t node_count;
    int32_t node_capacity;
    int32_t max_depth;
    float *tri_bmin;            /* 3 floats per face */
    float *tri_bmax;
} tvdb_bvh_t;

struct tvdb_mesh_bvh { tvdb_bvh_t b; };

static void tvdb_bvh_free(tvdb_bvh_t *b) {
    if (!b) return;
    free(b->prim);
    free(b->nodes);
    free(b->tri_bmin);
    free(b->tri_bmax);
    memset(b, 0, sizeof(*b));
}

static int32_t tvdb_bvh_new_node(tvdb_bvh_t *b) {
    if (b->node_count >= b->node_capacity) {
        int32_t new_cap = b->node_capacity ? b->node_capacity * 2 : 256;
        tvdb_bvh_node_t *n = (tvdb_bvh_node_t *)realloc(
            b->nodes, (size_t)new_cap * sizeof(*n));
        if (!n) return -1;
        b->nodes = n;
        b->node_capacity = new_cap;
    }
    int32_t idx = b->node_count++;
    tvdb_bvh_node_t *nd = &b->nodes[idx];
    nd->left = -1; nd->right = -1; nd->start = 0; nd->count = 0;
    return idx;
}

static inline float tvdb_aabb_dist_sq(const float *bmin, const float *bmax,
                                     const tvdb_vec3f *p) {
    const float v[3] = { p->x, p->y, p->z };
    float d2 = 0.0f;
    for (int a = 0; a < 3; ++a) {
        if (v[a] < bmin[a]) { float t = bmin[a] - v[a]; d2 += t * t; }
        else if (v[a] > bmax[a]) { float t = v[a] - bmax[a]; d2 += t * t; }
    }
    return d2;
}

/* Split [lo,hi) of b->prim at the median centroid on the widest axis.
 *
 * A binned surface-area heuristic and a Morton-ordered midpoint split were
 * both implemented and measured; neither beat this. SAH scored planes against
 * triangle AABB centroids, and for a level-set shell every centroid sits on the
 * same thin surface, so the bins carry no information. Morton ordering groups
 * space well but its balanced midpoint split produces long, thin boxes across
 * the shell. The median split wins because the resulting node boxes stay
 * compact even though the ordering ignores that structure.
 *
 * Returns a split point strictly inside the range. */
static int32_t tvdb_bvh_split(tvdb_bvh_t *b, int32_t lo, int32_t hi) {
    float cmin[3] = { INFINITY, INFINITY, INFINITY };
    float cmax[3] = { -INFINITY, -INFINITY, -INFINITY };
    for (int32_t i = lo; i < hi; ++i) {
        int32_t f = b->prim[i];
        for (int a = 0; a < 3; ++a) {
            float c = 0.5f * (b->tri_bmin[(size_t)f * 3 + a] +
                              b->tri_bmax[(size_t)f * 3 + a]);
            if (c < cmin[a]) cmin[a] = c;
            if (c > cmax[a]) cmax[a] = c;
        }
    }
    int axis = 0;
    float widest = cmax[0] - cmin[0];
    for (int a = 1; a < 3; ++a) {
        float e = cmax[a] - cmin[a];
        if (e > widest) { widest = e; axis = a; }
    }
    if (!(widest > 0.0f)) return lo + 1;   /* all centroids coincide */

    int32_t mid = lo + (hi - lo) / 2;
    int32_t mf = b->prim[mid];
    float pivot = 0.5f * (b->tri_bmin[(size_t)mf * 3 + axis] +
                          b->tri_bmax[(size_t)mf * 3 + axis]);
    int32_t i = lo, j = hi - 1;
    for (;;) {
        while (i < hi) {
            int32_t f = b->prim[i];
            float c = 0.5f * (b->tri_bmin[(size_t)f * 3 + axis] +
                              b->tri_bmax[(size_t)f * 3 + axis]);
            if (!(c < pivot)) break;
            i++;
        }
        while (j > lo) {
            int32_t f = b->prim[j];
            float c = 0.5f * (b->tri_bmin[(size_t)f * 3 + axis] +
                              b->tri_bmax[(size_t)f * 3 + axis]);
            if (!(c > pivot)) break;
            j--;
        }
        if (i >= j) break;
        int32_t t = b->prim[i]; b->prim[i] = b->prim[j]; b->prim[j] = t;
        i++; j--;
    }
    int32_t split = i;
    if (split <= lo) split = lo + 1;
    if (split >= hi) split = hi - 1;
    return split;
}

/* Recursively build a node covering [lo,hi). Returns its index, or -1 on OOM.
 * Node indices are stable because the array only grows and existing entries
 * are never moved. */
static int32_t tvdb_bvh_build(tvdb_bvh_t *b, int32_t lo, int32_t hi, int depth) {
    int32_t self = tvdb_bvh_new_node(b);
    if (self < 0) return -1;

    float nmin[3] = { INFINITY, INFINITY, INFINITY };
    float nmax[3] = { -INFINITY, -INFINITY, -INFINITY };
    for (int32_t i = lo; i < hi; ++i) {
        int32_t f = b->prim[i];
        for (int a = 0; a < 3; ++a) {
            float l0 = b->tri_bmin[(size_t)f * 3 + a];
            float h0 = b->tri_bmax[(size_t)f * 3 + a];
            if (l0 < nmin[a]) nmin[a] = l0;
            if (h0 > nmax[a]) nmax[a] = h0;
        }
    }
    for (int a = 0; a < 3; ++a) {
        b->nodes[self].bmin[a] = nmin[a];
        b->nodes[self].bmax[a] = nmax[a];
    }

    int32_t n = hi - lo;
    /* Small leaves, or exhausted depth, become leaves. The depth cap also
     * bounds the traversal stack in tvdb_bvh_closest to 64+1 entries. */
    if (n <= 4 || depth >= 64) {
        b->nodes[self].start = lo;
        b->nodes[self].count = n;
        if (depth > b->max_depth) b->max_depth = depth;
        return self;
    }

    int32_t split = tvdb_bvh_split(b, lo, hi);
    int32_t l = tvdb_bvh_build(b, lo, split, depth + 1);
    if (l < 0) return -1;
    int32_t r = tvdb_bvh_build(b, split, hi, depth + 1);
    if (r < 0) return -1;
    b->nodes[self].left = l;
    b->nodes[self].right = r;
    return self;
}

/* Build the hierarchy over all `nf` faces of `mesh`. Returns 0 on success. */
static int tvdb_bvh_init(tvdb_bvh_t *b, const tvdb_triangle_mesh *mesh, size_t nf) {
    memset(b, 0, sizeof(*b));
    if (nf == 0) return -1;
    if (nf > (size_t)INT32_MAX) return -1;
    b->prim_count = (int32_t)nf;

    b->prim = (int32_t *)malloc(nf * sizeof(int32_t));
    b->tri_bmin = (float *)malloc(nf * 3 * sizeof(float));
    b->tri_bmax = (float *)malloc(nf * 3 * sizeof(float));
    if (!b->prim || !b->tri_bmin || !b->tri_bmax) { tvdb_bvh_free(b); return -1; }

    for (size_t f = 0; f < nf; ++f) {
        b->prim[f] = (int32_t)f;
        const tvdb_triangle *face = &mesh->faces[f];
        float lo[3], hi[3];
        /* Derive the bounds from the three corners the distance routine will
         * actually use, so a degenerate face (repeated index, NaN-free) still
         * produces a well-defined box. */
        const uint32_t vi[3] = { face->v0, face->v1, face->v2 };
        for (int a = 0; a < 3; ++a) { lo[a] = INFINITY; hi[a] = -INFINITY; }
        for (int c = 0; c < 3; ++c) {
            const tvdb_vec3f *v = &mesh->vertices[vi[c]];
            float xyz[3] = { v->x, v->y, v->z };
            for (int a = 0; a < 3; ++a) {
                if (xyz[a] < lo[a]) lo[a] = xyz[a];
                if (xyz[a] > hi[a]) hi[a] = xyz[a];
            }
        }
        for (int a = 0; a < 3; ++a) {
            b->tri_bmin[f * 3 + a] = lo[a];
            b->tri_bmax[f * 3 + a] = hi[a];
        }
    }

    int32_t root = tvdb_bvh_build(b, 0, (int32_t)nf, 0);
    if (root < 0) { tvdb_bvh_free(b); return -1; }
    return 0;
}

/* ---- public BVH accessors -------------------------------------------------
 *
 * Heap-wrapped so a caller can hold one for the lifetime of a GPU job and free
 * it deterministically; the query inside tvdb_mesh_to_sdf still builds on the
 * stack, as it did before. */
bool tvdb_mesh_bvh_build(const tvdb_triangle_mesh* mesh, tvdb_mesh_bvh_t** out) {
    if (!out) return false;
    *out = NULL;
    if (!mesh || mesh->face_count == 0) return false;
    tvdb_mesh_bvh_t* h = (tvdb_mesh_bvh_t*)calloc(1, sizeof(*h));
    if (!h) return false;
    if (tvdb_bvh_init(&h->b, mesh, mesh->face_count) != 0) { free(h); return false; }
    *out = h;
    return true;
}

void tvdb_mesh_bvh_destroy(tvdb_mesh_bvh_t* h) {
    if (!h) return;
    tvdb_bvh_free(&h->b);
    free(h);
}

int32_t     tvdb_mesh_bvh_node_count(const tvdb_mesh_bvh_t* h) { return h ? h->b.node_count : 0; }
int32_t     tvdb_mesh_bvh_prim_count(const tvdb_mesh_bvh_t* h) { return h ? h->b.prim_count : 0; }
int32_t     tvdb_mesh_bvh_max_depth(const tvdb_mesh_bvh_t* h) { return h ? h->b.max_depth : 0; }
const tvdb_mesh_bvh_node_t* tvdb_mesh_bvh_nodes(const tvdb_mesh_bvh_t* h) { return h ? h->b.nodes : NULL; }
const int32_t* tvdb_mesh_bvh_prims(const tvdb_mesh_bvh_t* h) { return h ? h->b.prim : NULL; }

/* Closest face to `p`, by squared distance. On return `*out_cp` is the
 * closest point and `*out_n` that face's normal, mirroring the brute-force
 * loop's initialization exactly: if no face is ever accepted (which happens
 * when every candidate distance is NaN, e.g. a mesh of zero-area triangles),
 * both stay {0,0,0} and the caller produces the same signed value it always
 * did. Recomputing the closest point from `best_face` would instead yield NaN
 * and flip the sign at those voxels. */
static float tvdb_bvh_closest(const tvdb_bvh_t *b,
                              const tvdb_triangle_mesh *mesh,
                              const tvdb_vec3f *tri_n,
                              tvdb_vec3f p,
                              tvdb_vec3f *out_cp, tvdb_vec3f *out_n) {
    float best_dsq = INFINITY;
    int32_t best_face = -1;
    tvdb_vec3f best_cp = { 0, 0, 0 };
    tvdb_vec3f best_n  = { 0, 0, 0 };

    /* Explicit stack of (node index, lower-bound distance).
     *
     * A binary DFS pops one node and pushes at most two, so the stack can
     * never hold more than tree_depth + 1 entries. The builder caps depth at
     * 64, so 128 is a comfortable margin and the `sp < 126` guards below are
     * unreachable in practice -- but they are written to leave the traversal
     * safe (never out of bounds) rather than to silently corrupt results. */
    int32_t stack_node[128];
    float  stack_d[128];
    int sp = 0;

    stack_node[sp] = 0;
    stack_d[sp] = 0.0f;
    sp++;

    while (sp > 0) {
        sp--;
        int32_t ni = stack_node[sp];
        float nd = stack_d[sp];
        /* Prune only when the subtree provably cannot match the current best.
         *
         * The test must be strict `>`, not `>=`. The brute-force original keeps
         * the *lowest* face index among exact ties, so a triangle sitting at
         * exactly best_dsq can still improve the result by having a smaller
         * index. Pruning on equality would silently drop those. (The bound is
         * inclusive of the node's own surface, so equality is reachable.) */
        if (nd > best_dsq) continue;
        const tvdb_bvh_node_t *node = &b->nodes[ni];

        if (node->left < 0) {
            for (int32_t k = 0; k < node->count; ++k) {
                int32_t f = b->prim[node->start + k];
                const tvdb_triangle *face = &mesh->faces[f];
                tvdb_vec3f a = mesh->vertices[face->v0];
                tvdb_vec3f bv = mesh->vertices[face->v1];
                tvdb_vec3f c = mesh->vertices[face->v2];
                tvdb_vec3f cp = tri_closest_point_c(p, a, bv, c);
                tvdb_vec3f d = sub_c(p, cp);
                float dsq = dot_c(d, d);
                /* Strict `<` mirrors the original loop; the index tie-break
                 * reproduces "lowest face index wins" for exact ties. */
                if (dsq < best_dsq || (dsq == best_dsq && f < best_face)) {
                    best_dsq = dsq;
                    best_face = f;
                    best_cp = cp;
                    best_n = tri_n[f];
                }
            }
        } else {
            int32_t l = node->left, r = node->right;
            float dl = tvdb_aabb_dist_sq(b->nodes[l].bmin, b->nodes[l].bmax, &p);
            float dr = tvdb_aabb_dist_sq(b->nodes[r].bmin, b->nodes[r].bmax, &p);
            /* Same inclusive test as the pop: an equidistant subtree may hold
             * a lower-indexed triangle. Push the farther child first so the
             * nearer one is examined next. */
            if (dl <= dr) {
                if (dr <= best_dsq && sp < 126) {
                    stack_node[sp] = r; stack_d[sp] = dr; sp++;
                }
                if (dl <= best_dsq && sp < 126) {
                    stack_node[sp] = l; stack_d[sp] = dl; sp++;
                }
            } else {
                if (dl <= best_dsq && sp < 126) {
                    stack_node[sp] = l; stack_d[sp] = dl; sp++;
                }
                if (dr <= best_dsq && sp < 126) {
                    stack_node[sp] = r; stack_d[sp] = dr; sp++;
                }
            }
        }
    }
    (void)best_face;
    *out_cp = best_cp;
    *out_n = best_n;
    return best_dsq;
}

bool tvdb_mesh_to_sdf(const tvdb_triangle_mesh* mesh, float voxel_size,
                      float band_width, tvdb_dense_grid* grid,
                      tvdb_arena_allocator_t* arena) {
    if (!mesh || !grid || mesh->vertex_count == 0 || mesh->face_count == 0) return false;
    if (voxel_size <= 0.0f || band_width <= 0.0f) return false;

    // World-space bounding box of the mesh, padded by band_width.
    tvdb_vec3f bb_min = mesh->vertices[0], bb_max = mesh->vertices[0];
    for (size_t i = 1; i < mesh->vertex_count; ++i) {
        tvdb_vec3f v = mesh->vertices[i];
        if (v.x < bb_min.x) bb_min.x = v.x; if (v.x > bb_max.x) bb_max.x = v.x;
        if (v.y < bb_min.y) bb_min.y = v.y; if (v.y > bb_max.y) bb_max.y = v.y;
        if (v.z < bb_min.z) bb_min.z = v.z; if (v.z > bb_max.z) bb_max.z = v.z;
    }
    bb_min.x -= band_width; bb_min.y -= band_width; bb_min.z -= band_width;
    bb_max.x += band_width; bb_max.y += band_width; bb_max.z += band_width;

    int nx = (int)ceilf((bb_max.x - bb_min.x) / voxel_size);
    int ny = (int)ceilf((bb_max.y - bb_min.y) / voxel_size);
    int nz = (int)ceilf((bb_max.z - bb_min.z) / voxel_size);
    if (nx < 1) nx = 1; if (ny < 1) ny = 1; if (nz < 1) nz = 1;
    if (nx > TVDB_MAX_GRID_DIM || ny > TVDB_MAX_GRID_DIM || nz > TVDB_MAX_GRID_DIM)
        return false;

    grid->nx = nx; grid->ny = ny; grid->nz = nz;
    grid->voxel_size = voxel_size;
    grid->ox = bb_min.x; grid->oy = bb_min.y; grid->oz = bb_min.z;
    size_t total = (size_t)nx * ny * nz;
    grid->data = (float*)arena_alloc_wrapper(arena, total * sizeof(float));
    if (!grid->data) return false;

    // Pre-compute triangle data for speed.
    size_t nf = mesh->face_count;
    tvdb_vec3f* tri_n = (tvdb_vec3f*)arena_alloc_wrapper(arena, nf * sizeof(tvdb_vec3f));
    if (!tri_n) return false;
    for (size_t f = 0; f < nf; ++f) {
        tvdb_vec3f a = mesh->vertices[mesh->faces[f].v0];
        tvdb_vec3f b = mesh->vertices[mesh->faces[f].v1];
        tvdb_vec3f c = mesh->vertices[mesh->faces[f].v2];
        tri_n[f] = normalize_c(cross_c(sub_c(b, a), sub_c(c, a)));
    }

    // Accelerate the nearest-face query with a BVH. If the build fails for any
    // reason (OOM, degenerate input) we fall back to the original exhaustive
    // scan, which produces identical values.
    tvdb_bvh_t bvh;
    int use_bvh = (tvdb_bvh_init(&bvh, mesh, nf) == 0);

    /* Every voxel is independent and the BVH is read-only once built, so the
     * fill parallelizes directly. `collapse(2)` over (z,y) keeps the x loop
     * contiguous, which is the access pattern the traversal wants. */
    #pragma omp parallel for collapse(2) schedule(static)
    for (int z = 0; z < nz; ++z) {
      for (int y = 0; y < ny; ++y) {
        for (int x = 0; x < nx; ++x) {
            tvdb_vec3f p = voxel_pos_c(grid, x, y, z);
            float best_dsq = INFINITY;
            tvdb_vec3f best_cp = {0, 0, 0};
            tvdb_vec3f best_n  = {0, 0, 0};
            if (use_bvh) {
                best_dsq = tvdb_bvh_closest(&bvh, mesh, tri_n, p, &best_cp, &best_n);
            } else {
                for (size_t f = 0; f < nf; ++f) {
                    tvdb_vec3f a = mesh->vertices[mesh->faces[f].v0];
                    tvdb_vec3f b = mesh->vertices[mesh->faces[f].v1];
                    tvdb_vec3f c = mesh->vertices[mesh->faces[f].v2];
                    tvdb_vec3f cp = tri_closest_point_c(p, a, b, c);
                    tvdb_vec3f d = sub_c(p, cp);
                    float dsq = dot_c(d, d);
                    if (dsq < best_dsq) {
                        best_dsq = dsq;
                        best_cp = cp;
                        best_n = tri_n[f];
                    }
                }
            }
            float dist = sqrtf(best_dsq);
            float s = dot_c(sub_c(p, best_cp), best_n) >= 0.0f ? 1.0f : -1.0f;
            float v = s * dist;
            if (v >  band_width) v =  band_width;
            if (v < -band_width) v = -band_width;
            grid->data[voxel_idx_c(nx, ny, x, y, z)] = v;
        }
      }
    }
    if (use_bvh) tvdb_bvh_free(&bvh);
    return true;
}

// -------------------------------------------------------------------------
// Mesh -> SDF -> Mesh (remeshing for manifold-ness)
// -------------------------------------------------------------------------

bool tvdb_make_manifold(const tvdb_triangle_mesh* input, double resolution,
                        double isovalue, tvdb_triangle_mesh* output,
                        tvdb_arena_allocator_t* arena) {
    if (!input || !output || resolution <= 0.0) return false;

    tvdb_dense_grid grid;
    grid.data = NULL;
    float band = (float)(resolution * 4.0);
    if (!tvdb_mesh_to_sdf(input, (float)resolution, band, &grid, arena)) return false;
    bool ok = tvdb_sdf_to_mesh(&grid, (float)isovalue, output, arena);
    if (!arena) tvdb_dense_grid_free(&grid);
    return ok;
}

// -------------------------------------------------------------------------
// _vdb variants (sign_method is currently advisory; the implementation uses
// closest-triangle pseudo-normal sign regardless).
// -------------------------------------------------------------------------

bool tvdb_mesh_to_sdf_vdb(const tvdb_triangle_mesh* mesh, float voxel_size,
                          float band_width, tvdb_dense_grid* grid,
                          tvdb_sign_method sign_method,
                          tvdb_arena_allocator_t* arena) {
    (void)sign_method;
    return tvdb_mesh_to_sdf(mesh, voxel_size, band_width, grid, arena);
}

bool tvdb_make_manifold_vdb(const tvdb_triangle_mesh* input, double resolution,
                            double isovalue, tvdb_triangle_mesh* output,
                            tvdb_sign_method sign_method,
                            tvdb_arena_allocator_t* arena) {
    (void)sign_method;
    return tvdb_make_manifold(input, resolution, isovalue, output, arena);
}
