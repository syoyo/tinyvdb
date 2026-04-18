#include "tinyvdb_mesh.h"
#include "tvdb_memory.h" // Include the memory arena header
#include <string.h>
#include <stdio.h>
#include <math.h>
#include <stdlib.h> // For malloc, free, size_t
#include <assert.h>
#include <stdint.h> // For uint64_t, uint32_t

#define TVDB_MAX_GRID_DIM 2048 // Limit grid dimensions to prevent excessive memory allocation

// --- Arena Allocator Wrapper ---
static void* arena_alloc(tvdb_arena_allocator_t* arena, size_t size) {
    if (!arena) return malloc(size); // Fallback if no arena is provided
    return tvdb_arena_alloc(arena, size);
}

// --- C-compatible helper functions for math and data structures ---

static inline float dot_c(tvdb_vec3f a, tvdb_vec3f b) {
  return a.x * b.x + a.y * b.y + a.z * b.z;
}

static inline tvdb_vec3f sub_c(tvdb_vec3f a, tvdb_vec3f b) {
  return (tvdb_vec3f){a.x - b.x, a.y - b.y, a.z - b.z};
}

static inline tvdb_vec3f add_c(tvdb_vec3f a, tvdb_vec3f b) {
  return (tvdb_vec3f){a.x + b.x, a.y + b.y, a.z + b.z};
}

static inline tvdb_vec3f mul_c(tvdb_vec3f a, float s) {
  return (tvdb_vec3f){a.x * s, a.y * s, a.z * s};
}

static float dist_sq_c(tvdb_vec3f a, tvdb_vec3f b) {
  tvdb_vec3f d = sub_c(a, b);
  return dot_c(d, d);
}

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
    return static_cast<uint64_t>(ix) +
           static_cast<uint64_t>(iy) * nx +
           static_cast<uint64_t>(iz) * nx * ny;
}

static uint64_t edge_key_c(uint64_t v0, uint64_t v1) {
    if (v0 > v1) { uint64_t temp = v0; v0 = v1; v1 = temp; }
    return (v0 << 32) | v1;
}

// --- Edge Cache ---
typedef struct {
    uint64_t key;
    uint32_t value;
} edge_cache_entry_t;

typedef struct {
    edge_cache_entry_t* entries;
    size_t count;
    size_t capacity;
} edge_cache_t;

static void edge_cache_init(edge_cache_t* cache, tvdb_arena_allocator_t* arena) {
    cache->count = 0;
    cache->capacity = 16; // Initial capacity
    cache->entries = (edge_cache_entry_t*)arena_alloc(arena, cache->capacity * sizeof(edge_cache_entry_t));
}

// Helper function to get or insert into the edge cache.
// Returns 0 on allocation failure.
static uint32_t edge_cache_get_or_insert(edge_cache_t* cache, tvdb_arena_allocator_t* arena, uint64_t key, uint32_t new_value) {
    for (size_t i = 0; i < cache->count; ++i) {
        if (cache->entries[i].key == key) {
            return cache->entries[i].value;
        }
    }

    if (cache->count == cache->capacity) {
        size_t new_capacity = cache->capacity * 2;
        edge_cache_entry_t* new_entries = (edge_cache_entry_t*)arena_alloc(arena, new_capacity * sizeof(edge_cache_entry_t));
        if (!new_entries) return 0; // Allocation failed
        memcpy(new_entries, cache->entries, cache->count * sizeof(edge_cache_entry_t));
        cache->entries = new_entries;
        cache->capacity = new_capacity;
    }
    cache->entries[cache->count].key = key;
    cache->entries[cache->count].value = new_value;
    return cache->entries[cache->count++].value;
}

// Get or create edge vertex using the C-style cache and arena
static uint32_t get_or_create_edge_vertex_c(edge_cache_t* cache, tvdb_arena_allocator_t* arena,
                                            const tvdb_dense_grid* grid, float isovalue,
                                            int x0, int y0, int z0, int x1, int y1, int z1) {
    uint64_t v0_flat_idx = voxel_idx_c(grid->nx, grid->ny, x0, y0, z0);
    uint64_t v1_flat_idx = voxel_idx_c(grid->nx, grid->ny, x1, y1, z1);
    uint64_t edge_key = edge_key_c(v0_flat_idx, v1_flat_idx);

    // Check if vertex already exists in cache
    for (size_t i = 0; i < cache->count; ++i) {
        if (cache->entries[i].key == edge_key) {
            return cache->entries[i].value;
        }
    }

    // Vertex does not exist, create it
    tvdb_vec3f p0 = voxel_pos_c(grid, x0, y0, z0);
    tvdb_vec3f p1 = voxel_pos_c(grid, x1, y1, z1);
    float v0 = grid->data[voxel_idx_c(grid->nx, grid->ny, x0, y0, z0)];
    float v1 = grid->data[voxel_idx_c(grid->nx, grid->ny, x1, y1, z1)];

    tvdb_vec3f p = vertex_interp_c(isovalue, p0, p1, v0, v1);

    // Allocate vertex from arena (via mesh's dynamic arrays)
    uint32_t idx = (uint32_t)mesh->vertex_count;
    if (mesh->vertex_count == mesh->vertex_capacity) {
        size_t new_capacity = mesh->vertex_capacity == 0 ? 16 : mesh->vertex_capacity * 2;
        tvdb_vec3f* new_vertices = (tvdb_vec3f*)arena_alloc(arena, new_capacity * sizeof(tvdb_vec3f));
        if (!new_vertices) return 0; // Allocation failed
        memcpy(new_vertices, mesh->vertices, mesh->vertex_count * sizeof(tvdb_vec3f));
        mesh->vertices = new_vertices;
        mesh->vertex_capacity = new_capacity;
    }
    mesh->vertices[mesh->vertex_count++] = p;
    
    // Add to edge cache
    uint32_t new_cache_value = idx; // The index in the mesh's vertex list is the value
    uint32_t cached_idx = edge_cache_get_or_insert(cache, arena, edge_key, new_cache_value);
    if (cached_idx == 0 && cache->count > 0) { // Check for allocation failure from cache insertion
        return 0; // Indicate failure
    }
    
    return idx; // Return the index of the newly created vertex
}

// --- C-compatible helper functions mimicking C++ std:: namespace ---
static inline tvdb_vec3f vmin_c(tvdb_vec3f a, tvdb_vec3f b) {
  return (tvdb_vec3f){(a.x < b.x ? a.x : b.x), (a.y < b.y ? a.y : b.y), (a.z < b.z ? a.z : b.z)};
}
static inline tvdb_vec3f vmax_c(tvdb_vec3f a, tvdb_vec3f b) {
  return (tvdb_vec3f){(a.x > b.x ? a.x : b.x), (a.y > b.y ? a.y : b.y), (a.z > b.z ? a.z : b.z)};
}
static inline float fmaxf_c(float a, float b) { return a > b ? a : b; }
static inline float fmax3f_c(float a, float b, float c) { return fmaxf_c(a, fmaxf_c(b, c)); }

// Replicating VertexInterp from C++ std lib namespace.
static tvdb_vec3f vertex_interp_c(float iso, tvdb_vec3f p1, tvdb_vec3f p2, float v1, float v2) {
  if (fabsf(v1 - v2) < 1e-10f) return p1;
  float mu = (iso - v1) / (v2 - v1);
  return (tvdb_vec3f){p1.x + mu * (p2.x - p1.x),
                      p1.y + mu * (p2.y - p1.y),
                      p1.z + mu * (p2.z - p1.z)};
}


// --- Flood Fill for Sign Determination ---
static void flood_fill_sign_c(tvdb_dense_grid* grid, tvdb_arena_allocator_t* arena) {
  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  const float thresh = 0.75f * grid->voxel_size;
  
  size_t grid_size = (size_t)nx * ny * nz;
  uint8_t* exterior = (uint8_t*)arena_alloc(arena, grid_size * sizeof(uint8_t));
  if (!exterior) return; // Allocation failed

  size_t queue_capacity = grid_size > 1024 ? 1024 : grid_size; 
  int32_t* queue = (int32_t*)arena_alloc(arena, queue_capacity * sizeof(int32_t));
  if (!queue) return; // Allocation failed
  size_t queue_size = 0;

  auto Idx = [&](int x, int y, int z) -> size_t {
    return static_cast<size_t>(x) + nx * (static_cast<size_t>(y) + ny * static_cast<size_t>(z));
  };
  
  for (int iz = 0; iz < nz; ++iz)
    for (int iy = 0; iy < ny; ++iy)
      for (int ix = 0; ix < nx; ++ix)
        if (ix==0||ix==nx-1||iy==0||iy==ny-1||iz==0||iz==nz-1) {
          exterior[Idx(ix,iy,iz)] = 1;
          if (queue_size < queue_capacity) {
            queue[queue_size++] = static_cast<int32_t>(Idx(ix,iy,iz));
          }
        }

  size_t head = 0;
  static const int dirs[6][3] = {{-1,0,0},{1,0,0},{0,-1,0},{0,1,0},{0,0,-1},{0,0,1}};
  while (head < queue_size) {
    int32_t ci = queue[head++];
    int iz = ci / (nx * ny), iy = (ci / nx) % ny, ix = ci % nx;
    for (const auto& d : dirs) {
      int x2=ix+d[0], y2=iy+d[1], z2=iz+d[2];
      if (x2<0||x2>=nx||y2<0||y2>=ny||z2<0||z2>=nz) continue;
      size_t ni = Idx(x2, y2, z2);
      if (exterior[ni] || grid->data[ni] <= thresh) continue;
      exterior[ni] = 1;
      if (queue_size < queue_capacity) {
        queue[queue_size++] = static_cast<int32_t>(ni);
      }
    }
  }
  
  for (size_t i = 0; i < grid_size; ++i)
    if (!exterior[i]) grid->data[i] = -grid->data[i];
}


// ============================================================================
// MeshToSDF
// ============================================================================

bool tvdb_mesh_to_sdf(const tvdb_triangle_mesh* mesh,
                      float voxel_size,
                      float band_width,
                      tvdb_dense_grid* grid,
                      tvdb_arena_allocator_t* arena) {
  if (!mesh || !grid || mesh->vertex_count == 0 || !arena) return false;

  tvdb_vec3f bmin = mesh->vertices[0], bmax = mesh->vertices[0];
  for(size_t i=0; i<mesh->vertex_count; ++i) {
    if(mesh->vertices[i].x < bmin.x) bmin.x = mesh->vertices[i].x;
    if(mesh->vertices[i].y < bmin.y) bmin.y = mesh->vertices[i].y;
    if(mesh->vertices[i].z < bmin.z) bmin.z = mesh->vertices[i].z;
    if(mesh->vertices[i].x > bmax.x) bmax.x = mesh->vertices[i].x;
    if(mesh->vertices[i].y > bmax.y) bmax.y = mesh->vertices[i].y;
    if(mesh->vertices[i].z > bmax.z) bmax.z = mesh->vertices[i].z;
  }

  float pad = (band_width + 2.0f) * voxel_size;
  bmin = sub_c(bmin, (tvdb_vec3f){pad, pad, pad});
  bmax = add_c(bmax, (tvdb_vec3f){pad, pad, pad});

  int nx = (int)ceil((bmax.x - bmin.x) / voxel_size) + 1;
  int ny = (int)ceil((bmax.y - bmin.y) / voxel_size) + 1;
  int nz = (int)ceil((bmax.z - bmin.z) / voxel_size) + 1;

  nx = (nx > TVDB_MAX_GRID_DIM) ? TVDB_MAX_GRID_DIM : nx;
  ny = (ny > TVDB_MAX_GRID_DIM) ? TVDB_MAX_GRID_DIM : ny;
  nz = (nz > TVDB_MAX_GRID_DIM) ? TVDB_MAX_GRID_DIM : nz;

  tvdb_dense_grid_init_arena(grid, nx, ny, nz, arena);
  if (!grid->data) return false;

  grid->ox = bmin.x; grid->oy = bmin.y; grid->oz = bmin.z;
  grid->voxel_size = voxel_size;

  float bg = band_width * voxel_size;
  for(size_t i=0; i<(size_t)nx*ny*nz; ++i) grid->data[i] = bg;

  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        tvdb_vec3f p = {bmin.x + (ix + 0.5f) * voxel_size,
                        bmin.y + (iy + 0.5f) * voxel_size,
                        bmin.z + (iz + 0.5f) * voxel_size};

        float dsq = bg * bg;
        for (size_t t = 0; t < mesh->face_count; ++t) {
          float distsq = point_triangle_dist_sq_c(p, mesh->vertices[mesh->faces[t].v0],
                                                   mesh->vertices[mesh->faces[t].v1],
                                                   mesh->vertices[mesh->faces[t].v2]);
          if (distsq < dsq) dsq = distsq;
        }
        grid->data[ix + nx * (iy + ny * iz)] = sqrtf(dsq);
      }
    }
  }

  flood_fill_sign_c(grid, arena);
  return true;
}

bool tvdb_sdf_to_mesh(const tvdb_dense_grid* grid, float isovalue, tvdb_triangle_mesh* mesh, tvdb_arena_allocator_t* arena) {
  if (!mesh || !grid || !arena) return false;
  tvdb_triangle_mesh_init_arena(mesh, arena);
  if (!mesh->vertices || !mesh->faces) return false;

  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  if (nx < 2 || ny < 2 || nz < 2) return false;

  edge_cache_t edge_cache;
  edge_cache_init(&edge_cache, arena);

  // Get or create edge vertex helper function
  // Note: 'isovalue' needs to be captured or passed. It's captured implicitly here from parent scope.
  uint32_t (*GetOrCreateEdgeVertex_c_ptr)(edge_cache_t* cache, tvdb_arena_allocator_t* arena,
                                         const tvdb_dense_grid* grid, float isovalue_param,
                                         int x0, int y0, int z0, int x1, int y1, int z1);
  
  get_or_create_edge_vertex_c = [](edge_cache_t* cache, tvdb_arena_allocator_t* arena,
                                    const tvdb_dense_grid* grid, float isovalue_param,
                                    int x0, int y0, int z0, int x1, int y1, int z1) -> uint32_t {
    uint64_t v0_flat_idx = voxel_idx_c(grid->nx, grid->ny, x0, y0, z0);
    uint64_t v1_flat_idx = voxel_idx_c(grid->nx, grid->ny, x1, y1, z1);
    
    uint64_t key = edge_key_c(v0_flat_idx, v1_flat_idx);
    for (size_t i = 0; i < cache->count; ++i) {
        if (cache->entries[i].key == key) {
            return cache->entries[i].value;
        }
    }

    tvdb_vec3f p0 = voxel_pos_c(grid, x0, y0, z0);
    tvdb_vec3f p1 = voxel_pos_c(grid, x1, y1, z1);
    float v0 = grid->data[voxel_idx_c(grid->nx, grid->ny, x0, y0, z0)];
    float v1 = grid->data[voxel_idx_c(grid->nx, grid->ny, x1, y1, z1)];

    tvdb_vec3f p = vertex_interp_c(isovalue_param, p0, p1, v0, v1);

    uint32_t idx = (uint32_t)mesh->vertex_count;
    if (mesh->vertex_count == mesh->vertex_capacity) {
        size_t new_capacity = mesh->vertex_capacity == 0 ? 16 : mesh->vertex_capacity * 2;
        tvdb_vec3f* new_vertices = (tvdb_vec3f*)arena_alloc(arena, new_capacity * sizeof(tvdb_vec3f));
        if (!new_vertices) return 0;
        memcpy(new_vertices, mesh->vertices, mesh->vertex_count * sizeof(tvdb_vec3f));
        mesh->vertices = new_vertices;
        mesh->vertex_capacity = new_capacity;
    }
    mesh->vertices[mesh->vertex_count++] = p;
    
    uint32_t new_cache_value = idx;
    uint32_t cached_idx = edge_cache_get_or_insert(cache, arena, key, new_cache_value);
    if (cached_idx == 0 && cache->count > 0) {
        return 0;
    }
    
    return idx;
  };

  static const int corner[8][3] = {
    {0,0,0},{1,0,0},{1,1,0},{0,1,0},
    {0,0,1},{1,0,1},{1,1,1},{0,1,1}
  };

  static const int edge_conn[12][2] = {
    {0,1},{1,2},{2,3},{3,0},
    {4,5},{5,6},{6,7},{7,4},
    {0,4},{1,5},{2,6},{3,7}
  };

  for (int iz = 0; iz < nz - 1; ++iz) {
    for (int iy = 0; iy < ny - 1; ++iy) {
      for (int ix = 0; ix < nx - 1; ++ix) {
        float val[8];
        int cx[8], cy[8], cz[8];
        for (int i = 0; i < 8; ++i) {
          cx[i] = ix + corner[i][0];
          cy[i] = iy + corner[i][1];
          cz[i] = iz + corner[i][2];
          val[i] = grid->data[voxel_idx_c(nx, ny, cx[i], cy[i], cz[i])];
        }

        int cubeindex = 0;
        for (int i = 0; i < 8; ++i) {
          if (val[i] < isovalue) cubeindex |= (1 << i);
        }

        if (MC_EDGE_TABLE[cubeindex] == 0) continue;

        uint32_t vertlist[12] = {};
        int edges = MC_EDGE_TABLE[cubeindex];
        for (int e = 0; e < 12; ++e) {
          if (edges & (1 << e)) {
            int c0 = edge_conn[e][0], c1 = edge_conn[e][1];
            vertlist[e] = GetOrCreateEdgeVertex_c(&edge_cache, arena, grid, isovalue,
                                                  cx[c0], cy[c0], cz[c0], cx[c1], cy[c1], cz[c1]);
            if (vertlist[e] == 0) { 
              return false; // Allocation failed
            }
          }
        }

        for (int i = 0; MC_TRI_TABLE[cubeindex][i] != -1; i += 3) {
          uint32_t a = vertlist[MC_TRI_TABLE[cubeindex][i]];
          uint32_t b = vertlist[MC_TRI_TABLE[cubeindex][i + 1]];
          uint32_t c = vertlist[MC_TRI_TABLE[cubeindex][i + 2]];
          
          if (mesh->face_count == mesh->face_capacity) {
              size_t new_capacity = mesh->face_capacity == 0 ? 16 : mesh->face_capacity * 2;
              tvdb_triangle* new_faces = (tvdb_triangle*)arena_alloc(arena, new_capacity * sizeof(tvdb_triangle));
              if (!new_faces) return false;
              memcpy(new_faces, mesh->faces, mesh->face_count * sizeof(tvdb_triangle));
              mesh->faces = new_faces;
              mesh->face_capacity = new_capacity;
          }
          mesh->faces[mesh->face_count++] = {a, b, c};
        }
      }
    }
  }

  return !mesh->faces.empty();
}


bool tvdb_make_manifold(const tvdb_triangle_mesh* input, double resolution, double isovalue, TriangleMesh* output, tvdb_arena_allocator_t* arena) {
  if (!output || input->vertices.empty() || input->faces.empty() || !arena) return false;

  tvdb_vec3f bmin = input->vertices[0], bmax = input->vertices[0];
  for (size_t i = 0; i < input->vertex_count; ++i) {
    bmin = vmin_c(bmin, input->vertices[i]);
    bmax = vmax_c(bmax, input->vertices[i]);
  }
  float extent = fmax3f_c(bmax.x - bmin.x, bmax.y - bmin.y, bmax.z - bmin.z);
  if (extent < 1e-12f) return false;

  float voxel_size = extent / static_cast<float>(resolution);

  tvdb_dense_grid sdf;
  if (!tvdb_mesh_to_sdf(input, voxel_size, 3.0f, &sdf, arena)) return false;

  float iso_dist = static_cast<float>(isovalue) * voxel_size;
  if (!tvdb_sdf_to_mesh(&sdf, iso_dist, output, arena)) return false;

  return true;
}

// Forward declarations for VDB versions
bool tvdb_mesh_to_sdf_vdb(const tvdb_triangle_mesh* mesh,
                          float voxel_size,
                          float band_width,
                          tvdb_dense_grid* grid,
                          tvdb_sign_method sign_method,
                          tvdb_arena_allocator_t* arena);

bool tvdb_make_manifold_vdb(const tvdb_triangle_mesh* input,
                            double resolution,
                            double isovalue,
                            tvdb_triangle_mesh* output,
                            tvdb_sign_method sign_method,
                            tvdb_arena_allocator_t* arena);

// Arena-aware init/free for mesh/grid structures
void tvdb_triangle_mesh_init_arena(tvdb_triangle_mesh* mesh, tvdb_arena_allocator_t* arena) {
    memset(mesh, 0, sizeof(tvdb_triangle_mesh));
    size_t vertex_cap = 16;
    size_t face_cap = 16;

    mesh->vertices = (tvdb_vec3f*)arena_alloc(arena, vertex_cap * sizeof(tvdb_vec3f));
    mesh->faces = (tvdb_triangle*)arena_alloc(arena, face_cap * sizeof(tvdb_triangle));
    
    if (!mesh->vertices || !mesh->faces) {
        mesh->vertices = NULL; mesh->faces = NULL;
        mesh->vertex_capacity = 0; mesh->face_capacity = 0;
    } else {
        mesh->vertex_capacity = vertex_cap;
        mesh->face_capacity = face_cap;
    }
}

void tvdb_dense_grid_init_arena(tvdb_dense_grid* grid, int nx, int ny, int nz, tvdb_arena_allocator_t* arena) {
  grid->nx = nx; grid->ny = ny; grid->nz = nz;
  grid->data = (float*)arena_alloc(arena, (size_t)nx * ny * nz * sizeof(float));
}
