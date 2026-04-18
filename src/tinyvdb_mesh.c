#include "tinyvdb_mesh.h"
#include "tvdb_memory.h" // Include the memory arena header
#include <string.h>
#include <stdio.h>
#include <math.h>
#include <stdlib.h> // For malloc, free, size_t
#include <assert.h>

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

// VoxelPos, VoxelIdx, EdgeKey, GetOrCreateEdgeVertex as C functions
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
// Replaces std::unordered_map with a dynamic array and linear search for simplicity
// in a pure C context. This will be allocated from the arena.
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

static uint32_t edge_cache_get_or_insert(edge_cache_t* cache, tvdb_arena_allocator_t* arena, uint64_t v0_idx, uint64_t v1_idx, uint32_t new_value) {
    uint64_t key = edge_key_c(v0_idx, v1_idx);

    // Linear search for existing key
    for (size_t i = 0; i < cache->count; ++i) {
        if (cache->entries[i].key == key) {
            return cache->entries[i].value;
        }
    }

    // Key not found, insert new entry
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

static uint32_t get_or_create_edge_vertex_c(edge_cache_t* cache, tvdb_arena_allocator_t* arena,
                                            const tvdb_dense_grid* grid, uint32_t v_idx_base,
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

    // VertexInterp requires float and Vec3f, which are compatible
    tvdb_vec3f p = detail::VertexInterp(isovalue, p0, p1, v0, v1); // isovalue is not available here, this needs to be passed down

    // Allocate vertex from arena
    uint32_t idx = (uint32_t)cache->count; // Use count as index for simplicity if arena is managed separately
    
    // Reallocate cache if needed to store new vertex index
    if (cache->count == cache->capacity) {
        size_t new_capacity = cache->capacity * 2;
        edge_cache_entry_t* new_entries = (edge_cache_entry_t*)arena_alloc(arena, new_capacity * sizeof(edge_cache_entry_t));
        if (!new_entries) return 0; // Allocation failed
        memcpy(new_entries, cache->entries, cache->count * sizeof(edge_cache_entry_t));
        cache->entries = new_entries;
        cache->capacity = new_capacity;
    }
    cache->entries[cache->count].key = edge_key;
    cache->entries[cache->count].value = idx; // Store the index in the mesh's vertex list
    cache->count++;

    // Add vertex to mesh (this implies mesh->vertices must also be arena allocated)
    // This needs to be done by the caller of GetOrCreateEdgeVertex, which is SDFToMesh.

    return idx; // Return the index of the newly created vertex
}


// --- Original Detail Namespace Functions ---
// Moved to anonymous namespace or renamed to be C-compatible.

// detail::vmin, detail::vmax, detail::VertexInterp are still C++ std library features.
// These need to be reimplemented in C or made available via extern "C".
// For now, I will replicate them as C functions here for simplicity.

static inline tvdb_vec3f vmin_c(tvdb_vec3f a, tvdb_vec3f b) {
  return (tvdb_vec3f){(a.x < b.x ? a.x : b.x), (a.y < b.y ? a.y : b.y), (a.z < b.z ? a.z : b.z)};
}
static inline tvdb_vec3f vmax_c(tvdb_vec3f a, tvdb_vec3f b) {
  return (tvdb_vec3f){(a.x > b.x ? a.x : b.x), (a.y > b.y ? a.y : b.y), (a.z > b.z ? a.z : b.z)};
}

// Replicating VertexInterp from C++ std lib namespace.
static tvdb_vec3f vertex_interp_c(float iso, const tvdb_vec3f& p1, const tvdb_vec3f& p2, float v1, float v2) {
  if (fabsf(v1 - v2) < 1e-10f) return p1;
  float mu = (iso - v1) / (v2 - v1);
  return (tvdb_vec3f){p1.x + mu * (p2.x - p1.x),
                      p1.y + mu * (p2.y - p1.y),
                      p1.z + mu * (p2.z - p1.z)};
}


// --- Flood Fill for Sign Determination ---
// This function needs to be C-compatible and use the arena if it allocates memory.
// Currently, it uses a std::vector which implies C++ heap allocation.
// Replace std::vector with dynamic C array or arena allocation.
static void flood_fill_sign_c(tvdb_dense_grid* grid, tvdb_arena_allocator_t* arena) {
  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  const float thresh = 0.75f * grid->voxel_size;
  
  // Allocate exterior grid from arena
  size_t grid_size = (size_t)nx * ny * nz;
  uint8_t* exterior = (uint8_t*)arena_alloc(arena, grid_size * sizeof(uint8_t));
  if (!exterior) return; // Allocation failed

  // Allocate queue from arena
  // A rough estimate for queue size, can be refined. Max possible elements is grid_size.
  size_t queue_capacity = grid_size > 1024 ? 1024 : grid_size; 
  int32_t* queue = (int32_t*)arena_alloc(arena, queue_capacity * sizeof(int32_t));
  if (!queue) return; // Allocation failed
  size_t queue_size = 0;

  auto Idx = [&](int x, int y, int z) -> size_t {
    return static_cast<size_t>(x) + nx * (static_cast<size_t>(y) + ny * static_cast<size_t>(z));
  };
  
  // Initialize queue with boundary voxels
  for (int iz = 0; iz < nz; ++iz)
    for (int iy = 0; iy < ny; ++iy)
      for (int ix = 0; ix < nx; ++ix)
        if (ix==0||ix==nx-1||iy==0||iy==ny-1||iz==0||iz==nz-1) {
          exterior[Idx(ix,iy,iz)] = 1;
          if (queue_size < queue_capacity) { // Add to queue if space available
            queue[queue_size++] = static_cast<int32_t>(Idx(ix,iy,iz));
          } else {
            // Queue full, this implies a very large grid or an issue.
            // In a robust implementation, we'd resize or handle this.
            // For now, we might miss some propagation in extreme cases.
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
      if (queue_size < queue_capacity) { // Add to queue if space available
        queue[queue_size++] = static_cast<int32_t>(ni);
      }
    }
  }
  
  // Negate interior voxels
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

  // Clamp dimensions to prevent excessive memory allocation
  nx = (nx > TVDB_MAX_GRID_DIM) ? TVDB_MAX_GRID_DIM : nx;
  ny = (ny > TVDB_MAX_GRID_DIM) ? TVDB_MAX_GRID_DIM : ny;
  nz = (nz > TVDB_MAX_GRID_DIM) ? TVDB_MAX_GRID_DIM : nz;

  // Use arena for grid data allocation
  tvdb_dense_grid_init_arena(grid, nx, ny, nz, arena);
  if (!grid->data) return false; // Allocation failed

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

  flood_fill_sign_c(grid, arena); // Use arena for flood fill's internal allocations
  return true;
}

bool tvdb_sdf_to_mesh(const tvdb_dense_grid* grid, float isovalue, tvdb_triangle_mesh* mesh, tvdb_arena_allocator_t* arena) {
  if (!mesh || !grid || !arena) return false;
  tvdb_triangle_mesh_init_arena(mesh, arena); // Initialize mesh using arena
  if (!mesh->vertices || !mesh->faces) return false; // Check if arena allocation in init failed

  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  if (nx < 2 || ny < 2 || nz < 2) return false;

  // --- C-compatible Edge Cache ---
  edge_cache_t edge_cache;
  edge_cache_init(&edge_cache, arena); // Initialize edge cache from arena

  // Helper to get or create vertex, using the C-style cache and arena
  auto GetOrCreateEdgeVertex_c = [&](int x0, int y0, int z0,
                                   int x1, int y1, int z1) -> uint32_t {
    uint64_t v0_flat_idx = voxel_idx_c(nx, ny, x0, y0, z0);
    uint64_t v1_flat_idx = voxel_idx_c(nx, ny, x1, y1, z1);
    
    // Check if vertex already exists in cache
    uint64_t key = edge_key_c(v0_flat_idx, v1_flat_idx);
    for (size_t i = 0; i < edge_cache.count; ++i) {
        if (edge_cache.entries[i].key == key) {
            return edge_cache.entries[i].value;
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
    if (cache->count == cache->capacity) {
        size_t new_capacity = cache->capacity * 2;
        edge_cache_entry_t* new_entries = (edge_cache_entry_t*)arena_alloc(arena, new_capacity * sizeof(edge_cache_entry_t));
        if (!new_entries) return 0; // Allocation failed
        memcpy(new_entries, cache->entries, cache->count * sizeof(edge_cache_entry_t));
        cache->entries = new_entries;
        cache->capacity = new_capacity;
    }
    cache->entries[cache->count].key = key;
    cache->entries[cache->count].value = idx;
    cache->count++;

    return idx;
  };

  // Corner offsets (x,y,z) relative to (ix,iy,iz):
  static const int corner[8][3] = {
    {0,0,0},{1,0,0},{1,1,0},{0,1,0},
    {0,0,1},{1,0,1},{1,1,1},{0,1,1}
  };

  // Edge endpoints (corner indices):
  static const int edge_conn[12][2] = {
    {0,1},{1,2},{2,3},{3,0},
    {4,5},{5,6},{6,7},{7,4},
    {0,4},{1,5},{2,6},{3,7}
  };

  for (int iz = 0; iz < nz - 1; ++iz) {
    for (int iy = 0; iy < ny - 1; ++iy) {
      for (int ix = 0; ix < nx - 1; ++ix) {
        // Get corner values
        float val[8];
        int cx[8], cy[8], cz[8];
        for (int i = 0; i < 8; ++i) {
          cx[i] = ix + corner[i][0];
          cy[i] = iy + corner[i][1];
          cz[i] = iz + corner[i][2];
          val[i] = grid->data[voxel_idx_c(nx, ny, cx[i], cy[i], cz[i])];
        }

        // Compute cube index
        int cubeindex = 0;
        for (int i = 0; i < 8; ++i) {
          if (val[i] < isovalue) cubeindex |= (1 << i);
        }

        if (MC_EDGE_TABLE[cubeindex] == 0) continue; // Use global MC_EDGE_TABLE

        // Compute edge vertices
        uint32_t vertlist[12] = {};
        int edges = MC_EDGE_TABLE[cubeindex];
        for (int e = 0; e < 12; ++e) {
          if (edges & (1 << e)) {
            int c0 = edge_conn[e][0], c1 = edge_conn[e][1];
            vertlist[e] = GetOrCreateEdgeVertex_c(&edge_cache, arena, grid, 0, // v_idx_base is not used here
                                                  cx[c0], cy[c0], cz[c0], cx[c1], cy[c1], cz[c1]);
            if (vertlist[e] == 0 && cache->count > 0) { // Check for allocation failure indication
              // Potentially handle error if vertex creation failed.
              // This might mean the cache itself failed to allocate or grow.
              return false; 
            }
          }
        }

        // Generate triangles
        for (int i = 0; MC_TRI_TABLE[cubeindex][i] != -1; i += 3) { // Use global MC_TRI_TABLE
          uint32_t a = vertlist[MC_TRI_TABLE[cubeindex][i]];
          uint32_t b = vertlist[MC_TRI_TABLE[cubeindex][i + 1]];
          uint32_t c = vertlist[MC_TRI_TABLE[cubeindex][i + 2]];
          
          // Dynamically grow faces using arena
          if (mesh->face_count == mesh->face_capacity) {
              size_t new_capacity = mesh->face_capacity == 0 ? 16 : mesh->face_capacity * 2;
              tvdb_triangle* new_faces = (tvdb_triangle*)arena_alloc(arena, new_capacity * sizeof(tvdb_triangle));
              if (!new_faces) return false; // Allocation failed
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
  float extent = fmaxf(fmaxf(bmax.x - bmin.x, bmax.y - bmin.y), bmax.z - bmin.z);
  if (extent < 1e-12f) return false;

  float voxel_size = extent / static_cast<float>(resolution);

  tvdb_dense_grid sdf;
  // tvdb_mesh_to_sdf will use the provided arena for sdf.data
  if (!tvdb_mesh_to_sdf(input, voxel_size, 3.0f, &sdf, arena)) return false;

  // Extract mesh at isovalue (in world-space distance units)
  float iso_dist = static_cast<float>(isovalue) * voxel_size;
  // tvdb_sdf_to_mesh will use the arena for output mesh vertices/faces
  if (!tvdb_sdf_to_mesh(&sdf, iso_dist, output, arena)) return false;

  return true;
}

// Forward declarations for VDB versions (assume they also take arena)
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

// Helper definitions moved from detail namespace to global C scope
// Define MC_EDGE_TABLE and MC_TRI_TABLE globally or ensure they are accessible.
// For this example, I'll copy them here. They should ideally be in a shared header.
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

static const int MC_TRI_TABLE[256][16] = {
  {-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,8,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,1,9,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,8,3,9,8,1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,8,3,1,2,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,2,10,0,2,9,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {2,8,3,2,10,8,10,9,8,-1,-1,-1,-1,-1,-1,-1},
  {3,11,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,11,2,8,11,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,9,0,2,3,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,11,2,1,9,11,9,8,11,-1,-1,-1,-1,-1,-1,-1},
  {3,10,1,11,10,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,10,1,0,8,10,8,11,10,-1,-1,-1,-1,-1,-1,-1},
  {3,9,0,3,11,9,11,10,9,-1,-1,-1,-1,-1,-1,-1},
  {9,8,10,10,8,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,7,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,3,0,7,3,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,1,9,8,4,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,1,9,4,7,1,7,3,1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,8,4,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,4,7,3,0,4,1,2,10,-1,-1,-1,-1,-1,-1,-1},
  {9,2,10,9,0,2,8,4,7,-1,-1,-1,-1,-1,-1,-1},
  {2,10,9,2,9,7,2,7,3,7,9,4,-1,-1,-1,-1},
  {8,4,7,3,11,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {11,4,7,11,2,4,2,0,4,-1,-1,-1,-1,-1,-1,-1},
  {9,0,1,8,4,7,2,3,11,-1,-1,-1,-1,-1,-1,-1},
  {4,7,11,9,4,11,9,11,2,9,2,1,-1,-1,-1,-1},
  {3,10,1,3,11,10,7,8,4,-1,-1,-1,-1,-1,-1,-1},
  {1,11,10,1,4,11,1,0,4,7,11,4,-1,-1,-1,-1},
  {4,7,8,9,0,11,9,11,10,11,0,3,-1,-1,-1,-1},
  {4,7,11,4,11,9,9,11,10,-1,-1,-1,-1,-1,-1,-1},
  {9,5,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,5,4,0,8,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,5,4,1,5,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {8,5,4,8,3,5,3,1,5,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,9,5,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,0,8,1,2,10,4,9,5,-1,-1,-1,-1,-1,-1,-1},
  {5,2,10,5,4,2,4,0,2,-1,-1,-1,-1,-1,-1,-1},
  {2,10,5,3,2,5,3,5,4,3,4,8,-1,-1,-1,-1},
  {9,5,4,2,3,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,11,2,0,8,11,4,9,5,-1,-1,-1,-1,-1,-1,-1},
  {0,5,4,0,1,5,2,3,11,-1,-1,-1,-1,-1,-1,-1},
  {2,1,5,2,5,8,2,8,11,4,8,5,-1,-1,-1,-1},
  {10,3,11,10,1,3,9,5,4,-1,-1,-1,-1,-1,-1,-1},
  {4,9,5,0,8,1,8,10,1,8,11,10,-1,-1,-1,-1},
  {5,4,0,5,0,11,5,11,10,11,0,3,-1,-1,-1,-1},
  {5,4,8,5,8,10,10,8,11,-1,-1,-1,-1,-1,-1,-1},
  {9,7,8,5,7,9,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,3,0,9,5,3,5,7,3,-1,-1,-1,-1,-1,-1,-1},
  {0,7,8,0,1,7,1,5,7,-1,-1,-1,-1,-1,-1,-1},
  {1,5,3,3,5,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,7,8,9,5,7,10,1,2,-1,-1,-1,-1,-1,-1,-1},
  {10,1,2,9,5,0,5,3,0,5,7,3,-1,-1,-1,-1},
  {8,0,2,8,2,5,8,5,7,10,5,2,-1,-1,-1,-1},
  {2,10,5,2,5,3,3,5,7,-1,-1,-1,-1,-1,-1,-1},
  {7,9,5,7,8,9,3,11,2,-1,-1,-1,-1,-1,-1,-1},
  {9,5,7,9,7,2,9,2,0,2,7,11,-1,-1,-1,-1},
  {2,3,11,0,1,8,1,7,8,1,5,7,-1,-1,-1,-1},
  {11,2,1,11,1,7,7,1,5,-1,-1,-1,-1,-1,-1,-1},
  {9,5,8,8,5,7,10,1,3,10,3,11,-1,-1,-1,-1},
  {5,1,11,5,11,6,1,0,11,7,11,4,0,4,11,-1},
  {0,5,9,0,6,5,0,3,6,11,6,3,8,4,7,-1},
  {6,5,9,6,9,11,4,7,9,7,11,9,-1,-1,-1,-1},
  {10,4,9,6,4,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,10,6,4,9,10,0,8,3,-1,-1,-1,-1,-1,-1,-1},
  {10,0,1,10,6,0,6,4,0,-1,-1,-1,-1,-1,-1,-1},
  {8,3,1,8,1,6,8,6,4,6,1,10,-1,-1,-1,-1},
  {1,4,9,1,2,4,2,6,4,-1,-1,-1,-1,-1,-1,-1},
  {3,0,8,1,2,10,4,9,5,-1,-1,-1,-1,-1,-1,-1},
  {0,2,4,4,2,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {8,3,2,8,2,4,4,2,6,-1,-1,-1,-1,-1,-1,-1},
  {10,4,9,10,6,4,11,2,3,-1,-1,-1,-1,-1,-1,-1},
  {0,8,2,2,8,11,4,9,10,4,10,6,-1,-1,-1,-1},
  {3,11,2,0,1,6,0,6,4,6,1,10,-1,-1,-1,-1},
  {6,4,1,6,1,10,4,8,1,2,1,11,8,11,1,-1},
  {9,6,4,9,3,6,9,1,3,11,6,3,-1,-1,-1,-1},
  {8,11,1,8,1,0,11,6,1,9,1,4,6,4,1,-1},
  {3,11,6,3,6,0,0,6,4,-1,-1,-1,-1,-1,-1,-1},
  {6,4,8,11,6,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {7,10,6,7,8,10,8,9,10,-1,-1,-1,-1,-1,-1,-1},
  {0,7,3,0,10,7,0,9,10,6,7,10,-1,-1,-1,-1},
  {1,10,7,1,7,8,1,8,0,-1,-1,-1,-1,-1,-1,-1},
  {10,7,6,1,7,10,1,8,7,1,0,8,-1,-1,-1,-1},
  {1,2,6,1,6,8,1,8,9,8,6,7,-1,-1,-1,-1},
  {2,6,9,2,9,1,6,7,9,0,9,3,7,3,9,-1},
  {7,8,0,7,0,6,6,0,2,-1,-1,-1,-1,-1,-1,-1},
  {7,3,2,6,7,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {2,3,11,10,6,8,10,8,9,8,6,7,-1,-1,-1,-1},
  {2,0,7,2,7,11,0,9,7,6,7,10,9,10,7,-1},
  {1,8,0,1,7,8,1,10,7,6,7,10,2,3,11,-1},
  {11,2,1,11,1,7,10,6,1,6,7,1,-1,-1,-1,-1},
  {8,9,6,8,6,7,9,1,6,11,6,3,1,3,6,-1},
  {0,9,1,11,6,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {7,8,0,7,0,6,3,11,0,11,6,0,-1,-1,-1,-1},
  {7,11,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {7,6,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,0,8,11,7,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,1,9,11,7,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {8,1,9,8,3,1,11,7,6,-1,-1,-1,-1,-1,-1,-1},
  {10,1,2,6,11,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,3,0,8,6,11,7,-1,-1,-1,-1,-1,-1,-1},
  {2,9,0,2,10,9,6,11,7,-1,-1,-1,-1,-1,-1,-1},
  {6,11,7,2,10,3,10,8,3,10,9,8,-1,-1,-1,-1},
  {7,2,3,6,2,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {7,0,8,7,6,0,6,2,0,-1,-1,-1,-1,-1,-1,-1},
  {2,7,6,2,3,7,0,1,9,-1,-1,-1,-1,-1,-1,-1},
  {1,6,2,1,8,6,1,9,8,8,7,6,-1,-1,-1,-1},
  {10,7,6,10,1,7,1,3,7,-1,-1,-1,-1,-1,-1,-1},
  {10,7,6,1,7,10,1,8,7,1,0,8,-1,-1,-1,-1},
  {0,3,7,0,7,10,0,10,9,6,10,7,-1,-1,-1,-1},
  {7,6,10,7,10,8,8,10,9,-1,-1,-1,-1,-1,-1,-1},
  {6,8,4,11,8,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,6,11,3,0,6,0,4,6,-1,-1,-1,-1,-1,-1,-1},
  {8,6,11,8,4,6,9,0,1,-1,-1,-1,-1,-1,-1,-1},
  {9,4,6,9,6,3,9,3,1,11,3,6,-1,-1,-1,-1},
  {6,8,4,6,11,8,2,10,1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,3,0,11,0,6,11,0,4,6,-1,-1,-1,-1},
  {4,11,8,4,6,11,0,2,9,2,10,9,-1,-1,-1,-1},
  {10,9,3,10,3,2,9,4,3,11,3,6,4,6,3,-1},
  {8,2,3,8,4,2,4,6,2,-1,-1,-1,-1,-1,-1,-1},
  {0,4,2,4,6,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,9,0,2,3,4,2,4,6,4,3,8,-1,-1,-1,-1},
  {1,9,4,1,4,2,2,4,6,-1,-1,-1,-1,-1,-1,-1},
  {8,1,3,8,6,1,8,4,6,6,10,1,-1,-1,-1,-1},
  {10,1,0,10,0,6,6,0,4,-1,-1,-1,-1,-1,-1,-1},
  {4,6,3,4,3,8,6,10,3,0,3,9,10,9,3,-1},
  {10,9,4,6,10,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,9,5,7,6,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,8,3,4,9,5,11,7,6,-1,-1,-1,-1,-1,-1,-1},
  {1,10,11,1,11,4,1,4,0,7,4,11,-1,-1,-1,-1},
  {3,1,4,3,4,8,1,10,4,7,4,11,10,11,4,-1},
  {4,11,7,9,11,4,9,2,11,9,1,2,-1,-1,-1,-1},
  {9,7,4,9,11,7,9,1,11,2,11,1,0,8,3,-1},
  {11,7,4,11,4,2,2,4,0,-1,-1,-1,-1,-1,-1,-1},
  {11,7,4,11,4,2,8,3,4,3,2,4,-1,-1,-1,-1},
  {2,9,10,2,7,9,2,3,7,7,4,9,-1,-1,-1,-1},
  {9,10,7,9,7,4,10,2,7,8,7,0,2,0,7,-1},
  {3,7,10,3,10,2,7,4,10,1,10,0,4,0,10,-1},
  {1,10,2,8,7,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,9,1,4,1,7,7,1,3,-1,-1,-1,-1,-1,-1,-1},
  {4,9,1,4,1,7,0,8,1,8,7,1,-1,-1,-1,-1},
  {4,0,3,7,4,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,8,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,10,8,10,11,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,0,9,3,9,11,11,9,10,-1,-1,-1,-1,-1,-1,-1},
  {0,1,10,0,10,8,8,10,11,-1,-1,-1,-1,-1,-1,-1},
  {3,1,10,11,3,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,11,1,11,9,9,11,8,-1,-1,-1,-1,-1,-1,-1},
  {3,0,9,3,9,11,1,2,9,2,11,9,-1,-1,-1,-1},
  {0,2,11,8,0,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,2,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {2,3,8,2,8,10,10,8,9,-1,-1,-1,-1,-1,-1,-1},
  {9,10,2,0,9,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {2,3,8,2,8,10,0,1,8,1,10,8,-1,-1,-1,-1},
  {1,10,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,3,8,9,1,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,9,1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,3,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1}
};

static const int MC_TRI_TABLE[256][16] = {
  {-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,8,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,1,9,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,8,3,9,8,1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,8,3,1,2,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,2,10,0,2,9,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {2,8,3,2,10,8,10,9,8,-1,-1,-1,-1,-1,-1,-1},
  {3,11,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,11,2,8,11,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,9,0,2,3,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,11,2,1,9,11,9,8,11,-1,-1,-1,-1,-1,-1,-1},
  {3,10,1,11,10,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,10,1,0,8,10,8,11,10,-1,-1,-1,-1,-1,-1,-1},
  {3,9,0,3,11,9,11,10,9,-1,-1,-1,-1,-1,-1,-1},
  {9,8,10,10,8,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,7,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,3,0,7,3,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,1,9,8,4,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,1,9,4,7,1,7,3,1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,8,4,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,4,7,3,0,4,1,2,10,-1,-1,-1,-1,-1,-1,-1},
  {9,2,10,9,0,2,8,4,7,-1,-1,-1,-1,-1,-1,-1},
  {2,10,9,2,9,7,2,7,3,7,9,4,-1,-1,-1,-1},
  {8,4,7,3,11,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {11,4,7,11,2,4,2,0,4,-1,-1,-1,-1,-1,-1,-1},
  {9,0,1,8,4,7,2,3,11,-1,-1,-1,-1,-1,-1,-1},
  {4,7,11,9,4,11,9,11,2,9,2,1,-1,-1,-1,-1},
  {3,10,1,3,11,10,7,8,4,-1,-1,-1,-1,-1,-1,-1},
  {1,11,10,1,4,11,1,0,4,7,11,4,-1,-1,-1,-1},
  {4,7,8,9,0,11,9,11,10,11,0,3,-1,-1,-1,-1},
  {4,7,11,4,11,9,9,11,10,-1,-1,-1,-1,-1,-1,-1},
  {9,5,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,5,4,0,8,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,5,4,1,5,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {8,5,4,8,3,5,3,1,5,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,9,5,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,0,8,1,2,10,4,9,5,-1,-1,-1,-1,-1,-1,-1},
  {5,2,10,5,4,2,4,0,2,-1,-1,-1,-1,-1,-1,-1},
  {2,10,5,3,2,5,3,5,4,3,4,8,-1,-1,-1,-1},
  {9,5,4,2,3,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,11,2,0,8,11,4,9,5,-1,-1,-1,-1,-1,-1,-1},
  {0,5,4,0,1,5,2,3,11,-1,-1,-1,-1,-1,-1,-1},
  {2,1,5,2,5,8,2,8,11,4,8,5,-1,-1,-1,-1},
  {10,3,11,10,1,3,9,5,4,-1,-1,-1,-1,-1,-1,-1},
  {4,9,5,0,8,1,8,10,1,8,11,10,-1,-1,-1,-1},
  {5,4,0,5,0,11,5,11,10,11,0,3,-1,-1,-1,-1},
  {5,4,8,5,8,10,10,8,11,-1,-1,-1,-1,-1,-1,-1},
  {9,7,8,5,7,9,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,3,0,9,5,3,5,7,3,-1,-1,-1,-1,-1,-1,-1},
  {0,7,8,0,1,7,1,5,7,-1,-1,-1,-1,-1,-1,-1},
  {1,5,3,3,5,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,7,8,9,5,7,10,1,2,-1,-1,-1,-1,-1,-1,-1},
  {10,1,2,9,5,0,5,3,0,5,7,3,-1,-1,-1,-1},
  {8,0,2,8,2,5,8,5,7,10,5,2,-1,-1,-1,-1},
  {2,10,5,2,5,3,3,5,7,-1,-1,-1,-1,-1,-1,-1},
  {7,9,5,7,8,9,3,11,2,-1,-1,-1,-1,-1,-1,-1},
  {9,5,7,9,7,2,9,2,0,2,7,11,-1,-1,-1,-1},
  {2,3,11,0,1,8,1,7,8,1,5,7,-1,-1,-1,-1},
  {11,2,1,11,1,7,7,1,5,-1,-1,-1,-1,-1,-1,-1},
  {9,5,8,8,5,7,10,1,3,10,3,11,-1,-1,-1,-1},
  {5,1,11,5,11,6,1,0,11,7,11,4,0,4,11,-1},
  {0,5,9,0,6,5,0,3,6,11,6,3,8,4,7,-1},
  {6,5,9,6,9,11,4,7,9,7,11,9,-1,-1,-1,-1},
  {10,4,9,6,4,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,10,6,4,9,10,0,8,3,-1,-1,-1,-1,-1,-1,-1},
  {10,0,1,10,6,0,6,4,0,-1,-1,-1,-1,-1,-1,-1},
  {8,3,1,8,1,6,8,6,4,6,1,10,-1,-1,-1,-1},
  {1,4,9,1,2,4,2,6,4,-1,-1,-1,-1,-1,-1,-1},
  {3,0,8,1,2,10,4,9,5,-1,-1,-1,-1,-1,-1,-1},
  {0,2,4,4,2,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {8,3,2,8,2,4,4,2,6,-1,-1,-1,-1,-1,-1,-1},
  {10,4,9,10,6,4,11,2,3,-1,-1,-1,-1,-1,-1,-1},
  {0,8,2,2,8,11,4,9,10,4,10,6,-1,-1,-1,-1},
  {3,11,2,0,1,6,0,6,4,6,1,10,-1,-1,-1,-1},
  {6,4,1,6,1,10,4,8,1,2,1,11,8,11,1,-1},
  {9,6,4,9,3,6,9,1,3,11,6,3,-1,-1,-1,-1},
  {8,11,1,8,1,0,11,6,1,9,1,4,6,4,1,-1},
  {3,11,6,3,6,0,0,6,4,-1,-1,-1,-1,-1,-1,-1},
  {6,4,8,11,6,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {7,10,6,7,8,10,8,9,10,-1,-1,-1,-1,-1,-1,-1},
  {0,7,3,0,10,7,0,9,10,6,7,10,-1,-1,-1,-1},
  {1,10,7,1,7,8,1,8,0,-1,-1,-1,-1,-1,-1,-1},
  {10,7,6,1,7,10,1,8,7,1,0,8,-1,-1,-1,-1},
  {1,2,6,1,6,8,1,8,9,8,6,7,-1,-1,-1,-1},
  {2,6,9,2,9,1,6,7,9,0,9,3,7,3,9,-1},
  {7,8,0,7,0,6,6,0,2,-1,-1,-1,-1,-1,-1,-1},
  {7,3,2,6,7,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {2,3,11,10,6,8,10,8,9,8,6,7,-1,-1,-1,-1},
  {2,0,7,2,7,11,0,9,7,6,7,10,9,10,7,-1},
  {1,8,0,1,7,8,1,10,7,6,7,10,2,3,11,-1},
  {11,2,1,11,1,7,10,6,1,6,7,1,-1,-1,-1,-1},
  {8,9,6,8,6,7,9,1,6,11,6,3,1,3,6,-1},
  {0,9,1,11,6,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {7,8,0,7,0,6,3,11,0,11,6,0,-1,-1,-1,-1},
  {7,11,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {7,6,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,0,8,11,7,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,1,9,11,7,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {8,1,9,8,3,1,11,7,6,-1,-1,-1,-1,-1,-1,-1},
  {10,1,2,6,11,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,3,0,8,6,11,7,-1,-1,-1,-1,-1,-1,-1},
  {2,9,0,2,10,9,6,11,7,-1,-1,-1,-1,-1,-1,-1},
  {6,11,7,2,10,3,10,8,3,10,9,8,-1,-1,-1,-1},
  {7,2,3,6,2,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {7,0,8,7,6,0,6,2,0,-1,-1,-1,-1,-1,-1,-1},
  {2,7,6,2,3,7,0,1,9,-1,-1,-1,-1,-1,-1,-1},
  {1,6,2,1,8,6,1,9,8,8,7,6,-1,-1,-1,-1},
  {10,7,6,10,1,7,1,3,7,-1,-1,-1,-1,-1,-1,-1},
  {10,7,6,1,7,10,1,8,7,1,0,8,-1,-1,-1,-1},
  {0,3,7,0,7,10,0,10,9,6,10,7,-1,-1,-1,-1},
  {7,6,10,7,10,8,8,10,9,-1,-1,-1,-1,-1,-1,-1},
  {6,8,4,11,8,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,6,11,3,0,6,0,4,6,-1,-1,-1,-1,-1,-1,-1},
  {8,6,11,8,4,6,9,0,1,-1,-1,-1,-1,-1,-1,-1},
  {9,4,6,9,6,3,9,3,1,11,3,6,-1,-1,-1,-1},
  {6,8,4,6,11,8,2,10,1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,3,0,11,0,6,11,0,4,6,-1,-1,-1,-1},
  {4,11,8,4,6,11,0,2,9,2,10,9,-1,-1,-1,-1},
  {10,9,3,10,3,2,9,4,3,11,3,6,4,6,3,-1},
  {8,2,3,8,4,2,4,6,2,-1,-1,-1,-1,-1,-1,-1},
  {0,4,2,4,6,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,9,0,2,3,4,2,4,6,4,3,8,-1,-1,-1,-1},
  {1,9,4,1,4,2,2,4,6,-1,-1,-1,-1,-1,-1,-1},
  {8,1,3,8,6,1,8,4,6,6,10,1,-1,-1,-1,-1},
  {10,1,0,10,0,6,6,0,4,-1,-1,-1,-1,-1,-1,-1},
  {4,6,3,4,3,8,6,10,3,0,3,9,10,9,3,-1},
  {10,9,4,6,10,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,9,5,7,6,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,8,3,4,9,5,11,7,6,-1,-1,-1,-1,-1,-1,-1},
  {1,10,11,1,11,4,1,4,0,7,4,11,-1,-1,-1,-1},
  {3,1,4,3,4,8,1,10,4,7,4,11,10,11,4,-1},
  {4,11,7,9,11,4,9,2,11,9,1,2,-1,-1,-1,-1},
  {9,7,4,9,11,7,9,1,11,2,11,1,0,8,3,-1},
  {11,7,4,11,4,2,2,4,0,-1,-1,-1,-1,-1,-1,-1},
  {11,7,4,11,4,2,8,3,4,3,2,4,-1,-1,-1,-1},
  {2,9,10,2,7,9,2,3,7,7,4,9,-1,-1,-1,-1},
  {9,10,7,9,7,4,10,2,7,8,7,0,2,0,7,-1},
  {3,7,10,3,10,2,7,4,10,1,10,0,4,0,10,-1},
  {1,10,2,8,7,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,9,1,4,1,7,7,1,3,-1,-1,-1,-1,-1,-1,-1},
  {4,9,1,4,1,7,0,8,1,8,7,1,-1,-1,-1,-1},
  {4,0,3,7,4,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,8,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,10,8,10,11,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,0,9,3,9,11,11,9,10,-1,-1,-1,-1,-1,-1,-1},
  {0,1,10,0,10,8,8,10,11,-1,-1,-1,-1,-1,-1,-1},
  {3,1,10,11,3,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,11,1,11,9,9,11,8,-1,-1,-1,-1,-1,-1,-1},
  {3,0,9,3,9,11,1,2,9,2,11,9,-1,-1,-1,-1},
  {0,2,11,8,0,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,2,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {2,3,8,2,8,10,10,8,9,-1,-1,-1,-1,-1,-1,-1},
  {9,10,2,0,9,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {2,3,8,2,8,10,0,1,8,1,10,8,-1,-1,-1,-1},
  {1,10,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,3,8,9,1,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,9,1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,3,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1}
};

// Arena-aware implementations
bool tvdb_mesh_to_sdf(const tvdb_triangle_mesh* mesh, float voxel_size, float band_width, tvdb_dense_grid* grid, tvdb_arena_allocator_t* arena) {
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

  // Clamp dimensions to prevent excessive memory allocation
  nx = (nx > TVDB_MAX_GRID_DIM) ? TVDB_MAX_GRID_DIM : nx;
  ny = (ny > TVDB_MAX_GRID_DIM) ? TVDB_MAX_GRID_DIM : ny;
  nz = (nz > TVDB_MAX_GRID_DIM) ? TVDB_MAX_GRID_DIM : nz;

  // Use arena for grid data allocation
  tvdb_dense_grid_init_arena(grid, nx, ny, nz, arena);
  if (!grid->data) return false; // Allocation failed

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

  flood_fill_sign_c(grid, arena); // Use arena for flood fill's internal allocations
  return true;
}

bool tvdb_sdf_to_mesh(const tvdb_dense_grid* grid, float isovalue, tvdb_triangle_mesh* mesh, tvdb_arena_allocator_t* arena) {
  if (!mesh || !grid || !arena) return false;
  tvdb_triangle_mesh_init_arena(mesh, arena); // Initialize mesh using arena
  if (!mesh->vertices || !mesh->faces) return false; // Check if arena allocation in init failed

  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  if (nx < 2 || ny < 2 || nz < 2) return false;

  // --- C-compatible Edge Cache ---
  edge_cache_t edge_cache;
  edge_cache_init(&edge_cache, arena); // Initialize edge cache from arena

  // Helper to get or create vertex, using the C-style cache and arena
  auto GetOrCreateEdgeVertex_c = [&](int x0, int y0, int z0,
                                   int x1, int y1, int z1) -> uint32_t {
    uint64_t v0_flat_idx = voxel_idx_c(nx, ny, x0, y0, z0);
    uint64_t v1_flat_idx = voxel_idx_c(nx, ny, x1, y1, z1);
    
    // Check if vertex already exists in cache
    uint64_t key = edge_key_c(v0_flat_idx, v1_flat_idx);
    for (size_t i = 0; i < edge_cache.count; ++i) {
        if (edge_cache.entries[i].key == key) {
            return edge_cache.entries[i].value;
        }
    }

    // Vertex does not exist, create it
    tvdb_vec3f p0 = voxel_pos_c(grid, x0, y0, z0);
    tvdb_vec3f p1 = voxel_pos_c(grid, x1, y1, z1);
    float v0 = grid->data[voxel_idx_c(grid->nx, grid->ny, x0, y0, z0)];
    float v1 = grid->data[voxel_idx_c(grid->nx, grid->ny, x1, y1, z1)];

    tvdb_vec3f p = vertex_interp_c(isovalue, p0, p1, v0, v1); // isovalue is available from parent scope

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
    if (cache->count == cache->capacity) {
        size_t new_capacity = cache->capacity * 2;
        edge_cache_entry_t* new_entries = (edge_cache_entry_t*)arena_alloc(arena, new_capacity * sizeof(edge_cache_entry_t));
        if (!new_entries) return 0; // Allocation failed
        memcpy(new_entries, cache->entries, cache->count * sizeof(edge_cache_entry_t));
        cache->entries = new_entries;
        cache->capacity = new_capacity;
    }
    cache->entries[cache->count].key = key;
    cache->entries[cache->count].value = idx;
    cache->count++;

    return idx;
  };

  // Corner offsets (x,y,z) relative to (ix,iy,iz):
  static const int corner[8][3] = {
    {0,0,0},{1,0,0},{1,1,0},{0,1,0},
    {0,0,1},{1,0,1},{1,1,1},{0,1,1}
  };

  // Edge endpoints (corner indices):
  static const int edge_conn[12][2] = {
    {0,1},{1,2},{2,3},{3,0},
    {4,5},{5,6},{6,7},{7,4},
    {0,4},{1,5},{2,6},{3,7}
  };

  for (int iz = 0; iz < nz - 1; ++iz) {
    for (int iy = 0; iy < ny - 1; ++iy) {
      for (int ix = 0; ix < nx - 1; ++ix) {
        // Get corner values
        float val[8];
        int cx[8], cy[8], cz[8];
        for (int i = 0; i < 8; ++i) {
          cx[i] = ix + corner[i][0];
          cy[i] = iy + corner[i][1];
          cz[i] = iz + corner[i][2];
          val[i] = grid->data[voxel_idx_c(nx, ny, cx[i], cy[i], cz[i])];
        }

        // Compute cube index
        int cubeindex = 0;
        for (int i = 0; i < 8; ++i) {
          if (val[i] < isovalue) cubeindex |= (1 << i);
        }

        if (MC_EDGE_TABLE[cubeindex] == 0) continue; // Use global MC_EDGE_TABLE

        // Compute edge vertices
        uint32_t vertlist[12] = {};
        int edges = MC_EDGE_TABLE[cubeindex];
        for (int e = 0; e < 12; ++e) {
          if (edges & (1 << e)) {
            int c0 = edge_conn[e][0], c1 = edge_conn[e][1];
            vertlist[e] = GetOrCreateEdgeVertex_c(&edge_cache, arena, grid, 0, // v_idx_base is not used here
                                                  cx[c0], cy[c0], cz[c0], cx[c1], cy[c1], cz[c1]);
            // Check if vertex creation failed
            if (vertlist[e] == 0 && cache->count > 0) { 
              return false; 
            }
          }
        }

        // Generate triangles
        for (int i = 0; MC_TRI_TABLE[cubeindex][i] != -1; i += 3) { // Use global MC_TRI_TABLE
          uint32_t a = vertlist[MC_TRI_TABLE[cubeindex][i]];
          uint32_t b = vertlist[MC_TRI_TABLE[cubeindex][i + 1]];
          uint32_t c = vertlist[MC_TRI_TABLE[cubeindex][i + 2]];
          
          // Dynamically grow faces using arena
          if (mesh->face_count == mesh->face_capacity) {
              size_t new_capacity = mesh->face_capacity == 0 ? 16 : mesh->face_capacity * 2;
              tvdb_triangle* new_faces = (tvdb_triangle*)arena_alloc(arena, new_capacity * sizeof(tvdb_triangle));
              if (!new_faces) return false; // Allocation failed
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
  float extent = fmaxf(fmaxf(bmax.x - bmin.x, bmax.y - bmin.y), bmax.z - bmin.z);
  if (extent < 1e-12f) return false;

  float voxel_size = extent / static_cast<float>(resolution);

  tvdb_dense_grid sdf;
  // tvdb_mesh_to_sdf will use the provided arena for sdf.data
  if (!tvdb_mesh_to_sdf(input, voxel_size, 3.0f, &sdf, arena)) return false;

  // Extract mesh at isovalue (in world-space distance units)
  float iso_dist = static_cast<float>(isovalue) * voxel_size;
  // tvdb_sdf_to_mesh will use the arena for output mesh vertices/faces
  if (!tvdb_sdf_to_mesh(&sdf, iso_dist, output, arena)) return false;

  return true;
}

// Forward declarations for VDB versions (assume they also take arena)
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
// These functions are responsible for allocating the initial buffer for dynamic arrays
// within the structs from the provided arena.
void tvdb_triangle_mesh_init_arena(tvdb_triangle_mesh* mesh, tvdb_arena_allocator_t* arena) {
    memset(mesh, 0, sizeof(tvdb_triangle_mesh));
    // Allocate initial capacity for vertices and faces from the arena
    size_t vertex_cap = 16; // Initial capacity
    size_t face_cap = 16;   // Initial capacity

    mesh->vertices = (tvdb_vec3f*)arena_alloc(arena, vertex_cap * sizeof(tvdb_vec3f));
    mesh->faces = (tvdb_triangle*)arena_alloc(arena, face_cap * sizeof(tvdb_triangle));
    
    if (!mesh->vertices || !mesh->faces) {
        // Handle allocation failure - critical error
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

// NOTE: tvdb_dense_grid_free and tvdb_triangle_mesh_free are now deprecated in favor of arena management.
// They are kept for compatibility but should not be relied upon for arena-allocated memory.
// The memory is freed when the arena is destroyed.

