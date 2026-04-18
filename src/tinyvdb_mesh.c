#include "tinyvdb_mesh.h"
#include "tvdb_memory.h" // Include the memory arena header
#include <string.h>
#include <stdio.h>
#include <math.h>
#include <assert.h>

// Helper to allocate from an arena
static void* arena_alloc(tvdb_arena_allocator_t* arena, size_t size) {
    if (!arena) return malloc(size); // Fallback if no arena is provided
    return tvdb_arena_alloc(arena, size);
}

// Memory management using arena
void tvdb_triangle_mesh_init_arena(tvdb_triangle_mesh* mesh, tvdb_arena_allocator_t* arena) {
  memset(mesh, 0, sizeof(tvdb_triangle_mesh));
  // Allocation will be handled by the calling function using the arena
}

void tvdb_dense_grid_init_arena(tvdb_dense_grid* grid, int nx, int ny, int nz, tvdb_arena_allocator_t* arena) {
  grid->nx = nx; grid->ny = ny; grid->nz = nz;
  // Allocate data using the arena
  grid->data = (float*)arena_alloc(arena, (size_t)nx * ny * nz * sizeof(float));
}

// NOTE: We are not providing a free function for arena-allocated memory.
// The arena itself is destroyed after the operation scope.

// Keep original init/free for potential direct use or fallback, though ideally replaced.
// However, the new API requires an arena, so direct use of these might be phased out.
void tvdb_triangle_mesh_init(tvdb_triangle_mesh* mesh) {
  memset(mesh, 0, sizeof(tvdb_triangle_mesh));
}

void tvdb_triangle_mesh_free(tvdb_triangle_mesh* mesh) {
  // This function should ideally not be called if memory is arena-managed and the arena is destroyed.
  // If it's called, it implies memory not managed by the arena, so we fall back to free.
  if (mesh->vertices) free(mesh->vertices);
  if (mesh->faces) free(mesh->faces);
  tvdb_triangle_mesh_init(mesh); // Reset struct
}

void tvdb_dense_grid_init(tvdb_dense_grid* grid, int nx, int ny, int nz) {
  // This function should ideally not be called if memory is arena-managed.
  // Fallback to malloc.
  grid->nx = nx; grid->ny = ny; grid->nz = nz;
  grid->data = (float*)malloc((size_t)nx * ny * nz * sizeof(float));
}

void tvdb_dense_grid_free(tvdb_dense_grid* grid) {
  // This function should ideally not be called if memory is arena-managed.
  // Fallback to free.
  if (grid->data) free(grid->data);
  grid->data = NULL;
}

// Helpers (unchanged)
static inline float dot(tvdb_vec3f a, tvdb_vec3f b) {
  return a.x * b.x + a.y * b.y + a.z * b.z;
}

static inline tvdb_vec3f sub(tvdb_vec3f a, tvdb_vec3f b) {
  return (tvdb_vec3f){a.x - b.x, a.y - b.y, a.z - b.z};
}

static inline tvdb_vec3f add(tvdb_vec3f a, tvdb_vec3f b) {
  return (tvdb_vec3f){a.x + b.x, a.y + b.y, a.z + b.z};
}

static inline tvdb_vec3f mul(tvdb_vec3f a, float s) {
  return (tvdb_vec3f){a.x * s, a.y * s, a.z * s};
}

static float dist_sq(tvdb_vec3f a, tvdb_vec3f b) {
  tvdb_vec3f d = sub(a, b);
  return dot(d, d);
}

static float point_triangle_dist_sq(tvdb_vec3f p, tvdb_vec3f a, tvdb_vec3f b, tvdb_vec3f c) {
  tvdb_vec3f ab = sub(b, a), ac = sub(c, a), ap = sub(p, a);
  float d1 = dot(ab, ap), d2 = dot(ac, ap);
  if (d1 <= 0.0f && d2 <= 0.0f) return dist_sq(p, a);

  tvdb_vec3f bp = sub(p, b);
  float d3 = dot(ab, bp), d4 = dot(ac, bp);
  if (d3 >= 0.0f && d4 <= d3) return dist_sq(p, b);

  float vc = d1 * d4 - d3 * d2;
  if (vc <= 0.0f && d1 >= 0.0f && d3 <= 0.0f) {
    float v = d1 / (d1 - d3);
    return dist_sq(p, add(a, mul(ab, v)));
  }

  tvdb_vec3f cp = sub(p, c);
  float d5 = dot(ab, cp), d6 = dot(ac, cp);
  if (d6 >= 0.0f && d5 <= d6) return dist_sq(p, c);

  float vb = d5 * d2 - d1 * d6;
  if (vb <= 0.0f && d2 >= 0.0f && d6 <= 0.0f) {
    float w = d2 / (d2 - d6);
    return dist_sq(p, add(a, mul(ac, w)));
  }

  float va = d3 * d6 - d5 * d4;
  if (va <= 0.0f && (d4 - d3) >= 0.0f && (d5 - d6) >= 0.0f) {
    float w = (d4 - d3) / ((d4 - d3) + (d5 - d6));
    return dist_sq(p, add(b, mul(sub(c, b), w)));
  }

  float denom = 1.0f / (va + vb + vc);
  return dist_sq(p, add(add(a, mul(ab, vb * denom)), mul(ac, vc * denom)));
}

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
  bmin = sub(bmin, (tvdb_vec3f){pad, pad, pad});
  bmax = add(bmax, (tvdb_vec3f){pad, pad, pad});

  int nx = (int)ceil((bmax.x - bmin.x) / voxel_size) + 1;
  int ny = (int)ceil((bmax.y - bmin.y) / voxel_size) + 1;
  int nz = (int)ceil((bmax.z - bmin.z) / voxel_size) + 1;

  // Use arena for grid data allocation
  tvdb_dense_grid_init_arena(grid, nx, ny, nz, arena);
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
          float distsq = point_triangle_dist_sq(p, mesh->vertices[mesh->faces[t].v0],
                                                   mesh->vertices[mesh->faces[t].v1],
                                                   mesh->vertices[mesh->faces[t].v2]);
          if (distsq < dsq) dsq = distsq;
        }
        grid->data[ix + nx * (iy + ny * iz)] = sqrtf(dsq);
      }
    }
  }
  return true;
}

bool tvdb_sdf_to_mesh(const tvdb_dense_grid* grid, float isovalue, tvdb_triangle_mesh* mesh, tvdb_arena_allocator_t* arena) {
  if (!mesh || !grid || !arena) return false;
  tvdb_triangle_mesh_init_arena(mesh, arena); // Initialize mesh using arena

  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  if (nx < 2 || ny < 2 || nz < 2) return false;

  // Edge-to-vertex cache: key = edge encoding, value = vertex index
  // This cache can grow large. Consider an arena for it too, or size it appropriately.
  // For now, it uses std::unordered_map which is part of C++ standard library,
  // but we need to ensure memory for its nodes comes from the arena if possible.
  // Since it's C++ std lib, direct arena integration is tricky.
  // For now, let's assume std::unordered_map uses its own heap allocation,
  // and we'll focus on arena for our own C structs.
  // A better approach would be a C-based hash map using the arena.

  // For now, using default C++ map behavior, which might use malloc.
  // This is a known limitation in this quick port.

  auto VoxelPos = [&](int ix, int iy, int iz) -> tvdb_vec3f {
    return {grid->ox + (ix + 0.5f) * grid->voxel_size,
            grid->oy + (iy + 0.5f) * grid->voxel_size,
            grid->oz + (iz + 0.5f) * grid->voxel_size};
  };

  auto VoxelIdx = [&](int ix, int iy, int iz) -> uint64_t {
    return static_cast<uint64_t>(ix) +
           static_cast<uint64_t>(iy) * nx +
           static_cast<uint64_t>(iz) * nx * ny;
  };

  auto EdgeKey = [&](uint64_t v0, uint64_t v1) -> uint64_t {
    if (v0 > v1) std::swap(v0, v1);
    return (v0 << 32) | v1;
  };

  auto GetOrCreateEdgeVertex = [&](int x0, int y0, int z0,
                                   int x1, int y1, int z1) -> uint32_t {
    uint64_t key = EdgeKey(VoxelIdx(x0, y0, z0), VoxelIdx(x1, y1, z1));
    auto it = edge_cache.find(key);
    if (it != edge_cache.end()) return it->second;

    tvdb_vec3f p0 = VoxelPos(x0, y0, z0);
    tvdb_vec3f p1 = VoxelPos(x1, y1, z1);
    float v0 = grid->data[x0 + nx * (y0 + ny * z0)]; // grid->at(x0,y0,z0) is C++ style
    float v1 = grid->data[x1 + nx * (y1 + ny * z1)]; // grid->at(x1,y1,z1)

    // VertexInterp expects Vec3f, which is compatible.
    tvdb_vec3f p = detail::VertexInterp(isovalue, p0, p1, v0, v1);

    uint32_t idx = static_cast<uint32_t>(mesh->vertex_count);
    // Dynamically grow vertices and faces using arena
    if (mesh->vertex_count == mesh->vertex_capacity) {
        size_t new_capacity = mesh->vertex_capacity == 0 ? 16 : mesh->vertex_capacity * 2;
        tvdb_vec3f* new_vertices = (tvdb_vec3f*)arena_alloc(arena, new_capacity * sizeof(tvdb_vec3f));
        if (!new_vertices) return 0; // Allocation failed, return invalid index
        memcpy(new_vertices, mesh->vertices, mesh->vertex_count * sizeof(tvdb_vec3f));
        mesh->vertices = new_vertices;
        mesh->vertex_capacity = new_capacity;
    }
    mesh->vertices[mesh->vertex_count++] = p;
    
    edge_cache[key] = idx;
    return idx;
  };

  // Cube corners:
  //    4----5
  //   /|   /|
  //  7----6 |
  //  | 0--|-1
  //  |/   |/
  //  3----2
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
          val[i] = grid->data[cx[i] + nx * (cy[i] + ny * cz[i])];
        }

        // Compute cube index
        int cubeindex = 0;
        for (int i = 0; i < 8; ++i) {
          if (val[i] < isovalue) cubeindex |= (1 << i);
        }

        if (detail::MC_EDGE_TABLE[cubeindex] == 0) continue;

        // Compute edge vertices
        uint32_t vertlist[12] = {};
        int edges = detail::MC_EDGE_TABLE[cubeindex];
        for (int e = 0; e < 12; ++e) {
          if (edges & (1 << e)) {
            int c0 = edge_conn[e][0], c1 = edge_conn[e][1];
            vertlist[e] = GetOrCreateEdgeVertex(
                cx[c0], cy[c0], cz[c0], cx[c1], cy[c1], cz[c1]);
          }
        }

        // Generate triangles
        for (int i = 0; detail::MC_TRI_TABLE[cubeindex][i] != -1; i += 3) {
          uint32_t a = vertlist[detail::MC_TRI_TABLE[cubeindex][i]];
          uint32_t b = vertlist[detail::MC_TRI_TABLE[cubeindex][i + 1]];
          uint32_t c = vertlist[detail::MC_TRI_TABLE[cubeindex][i + 2]];
          
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
    bmin = detail::vmin(bmin, input->vertices[i]);
    bmax = detail::vmax(bmax, input->vertices[i]);
  }
  float extent = std::max({bmax.x - bmin.x, bmax.y - bmin.y, bmax.z - bmin.z});
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
    // Allocate initial capacity for vertices and faces from the arena
    size_t vertex_cap = 16; // Initial capacity
    size_t face_cap = 16;   // Initial capacity

    mesh->vertices = (tvdb_vec3f*)arena_alloc(arena, vertex_cap * sizeof(tvdb_vec3f));
    mesh->faces = (tvdb_triangle*)arena_alloc(arena, face_cap * sizeof(tvdb_triangle));
    
    if (!mesh->vertices || !mesh->faces) {
        // Handle allocation failure - this is a critical error in setup
        // In a real scenario, this should propagate an error or assert.
        // For now, we'll leave them NULL and let higher functions fail.
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

