#pragma once

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include "tvdb_memory.h"

// Data types
typedef struct {
  float x, y, z;
} tvdb_vec3f;

typedef struct {
  uint32_t v0, v1, v2;
} tvdb_triangle;

typedef struct {
  tvdb_vec3f* vertices;
  size_t vertex_count;
  size_t vertex_capacity;
  tvdb_triangle* faces;
  size_t face_count;
  size_t face_capacity;
} tvdb_triangle_mesh;

typedef struct {
  int nx, ny, nz;
  float ox, oy, oz;
  float voxel_size;
  float* data;
} tvdb_dense_grid;

// API
// These functions now require an arena allocator for internal memory management.
bool tvdb_mesh_to_sdf(const tvdb_triangle_mesh* mesh,
                      float voxel_size,
                      float band_width,
                      tvdb_dense_grid* grid,
                      tvdb_arena_allocator_t* arena);

bool tvdb_sdf_to_mesh(const tvdb_dense_grid* grid,
                      float isovalue,
                      tvdb_triangle_mesh* mesh,
                      tvdb_arena_allocator_t* arena);

bool tvdb_make_manifold(const tvdb_triangle_mesh* input,
                        double resolution,
                        double isovalue,
                        tvdb_triangle_mesh* output,
                        tvdb_arena_allocator_t* arena);

typedef enum {
  TVDB_SIGN_FLOOD_FILL = 0,
  TVDB_SIGN_SWEEP = 1,
} tvdb_sign_method;

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

// Memory management - these will now use the arena passed to the higher-level functions
// Existing init/free functions can be kept for compatibility or removed if not used directly.
void tvdb_triangle_mesh_init_arena(tvdb_triangle_mesh* mesh, tvdb_arena_allocator_t* arena);
void tvdb_dense_grid_init_arena(tvdb_dense_grid* grid, int nx, int ny, int nz, tvdb_arena_allocator_t* arena);

#ifdef __cplusplus
}
#endif
