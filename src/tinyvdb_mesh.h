#pragma once

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>

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
bool tvdb_mesh_to_sdf(const tvdb_triangle_mesh* mesh,
                      float voxel_size,
                      float band_width,
                      tvdb_dense_grid* grid);

bool tvdb_sdf_to_mesh(const tvdb_dense_grid* grid,
                      float isovalue,
                      tvdb_triangle_mesh* mesh);

bool tvdb_make_manifold(const tvdb_triangle_mesh* input,
                        double resolution,
                        double isovalue,
                        tvdb_triangle_mesh* output);

typedef enum {
  TVDB_SIGN_FLOOD_FILL = 0,
  TVDB_SIGN_SWEEP = 1,
} tvdb_sign_method;

bool tvdb_mesh_to_sdf_vdb(const tvdb_triangle_mesh* mesh,
                          float voxel_size,
                          float band_width,
                          tvdb_dense_grid* grid,
                          tvdb_sign_method sign_method);

bool tvdb_make_manifold_vdb(const tvdb_triangle_mesh* input,
                            double resolution,
                            double isovalue,
                            tvdb_triangle_mesh* output,
                            tvdb_sign_method sign_method);

// Memory management
void tvdb_triangle_mesh_init(tvdb_triangle_mesh* mesh);
void tvdb_triangle_mesh_free(tvdb_triangle_mesh* mesh);
void tvdb_dense_grid_init(tvdb_dense_grid* grid, int nx, int ny, int nz);
void tvdb_dense_grid_free(tvdb_dense_grid* grid);

#ifdef __cplusplus
}
#endif
