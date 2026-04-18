#include "tinyvdb_mesh.h"
#include <string.h>
#include <stdio.h>
#include <math.h>
#include <assert.h>

void tvdb_triangle_mesh_init(tvdb_triangle_mesh* mesh) {
  memset(mesh, 0, sizeof(tvdb_triangle_mesh));
}

void tvdb_triangle_mesh_free(tvdb_triangle_mesh* mesh) {
  if (mesh->vertices) free(mesh->vertices);
  if (mesh->faces) free(mesh->faces);
  tvdb_triangle_mesh_init(mesh);
}

void tvdb_dense_grid_init(tvdb_dense_grid* grid, int nx, int ny, int nz) {
  grid->nx = nx; grid->ny = ny; grid->nz = nz;
  grid->data = (float*)malloc((size_t)nx * ny * nz * sizeof(float));
}

void tvdb_dense_grid_free(tvdb_dense_grid* grid) {
  if (grid->data) free(grid->data);
  grid->data = NULL;
}

// Helpers
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

bool tvdb_mesh_to_sdf(const tvdb_triangle_mesh* mesh, float voxel_size, float band_width, tvdb_dense_grid* grid) {
  if (!mesh || !grid || mesh->vertex_count == 0) return false;

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

  tvdb_dense_grid_free(grid);
  tvdb_dense_grid_init(grid, nx, ny, nz);
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
