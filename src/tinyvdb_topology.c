#include "tinyvdb_topology.h"
#include "tinyvdb_sample.h"
#include "tinyvdb_ops_internal.h"

#include <math.h>
#include <stdlib.h>
#include <string.h>

static void* tvdb_alloc_or_arena(size_t bytes, tvdb_arena_allocator_t* arena) {
  if (arena) return tvdb_arena_alloc(arena, bytes);
  return malloc(bytes);
}

static void tvdb_init_grid_buffer(tvdb_dense_grid* g, int nx, int ny, int nz,
                                  float voxel_size, float ox, float oy, float oz,
                                  tvdb_arena_allocator_t* arena) {
  g->nx = nx; g->ny = ny; g->nz = nz;
  g->voxel_size = voxel_size;
  g->ox = ox; g->oy = oy; g->oz = oz;
  size_t bytes = (size_t)nx * (size_t)ny * (size_t)nz * sizeof(float);
  g->data = (float*)tvdb_alloc_or_arena(bytes, arena);
  if (g->data) memset(g->data, 0, bytes);
}

bool tvdb_coarsen_grid(const tvdb_dense_grid* in,
                       int factor,
                       tvdb_dense_grid* out,
                       tvdb_arena_allocator_t* arena) {
  if (!in || !in->data || !out || factor <= 0) return false;
  int nx = (in->nx + factor - 1) / factor;
  int ny = (in->ny + factor - 1) / factor;
  int nz = (in->nz + factor - 1) / factor;
  tvdb_init_grid_buffer(out, nx, ny, nz,
                        in->voxel_size * (float)factor,
                        in->ox, in->oy, in->oz, arena);
  if (!out->data) return false;

  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        double sum = 0.0;
        int count = 0;
        for (int dz = 0; dz < factor; ++dz) {
          int sz = iz * factor + dz; if (sz >= in->nz) break;
          for (int dy = 0; dy < factor; ++dy) {
            int sy = iy * factor + dy; if (sy >= in->ny) break;
            for (int dx = 0; dx < factor; ++dx) {
              int sx = ix * factor + dx; if (sx >= in->nx) break;
              sum += in->data[tvdb_idx(in, sx, sy, sz)];
              ++count;
            }
          }
        }
        out->data[tvdb_idx(out, ix, iy, iz)] = count ? (float)(sum / (double)count) : 0.0f;
      }
    }
  }
  return true;
}

bool tvdb_refine_grid(const tvdb_dense_grid* in,
                      int factor,
                      tvdb_dense_grid* out,
                      tvdb_arena_allocator_t* arena) {
  if (!in || !in->data || !out || factor <= 0) return false;
  int nx = in->nx * factor;
  int ny = in->ny * factor;
  int nz = in->nz * factor;
  float new_vs = in->voxel_size / (float)factor;
  tvdb_init_grid_buffer(out, nx, ny, nz, new_vs,
                        in->ox, in->oy, in->oz, arena);
  if (!out->data) return false;

  for (int iz = 0; iz < nz; ++iz) {
    float wz = out->oz + ((float)iz + 0.5f) * new_vs;
    for (int iy = 0; iy < ny; ++iy) {
      float wy = out->oy + ((float)iy + 0.5f) * new_vs;
      for (int ix = 0; ix < nx; ++ix) {
        float wx = out->ox + ((float)ix + 0.5f) * new_vs;
        out->data[tvdb_idx(out, ix, iy, iz)] = tvdb_sample_trilinear_dense(in, wx, wy, wz);
      }
    }
  }
  return true;
}

void tvdb_prune_grid(tvdb_dense_grid* g, float background, float tolerance) {
  if (!g || !g->data) return;
  size_t n = (size_t)g->nx * (size_t)g->ny * (size_t)g->nz;
  for (size_t i = 0; i < n; ++i) {
    if (fabsf(g->data[i] - background) <= tolerance) g->data[i] = background;
  }
}

bool tvdb_clip_grid(const tvdb_dense_grid* in,
                    const float bbox_min[3],
                    const float bbox_max[3],
                    tvdb_dense_grid* out,
                    tvdb_arena_allocator_t* arena) {
  if (!in || !in->data || !out) return false;
  const float vs = in->voxel_size;
  // map world bbox to voxel indices, clamp to grid extents
  int x0 = (int)floorf((bbox_min[0] - in->ox) / vs);
  int y0 = (int)floorf((bbox_min[1] - in->oy) / vs);
  int z0 = (int)floorf((bbox_min[2] - in->oz) / vs);
  int x1 = (int)ceilf ((bbox_max[0] - in->ox) / vs);
  int y1 = (int)ceilf ((bbox_max[1] - in->oy) / vs);
  int z1 = (int)ceilf ((bbox_max[2] - in->oz) / vs);
  if (x0 < 0) x0 = 0; if (y0 < 0) y0 = 0; if (z0 < 0) z0 = 0;
  if (x1 > in->nx) x1 = in->nx; if (y1 > in->ny) y1 = in->ny; if (z1 > in->nz) z1 = in->nz;
  if (x1 <= x0 || y1 <= y0 || z1 <= z0) return false;

  int nx = x1 - x0, ny = y1 - y0, nz = z1 - z0;
  tvdb_init_grid_buffer(out, nx, ny, nz, vs,
                        in->ox + (float)x0 * vs,
                        in->oy + (float)y0 * vs,
                        in->oz + (float)z0 * vs,
                        arena);
  if (!out->data) return false;
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        out->data[tvdb_idx(out, ix, iy, iz)] =
            in->data[tvdb_idx(in, ix + x0, iy + y0, iz + z0)];
      }
    }
  }
  return true;
}

bool tvdb_merge_grids(const tvdb_dense_grid* a,
                      const tvdb_dense_grid* b,
                      float background,
                      tvdb_dense_grid* out,
                      tvdb_arena_allocator_t* arena) {
  if (!a || !b || !out || !a->data || !b->data) return false;
  if (fabsf(a->voxel_size - b->voxel_size) > 1e-6f) return false;
  const float vs = a->voxel_size;

  // World bboxes
  float ax0 = a->ox, ay0 = a->oy, az0 = a->oz;
  float ax1 = ax0 + (float)a->nx * vs, ay1 = ay0 + (float)a->ny * vs, az1 = az0 + (float)a->nz * vs;
  float bx0 = b->ox, by0 = b->oy, bz0 = b->oz;
  float bx1 = bx0 + (float)b->nx * vs, by1 = by0 + (float)b->ny * vs, bz1 = bz0 + (float)b->nz * vs;

  float ox = ax0 < bx0 ? ax0 : bx0;
  float oy = ay0 < by0 ? ay0 : by0;
  float oz = az0 < bz0 ? az0 : bz0;
  float mx = ax1 > bx1 ? ax1 : bx1;
  float my = ay1 > by1 ? ay1 : by1;
  float mz = az1 > bz1 ? az1 : bz1;
  int nx = (int)ceilf((mx - ox) / vs);
  int ny = (int)ceilf((my - oy) / vs);
  int nz = (int)ceilf((mz - oz) / vs);

  tvdb_init_grid_buffer(out, nx, ny, nz, vs, ox, oy, oz, arena);
  if (!out->data) return false;
  // fill with background
  size_t total = (size_t)nx * (size_t)ny * (size_t)nz;
  for (size_t i = 0; i < total; ++i) out->data[i] = background;

  // Helper to splat one input into out using min for SDF union semantics.
  #define MERGE_FROM(SRC) do {                                                  \
    int sx0 = (int)roundf(((SRC)->ox - ox) / vs);                               \
    int sy0 = (int)roundf(((SRC)->oy - oy) / vs);                               \
    int sz0 = (int)roundf(((SRC)->oz - oz) / vs);                               \
    for (int iz = 0; iz < (SRC)->nz; ++iz)                                      \
      for (int iy = 0; iy < (SRC)->ny; ++iy)                                    \
        for (int ix = 0; ix < (SRC)->nx; ++ix) {                                \
          int ox_ = ix + sx0, oy_ = iy + sy0, oz_ = iz + sz0;                   \
          if (ox_ < 0 || oy_ < 0 || oz_ < 0) continue;                          \
          if (ox_ >= nx || oy_ >= ny || oz_ >= nz) continue;                    \
          float sv = (SRC)->data[tvdb_idx((SRC), ix, iy, iz)];                  \
          size_t oi = tvdb_idx(out, ox_, oy_, oz_);                             \
          if (sv < out->data[oi]) out->data[oi] = sv;                           \
        }                                                                       \
  } while (0)
  MERGE_FROM(a);
  MERGE_FROM(b);
  #undef MERGE_FROM
  return true;
}

static void tvdb_pool_impl(const tvdb_dense_grid* in,
                           int kx, int ky, int kz,
                           tvdb_dense_grid* out,
                           tvdb_arena_allocator_t* arena,
                           int is_max) {
  if (!in || !in->data || !out || kx <= 0 || ky <= 0 || kz <= 0) return;
  int nx = (in->nx + kx - 1) / kx;
  int ny = (in->ny + ky - 1) / ky;
  int nz = (in->nz + kz - 1) / kz;
  tvdb_init_grid_buffer(out, nx, ny, nz, in->voxel_size,
                        in->ox, in->oy, in->oz, arena);
  if (!out->data) return;

  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        float r = is_max ? -INFINITY : 0.0f;
        int count = 0;
        for (int dz = 0; dz < kz; ++dz) {
          int sz = iz * kz + dz; if (sz >= in->nz) break;
          for (int dy = 0; dy < ky; ++dy) {
            int sy = iy * ky + dy; if (sy >= in->ny) break;
            for (int dx = 0; dx < kx; ++dx) {
              int sx = ix * kx + dx; if (sx >= in->nx) break;
              float v = in->data[tvdb_idx(in, sx, sy, sz)];
              if (is_max) { if (v > r) r = v; }
              else        { r += v; }
              ++count;
            }
          }
        }
        out->data[tvdb_idx(out, ix, iy, iz)] = is_max ? r : (count ? r / (float)count : 0.0f);
      }
    }
  }
}

void tvdb_max_pool(const tvdb_dense_grid* in,
                   int kx, int ky, int kz,
                   tvdb_dense_grid* out,
                   tvdb_arena_allocator_t* arena) {
  tvdb_pool_impl(in, kx, ky, kz, out, arena, /*is_max=*/1);
}
void tvdb_avg_pool(const tvdb_dense_grid* in,
                   int kx, int ky, int kz,
                   tvdb_dense_grid* out,
                   tvdb_arena_allocator_t* arena) {
  tvdb_pool_impl(in, kx, ky, kz, out, arena, /*is_max=*/0);
}
