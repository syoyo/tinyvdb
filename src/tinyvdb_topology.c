#include "tinyvdb_topology.h"
#include "tinyvdb_sample.h"
#include "tinyvdb_ops_internal.h"

#include <math.h>
#include <stdlib.h>
#include <string.h>

/* The reshape and pool loops below are `collapse(2)` over (iz, iy): each output
 * voxel is a pure function of its own input window, and partitioning by z-plane
 * keeps every thread's writes contiguous, so there is nothing to synchronize.
 * They were serial even though every comparable kernel in tinyvdb_ops.c is
 * parallel. schedule(static) keeps the result independent of the thread count.
 * tvdb_merge_grids is the exception -- see the note on MERGE_FROM. */

static void* tvdb_alloc_or_arena(size_t bytes, tvdb_arena_allocator_t* arena) {
  if (arena) return tvdb_arena_alloc_uninit(arena, bytes, 32);
  return malloc(bytes);
}

/* Builds the output descriptor locally and assigns it to `g` only once the
 * dimensions, spacing and origin are valid and the buffer is allocated, so a
 * rejected spacing (e.g. a coarsened voxel size that overflows to inf, or a
 * refined one that underflows to 0) or a failed allocation leaves the caller's
 * prior output untouched, as the header promises. */
static bool tvdb_init_grid_buffer(tvdb_dense_grid* g, int nx, int ny, int nz,
                                  float voxel_size, float ox, float oy, float oz,
                                  tvdb_arena_allocator_t* arena) {
  size_t bytes;
  if (!tvdb_grid_bytes(nx,ny,nz,sizeof(float),&bytes) || !isfinite(voxel_size) || voxel_size <= 0 ||
      !isfinite(ox) || !isfinite(oy) || !isfinite(oz)) {
    return false;
  }
  float* data = (float*)tvdb_alloc_or_arena(bytes, arena);
  if (!data) return false;
  memset(data, 0, bytes);
  g->nx = nx; g->ny = ny; g->nz = nz;
  g->voxel_size = voxel_size;
  g->ox = ox; g->oy = oy; g->oz = oz;
  g->data = data;
  return true;
}

bool tvdb_coarsen_grid(const tvdb_dense_grid* in,
                       int factor,
                       tvdb_dense_grid* out,
                       tvdb_arena_allocator_t* arena) {
  if (!in || !out || in == out || !isfinite(in->ox) || !isfinite(in->oy) || !isfinite(in->oz) || !tvdb_grid_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,sizeof(float)) || factor <= 0) return false;
  int nx = in->nx / factor + (in->nx % factor != 0);
  int ny = in->ny / factor + (in->ny % factor != 0);
  int nz = in->nz / factor + (in->nz % factor != 0);
  if (!tvdb_init_grid_buffer(out, nx, ny, nz,
                        in->voxel_size * (float)factor,
                        in->ox, in->oy, in->oz, arena)) return false;

  #pragma omp parallel for collapse(2) schedule(static)
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        double sum = 0.0;
        size_t count = 0;
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

// Border-clamped voxel read (for nearest / quadratic stencils).
static inline float tvdb_topo_get(const tvdb_dense_grid* g, int ix, int iy, int iz) {
  if (ix < 0) ix = 0; else if (ix >= g->nx) ix = g->nx - 1;
  if (iy < 0) iy = 0; else if (iy >= g->ny) iy = g->ny - 1;
  if (iz < 0) iz = 0; else if (iz >= g->nz) iz = g->nz - 1;
  return g->data[((size_t)iz * g->ny + iy) * g->nx + ix];
}

// 3-point parabola through (val[0], val[1], val[2]) at offsets (-1,0,1),
// evaluated at `w` in [0,1) relative to val[1] (OpenVDB QuadraticSampler).
static inline float tvdb_quad1(const float* val, float w) {
  float a = 0.5f * (val[0] + val[2]) - val[1];
  float b = 0.5f * (val[2] - val[0]);
  float c = val[1];
  return w * (w * a + b) + c;
}

static float tvdb_sample_nearest_world(const tvdb_dense_grid* g, float wx, float wy, float wz) {
  double q_ix=tvdb_sample_coord(((double)wx-g->ox)/g->voxel_size-0.5,g->nx);
  int ix=tvdb_sample_floor(floor(q_ix+0.5),g->nx);
  double q_iy=tvdb_sample_coord(((double)wy-g->oy)/g->voxel_size-0.5,g->ny);
  int iy=tvdb_sample_floor(floor(q_iy+0.5),g->ny);
  double q_iz=tvdb_sample_coord(((double)wz-g->oz)/g->voxel_size-0.5,g->nz);
  int iz=tvdb_sample_floor(floor(q_iz+0.5),g->nz);
  return tvdb_topo_get(g, ix, iy, iz);
}

static float tvdb_sample_triquadratic_world(const tvdb_dense_grid* g, float wx, float wy, float wz) {
  return tvdb_sample_quadratic_dense(g,wx,wy,wz);
}

bool tvdb_resample_grid(const tvdb_dense_grid* in,
                        float voxel_size,
                        int order,
                        tvdb_dense_grid* out,
                        tvdb_arena_allocator_t* arena) {
  if (!in || !out || in == out || !isfinite(in->ox) || !isfinite(in->oy) || !isfinite(in->oz) || !tvdb_grid_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,sizeof(float)) || !isfinite(voxel_size) || voxel_size <= 0.0f) return false;
  if (order < 0 || order > 2) return false;
  // Preserve the world AABB: out spans [origin, origin + dim_in*vs_in].
  double d_nx = ceil((double)in->nx * in->voxel_size / voxel_size);
  if (!isfinite(d_nx) || d_nx > INT_MAX) return false;
  int nx = (int)d_nx;
  double d_ny = ceil((double)in->ny * in->voxel_size / voxel_size);
  if (!isfinite(d_ny) || d_ny > INT_MAX) return false;
  int ny = (int)d_ny;
  double d_nz = ceil((double)in->nz * in->voxel_size / voxel_size);
  if (!isfinite(d_nz) || d_nz > INT_MAX) return false;
  int nz = (int)d_nz;
  if (nx < 1) nx = 1; if (ny < 1) ny = 1; if (nz < 1) nz = 1;
  if (!tvdb_init_grid_buffer(out, nx, ny, nz, voxel_size, in->ox, in->oy, in->oz, arena)) return false;

  tvdb_sampler samp;
  const bool have_samp = (order == 1) && tvdb_sampler_init(&samp, in);
  #pragma omp parallel for collapse(2) schedule(static)
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      /* Inside the collapsed pair, not between the loops: collapse(2) needs the
         loops perfectly nested, and hoisting these two lines out of the body is
         what broke that. */
      float wz = out->oz + ((float)iz + 0.5f) * voxel_size;
      float wy = out->oy + ((float)iy + 0.5f) * voxel_size;
      for (int ix = 0; ix < nx; ++ix) {
        float wx = out->ox + ((float)ix + 0.5f) * voxel_size;
        float val;
        if (order == 0)      val = tvdb_sample_nearest_world(in, wx, wy, wz);
        else if (order == 1) val = have_samp ? tvdb_sampler_trilinear(&samp, wx, wy, wz)
                                             : tvdb_sample_trilinear_dense(in, wx, wy, wz);
        else                 val = tvdb_sample_triquadratic_world(in, wx, wy, wz);
        out->data[tvdb_idx(out, ix, iy, iz)] = val;
      }
    }
  }
  return true;
}

bool tvdb_refine_grid(const tvdb_dense_grid* in,
                      int factor,
                      tvdb_dense_grid* out,
                      tvdb_arena_allocator_t* arena) {
  if (!in || !out || in == out || !isfinite(in->ox) || !isfinite(in->oy) || !isfinite(in->oz) || !tvdb_grid_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,sizeof(float)) || factor <= 0) return false;
  if (in->nx > INT_MAX / factor) return false;
  int nx = in->nx * factor;
  if (in->ny > INT_MAX / factor) return false;
  int ny = in->ny * factor;
  if (in->nz > INT_MAX / factor) return false;
  int nz = in->nz * factor;
  float new_vs = in->voxel_size / (float)factor;
  if (!tvdb_init_grid_buffer(out, nx, ny, nz, new_vs,
                        in->ox, in->oy, in->oz, arena)) return false;

  tvdb_sampler samp;
  const bool have_samp = tvdb_sampler_init(&samp, in);
  #pragma omp parallel for collapse(2) schedule(static)
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      float wz = out->oz + ((float)iz + 0.5f) * new_vs;
      float wy = out->oy + ((float)iy + 0.5f) * new_vs;
      for (int ix = 0; ix < nx; ++ix) {
        float wx = out->ox + ((float)ix + 0.5f) * new_vs;
        out->data[tvdb_idx(out, ix, iy, iz)] = have_samp
            ? tvdb_sampler_trilinear(&samp, wx, wy, wz)
            : tvdb_sample_trilinear_dense(in, wx, wy, wz);
      }
    }
  }
  return true;
}

void tvdb_prune_grid(tvdb_dense_grid* g, float background, float tolerance) {
  /* The voxel count used to be computed behind only `g && g->data`, so a
     negative extent made (size_t)nx*ny*nz wrap to a huge value and the loop both
     read and wrote out of bounds. Every sibling in this file goes through
     tvdb_grid_valid; do the same. */
  if (!g || !g->data || g->nx <= 0 || g->ny <= 0 || g->nz <= 0) return;
  size_t n;
  if (!tvdb_grid_bytes(g->nx, g->ny, g->nz, sizeof(float), &n)) return;
  n /= sizeof(float);
  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)n; ++i) {
    if (fabsf(g->data[i] - background) <= tolerance) g->data[i] = background;
  }
}

bool tvdb_clip_grid(const tvdb_dense_grid* in,
                    const float bbox_min[3],
                    const float bbox_max[3],
                    tvdb_dense_grid* out,
                    tvdb_arena_allocator_t* arena) {
  if (!in || !out || in == out || !isfinite(in->ox) || !isfinite(in->oy) || !isfinite(in->oz) || !tvdb_grid_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,sizeof(float))) return false;
  if (!bbox_min || !bbox_max) return false;
  for (int k=0;k<3;++k) if (!isfinite(bbox_min[k]) || !isfinite(bbox_max[k]) || bbox_min[k] > bbox_max[k]) return false;
  const float vs = in->voxel_size;
  // map world bbox to voxel indices, clamp to grid extents
  double lo_x=floor(((double)bbox_min[0]-in->ox)/vs);
  int x0=(int)fmin(fmax(lo_x,0),in->nx);
  double lo_y=floor(((double)bbox_min[1]-in->oy)/vs);
  int y0=(int)fmin(fmax(lo_y,0),in->ny);
  double lo_z=floor(((double)bbox_min[2]-in->oz)/vs);
  int z0=(int)fmin(fmax(lo_z,0),in->nz);
  double hi_x=ceil(((double)bbox_max[0]-in->ox)/vs);
  int x1=(int)fmin(fmax(hi_x,0),in->nx);
  double hi_y=ceil(((double)bbox_max[1]-in->oy)/vs);
  int y1=(int)fmin(fmax(hi_y,0),in->ny);
  double hi_z=ceil(((double)bbox_max[2]-in->oz)/vs);
  int z1=(int)fmin(fmax(hi_z,0),in->nz);
  if (x0 < 0) x0 = 0; if (y0 < 0) y0 = 0; if (z0 < 0) z0 = 0;
  if (x1 > in->nx) x1 = in->nx; if (y1 > in->ny) y1 = in->ny; if (z1 > in->nz) z1 = in->nz;
  if (x1 <= x0 || y1 <= y0 || z1 <= z0) return false;

  int nx = x1 - x0, ny = y1 - y0, nz = z1 - z0;
  if (!tvdb_init_grid_buffer(out, nx, ny, nz, vs,
                        in->ox + (float)x0 * vs,
                        in->oy + (float)y0 * vs,
                        in->oz + (float)z0 * vs,
                        arena)) return false;
  #pragma omp parallel for collapse(2) schedule(static)
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
  if (!a || !b || !out || out == a || out == b ||
      !isfinite(a->ox) || !isfinite(a->oy) || !isfinite(a->oz) ||
      !isfinite(b->ox) || !isfinite(b->oy) || !isfinite(b->oz) ||
      !tvdb_grid_valid(a->nx,a->ny,a->nz,a->voxel_size,a->data,sizeof(float)) ||
      !tvdb_grid_valid(b->nx,b->ny,b->nz,b->voxel_size,b->data,sizeof(float))) return false;
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
  double d_nx=ceil(((double)mx-ox)/vs);
  if (!isfinite(d_nx) || d_nx < 1 || d_nx > INT_MAX) return false;
  int nx=(int)d_nx;
  double d_ny=ceil(((double)my-oy)/vs);
  if (!isfinite(d_ny) || d_ny < 1 || d_ny > INT_MAX) return false;
  int ny=(int)d_ny;
  double d_nz=ceil(((double)mz-oz)/vs);
  if (!isfinite(d_nz) || d_nz < 1 || d_nz > INT_MAX) return false;
  int nz=(int)d_nz;

  if (!tvdb_init_grid_buffer(out, nx, ny, nz, vs, ox, oy, oz, arena)) return false;
  // fill with background
  size_t total = (size_t)nx * (size_t)ny * (size_t)nz;
  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)total; ++i) out->data[i] = background;

  // Helper to splat one input into out using min for SDF union semantics.
  // Deliberately serial: every voxel is a read-modify-write min on out->data,
  // and the two splats can land on the same output voxel, so parallelising
  // it would drop updates. Only the background fill above is independent.
  #define MERGE_FROM(SRC) do {                                                  \
    int sx0 = (int)roundf(((SRC)->ox - ox) / vs);                               \
    int sy0 = (int)roundf(((SRC)->oy - oy) / vs);                               \
    int sz0 = (int)roundf(((SRC)->oz - oz) / vs);                               \
    for (int iz = 0; iz < (SRC)->nz; ++iz)                                      \
      for (int iy = 0; iy < (SRC)->ny; ++iy)                                    \
        for (int ix = 0; ix < (SRC)->nx; ++ix) {                                \
          int64_t ox_ = (int64_t)ix + sx0, oy_ = (int64_t)iy + sy0, oz_ = (int64_t)iz + sz0;                   \
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
  if (!in || !out || in == out || !isfinite(in->ox) || !isfinite(in->oy) || !isfinite(in->oz) || !tvdb_grid_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,sizeof(float)) || kx <= 0 || ky <= 0 || kz <= 0) return;
  int nx = in->nx / kx + (in->nx % kx != 0);
  int ny = in->ny / ky + (in->ny % ky != 0);
  int nz = in->nz / kz + (in->nz % kz != 0);
  if (!tvdb_init_grid_buffer(out, nx, ny, nz, in->voxel_size,
                        in->ox, in->oy, in->oz, arena)) {
    /* The void pooling API reports failure through a NULL output buffer. */
    out->data = NULL; out->nx = out->ny = out->nz = 0;
    return;
  }

  #pragma omp parallel for collapse(2) schedule(static)
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        float r = is_max ? -INFINITY : 0.0f;
        size_t count = 0;
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
