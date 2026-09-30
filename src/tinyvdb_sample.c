#include "tinyvdb_sample.h"
#include "tinyvdb_ops_internal.h"

#include <math.h>
#include <stddef.h>

// Cell-center convention: voxel `i` stores its sample at world position
// `ox + (i + 0.5) * vs`. The voxel-index coordinate of a world point is
// therefore (w - ox)/vs - 0.5, so that vx = i exactly hits voxel i's sample.
static inline void tvdb_world_to_voxel_index(const tvdb_dense_grid* g,
                                             float wx, float wy, float wz,
                                             float* vx, float* vy, float* vz) {
  *vx = (float)tvdb_sample_coord(((double)wx - g->ox) / g->voxel_size - 0.5, g->nx);
  *vy = (float)tvdb_sample_coord(((double)wy - g->oy) / g->voxel_size - 0.5, g->ny);
  *vz = (float)tvdb_sample_coord(((double)wz - g->oz) / g->voxel_size - 0.5, g->nz);
}

float tvdb_sample_trilinear_dense(const tvdb_dense_grid* g,
                                  float wx, float wy, float wz) {
  if (!g || !tvdb_grid_valid(g->nx,g->ny,g->nz,g->voxel_size,g->data,sizeof(float)) ||
      !isfinite(g->ox) || !isfinite(g->oy) || !isfinite(g->oz) ||
      !isfinite(wx) || !isfinite(wy) || !isfinite(wz)) return 0.0f;
  float vx, vy, vz;
  tvdb_world_to_voxel_index(g, wx, wy, wz, &vx, &vy, &vz);
  int ix = tvdb_sample_floor(vx,g->nx), iy = tvdb_sample_floor(vy,g->ny), iz = tvdb_sample_floor(vz,g->nz);
  float fx = vx - (float)ix, fy = vy - (float)iy, fz = vz - (float)iz;

  float c000 = tvdb_at(g, ix,     iy,     iz);
  float c100 = tvdb_at(g, ix + 1, iy,     iz);
  float c010 = tvdb_at(g, ix,     iy + 1, iz);
  float c110 = tvdb_at(g, ix + 1, iy + 1, iz);
  float c001 = tvdb_at(g, ix,     iy,     iz + 1);
  float c101 = tvdb_at(g, ix + 1, iy,     iz + 1);
  float c011 = tvdb_at(g, ix,     iy + 1, iz + 1);
  float c111 = tvdb_at(g, ix + 1, iy + 1, iz + 1);
  float c00 = c000 * (1.0f - fx) + c100 * fx;
  float c10 = c010 * (1.0f - fx) + c110 * fx;
  float c01 = c001 * (1.0f - fx) + c101 * fx;
  float c11 = c011 * (1.0f - fx) + c111 * fx;
  float c0 = c00 * (1.0f - fy) + c10 * fy;
  float c1 = c01 * (1.0f - fy) + c11 * fy;
  return c0 * (1.0f - fz) + c1 * fz;
}

void tvdb_sample_trilinear_dense_batch(const tvdb_dense_grid* g,
                                       const tvdb_vec3f* pts,
                                       size_t n,
                                       float* out) {
  if (!g || (n && (!pts || !out)) || n > LLONG_MAX) return;
  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)n; ++i) {
    out[i] = tvdb_sample_trilinear_dense(g, pts[i].x, pts[i].y, pts[i].z);
  }
}

// 3-point parabola through (val[0],val[1],val[2]) at offsets (-1,0,1) at `w`.
static inline float tvdb_quad1_s(const float* val, float w) {
  float a = 0.5f * (val[0] + val[2]) - val[1];
  float b = 0.5f * (val[2] - val[0]);
  return w * (w * a + b) + val[1];
}

float tvdb_sample_quadratic_dense(const tvdb_dense_grid* g,
                                  float wx, float wy, float wz) {
  if (!g || !tvdb_grid_valid(g->nx,g->ny,g->nz,g->voxel_size,g->data,sizeof(float)) ||
      !isfinite(g->ox) || !isfinite(g->oy) || !isfinite(g->oz) ||
      !isfinite(wx) || !isfinite(wy) || !isfinite(wz)) return 0;
  float cx, cy, cz;
  tvdb_world_to_voxel_index(g,wx,wy,wz,&cx,&cy,&cz);
  int ix = tvdb_sample_floor(cx,g->nx), iy = tvdb_sample_floor(cy,g->ny), iz = tvdb_sample_floor(cz,g->nz);
  float u = cx - ix, v = cy - iy, w = cz - iz;
  float vx[3];
  for (int dx = 0; dx < 3; ++dx) {
    float vy[3];
    for (int dy = 0; dy < 3; ++dy) {
      float vz[3];
      for (int dz = 0; dz < 3; ++dz)
        vz[dz] = tvdb_at(g, (int64_t)ix - 1 + dx, (int64_t)iy - 1 + dy, (int64_t)iz - 1 + dz);  // clamped
      vy[dy] = tvdb_quad1_s(vz, w);
    }
    vx[dx] = tvdb_quad1_s(vy, v);
  }
  return tvdb_quad1_s(vx, u);
}

void tvdb_sample_quadratic_dense_batch(const tvdb_dense_grid* g,
                                       const tvdb_vec3f* pts,
                                       size_t n,
                                       float* out) {
  if (!g || (n && (!pts || !out)) || n > LLONG_MAX) return;
  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)n; ++i) {
    out[i] = tvdb_sample_quadratic_dense(g, pts[i].x, pts[i].y, pts[i].z);
  }
}

void tvdb_sample_trilinear_vec_dense(const tvdb_dense_vec_grid* g,
                                     float wx, float wy, float wz,
                                     tvdb_vec3f* out) {
  if (!out) return;
  if (!g || !tvdb_grid_valid(g->nx,g->ny,g->nz,g->voxel_size,g->data,3*sizeof(float)) ||
      !isfinite(g->ox) || !isfinite(g->oy) || !isfinite(g->oz) ||
      !isfinite(wx) || !isfinite(wy) || !isfinite(wz)) {
    out->x = out->y = out->z = 0.0f;
    return;
  }
  // Same world->voxel mapping (cell-center) as scalar sampler.
  float vx = (float)tvdb_sample_coord(((double)wx - g->ox) / g->voxel_size - 0.5,g->nx);
  float vy = (float)tvdb_sample_coord(((double)wy - g->oy) / g->voxel_size - 0.5,g->ny);
  float vz = (float)tvdb_sample_coord(((double)wz - g->oz) / g->voxel_size - 0.5,g->nz);
  int ix = tvdb_sample_floor(vx,g->nx), iy = tvdb_sample_floor(vy,g->ny), iz = tvdb_sample_floor(vz,g->nz);
  float fx = vx - (float)ix, fy = vy - (float)iy, fz = vz - (float)iz;

  float r[3] = {0.0f, 0.0f, 0.0f};
  for (int c = 0; c < 3; ++c) {
    float c000 = 0, c100 = 0, c010 = 0, c110 = 0, c001 = 0, c101 = 0, c011 = 0, c111 = 0;
    int X0 = tvdb_clamp_i(ix,     0, g->nx - 1);
    int X1 = tvdb_clamp_i(ix + 1, 0, g->nx - 1);
    int Y0 = tvdb_clamp_i(iy,     0, g->ny - 1);
    int Y1 = tvdb_clamp_i(iy + 1, 0, g->ny - 1);
    int Z0 = tvdb_clamp_i(iz,     0, g->nz - 1);
    int Z1 = tvdb_clamp_i(iz + 1, 0, g->nz - 1);
    #define VEC_AT(X, Y, Z) (g->data[((((size_t)(Z) * g->ny + (Y)) * g->nx + (X)) * 3u) + (size_t)c])
    c000 = VEC_AT(X0, Y0, Z0);
    c100 = VEC_AT(X1, Y0, Z0);
    c010 = VEC_AT(X0, Y1, Z0);
    c110 = VEC_AT(X1, Y1, Z0);
    c001 = VEC_AT(X0, Y0, Z1);
    c101 = VEC_AT(X1, Y0, Z1);
    c011 = VEC_AT(X0, Y1, Z1);
    c111 = VEC_AT(X1, Y1, Z1);
    #undef VEC_AT
    float c00 = c000 * (1.0f - fx) + c100 * fx;
    float c10 = c010 * (1.0f - fx) + c110 * fx;
    float c01 = c001 * (1.0f - fx) + c101 * fx;
    float c11 = c011 * (1.0f - fx) + c111 * fx;
    float c0 = c00 * (1.0f - fy) + c10 * fy;
    float c1 = c01 * (1.0f - fy) + c11 * fy;
    r[c] = c0 * (1.0f - fz) + c1 * fz;
  }
  out->x = r[0]; out->y = r[1]; out->z = r[2];
}

void tvdb_splat_trilinear_dense(tvdb_dense_grid* g,
                                const tvdb_vec3f* pts,
                                const float* vals,
                                size_t n,
                                float* weights) {
  if (!g || !tvdb_grid_valid(g->nx,g->ny,g->nz,g->voxel_size,g->data,sizeof(float)) ||
      (n && (!pts || !vals))) return;
  // Multiple points may scatter to the same voxel (write-write hazard).
  // Under OpenMP we use `omp atomic update` per-tap; with no parallelism
  // the omp pragmas vanish and we get the original scalar path.
  #pragma omp parallel for schedule(static)
  for (long long pp = 0; pp < (long long)n; ++pp) {
    size_t p = (size_t)pp;
    float vx, vy, vz;
    double qx = ((double)pts[p].x-g->ox)/g->voxel_size-0.5;
    double qy = ((double)pts[p].y-g->oy)/g->voxel_size-0.5;
    double qz = ((double)pts[p].z-g->oz)/g->voxel_size-0.5;
    if (!isfinite(qx) || !isfinite(qy) || !isfinite(qz) ||
        qx < -1 || qy < -1 || qz < -1 || qx >= g->nx || qy >= g->ny || qz >= g->nz) continue;
    vx=(float)qx; vy=(float)qy; vz=(float)qz;
    int ix = tvdb_sample_floor(vx,g->nx), iy = tvdb_sample_floor(vy,g->ny), iz = tvdb_sample_floor(vz,g->nz);
    float fx = vx - (float)ix, fy = vy - (float)iy, fz = vz - (float)iz;
    if (ix < -1 || iy < -1 || iz < -1) continue;
    if (ix >= g->nx || iy >= g->ny || iz >= g->nz) continue;

    const float v = vals[p];
    for (int dz = 0; dz < 2; ++dz) {
      int z = iz + dz;
      if (z < 0 || z >= g->nz) continue;
      float wz = (dz == 0) ? (1.0f - fz) : fz;
      for (int dy = 0; dy < 2; ++dy) {
        int y = iy + dy;
        if (y < 0 || y >= g->ny) continue;
        float wy = (dy == 0) ? (1.0f - fy) : fy;
        for (int dx = 0; dx < 2; ++dx) {
          int x = ix + dx;
          if (x < 0 || x >= g->nx) continue;
          float wx = (dx == 0) ? (1.0f - fx) : fx;
          float w = wx * wy * wz;
          size_t idx = tvdb_idx(g, x, y, z);
          float wv = w * v;
          #pragma omp atomic update
          g->data[idx] += wv;
          if (weights) {
            #pragma omp atomic update
            weights[idx] += w;
          }
        }
      }
    }
  }
}

// Quadratic basis weights for the 3-point stencil at offsets (-1,0,1), the
// adjoint (scatter) form of tvdb_quad1_s: quad1(v,w) = sum_k w_k(w) * v[k].
static inline void tvdb_quad_w3(float t, float w[3]) {
  w[0] = 0.5f * t * (t - 1.0f);
  w[1] = 1.0f - t * t;
  w[2] = 0.5f * t * (t + 1.0f);
}

void tvdb_splat_quadratic_dense(tvdb_dense_grid* g,
                                const tvdb_vec3f* pts,
                                const float* vals,
                                size_t n,
                                float* weights) {
  if (!g || !tvdb_grid_valid(g->nx,g->ny,g->nz,g->voxel_size,g->data,sizeof(float)) ||
      (n && (!pts || !vals))) return;
  // Adjoint of tvdb_sample_quadratic_dense: a 3x3x3 stencil with per-axis
  // quadratic weights, scattered with the same cell-center convention. Like
  // tvdb_splat_trilinear_dense, taps outside the grid are skipped (zero-pad
  // adjoint), so this is the VJP of a zero-padded — not edge-clamped — sample.
  #pragma omp parallel for schedule(static)
  for (long long pp = 0; pp < (long long)n; ++pp) {
    size_t p = (size_t)pp;
    double qx=((double)pts[p].x-g->ox)/g->voxel_size-0.5;
    double qy=((double)pts[p].y-g->oy)/g->voxel_size-0.5;
    double qz=((double)pts[p].z-g->oz)/g->voxel_size-0.5;
    if (!isfinite(qx) || !isfinite(qy) || !isfinite(qz) ||
        qx < -1 || qy < -1 || qz < -1 || qx >= (double)g->nx+1 || qy >= (double)g->ny+1 || qz >= (double)g->nz+1) continue;
    float cx=(float)qx,cy=(float)qy,cz=(float)qz;
    int64_t ix=(int64_t)floor(qx),iy=(int64_t)floor(qy),iz=(int64_t)floor(qz);
    float u = cx - (float)ix, v = cy - (float)iy, w = cz - (float)iz;
    float wu[3], wv[3], ww[3];
    tvdb_quad_w3(u, wu); tvdb_quad_w3(v, wv); tvdb_quad_w3(w, ww);
    const float val = vals[p];
    for (int dz = 0; dz < 3; ++dz) {
      int64_t z = iz - 1 + dz;
      if (z < 0 || z >= g->nz) continue;
      for (int dy = 0; dy < 3; ++dy) {
        int64_t y = iy - 1 + dy;
        if (y < 0 || y >= g->ny) continue;
        for (int dx = 0; dx < 3; ++dx) {
          int64_t x = ix - 1 + dx;
          if (x < 0 || x >= g->nx) continue;
          float ww3 = wu[dx] * wv[dy] * ww[dz];
          size_t idx = tvdb_idx(g, x, y, z);
          float wval = ww3 * val;
          #pragma omp atomic update
          g->data[idx] += wval;
          if (weights) {
            #pragma omp atomic update
            weights[idx] += ww3;
          }
        }
      }
    }
  }
}

void tvdb_apply_xform(const float xform[12],
                      const tvdb_vec3f* in,
                      tvdb_vec3f* out,
                      size_t n) {
  if (!xform || (n && (!in || !out)) || n > LLONG_MAX) return;
  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)n; ++i) {
    float x = in[i].x, y = in[i].y, z = in[i].z;
    out[i].x = xform[0] * x + xform[1] * y + xform[2]  * z + xform[3];
    out[i].y = xform[4] * x + xform[5] * y + xform[6]  * z + xform[7];
    out[i].z = xform[8] * x + xform[9] * y + xform[10] * z + xform[11];
  }
}
