#include "tinyvdb_sample.h"
#include "tinyvdb_ops_internal.h"

#include <math.h>
#include <stddef.h>

// Cell-center convention: voxel `i` stores its sample at world position
// `ox + (i + 0.5) * vs`. The voxel-index coordinate of a world point is
// therefore (w - ox)/vs - 0.5, so that vx = i exactly hits voxel i's sample.
// Trilinear over pre-validated dense data. vx/vy/vz are voxel-index
// coordinates ((w - o)/vs - 0.5); each axis independently clamps, matching
// the historical tvdb_at-based behavior.
static inline float tvdb_trilinear_inner(const float* data,
                                         int nx, int ny, int nz,
                                         double vx, double vy, double vz) {
  int ix = tvdb_sample_floor(vx, nx), iy = tvdb_sample_floor(vy, ny), iz = tvdb_sample_floor(vz, nz);
  float fx = (float)vx - (float)ix, fy = (float)vy - (float)iy, fz = (float)vz - (float)iz;
  int X0 = tvdb_clamp_i(ix, 0, nx - 1),     X1 = tvdb_clamp_i(ix + 1, 0, nx - 1);
  int Y0 = tvdb_clamp_i(iy, 0, ny - 1),     Y1 = tvdb_clamp_i(iy + 1, 0, ny - 1);
  int Z0 = tvdb_clamp_i(iz, 0, nz - 1),     Z1 = tvdb_clamp_i(iz + 1, 0, nz - 1);
  const size_t sl = (size_t)nx * (size_t)ny;
  const size_t b = ((size_t)Z0 * ny + Y0) * nx + X0;
  const size_t dox = (size_t)(X1 - X0);
  const size_t doy = (size_t)(Y1 - Y0) * (size_t)nx;
  const size_t doz = (size_t)(Z1 - Z0) * sl;
  float c000 = data[b],            c100 = data[b + dox],
        c010 = data[b + doy],      c110 = data[b + dox + doy],
        c001 = data[b + doz],      c101 = data[b + dox + doz],
        c011 = data[b + doy + doz], c111 = data[b + dox + doy + doz];
  float c00 = c000 * (1.0f - fx) + c100 * fx;
  float c10 = c010 * (1.0f - fx) + c110 * fx;
  float c01 = c001 * (1.0f - fx) + c101 * fx;
  float c11 = c011 * (1.0f - fx) + c111 * fx;
  float c0 = c00 * (1.0f - fy) + c10 * fy;
  float c1 = c01 * (1.0f - fy) + c11 * fy;
  return c0 * (1.0f - fz) + c1 * fz;
}

bool tvdb_sampler_init(tvdb_sampler* s, const tvdb_dense_grid* g) {
  if (!s || !g || !tvdb_grid_valid(g->nx, g->ny, g->nz, g->voxel_size, g->data, sizeof(float)) ||
      !isfinite(g->ox) || !isfinite(g->oy) || !isfinite(g->oz)) {
    if (s) s->data = NULL;
    return false;
  }
  s->data = g->data;
  s->nx = g->nx; s->ny = g->ny; s->nz = g->nz;
  s->inv_vs = 1.0 / g->voxel_size;
  s->ox = g->ox; s->oy = g->oy; s->oz = g->oz;
  return true;
}

float tvdb_sampler_trilinear(const tvdb_sampler* s, float wx, float wy, float wz) {
  if (!s || !s->data || !isfinite(wx) || !isfinite(wy) || !isfinite(wz)) return 0.0f;
  double vx = tvdb_sample_coord(((double)wx - s->ox) * s->inv_vs - 0.5, s->nx);
  double vy = tvdb_sample_coord(((double)wy - s->oy) * s->inv_vs - 0.5, s->ny);
  double vz = tvdb_sample_coord(((double)wz - s->oz) * s->inv_vs - 0.5, s->nz);
  return tvdb_trilinear_inner(s->data, s->nx, s->ny, s->nz, vx, vy, vz);
}

float tvdb_sample_trilinear_dense(const tvdb_dense_grid* g,
                                  float wx, float wy, float wz) {
  tvdb_sampler s;
  if (!tvdb_sampler_init(&s, g) || !isfinite(wx) || !isfinite(wy) || !isfinite(wz)) return 0.0f;
  double vx = tvdb_sample_coord(((double)wx - s.ox) * s.inv_vs - 0.5, s.nx);
  double vy = tvdb_sample_coord(((double)wy - s.oy) * s.inv_vs - 0.5, s.ny);
  double vz = tvdb_sample_coord(((double)wz - s.oz) * s.inv_vs - 0.5, s.nz);
  return tvdb_trilinear_inner(s.data, s.nx, s.ny, s.nz, vx, vy, vz);
}

void tvdb_sample_trilinear_dense_batch(const tvdb_dense_grid* g,
                                       const tvdb_vec3f* pts,
                                       size_t n,
                                       float* out) {
  if (!g || (n && (!pts || !out)) || n > LLONG_MAX) return;
  tvdb_sampler s;
  if (!tvdb_sampler_init(&s, g)) {
    if (out) {
      for (size_t i = 0; i < n; ++i) out[i] = 0.0f;
    }
    return;
  }
  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)n; ++i) {
    out[i] = tvdb_sampler_trilinear(&s, pts[i].x, pts[i].y, pts[i].z);
  }
}

// 3-point parabola through (val[0],val[1],val[2]) at offsets (-1,0,1) at `w`.
static inline float tvdb_quad1_s(const float* val, float w) {
  float a = 0.5f * (val[0] + val[2]) - val[1];
  float b = 0.5f * (val[2] - val[0]);
  return w * (w * a + b) + val[1];
}

static inline float tvdb_quadratic_inner(const float* data,
                                         int nx, int ny, int nz,
                                         double cx, double cy, double cz) {
  int ix = tvdb_sample_floor(cx,nx), iy = tvdb_sample_floor(cy,ny), iz = tvdb_sample_floor(cz,nz);
  float u = (float)cx - ix, v = (float)cy - iy, w = (float)cz - iz;
  int X[3], Y[3], Z[3];
  for (int i = 0; i < 3; ++i) {
    X[i] = tvdb_clamp_i(ix - 1 + i, 0, nx - 1);
    Y[i] = tvdb_clamp_i(iy - 1 + i, 0, ny - 1);
    Z[i] = tvdb_clamp_i(iz - 1 + i, 0, nz - 1);
  }
  float vx[3];
  for (int dx = 0; dx < 3; ++dx) {
    float vy[3];
    for (int dy = 0; dy < 3; ++dy) {
      float vz[3];
      for (int dz = 0; dz < 3; ++dz)
        vz[dz] = data[((size_t)Z[dz] * ny + Y[dy]) * nx + X[dx]];
      vy[dy] = tvdb_quad1_s(vz, w);
    }
    vx[dx] = tvdb_quad1_s(vy, v);
  }
  return tvdb_quad1_s(vx, u);
}

float tvdb_sampler_quadratic(const tvdb_sampler* s, float wx, float wy, float wz) {
  if (!s || !s->data || !isfinite(wx) || !isfinite(wy) || !isfinite(wz)) return 0.0f;
  double cx = tvdb_sample_coord(((double)wx - s->ox) * s->inv_vs - 0.5, s->nx);
  double cy = tvdb_sample_coord(((double)wy - s->oy) * s->inv_vs - 0.5, s->ny);
  double cz = tvdb_sample_coord(((double)wz - s->oz) * s->inv_vs - 0.5, s->nz);
  return tvdb_quadratic_inner(s->data, s->nx, s->ny, s->nz, cx, cy, cz);
}

float tvdb_sample_quadratic_dense(const tvdb_dense_grid* g,
                                  float wx, float wy, float wz) {
  tvdb_sampler s;
  if (!tvdb_sampler_init(&s, g) || !isfinite(wx) || !isfinite(wy) || !isfinite(wz)) return 0;
  double cx = tvdb_sample_coord(((double)wx - s.ox) * s.inv_vs - 0.5, s.nx);
  double cy = tvdb_sample_coord(((double)wy - s.oy) * s.inv_vs - 0.5, s.ny);
  double cz = tvdb_sample_coord(((double)wz - s.oz) * s.inv_vs - 0.5, s.nz);
  return tvdb_quadratic_inner(s.data, s.nx, s.ny, s.nz, cx, cy, cz);
}

void tvdb_sample_quadratic_dense_batch(const tvdb_dense_grid* g,
                                       const tvdb_vec3f* pts,
                                       size_t n,
                                       float* out) {
  if (!g || (n && (!pts || !out)) || n > LLONG_MAX) return;
  tvdb_sampler s;
  if (!tvdb_sampler_init(&s, g)) {
    if (out) {
      for (size_t i = 0; i < n; ++i) out[i] = 0.0f;
    }
    return;
  }
  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)n; ++i) {
    out[i] = tvdb_sampler_quadratic(&s, pts[i].x, pts[i].y, pts[i].z);
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

  int X0 = tvdb_clamp_i(ix,     0, g->nx - 1);
  int X1 = tvdb_clamp_i(ix + 1, 0, g->nx - 1);
  int Y0 = tvdb_clamp_i(iy,     0, g->ny - 1);
  int Y1 = tvdb_clamp_i(iy + 1, 0, g->ny - 1);
  int Z0 = tvdb_clamp_i(iz,     0, g->nz - 1);
  int Z1 = tvdb_clamp_i(iz + 1, 0, g->nz - 1);
  const size_t vbase = ((size_t)Z0 * g->ny + Y0) * g->nx + X0;
  const size_t vdx = (size_t)(X1 - X0) * 3u;
  const size_t vdy = (size_t)(Y1 - Y0) * (size_t)g->nx * 3u;
  const size_t vdz = (size_t)(Z1 - Z0) * (size_t)g->nx * (size_t)g->ny * 3u;
  float r[3] = {0.0f, 0.0f, 0.0f};
  for (int c = 0; c < 3; ++c) {
    float c000 = 0, c100 = 0, c010 = 0, c110 = 0, c001 = 0, c101 = 0, c011 = 0, c111 = 0;
    const float* base = g->data + vbase * 3u + (size_t)c;
    c000 = base[0];
    c100 = base[vdx];
    c010 = base[vdy];
    c110 = base[vdx + vdy];
    c001 = base[vdz];
    c101 = base[vdx + vdz];
    c011 = base[vdy + vdz];
    c111 = base[vdx + vdy + vdz];
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
