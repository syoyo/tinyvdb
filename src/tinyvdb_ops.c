#include "tinyvdb_ops.h"
#include "tinyvdb_ops_internal.h"
#include "tinyvdb_simd.h"
#include "tinyvdb_checked.h"
#include "tinyvdb_poisson_internal.h"

#include <math.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

// -------------------------------------------------------------------------
// dense vec grid lifecycle
// -------------------------------------------------------------------------

void tvdb_dense_vec_grid_init(tvdb_dense_vec_grid* grid, int nx, int ny, int nz) {
  if (!grid) return;
  grid->nx = nx;
  grid->ny = ny;
  grid->nz = nz;
  grid->ox = grid->oy = grid->oz = 0.0f;
  grid->voxel_size = 1.0f;
  size_t bytes;
  if (!tvdb_grid_bytes(nx, ny, nz, 3u * sizeof(float), &bytes)) {
    grid->data = NULL; grid->nx = grid->ny = grid->nz = 0; return;
  }
  grid->data = (float*)calloc(1, bytes);
}

void tvdb_dense_vec_grid_free(tvdb_dense_vec_grid* grid) {
  if (!grid) return;
  if (grid->data) free(grid->data);
  grid->data = NULL;
}

// -------------------------------------------------------------------------
// helpers
// -------------------------------------------------------------------------

static size_t tvdb_grid_voxels(const tvdb_dense_grid* g) {
  size_t bytes;
  return g && tvdb_grid_bytes(g->nx, g->ny, g->nz, sizeof(float), &bytes) ? bytes / sizeof(float) : 0;
}

static int tvdb_grid_same_shape(const tvdb_dense_grid* a, const tvdb_dense_grid* b) {
  size_t bytes;
  return a && b && a->data && b->data &&
         tvdb_grid_bytes(a->nx,a->ny,a->nz,sizeof(float),&bytes) &&
         a->nx==b->nx && a->ny==b->ny && a->nz==b->nz;
}

// -------------------------------------------------------------------------
// Phase 1: morphology
// -------------------------------------------------------------------------

// SDF convention: f < 0 = inside, f > 0 = outside.
//   dilate (grow inside)  = pointwise 6-neighbor min
//   erode  (shrink inside)= pointwise 6-neighbor max
// One iteration moves the zero-isosurface by ~one voxel.

static void tvdb_morph_step(const tvdb_dense_grid* in, tvdb_dense_grid* out, int is_dilate) {
  const int nx = in->nx, ny = in->ny, nz = in->nz;
  /* `in` and `out` are always distinct ping-pong buffers (see
     tvdb_morph_iter), and each output voxel depends only on its own 7-cell
     neighborhood, so this is embarrassingly parallel. The fp64 twins of the
     neighbouring kernels already carried a pragma; this one did not. */
  #pragma omp parallel for collapse(2) schedule(static)
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        const size_t i = ((size_t)iz * ny + iy) * nx + ix;
        const size_t plane = (size_t)nx * (size_t)ny;
        float c = in->data[i];
        float xm = ix > 0 ? in->data[i - 1] : c;
        float xp = ix + 1 < nx ? in->data[i + 1] : c;
        float ym = iy > 0 ? in->data[i - nx] : c;
        float yp = iy + 1 < ny ? in->data[i + nx] : c;
        float zm = iz > 0 ? in->data[i - plane] : c;
        float zp = iz + 1 < nz ? in->data[i + plane] : c;
        float r = c;
        if (is_dilate) {
          if (xm < r) r = xm; if (xp < r) r = xp;
          if (ym < r) r = ym; if (yp < r) r = yp;
          if (zm < r) r = zm; if (zp < r) r = zp;
        } else {
          if (xm > r) r = xm; if (xp > r) r = xp;
          if (ym > r) r = ym; if (yp > r) r = yp;
          if (zm > r) r = zm; if (zp > r) r = zp;
        }
        out->data[((size_t)iz * ny + iy) * nx + ix] = r;
      }
    }
  }
}

static void tvdb_morph_iter(tvdb_dense_grid* grid, int iterations, int is_dilate) {
  if (!grid || !tvdb_grid_voxels(grid) || iterations <= 0 || !grid->data || !isfinite(grid->voxel_size) || grid->voxel_size <= 0) return;
  const size_t nv = (size_t)tvdb_grid_voxels(grid);
  float* tmp = (float*)malloc(nv * sizeof(float));
  if (!tmp) return;

  tvdb_dense_grid scratch = *grid;
  scratch.data = tmp;

  for (int it = 0; it < iterations; ++it) {
    tvdb_morph_step(grid, &scratch, is_dilate);
    // swap data pointers
    float* swap = grid->data;
    grid->data = scratch.data;
    scratch.data = swap;
  }
  // After even iterations, grid->data == original buffer. After odd, grid->data == tmp.
  // We need the result in the caller's original buffer. If pointer was swapped to tmp,
  // copy back and free tmp.
  if (grid->data == tmp) {
    memcpy(scratch.data, tmp, nv * sizeof(float));
    grid->data = scratch.data;
    free(tmp);
  } else {
    free(tmp);
  }
}

void tvdb_dilate(tvdb_dense_grid* grid, int iterations) {
  tvdb_morph_iter(grid, iterations, /*is_dilate=*/1);
}
void tvdb_erode(tvdb_dense_grid* grid, int iterations) {
  tvdb_morph_iter(grid, iterations, /*is_dilate=*/0);
}
void tvdb_open(tvdb_dense_grid* grid, int iterations) {
  tvdb_erode(grid, iterations);
  tvdb_dilate(grid, iterations);
}
void tvdb_close(tvdb_dense_grid* grid, int iterations) {
  tvdb_dilate(grid, iterations);
  tvdb_erode(grid, iterations);
}

// -------------------------------------------------------------------------
// Phase 1: filtering
// -------------------------------------------------------------------------

// Apply a separable 1-D kernel along one axis.
// axis: 0 = x, 1 = y, 2 = z.
static void tvdb_separable_pass(const tvdb_dense_grid* in, tvdb_dense_grid* out,
                                const float* kernel, int radius, int axis) {
  const int nx = in->nx, ny = in->ny, nz = in->nz;
  const size_t plane = (size_t)nx * (size_t)ny;
  const int extent = axis == 0 ? nx : (axis == 1 ? ny : nz);

  /* Distinct ping-pong buffers again, and the output is a pure function of the
     input along `axis`, so each output voxel is independent.

     The filtered axis is fixed for the whole pass, so the index of a tap is a
     constant plane/row base plus c*stride -- only c varies with the tap offset.
     The previous form called tvdb_at per tap, which rebuilt a full 3-D index (three
     multiplies, plus a branch on which axis it was) for each of the 2r+1 taps. */
  #pragma omp parallel for collapse(2) schedule(static)
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      /* Base of the slice this loop iteration walks, per axis. */
      /* For axis 1 the tap replaces iy, so its base must stop before iy's own
         offset; the axis-0 base is the row, and doubles as the output index. */
      const size_t row_x   = ((size_t)iz * ny + iy) * nx;   /* axis 0 + output index */
      const size_t plane_y = (size_t)iz * plane;           /* axis 1 */
      for (int ix = 0; ix < nx; ++ix) {
        float acc = 0.0f;
        if (axis == 0) {
          for (int k = -radius; k <= radius; ++k) {
            int c = ix + k;
            if (c < 0) c = 0; else if (c >= extent) c = extent - 1;
            acc += kernel[k + radius] * in->data[row_x + (size_t)c];
          }
        } else if (axis == 1) {
          for (int k = -radius; k <= radius; ++k) {
            int c = iy + k;
            if (c < 0) c = 0; else if (c >= extent) c = extent - 1;
            acc += kernel[k + radius] * in->data[plane_y + (size_t)c * nx + (size_t)ix];
          }
        } else {
          for (int k = -radius; k <= radius; ++k) {
            int c = iz + k;
            if (c < 0) c = 0; else if (c >= extent) c = extent - 1;
            acc += kernel[k + radius] * in->data[(size_t)c * plane + (size_t)iy * nx + (size_t)ix];
          }
        }
        out->data[row_x + (size_t)ix] = acc;
      }
    }
  }
}

static void tvdb_apply_separable(tvdb_dense_grid* grid, const float* kernel,
                                 int radius, int iterations) {
  if (!grid || !tvdb_grid_voxels(grid) || iterations <= 0 || radius <= 0 || !grid->data) return;
  const size_t nv = (size_t)tvdb_grid_voxels(grid);
  float* buf_a = (float*)malloc(nv * sizeof(float));
  float* buf_b = (float*)malloc(nv * sizeof(float));
  if (!buf_a || !buf_b) {
    free(buf_a);
    free(buf_b);
    return;
  }

  tvdb_dense_grid ping = *grid; ping.data = buf_a;
  tvdb_dense_grid pong = *grid; pong.data = buf_b;

  for (int it = 0; it < iterations; ++it) {
    tvdb_separable_pass(grid, &ping, kernel, radius, 0);
    tvdb_separable_pass(&ping, &pong, kernel, radius, 1);
    tvdb_separable_pass(&pong, grid, kernel, radius, 2);
  }
  free(buf_a);
  free(buf_b);
}

void tvdb_gaussian_filter(tvdb_dense_grid* grid, int width, int iterations) {
  if (!grid || !tvdb_grid_valid(grid->nx,grid->ny,grid->nz,grid->voxel_size,grid->data,sizeof(float)) || iterations <= 0 || width <= 0 || width > (INT_MAX - 1) / 2) return;
  const int radius = width;
  const int len = 2 * radius + 1;
  const float sigma = (float)width * 0.5f;
  const float two_s2 = 2.0f * sigma * sigma;
  size_t kbytes; if(!tvdb_size_mul((size_t)len,sizeof(float),&kbytes)) return;
  float* k = (float*)malloc(kbytes);
  if (!k) return;
  float sum = 0.0f;
  for (int i = -radius; i <= radius; ++i) {
    float v = expf(-((float)i * (float)i) / two_s2);
    k[i + radius] = v;
    sum += v;
  }
  for (int i = 0; i < len; ++i) k[i] /= sum;
  tvdb_apply_separable(grid, k, radius, iterations);
  free(k);
}

void tvdb_mean_filter(tvdb_dense_grid* grid, int width, int iterations) {
  if (!grid || !tvdb_grid_valid(grid->nx,grid->ny,grid->nz,grid->voxel_size,grid->data,sizeof(float)) || iterations <= 0 || width <= 0 || width > (INT_MAX - 1) / 2) return;
  const int radius = width;
  const int len = 2 * radius + 1;
  size_t kbytes; if(!tvdb_size_mul((size_t)len,sizeof(float),&kbytes)) return;
  float* k = (float*)malloc(kbytes);
  if (!k) return;
  const float w = 1.0f / (float)len;
  for (int i = 0; i < len; ++i) k[i] = w;
  tvdb_apply_separable(grid, k, radius, iterations);
  free(k);
}

// laplacian_filter: explicit-Euler diffusion step using a 7-point stencil.
// dt = h^2 / 8 (CFL stable for 3-D heat eq, margin below h^2/6).
void tvdb_laplacian_filter(tvdb_dense_grid* grid, int iterations) {
  if (!grid || !tvdb_grid_voxels(grid) || iterations <= 0 || !grid->data || !isfinite(grid->voxel_size) || grid->voxel_size <= 0) return;
  const size_t nv = (size_t)tvdb_grid_voxels(grid);
  float* tmp = (float*)malloc(nv * sizeof(float));
  if (!tmp) return;

  tvdb_dense_grid scratch = *grid;
  scratch.data = tmp;

  const float dt = 1.0f / 8.0f;  // h^2 cancels in the discrete laplacian below
  // discrete laplacian L = (sum6 - 6 c) / h^2; update u += dt * h^2 * L = dt*(sum6 - 6 c)

  for (int it = 0; it < iterations; ++it) {
    const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
    /* Ping-pong between grid->data and tmp: each output voxel depends only on
       its own 7-cell neighborhood, so writing the other buffer and swapping
       per iteration replaces the former full-grid memcpy. */
    const float* src = ((it & 1) == 0) ? grid->data : tmp;
    float* dst = ((it & 1) == 0) ? tmp : grid->data;
    #pragma omp parallel for collapse(2) schedule(static)
    for (int iz = 0; iz < nz; ++iz) {
      for (int iy = 0; iy < ny; ++iy) {
        for (int ix = 0; ix < nx; ++ix) {
          const size_t i = ((size_t)iz * ny + iy) * nx + ix;
          float c  = src[i];
          float s  = (ix > 0 ? src[i - 1] : src[i])
                   + (ix + 1 < nx ? src[i + 1] : src[i])
                   + (iy > 0 ? src[i - nx] : src[i])
                   + (iy + 1 < ny ? src[i + nx] : src[i])
                   + (iz > 0 ? src[i - (size_t)nx * ny] : src[i])
                   + (iz + 1 < nz ? src[i + (size_t)nx * ny] : src[i]);
          dst[i] = c + dt * (s - 6.0f * c);
        }
      }
    }
  }
  if ((iterations & 1) == 1) {
    memcpy(grid->data, tmp, nv * sizeof(float));
  }
  free(tmp);
}

// -------------------------------------------------------------------------
// Phase 1: CSG
// -------------------------------------------------------------------------

// SDF convention: union = min, intersection = max, difference = max(a, -b).
// Requires identical grid dimensions; result must be pre-allocated to same shape.

void tvdb_csg_union(const tvdb_dense_grid* a, const tvdb_dense_grid* b, tvdb_dense_grid* result) {
  if (!tvdb_grid_same_shape(a, b) || !tvdb_grid_same_shape(a, result)) return;
  const size_t nv = (size_t)tvdb_grid_voxels(a);
  /* Elementwise; the fp64 twin of this kernel already had a pragma. */
  #pragma omp parallel for schedule(static)
  for (size_t i = 0; i < nv; ++i) {
    float va = a->data[i], vb = b->data[i];
    result->data[i] = va < vb ? va : vb;
  }
}

void tvdb_csg_intersection(const tvdb_dense_grid* a, const tvdb_dense_grid* b, tvdb_dense_grid* result) {
  if (!tvdb_grid_same_shape(a, b) || !tvdb_grid_same_shape(a, result)) return;
  const size_t nv = (size_t)tvdb_grid_voxels(a);
  /* Elementwise; the fp64 twin of this kernel already had a pragma. */
  #pragma omp parallel for schedule(static)
  for (size_t i = 0; i < nv; ++i) {
    float va = a->data[i], vb = b->data[i];
    result->data[i] = va > vb ? va : vb;
  }
}

void tvdb_csg_difference(const tvdb_dense_grid* a, const tvdb_dense_grid* b, tvdb_dense_grid* result) {
  if (!tvdb_grid_same_shape(a, b) || !tvdb_grid_same_shape(a, result)) return;
  const size_t nv = (size_t)tvdb_grid_voxels(a);
  /* Elementwise; the fp64 twin of this kernel already had a pragma. */
  #pragma omp parallel for schedule(static)
  for (size_t i = 0; i < nv; ++i) {
    float va = a->data[i], nb = -b->data[i];
    result->data[i] = va > nb ? va : nb;
  }
}

// -------------------------------------------------------------------------
// Phase 1: measurement
// -------------------------------------------------------------------------

// Surface area: count zero-crossing faces (per +x/+y/+z neighbor pair),
// scale by voxel_size^2. Simple, monotonic estimator.
float tvdb_surface_area(const tvdb_dense_grid* grid) {
  if (!grid || !tvdb_grid_valid(grid->nx,grid->ny,grid->nz,grid->voxel_size,grid->data,sizeof(float))) return 0.0f;
  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  /* Accumulate into a double so the OpenMP reduction matches the fp64 twin's
     pattern. The counted quantity is an exact integer well below 2^53, so the
     sum is bit-identical regardless of how the work is split. */
  double crossings = 0.0;
  #pragma omp parallel for collapse(2) reduction(+ : crossings) schedule(static)
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        float c = grid->data[tvdb_idx(grid, ix, iy, iz)];
        /* A voxel is inside iff it is strictly negative, the same test tvdb_volume
           uses and the same one the fp64 twin and both measure shaders use. This
           used to be `<= 0` here only, which counted exact-zero voxels as inside:
           a grid containing a zero got a different answer from the fp32 and fp64
           paths, and a different answer from tvdb_volume on the same data. */
        if (ix + 1 < nx) {
          float n = grid->data[tvdb_idx(grid, ix + 1, iy, iz)];
          if ((c < 0.0f) != (n < 0.0f)) crossings += 1.0;
        }
        if (iy + 1 < ny) {
          float n = grid->data[tvdb_idx(grid, ix, iy + 1, iz)];
          if ((c < 0.0f) != (n < 0.0f)) crossings += 1.0;
        }
        if (iz + 1 < nz) {
          float n = grid->data[tvdb_idx(grid, ix, iy, iz + 1)];
          if ((c < 0.0f) != (n < 0.0f)) crossings += 1.0;
        }
      }
    }
  }
  return (float)crossings * grid->voxel_size * grid->voxel_size;
}

// Volume: integrate inside-region (f < 0). Each voxel contributes voxel_size^3.
float tvdb_volume(const tvdb_dense_grid* grid) {
  if (!grid || !tvdb_grid_valid(grid->nx,grid->ny,grid->nz,grid->voxel_size,grid->data,sizeof(float))) return 0.0f;
  const size_t nv = (size_t)tvdb_grid_voxels(grid);
  /* Exact integer count accumulated in a double, as above. */
  double inside = 0.0;
  #pragma omp parallel for reduction(+ : inside) schedule(static)
  for (size_t i = 0; i < nv; ++i) {
    if (grid->data[i] < 0.0f) inside += 1.0;
  }
  const float h = grid->voxel_size;
  return (float)inside * h * h * h;
}

// -------------------------------------------------------------------------
// Phase 2: differential operators
// -------------------------------------------------------------------------

float tvdb_central_diff_x(const tvdb_dense_grid* g, int ix, int iy, int iz) {
  if(!g || !tvdb_grid_valid(g->nx,g->ny,g->nz,g->voxel_size,g->data,sizeof(float))) return 0;
  return (tvdb_at(g, (int64_t)ix + 1, iy, iz) - tvdb_at(g, (int64_t)ix - 1, iy, iz)) / (2.0f * g->voxel_size);
}
float tvdb_central_diff_y(const tvdb_dense_grid* g, int ix, int iy, int iz) {
  if(!g || !tvdb_grid_valid(g->nx,g->ny,g->nz,g->voxel_size,g->data,sizeof(float))) return 0;
  return (tvdb_at(g, ix, (int64_t)iy + 1, iz) - tvdb_at(g, ix, (int64_t)iy - 1, iz)) / (2.0f * g->voxel_size);
}
float tvdb_central_diff_z(const tvdb_dense_grid* g, int ix, int iy, int iz) {
  if(!g || !tvdb_grid_valid(g->nx,g->ny,g->nz,g->voxel_size,g->data,sizeof(float))) return 0;
  return (tvdb_at(g, ix, iy, (int64_t)iz + 1) - tvdb_at(g, ix, iy, (int64_t)iz - 1)) / (2.0f * g->voxel_size);
}

static void tvdb_gradient_impl(const tvdb_dense_grid* scalar, tvdb_dense_vec_grid* grad) {
  if (!scalar->data || !grad->data) return;
  const int nx = scalar->nx, ny = scalar->ny, nz = scalar->nz;
  #pragma omp parallel for collapse(2) schedule(static)
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        const size_t plane = (size_t)nx * (size_t)ny;
        const size_t i = ((size_t)iz * ny + iy) * nx + ix;
        const float* d = scalar->data;
        const float inv2h = 1.0f / (2.0f * scalar->voxel_size);
        float gx = ((ix + 1 < nx ? d[i + 1] : d[i]) - (ix > 0 ? d[i - 1] : d[i])) * inv2h;
        float gy = ((iy + 1 < ny ? d[i + nx] : d[i]) - (iy > 0 ? d[i - nx] : d[i])) * inv2h;
        float gz = ((iz + 1 < nz ? d[i + plane] : d[i]) - (iz > 0 ? d[i - plane] : d[i])) * inv2h;
        size_t vi = i * 3u;
        grad->data[vi + 0] = gx;
        grad->data[vi + 1] = gy;
        grad->data[vi + 2] = gz;
      }
    }
  }
}

static inline float tvdb_vec_at(const tvdb_dense_vec_grid* v, int64_t ix, int64_t iy, int64_t iz, int c) {
  ix = ix < 0 ? 0 : (ix >= v->nx ? v->nx-1 : ix);
  iy = iy < 0 ? 0 : (iy >= v->ny ? v->ny-1 : iy);
  iz = iz < 0 ? 0 : (iz >= v->nz ? v->nz-1 : iz);
  size_t base = (((size_t)iz * v->ny + iy) * v->nx + ix) * 3u;
  return v->data[base + (size_t)c];
}

static void tvdb_divergence_impl(const tvdb_dense_vec_grid* vec, tvdb_dense_grid* div) {
  if (!vec->data || !div->data) return;
  const int nx = vec->nx, ny = vec->ny, nz = vec->nz;
  const float h2 = 2.0f * vec->voxel_size;
  #pragma omp parallel for collapse(2) schedule(static)
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        float dvx_dx = (tvdb_vec_at(vec, ix + 1, iy, iz, 0) - tvdb_vec_at(vec, ix - 1, iy, iz, 0)) / h2;
        float dvy_dy = (tvdb_vec_at(vec, ix, iy + 1, iz, 1) - tvdb_vec_at(vec, ix, iy - 1, iz, 1)) / h2;
        float dvz_dz = (tvdb_vec_at(vec, ix, iy, iz + 1, 2) - tvdb_vec_at(vec, ix, iy, iz - 1, 2)) / h2;
        div->data[tvdb_idx(div, ix, iy, iz)] = dvx_dx + dvy_dy + dvz_dz;
      }
    }
  }
}

static void tvdb_laplacian_impl(const tvdb_dense_grid* scalar, tvdb_dense_grid* laplacian) {
  if (!scalar->data || !laplacian->data) return;
  const int nx = scalar->nx, ny = scalar->ny, nz = scalar->nz;
  const float h = scalar->voxel_size;
  const float inv_h2 = 1.0f / (h * h);
  #pragma omp parallel for collapse(2) schedule(static)
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        const size_t i = ((size_t)iz * ny + iy) * nx + ix;
        const size_t plane = (size_t)nx * (size_t)ny;
        const float* d = scalar->data;
        float c = d[i];
        float s = (ix > 0 ? d[i - 1] : c) + (ix + 1 < nx ? d[i + 1] : c)
                + (iy > 0 ? d[i - nx] : c) + (iy + 1 < ny ? d[i + nx] : c)
                + (iz > 0 ? d[i - plane] : c) + (iz + 1 < nz ? d[i + plane] : c);
        laplacian->data[i] = (s - 6.0f * c) * inv_h2;
      }
    }
  }
}

static void tvdb_curl_impl(const tvdb_dense_vec_grid* vec, tvdb_dense_vec_grid* curl) {
  if (!vec->data || !curl->data) return;
  const int nx = vec->nx, ny = vec->ny, nz = vec->nz;
  const float h2 = 2.0f * vec->voxel_size;
  #pragma omp parallel for collapse(2) schedule(static)
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        float dvz_dy = (tvdb_vec_at(vec, ix, iy + 1, iz, 2) - tvdb_vec_at(vec, ix, iy - 1, iz, 2)) / h2;
        float dvy_dz = (tvdb_vec_at(vec, ix, iy, iz + 1, 1) - tvdb_vec_at(vec, ix, iy, iz - 1, 1)) / h2;
        float dvx_dz = (tvdb_vec_at(vec, ix, iy, iz + 1, 0) - tvdb_vec_at(vec, ix, iy, iz - 1, 0)) / h2;
        float dvz_dx = (tvdb_vec_at(vec, ix + 1, iy, iz, 2) - tvdb_vec_at(vec, ix - 1, iy, iz, 2)) / h2;
        float dvy_dx = (tvdb_vec_at(vec, ix + 1, iy, iz, 1) - tvdb_vec_at(vec, ix - 1, iy, iz, 1)) / h2;
        float dvx_dy = (tvdb_vec_at(vec, ix, iy + 1, iz, 0) - tvdb_vec_at(vec, ix, iy - 1, iz, 0)) / h2;
        size_t i = (((size_t)iz * ny + iy) * nx + ix) * 3u;
        curl->data[i + 0] = dvz_dy - dvy_dz;
        curl->data[i + 1] = dvx_dz - dvz_dx;
        curl->data[i + 2] = dvy_dx - dvx_dy;
      }
    }
  }
}

// -------------------------------------------------------------------------
// Vector-grid operators (GridOperators): magnitude, normalize, cpt
// -------------------------------------------------------------------------

static void tvdb_magnitude_impl(const tvdb_dense_vec_grid* vec, tvdb_dense_grid* out) {
  if (!vec->data || !out->data) return;
  if (vec->nx != out->nx || vec->ny != out->ny || vec->nz != out->nz) return;
  const size_t nv = (size_t)vec->nx * vec->ny * vec->nz;
  #pragma omp parallel for schedule(static)
  for (size_t i = 0; i < nv; ++i) {
    float x = vec->data[i*3+0], y = vec->data[i*3+1], z = vec->data[i*3+2];
    /* Scaled, for the same overflow reason as tvdb_normalize_vec_impl: a finite
       vector above ~1.8e19 used to produce +inf here. */
    float s = fmaxf(fabsf(x), fmaxf(fabsf(y), fabsf(z)));
    out->data[i] = (s > 0.0f)
      ? s * sqrtf((x/s)*(x/s) + (y/s)*(y/s) + (z/s)*(z/s))
      : (isnan(x) || isnan(y) || isnan(z)) ? (x + y + z) : 0.0f;
  }
}

static void tvdb_normalize_vec_impl(const tvdb_dense_vec_grid* vec, tvdb_dense_vec_grid* out) {
  if (!vec->data || !out->data) return;
  if (vec->nx != out->nx || vec->ny != out->ny || vec->nz != out->nz) return;
  const size_t nv = (size_t)vec->nx * vec->ny * vec->nz;
  #pragma omp parallel for schedule(static)
  for (size_t i = 0; i < nv; ++i) {
    float x = vec->data[i*3+0], y = vec->data[i*3+1], z = vec->data[i*3+2];
    /* Scale first, then take the root. sqrtf(x*x+y*y+z*z) overflows to +inf for
       a perfectly finite vector above ~1.8e19, and x/inf then silently writes 0
       for a large-but-valid input. Scaling by the largest component keeps every
       intermediate finite, and the result is the same to within a rounding step. */
    float s = fmaxf(fabsf(x), fmaxf(fabsf(y), fabsf(z)));
    if (!(s > 0.0f)) {
      /* Zero vector, or a NaN component: s is NaN and this comparison is false.
         Zero length has no direction, so 0 is the right answer there, but NaN in
         has to stay NaN out -- the old `m > 0.0f` test zeroed it instead, so a
         caller could not tell a zero vector from a poisoned one. */
      if (isnan(x) || isnan(y) || isnan(z)) {
        out->data[i*3+0] = x; out->data[i*3+1] = y; out->data[i*3+2] = z;
      } else {
        out->data[i*3+0] = out->data[i*3+1] = out->data[i*3+2] = 0.0f;
      }
      continue;
    }
    const float inv = 1.0f / sqrtf((x/s)*(x/s) + (y/s)*(y/s) + (z/s)*(z/s));
    out->data[i*3+0] = (x/s) * inv; out->data[i*3+1] = (y/s) * inv; out->data[i*3+2] = (z/s) * inv;
  }
}

static void tvdb_cpt_impl(const tvdb_dense_grid* sdf, tvdb_dense_vec_grid* out) {
  if (!sdf->data || !out->data) return;
  if (sdf->nx != out->nx || sdf->ny != out->ny || sdf->nz != out->nz) return;
  const int nx = sdf->nx, ny = sdf->ny, nz = sdf->nz;
  const float vs = sdf->voxel_size;
  const size_t plane = (size_t)nx * (size_t)ny;
  const float inv2h = 1.0f / (2.0f * vs);
  #pragma omp parallel for collapse(2) schedule(static)
  for (int iz = 0; iz < nz; ++iz)
    for (int iy = 0; iy < ny; ++iy)
      for (int ix = 0; ix < nx; ++ix) {
        size_t i = ((size_t)iz * ny + iy) * nx + ix;
        float px = sdf->ox + ((float)ix + 0.5f) * vs;
        float py = sdf->oy + ((float)iy + 0.5f) * vs;
        float pz = sdf->oz + ((float)iz + 0.5f) * vs;
        const float* d = sdf->data;
        float gx = ((ix + 1 < nx ? d[i + 1] : d[i]) - (ix > 0 ? d[i - 1] : d[i])) * inv2h;
        float gy = ((iy + 1 < ny ? d[i + nx] : d[i]) - (iy > 0 ? d[i - nx] : d[i])) * inv2h;
        float gz = ((iz + 1 < nz ? d[i + plane] : d[i]) - (iz > 0 ? d[i - plane] : d[i])) * inv2h;
        float dv = d[i];
        out->data[i*3+0] = px - dv*gx;
        out->data[i*3+1] = py - dv*gy;
        out->data[i*3+2] = pz - dv*gz;
      }
}

// -------------------------------------------------------------------------
// Composite (per-voxel binary ops)
// -------------------------------------------------------------------------

void tvdb_comp_max(const tvdb_dense_grid* a, const tvdb_dense_grid* b, tvdb_dense_grid* result) {
  if (!tvdb_grid_same_shape(a, b) || !tvdb_grid_same_shape(a, result)) return;
  const size_t nv = (size_t)tvdb_grid_voxels(a);
  #pragma omp parallel for schedule(static)
  for (size_t i = 0; i < nv; ++i) { float va = a->data[i], vb = b->data[i]; result->data[i] = va > vb ? va : vb; }
}
void tvdb_comp_min(const tvdb_dense_grid* a, const tvdb_dense_grid* b, tvdb_dense_grid* result) {
  if (!tvdb_grid_same_shape(a, b) || !tvdb_grid_same_shape(a, result)) return;
  const size_t nv = (size_t)tvdb_grid_voxels(a);
  #pragma omp parallel for schedule(static)
  for (size_t i = 0; i < nv; ++i) { float va = a->data[i], vb = b->data[i]; result->data[i] = va < vb ? va : vb; }
}
void tvdb_comp_sum(const tvdb_dense_grid* a, const tvdb_dense_grid* b, tvdb_dense_grid* result) {
  if (!tvdb_grid_same_shape(a, b) || !tvdb_grid_same_shape(a, result)) return;
  const size_t nv = (size_t)tvdb_grid_voxels(a);
  #pragma omp parallel for schedule(static)
  for (size_t i = 0; i < nv; ++i) result->data[i] = a->data[i] + b->data[i];
}
void tvdb_comp_mult(const tvdb_dense_grid* a, const tvdb_dense_grid* b, tvdb_dense_grid* result) {
  if (!tvdb_grid_same_shape(a, b) || !tvdb_grid_same_shape(a, result)) return;
  const size_t nv = (size_t)tvdb_grid_voxels(a);
  #pragma omp parallel for schedule(static)
  for (size_t i = 0; i < nv; ++i) result->data[i] = a->data[i] * b->data[i];
}

// -------------------------------------------------------------------------
// In-place filters: median, mean-curvature flow
// -------------------------------------------------------------------------

static int tvdb_cmp_float(const void* pa, const void* pb) {
  float a = *(const float*)pa, b = *(const float*)pb;
  return a < b ? -1 : (a > b ? 1 : 0);
}

/* In-place quickselect: rearrange `a` so that the element at index `k` is the
 * same value a full sort would place there, touching only the part of the
 * array that matters.
 *
 * Used to replace a per-voxel qsort in tvdb_median_filter. Sorting a
 * (2r+1)^3 window (343 elements at r=3) for every voxel is O(n log n); this
 * is O(n) expected. The selected value is identical to sorted[n/2] -- the
 * array is left permuted, which is fine because the caller refills it for the
 * next voxel.
 *
 * Pivot choice is median-of-three, which avoids the O(n^2) blowup on the
 * already-sorted or reverse-sorted windows that a level-set band produces.
 * Comparison matches tvdb_cmp_float, including its behaviour on NaN. */
static float tvdb_select_kth(float* a, size_t n, size_t k) {
  size_t lo = 0, hi = n - 1;
  while (lo < hi) {
    /* median-of-three, leaving a[lo] <= a[mid] <= a[hi]. That ordering is what
       bounds the partition scans below: the left scan cannot run past hi, and
       the right scan cannot run below lo, because a[lo] <= pivot <= a[hi]. */
    size_t mid = lo + (hi - lo) / 2;
    if (a[mid] < a[lo]) { float t = a[mid]; a[mid] = a[lo]; a[lo] = t; }
    if (a[hi] < a[lo])  { float t = a[hi]; a[hi] = a[lo]; a[lo] = t; }
    if (a[hi] < a[mid]) { float t = a[hi]; a[hi] = a[mid]; a[mid] = t; }
    float pivot = a[mid];

    size_t i = lo, j = hi;
    for (;;) {
      /* The explicit bounds are belt-and-braces: the ordering above already
         guarantees a stop, but size_t underflow here would be fatal. */
      while (i <= hi && a[i] < pivot) i++;
      while (j >= lo && pivot < a[j]) j--;
      if (i >= j) break;
      float t = a[i]; a[i] = a[j]; a[j] = t;
      i++;
      j--;
    }
    /* [lo..j] holds elements <= pivot; everything above is >= it. Narrow to
       the side containing k. Each step strictly shrinks the range because j
       starts at hi and, unless it is immediately below i, at least one swap
       has moved j down. */
    if (k <= j) hi = j;
    else        lo = j + 1;
  }
  return a[lo];
}

void tvdb_median_filter(tvdb_dense_grid* grid, int radius, int iterations) {
  if (!grid || !grid->data || radius < 1 || iterations < 1) return;
  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  size_t bytes, width, wsize, window_bytes;
  if (!tvdb_grid_bytes(nx, ny, nz, sizeof(float), &bytes)) return;
  width = 2u * (size_t)radius + 1u;
  if (!tvdb_size_mul(width, width, &wsize) ||
      !tvdb_size_mul(wsize, width, &wsize) ||
      !tvdb_size_mul(wsize, sizeof(float), &window_bytes)) return;
  float* tmp = (float*)malloc(bytes);
  if (!tmp) return;
  int allocation_failed = 0;
  /* Keep one team and one window per worker across all iterations. */
  #pragma omp parallel
  {
    float* lwin = (float*)malloc(window_bytes);
    if (!lwin) {
      #pragma omp atomic write
      allocation_failed = 1;
    }
    #pragma omp barrier
    if (!allocation_failed) {
      for (int it = 0; it < iterations; ++it) {
        /* Ping-pong src/dst by iteration parity; no per-iteration copy. */
        const float* src = ((it & 1) == 0) ? grid->data : tmp;
        float* dst = ((it & 1) == 0) ? tmp : grid->data;
        #pragma omp for collapse(2) schedule(static)
        for (int iz = 0; iz < nz; ++iz)
          for (int iy = 0; iy < ny; ++iy)
            for (int ix = 0; ix < nx; ++ix) {
              size_t n = 0;
              for (int64_t dz = -(int64_t)radius; dz <= radius; ++dz) {
                int64_t z = iz + dz;
                if (z < 0) z = 0; else if (z >= nz) z = nz - 1;
                for (int64_t dy = -(int64_t)radius; dy <= radius; ++dy) {
                  int64_t y = iy + dy;
                  if (y < 0) y = 0; else if (y >= ny) y = ny - 1;
                  size_t row = ((size_t)z * ny + (size_t)y) * nx;
                  for (int64_t dx = -(int64_t)radius; dx <= radius; ++dx) {
                    int64_t x = ix + dx;
                    if (x < 0) x = 0; else if (x >= nx) x = nx - 1;
                    lwin[n++] = src[row + (size_t)x];
                  }
                }
              }
              dst[tvdb_idx(grid, ix, iy, iz)] = tvdb_select_kth(lwin, n, n / 2);
            }
      }
    }
    free(lwin);
  }
  if (!allocation_failed && (iterations & 1) == 1) memcpy(grid->data, tmp, bytes);
  free(tmp);
}

void tvdb_mean_curvature_flow(tvdb_dense_grid* grid, float dt, int iterations) {
  if (!grid || !tvdb_grid_voxels(grid) || !grid->data || !isfinite(dt) || !isfinite(grid->voxel_size) || grid->voxel_size <= 0 || iterations < 1) return;
  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  if (nx < 3 || ny < 3 || nz < 3) return;
  const size_t nv = (size_t)nx * ny * nz;
  const size_t sl = (size_t)nx * ny;
  const float h = grid->voxel_size, h2 = grid->voxel_size * grid->voxel_size;
  float* tmp = (float*)malloc(nv * sizeof(float));
  if (!tmp) return;
  memcpy(tmp, grid->data, nv * sizeof(float));  // tmp keeps the border for both buffers
  for (int it = 0; it < iterations; ++it) {
    const float* src = ((it & 1) == 0) ? grid->data : tmp;
    float* dst = ((it & 1) == 0) ? tmp : grid->data;
    #pragma omp parallel for collapse(2) schedule(static)
    for (int iz = 1; iz < nz - 1; ++iz)
      for (int iy = 1; iy < ny - 1; ++iy)
        for (int ix = 1; ix < nx - 1; ++ix) {
          size_t i = ((size_t)iz * ny + iy) * nx + ix;
          float px = (src[i+1] - src[i-1]) / (2.0f*h);
          float py = (src[i+nx] - src[i-nx]) / (2.0f*h);
          float pz = (src[i+sl] - src[i-sl]) / (2.0f*h);
          float g2 = px*px + py*py + pz*pz;
          if (g2 < 1e-12f) { dst[i] = src[i]; continue; }
          float pxx = (src[i+1] - 2.0f*src[i] + src[i-1]) / h2;
          float pyy = (src[i+nx] - 2.0f*src[i] + src[i-nx]) / h2;
          float pzz = (src[i+sl] - 2.0f*src[i] + src[i-sl]) / h2;
          float pxy = (src[i+1+nx] - src[i-1+nx] - src[i+1-nx] + src[i-1-nx]) / (4.0f*h2);
          float pyz = (src[i+nx+sl] - src[i-nx+sl] - src[i+nx-sl] + src[i-nx-sl]) / (4.0f*h2);
          float pxz = (src[i+1+sl] - src[i-1+sl] - src[i+1-sl] + src[i-1-sl]) / (4.0f*h2);
          float num = pxx*(py*py + pz*pz) + pyy*(px*px + pz*pz) + pzz*(px*px + py*py)
                    - 2.0f*(pxy*px*py + pyz*py*pz + pxz*px*pz);
          dst[i] = src[i] + dt * (num / g2);   // dt * |grad| * kappa
        }
  }
  if ((iterations & 1) == 1) memcpy(grid->data, tmp, nv * sizeof(float));
  free(tmp);
}

// -------------------------------------------------------------------------
// Signed flood fill
// -------------------------------------------------------------------------

void tvdb_signed_flood_fill(tvdb_dense_grid* grid, float band_world) {
  if (!grid || !tvdb_grid_voxels(grid) || !grid->data || !isfinite(band_world) || band_world <= 0.0f) return;
  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  const size_t n = (size_t)nx * ny * nz, sl = (size_t)nx * ny;
  const float thresh = band_world;          // |value| >= thresh => "far"
  uint8_t* vis = (uint8_t*)calloc(n, 1);
  size_t stack_bytes;
  if (!tvdb_size_mul(n, sizeof(size_t), &stack_bytes)) { free(vis); return; }
  size_t* stack = (size_t*)malloc(stack_bytes);
  if (!vis || !stack) { free(vis); free(stack); return; }

  // Seed: far voxels on the grid boundary (connected to "infinity" = exterior).
  size_t sp = 0;
  for (int k = 0; k < nz; ++k)
    for (int j = 0; j < ny; ++j)
      for (int i = 0; i < nx; ++i) {
        if (i != 0 && i != nx-1 && j != 0 && j != ny-1 && k != 0 && k != nz-1) continue;
        size_t idx = ((size_t)k * ny + j) * nx + i;
        if (fabsf(grid->data[idx]) >= thresh && !vis[idx]) { vis[idx] = 1; stack[sp++] = idx; }
      }
  // Flood the exterior through far voxels only (the band blocks it).
  while (sp > 0) {
    size_t v = stack[--sp];
    int vi = (int)(v % nx), vj = (int)((v / nx) % ny), vk = (int)(v / sl);
    const int off[6][3] = { {1,0,0},{-1,0,0},{0,1,0},{0,-1,0},{0,0,1},{0,0,-1} };
    for (int t = 0; t < 6; ++t) {
      int ni = vi+off[t][0], nj = vj+off[t][1], nk = vk+off[t][2];
      if (ni<0||ni>=nx||nj<0||nj>=ny||nk<0||nk>=nz) continue;
      size_t nidx = ((size_t)nk * ny + nj) * nx + ni;
      if (fabsf(grid->data[nidx]) >= thresh && !vis[nidx]) { vis[nidx] = 1; stack[sp++] = nidx; }
    }
  }
  // Assign signs: reached far = exterior (+band), unreached far = interior (-band).
  for (size_t i = 0; i < n; ++i)
    if (fabsf(grid->data[i]) >= thresh)
      grid->data[i] = vis[i] ? band_world : -band_world;

  free(vis); free(stack);
}

// -------------------------------------------------------------------------
// Phase 2: trilinear sampler in voxel space (used by advection)
// -------------------------------------------------------------------------

// Sample a dense scalar grid at (vx, vy, vz) given in voxel-index coordinates
// (origin-relative, in units of voxel cells, NOT world-space).
static float tvdb_sample_dense_voxel(const tvdb_dense_grid* g, float vx, float vy, float vz) {
  if (!isfinite(vx) || !isfinite(vy) || !isfinite(vz)) { return 0; }
  vx=(float)tvdb_sample_coord(vx,g->nx); vy=(float)tvdb_sample_coord(vy,g->ny); vz=(float)tvdb_sample_coord(vz,g->nz);
  int ix = tvdb_sample_floor(vx,g->nx), iy = tvdb_sample_floor(vy,g->ny), iz = tvdb_sample_floor(vz,g->nz);
  float fx = vx - (float)ix, fy = vy - (float)iy, fz = vz - (float)iz;
  int X0 = ix < 0 ? 0 : (ix >= g->nx ? g->nx-1 : ix);
  int X1 = ix+1 < 0 ? 0 : (ix+1 >= g->nx ? g->nx-1 : ix+1);
  int Y0 = iy < 0 ? 0 : (iy >= g->ny ? g->ny-1 : iy);
  int Y1 = iy+1 < 0 ? 0 : (iy+1 >= g->ny ? g->ny-1 : iy+1);
  int Z0 = iz < 0 ? 0 : (iz >= g->nz ? g->nz-1 : iz);
  int Z1 = iz+1 < 0 ? 0 : (iz+1 >= g->nz ? g->nz-1 : iz+1);
  const size_t plane = (size_t)g->nx * (size_t)g->ny;
  const size_t b = ((size_t)Z0 * g->ny + Y0) * (size_t)g->nx + X0;
  const size_t dx = (size_t)(X1 - X0);
  const size_t dy = (size_t)(Y1 - Y0) * (size_t)g->nx;
  const size_t dz = (size_t)(Z1 - Z0) * plane;
  const float* d = g->data;
  float c000 = d[b],                 c100 = d[b + dx],
        c010 = d[b + dy],            c110 = d[b + dx + dy],
        c001 = d[b + dz],            c101 = d[b + dx + dz],
        c011 = d[b + dy + dz],       c111 = d[b + dx + dy + dz];
  float c00 = c000 * (1.0f - fx) + c100 * fx;
  float c10 = c010 * (1.0f - fx) + c110 * fx;
  float c01 = c001 * (1.0f - fx) + c101 * fx;
  float c11 = c011 * (1.0f - fx) + c111 * fx;
  float c0 = c00 * (1.0f - fy) + c10 * fy;
  float c1 = c01 * (1.0f - fy) + c11 * fy;
  return c0 * (1.0f - fz) + c1 * fz;
}

// -------------------------------------------------------------------------
// Phase 2: semi-Lagrangian advection
// -------------------------------------------------------------------------

static void tvdb_advect_semi_lagrangian_impl(const tvdb_dense_grid* field,
                                 const tvdb_dense_vec_grid* velocity,
                                 float dt,
                                 tvdb_dense_grid* result) {
  if (!field->data || !velocity->data || !result->data) return;
  if (field->nx != velocity->nx || field->ny != velocity->ny || field->nz != velocity->nz) return;
  if (!tvdb_grid_same_shape(field, result)) return;

  const int nx = field->nx, ny = field->ny, nz = field->nz;
  const float inv_h = 1.0f / field->voxel_size;
  #pragma omp parallel for collapse(2) schedule(static)
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        size_t vi = (((size_t)iz * ny + iy) * nx + ix) * 3u;
        float vx = velocity->data[vi + 0];
        float vy = velocity->data[vi + 1];
        float vz = velocity->data[vi + 2];
        // back-trace in voxel coordinates: x_back = x - dt*v / h
        float bx = (float)ix - dt * vx * inv_h;
        float by = (float)iy - dt * vy * inv_h;
        float bz = (float)iz - dt * vz * inv_h;
        result->data[tvdb_idx(result, ix, iy, iz)] =
            tvdb_sample_dense_voxel(field, bx, by, bz);
      }
    }
  }
}

// -------------------------------------------------------------------------
// Higher-order advection (RK1-4, MacCormack, BFECC)
// -------------------------------------------------------------------------

// Trilinear sample of a vector grid at voxel coordinates (clamped at borders).
static void tvdb_sample_vec_voxel(const tvdb_dense_vec_grid* g, float vx, float vy, float vz,
                                  float out[3]) {
  if (!isfinite(vx) || !isfinite(vy) || !isfinite(vz)) { out[0]=out[1]=out[2]=0; return; }
  vx=(float)tvdb_sample_coord(vx,g->nx); vy=(float)tvdb_sample_coord(vy,g->ny); vz=(float)tvdb_sample_coord(vz,g->nz);
  int ix = tvdb_sample_floor(vx,g->nx), iy = tvdb_sample_floor(vy,g->ny), iz = tvdb_sample_floor(vz,g->nz);
  float fx = vx - ix, fy = vy - iy, fz = vz - iz;
  int X0 = ix < 0 ? 0 : (ix >= g->nx ? g->nx-1 : ix);
  int X1 = ix+1 < 0 ? 0 : (ix+1 >= g->nx ? g->nx-1 : ix+1);
  int Y0 = iy < 0 ? 0 : (iy >= g->ny ? g->ny-1 : iy);
  int Y1 = iy+1 < 0 ? 0 : (iy+1 >= g->ny ? g->ny-1 : iy+1);
  int Z0 = iz < 0 ? 0 : (iz >= g->nz ? g->nz-1 : iz);
  int Z1 = iz+1 < 0 ? 0 : (iz+1 >= g->nz ? g->nz-1 : iz+1);
  const size_t b = ((size_t)Z0 * g->ny + Y0) * (size_t)g->nx + X0;
  const size_t dx = (size_t)(X1 - X0) * 3u;
  const size_t dy = (size_t)(Y1 - Y0) * (size_t)g->nx * 3u;
  const size_t dz = (size_t)(Z1 - Z0) * (size_t)g->nx * (size_t)g->ny * 3u;
  for (int c = 0; c < 3; ++c) {
    const float* p = g->data + b * 3u + (size_t)c;
    float c00 = p[0] * (1-fx) + p[dx] * fx;
    float c10 = p[dy] * (1-fx) + p[dx + dy] * fx;
    float c01 = p[dz] * (1-fx) + p[dx + dz] * fx;
    float c11 = p[dy + dz] * (1-fx) + p[dx + dy + dz] * fx;
    float c0 = c00 * (1-fy) + c10 * fy, c1 = c01 * (1-fy) + c11 * fy;
    out[c] = c0 * (1-fz) + c1 * fz;
  }
}

// Backtrace a voxel position by `dt` (negative dt = forward trace) under the
// steady velocity field, integrating dx/ds = -v(x)/h with an RK scheme of the
// given order (1..4).
static void tvdb_rk_backtrace(const tvdb_dense_vec_grid* vel, float inv_h, float dt, int order,
                              float x, float y, float z, float* bx, float* by, float* bz) {
  float v[3];
  tvdb_sample_vec_voxel(vel, x, y, z, v);
  float g1x = -v[0]*inv_h, g1y = -v[1]*inv_h, g1z = -v[2]*inv_h;
  if (order <= 1) { *bx = x + dt*g1x; *by = y + dt*g1y; *bz = z + dt*g1z; return; }
  if (order == 2) {  // midpoint
    tvdb_sample_vec_voxel(vel, x + 0.5f*dt*g1x, y + 0.5f*dt*g1y, z + 0.5f*dt*g1z, v);
    *bx = x - dt*v[0]*inv_h; *by = y - dt*v[1]*inv_h; *bz = z - dt*v[2]*inv_h; return;
  }
  if (order == 3) {  // Kutta's third order
    tvdb_sample_vec_voxel(vel, x + 0.5f*dt*g1x, y + 0.5f*dt*g1y, z + 0.5f*dt*g1z, v);
    float g2x = -v[0]*inv_h, g2y = -v[1]*inv_h, g2z = -v[2]*inv_h;
    tvdb_sample_vec_voxel(vel, x - dt*g1x + 2*dt*g2x, y - dt*g1y + 2*dt*g2y, z - dt*g1z + 2*dt*g2z, v);
    float g3x = -v[0]*inv_h, g3y = -v[1]*inv_h, g3z = -v[2]*inv_h;
    *bx = x + dt*(g1x + 4*g2x + g3x)/6.0f;
    *by = y + dt*(g1y + 4*g2y + g3y)/6.0f;
    *bz = z + dt*(g1z + 4*g2z + g3z)/6.0f;
    return;
  }
  // RK4
  tvdb_sample_vec_voxel(vel, x + 0.5f*dt*g1x, y + 0.5f*dt*g1y, z + 0.5f*dt*g1z, v);
  float g2x = -v[0]*inv_h, g2y = -v[1]*inv_h, g2z = -v[2]*inv_h;
  tvdb_sample_vec_voxel(vel, x + 0.5f*dt*g2x, y + 0.5f*dt*g2y, z + 0.5f*dt*g2z, v);
  float g3x = -v[0]*inv_h, g3y = -v[1]*inv_h, g3z = -v[2]*inv_h;
  tvdb_sample_vec_voxel(vel, x + dt*g3x, y + dt*g3y, z + dt*g3z, v);
  float g4x = -v[0]*inv_h, g4y = -v[1]*inv_h, g4z = -v[2]*inv_h;
  *bx = x + dt*(g1x + 2*g2x + 2*g3x + g4x)/6.0f;
  *by = y + dt*(g1y + 2*g2y + 2*g3y + g4y)/6.0f;
  *bz = z + dt*(g1z + 2*g2z + 2*g3z + g4z)/6.0f;
}

// Min/max of the trilinear stencil of `field` at voxel coords (for clamping).
static void tvdb_stencil_minmax(const tvdb_dense_grid* g, float vx, float vy, float vz,
                                float* mn, float* mx);

// Single semi-Lagrangian pass: result[x] = field(backtrace(x)).
//
// `bounds`, when non-NULL, is a caller-supplied 2*N array that receives the
// trilinear-stencil min and max of `field` at this voxel's backtrace point,
// interleaved as (mn, mx). That is exactly what the MacCormack and BFECC clamp
// steps need, and the backtrace depends only on the velocity, dt, order and
// position -- never on which field is being advected -- so the first pass of
// either scheme can produce those bounds for the later clamp step instead of the
// clamp redoing a full RK2 backtrace per voxel. The backtrace is 2 vector
// trilinear samples (48 taps); the min/max is 8 taps, and it replaces both the
// backtrace and the min/max scan that used to follow it.
//
// Parallel because every output voxel is a pure gather from read-only inputs.
// `result` must not alias `field` or `vel`; both public entry points guarantee
// that by routing an overlapping call through a scratch buffer first.
static void tvdb_advect_sl_ex(const tvdb_dense_grid* field, const tvdb_dense_vec_grid* vel,
                              float dt, int order, tvdb_dense_grid* result, float* bounds) {
  const int nx = field->nx, ny = field->ny, nz = field->nz;
  const float inv_h = 1.0f / field->voxel_size;
  #pragma omp parallel for collapse(2) schedule(static)
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        size_t i = tvdb_idx(result, ix, iy, iz);
        float bx, by, bz;
        tvdb_rk_backtrace(vel, inv_h, dt, order, (float)ix, (float)iy, (float)iz, &bx, &by, &bz);
        if (bounds) {
          tvdb_stencil_minmax(field, bx, by, bz, &bounds[2 * i], &bounds[2 * i + 1]);
        }
        result->data[i] = tvdb_sample_dense_voxel(field, bx, by, bz);
      }
    }
  }
}

static void tvdb_advect_sl(const tvdb_dense_grid* field, const tvdb_dense_vec_grid* vel,
                           float dt, int order, tvdb_dense_grid* result) {
  tvdb_advect_sl_ex(field, vel, dt, order, result, NULL);
}

// Min/max of the trilinear stencil of `field` at voxel coords (for clamping).
static void tvdb_stencil_minmax(const tvdb_dense_grid* g, float vx, float vy, float vz,
                                float* mn, float* mx) {
  if (!isfinite(vx) || !isfinite(vy) || !isfinite(vz)) { *mn=*mx=0; return; }
  vx=(float)tvdb_sample_coord(vx,g->nx); vy=(float)tvdb_sample_coord(vy,g->ny); vz=(float)tvdb_sample_coord(vz,g->nz);
  int ix = tvdb_sample_floor(vx,g->nx), iy = tvdb_sample_floor(vy,g->ny), iz = tvdb_sample_floor(vz,g->nz);
  *mn = 3.4e38f; *mx = -3.4e38f;
  for (int dz = 0; dz < 2; ++dz)
    for (int dy = 0; dy < 2; ++dy)
      for (int dx = 0; dx < 2; ++dx) {
        int x = ix + dx; if (x < 0) x = 0; else if (x >= g->nx) x = g->nx - 1;
        int yy = iy + dy; if (yy < 0) yy = 0; else if (yy >= g->ny) yy = g->ny - 1;
        int zz = iz + dz; if (zz < 0) zz = 0; else if (zz >= g->nz) zz = g->nz - 1;
        float s = g->data[((size_t)zz * g->ny + yy) * g->nx + x];
        if (s < *mn) *mn = s;
        if (s > *mx) *mx = s;
      }
}

static int tvdb_advect_impl(const tvdb_dense_grid* field, const tvdb_dense_vec_grid* velocity,
                 float dt, int scheme, int clamp, tvdb_dense_grid* result) {
  /* Returns nonzero only when every voxel of `result` was written. */
  if (!field->data || !velocity->data || !result->data) return 0;
  if (field->nx != velocity->nx || field->ny != velocity->ny || field->nz != velocity->nz) return 0;
  if (!tvdb_grid_same_shape(field, result)) return 0;

  if (scheme <= TVDB_ADVECT_RK4) {           // pure semi-Lagrangian, RK order = scheme+1
    tvdb_advect_sl(field, velocity, dt, scheme + 1, result);
    return 1;
  }

  const int nx = field->nx, ny = field->ny, nz = field->nz;
  const size_t n = (size_t)nx * ny * nz;
  size_t bnd_bytes = 0;
  tvdb_dense_grid phat, pstar;
  tvdb_dense_grid_init_uninit(&phat, nx, ny, nz); phat.voxel_size = field->voxel_size;
  tvdb_dense_grid_init_uninit(&pstar, nx, ny, nz); pstar.voxel_size = field->voxel_size;
  if (!phat.data || !pstar.data) { tvdb_dense_grid_free(&phat); tvdb_dense_grid_free(&pstar); return 0; }

  /* Clamp bounds, produced by the first pass. Both schemes clamp against the
     trilinear stencil of `field` at the RK2 backtrace point of each voxel, and
     the backtrace is independent of the advected field -- `corr` in the BFECC
     branch carries field->voxel_size, so inv_h and the trace are identical. One
     buffer therefore serves both, and the clamp loops below become pure
     elementwise. 2*N floats, and only when clamping was asked for. */
  float* bounds = NULL;
  if (clamp) {
    if (!tvdb_size_mul(n, 2 * sizeof(float), &bnd_bytes)) {
      tvdb_dense_grid_free(&phat); tvdb_dense_grid_free(&pstar); return 0;
    }
    bounds = (float*)malloc(bnd_bytes);
    if (!bounds) { tvdb_dense_grid_free(&phat); tvdb_dense_grid_free(&pstar); return 0; }
  }

  // Forward then backward advect (RK2 internally), giving a 2nd-order estimate
  // of the round-trip error (field - pstar).
  tvdb_advect_sl_ex(field, velocity, dt, 2, &phat, bounds);   // phat = A(field)
  tvdb_advect_sl(&phat, velocity, -dt, 2, &pstar);             // pstar = A^-1(phat)

  if (scheme == TVDB_ADVECT_MACCORMACK) {
    #pragma omp parallel for collapse(2) schedule(static)
    for (int iz = 0; iz < nz; ++iz) {
      for (int iy = 0; iy < ny; ++iy) {
        for (int ix = 0; ix < nx; ++ix) {
          size_t i = tvdb_idx(field, ix, iy, iz);
          float val = phat.data[i] + 0.5f * (field->data[i] - pstar.data[i]);
          if (clamp) {
            const float mn = bounds[2 * i], mx = bounds[2 * i + 1];
            if (val < mn) val = mn; else if (val > mx) val = mx;
          }
          result->data[i] = val;
        }
      }
    }
  } else {  // BFECC: advect the error-corrected field forward.
    tvdb_dense_grid corr;
    tvdb_dense_grid_init_uninit(&corr, nx, ny, nz); corr.voxel_size = field->voxel_size;
    if (!corr.data) {
      free(bounds);
      tvdb_dense_grid_free(&phat); tvdb_dense_grid_free(&pstar); return 0;
    }
    #pragma omp parallel for schedule(static)
    for (long long i = 0; i < (long long)n; ++i) {
      size_t k = (size_t)i;
      corr.data[k] = field->data[k] + 0.5f * (field->data[k] - pstar.data[k]);
    }
    tvdb_advect_sl(&corr, velocity, dt, 2, result);
    if (clamp) {
      #pragma omp parallel for collapse(2) schedule(static)
      for (int iz = 0; iz < nz; ++iz) {
        for (int iy = 0; iy < ny; ++iy) {
          for (int ix = 0; ix < nx; ++ix) {
            size_t i = tvdb_idx(field, ix, iy, iz);
            const float mn = bounds[2 * i], mx = bounds[2 * i + 1];
            if (result->data[i] < mn) result->data[i] = mn;
            else if (result->data[i] > mx) result->data[i] = mx;
          }
        }
      }
    }
    tvdb_dense_grid_free(&corr);
  }
  free(bounds);
  tvdb_dense_grid_free(&phat); tvdb_dense_grid_free(&pstar);
  return 1;
}

// -------------------------------------------------------------------------
// Phase 2: Poisson solver via Jacobi-preconditioned Conjugate Gradient
// -------------------------------------------------------------------------

// ---- Fast Sweeping (3D Eikonal solver, Zhao 2005) ----
//
// Solves (D^+x phi)^2 + (D^-x phi)^2 + ... = h^2 with upwind selection.
// Per-voxel: pick min(|x-|, |x+|), min(|y-|, |y+|), min(|z-|, |z+|), sort
// ascending as a,b,c. Try 1-D update, then 2-D, then 3-D solution; choose the
// smallest consistent root (first that satisfies the upwind condition).

static inline float tvdb__min2f(float a, float b) { return a < b ? a : b; }

static float tvdb__godunov_solve(float a, float b, float c, float h) {
    // a <= b <= c (sorted, all non-negative finite). h is voxel size.
    // 1D: x = a + h
    float x = a + h;
    if (x <= b) return x;
    // 2D: solve (x-a)^2 + (x-b)^2 = h^2  =>  2x^2 - 2(a+b)x + a^2+b^2-h^2 = 0
    float ab = a + b;
    float disc = 2.0f * h * h - (a - b) * (a - b);
    if (disc < 0.0f) return x;  // shouldn't happen if a<=b
    x = 0.5f * (ab + sqrtf(disc));
    if (x <= c) return x;
    // 3D: solve (x-a)^2 + (x-b)^2 + (x-c)^2 = h^2
    float abc = a + b + c;
    float sumsq = a * a + b * b + c * c;
    float disc3 = abc * abc - 3.0f * (sumsq - h * h);
    if (disc3 < 0.0f) return x;
    x = (abc + sqrtf(disc3)) / 3.0f;
    return x;
}

int tvdb_fast_sweeping(tvdb_dense_grid* grid, float frozen_band,
                       int max_iters, float tol) {
    if (!grid || !tvdb_grid_valid(grid->nx,grid->ny,grid->nz,grid->voxel_size,grid->data,sizeof(float)) || !isfinite(frozen_band) || !isfinite(tol) || tol<0) return 0;
    if (max_iters <= 0) max_iters = 1;
    if (frozen_band < 0.0f) frozen_band = 0.0f;
    const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
    const float h = grid->voxel_size > 0.0f ? grid->voxel_size : 1.0f;
    const size_t N = (size_t)nx * ny * nz;

    // Capture sign from the input field; voxels at exactly 0 are treated as
    // positive half-space.
    uint8_t* sign_pos = (uint8_t*)malloc(N);
    uint8_t* frozen   = (uint8_t*)malloc(N);
    float*   absphi   = (float*)malloc(N * sizeof(float));
    if (!sign_pos || !frozen || !absphi) {
        free(sign_pos); free(frozen); free(absphi); return 0;
    }
    const float HUGE_VAL_F = 1e30f;
    for (size_t i = 0; i < N; ++i) {
        float v = grid->data[i];
        sign_pos[i] = (v >= 0.0f) ? 1u : 0u;
        float av = fabsf(v);
        if (av <= frozen_band) {
            frozen[i] = 1u;
            absphi[i] = av;
        } else {
            frozen[i] = 0u;
            absphi[i] = HUGE_VAL_F;
        }
    }

    // 8 sweep directions over (x,y,z) ranges.
    const int dirs[8][3] = {
        { 1, 1, 1}, {-1, 1, 1}, { 1,-1, 1}, {-1,-1, 1},
        { 1, 1,-1}, {-1, 1,-1}, { 1,-1,-1}, {-1,-1,-1}
    };

    int iter = 0;
    for (; iter < max_iters; ++iter) {
        float max_change = 0.0f;
        for (int d = 0; d < 8; ++d) {
            int sx = dirs[d][0], sy = dirs[d][1], sz = dirs[d][2];
            int x0 = (sx > 0) ? 0 : nx - 1, x1 = (sx > 0) ? nx : -1;
            int y0 = (sy > 0) ? 0 : ny - 1, y1 = (sy > 0) ? ny : -1;
            int z0 = (sz > 0) ? 0 : nz - 1, z1 = (sz > 0) ? nz : -1;
            for (int z = z0; z != z1; z += sz) {
                for (int y = y0; y != y1; y += sy) {
                    for (int x = x0; x != x1; x += sx) {
                        size_t idx = tvdb_idx(grid, x, y, z);
                        if (frozen[idx]) continue;
                        // Upwind neighbor min on each axis.
                        float ax = HUGE_VAL_F;
                        if (x > 0)        ax = tvdb__min2f(ax, absphi[tvdb_idx(grid, x - 1, y, z)]);
                        if (x + 1 < nx)   ax = tvdb__min2f(ax, absphi[tvdb_idx(grid, x + 1, y, z)]);
                        float ay = HUGE_VAL_F;
                        if (y > 0)        ay = tvdb__min2f(ay, absphi[tvdb_idx(grid, x, y - 1, z)]);
                        if (y + 1 < ny)   ay = tvdb__min2f(ay, absphi[tvdb_idx(grid, x, y + 1, z)]);
                        float az = HUGE_VAL_F;
                        if (z > 0)        az = tvdb__min2f(az, absphi[tvdb_idx(grid, x, y, z - 1)]);
                        if (z + 1 < nz)   az = tvdb__min2f(az, absphi[tvdb_idx(grid, x, y, z + 1)]);
                        // Sort a<=b<=c.
                        float a = ax, b = ay, c = az;
                        if (a > b) { float t = a; a = b; b = t; }
                        if (b > c) { float t = b; b = c; c = t; }
                        if (a > b) { float t = a; a = b; b = t; }
                        if (a >= HUGE_VAL_F * 0.5f) continue;
                        float new_v = tvdb__godunov_solve(a, b, c, h);
                        if (new_v < absphi[idx]) {
                            float ch = absphi[idx] - new_v;
                            if (ch > max_change) max_change = ch;
                            absphi[idx] = new_v;
                        }
                    }
                }
            }
        }
        if (max_change <= tol) { ++iter; break; }
    }

    // Write back signed values.
    for (size_t i = 0; i < N; ++i) {
        if (frozen[i]) continue;
        float a = absphi[i];
        /* A voxel no sweep ever reached still holds the 1e30f sentinel it was
           initialised with. Writing that back replaced the caller's value with a
           ~1e30 sentinel and reported success, which is reachable whenever the
           iteration budget runs out before the wavefront covers the grid (the
           budget is clamped to >= 1). Leave the input value alone instead: a
           partially-propagated field is the honest result for a truncated solve. */
        if (a >= HUGE_VAL_F * 0.5f) continue;
        grid->data[i] = sign_pos[i] ? a : -a;
    }
    free(sign_pos); free(frozen); free(absphi);
    return iter;
}

// =============================================================================
// fp64 dense grid: lifecycle, conversion, and ops parallel to the fp32 path.
// =============================================================================

void tvdb_dense_grid_d_init(tvdb_dense_grid_d* g, int nx, int ny, int nz) {
  if (!g) return;
  g->nx = nx; g->ny = ny; g->nz = nz;
  g->voxel_size = 1.0;
  g->ox = g->oy = g->oz = 0.0;
  size_t bytes;
  if (!tvdb_grid_bytes(nx, ny, nz, sizeof(double), &bytes)) {
    g->data = NULL; g->nx = g->ny = g->nz = 0; return;
  }
  g->data = (double*)calloc(1, bytes);
}

void tvdb_dense_grid_d_free(tvdb_dense_grid_d* g) {
  if (!g) return;
  free(g->data); g->data = NULL;
  g->nx = g->ny = g->nz = 0;
}

void tvdb_dense_grid_f_to_d(const tvdb_dense_grid* in, tvdb_dense_grid_d* out) {
  if (!out) return;
  memset(out, 0, sizeof(*out));
  if (!in || !tvdb_grid_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,sizeof(float))) return;
  tvdb_dense_grid_d_init(out, in->nx, in->ny, in->nz);
  if (!out->data) { out->nx = out->ny = out->nz = 0; return; }
  out->voxel_size = (double)in->voxel_size;
  out->ox = (double)in->ox; out->oy = (double)in->oy; out->oz = (double)in->oz;
  size_t n = (size_t)in->nx * in->ny * in->nz;
  for (size_t i = 0; i < n; ++i) out->data[i] = (double)in->data[i];
}

void tvdb_dense_grid_d_to_f(const tvdb_dense_grid_d* in, tvdb_dense_grid* out) {
  if (!out) return;
  memset(out, 0, sizeof(*out));
  if (!in || !tvdb_grid_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,sizeof(double))) return;
  tvdb_dense_grid_init(out, in->nx, in->ny, in->nz);
  if (!out->data) { out->nx = out->ny = out->nz = 0; return; }
  out->voxel_size = (float)in->voxel_size;
  out->ox = (float)in->ox; out->oy = (float)in->oy; out->oz = (float)in->oz;
  size_t n = (size_t)in->nx * in->ny * in->nz;
  for (size_t i = 0; i < n; ++i) out->data[i] = (float)in->data[i];
}

double tvdb_sample_trilinear_dense_d(const tvdb_dense_grid_d* g,
                                     double wx, double wy, double wz) {
  if (!g || !tvdb_grid_valid(g->nx,g->ny,g->nz,g->voxel_size,g->data,sizeof(double)) ||
      !isfinite(wx) || !isfinite(wy) || !isfinite(wz)) return 0.0;
  // Cell-center convention: voxel `i` stores its sample at world position
  // `ox + (i + 0.5) * vs`. Same as the fp32 sampler.
  double vx = tvdb_sample_coord((wx - g->ox) / g->voxel_size - 0.5,g->nx);
  double vy = tvdb_sample_coord((wy - g->oy) / g->voxel_size - 0.5,g->ny);
  double vz = tvdb_sample_coord((wz - g->oz) / g->voxel_size - 0.5,g->nz);
  int ix = tvdb_sample_floor(vx,g->nx), iy = tvdb_sample_floor(vy,g->ny), iz = tvdb_sample_floor(vz,g->nz);
  double fx = vx - (double)ix, fy = vy - (double)iy, fz = vz - (double)iz;

  double c000 = tvdb_at_d(g, ix,     iy,     iz);
  double c100 = tvdb_at_d(g, ix + 1, iy,     iz);
  double c010 = tvdb_at_d(g, ix,     iy + 1, iz);
  double c110 = tvdb_at_d(g, ix + 1, iy + 1, iz);
  double c001 = tvdb_at_d(g, ix,     iy,     iz + 1);
  double c101 = tvdb_at_d(g, ix + 1, iy,     iz + 1);
  double c011 = tvdb_at_d(g, ix,     iy + 1, iz + 1);
  double c111 = tvdb_at_d(g, ix + 1, iy + 1, iz + 1);
  double c00 = c000 * (1.0 - fx) + c100 * fx;
  double c10 = c010 * (1.0 - fx) + c110 * fx;
  double c01 = c001 * (1.0 - fx) + c101 * fx;
  double c11 = c011 * (1.0 - fx) + c111 * fx;
  double c0 = c00 * (1.0 - fy) + c10 * fy;
  double c1 = c01 * (1.0 - fy) + c11 * fy;
  return c0 * (1.0 - fz) + c1 * fz;
}

static void tvdb_laplacian_d_impl(const tvdb_dense_grid_d* g, tvdb_dense_grid_d* out) {
  // 7-point Laplacian with edge clamp. h^2 normalization.
  double inv_h2 = 1.0 / (g->voxel_size * g->voxel_size);
  #pragma omp parallel for collapse(2) schedule(static)
  for (int z = 0; z < g->nz; ++z) {
    for (int y = 0; y < g->ny; ++y) {
      for (int x = 0; x < g->nx; ++x) {
        double c = g->data[tvdb_idx_d(g, x, y, z)];
        double s = tvdb_at_d(g, x - 1, y,     z)
                 + tvdb_at_d(g, x + 1, y,     z)
                 + tvdb_at_d(g, x,     y - 1, z)
                 + tvdb_at_d(g, x,     y + 1, z)
                 + tvdb_at_d(g, x,     y,     z - 1)
                 + tvdb_at_d(g, x,     y,     z + 1);
        out->data[tvdb_idx_d(out, x, y, z)] = (s - 6.0 * c) * inv_h2;
      }
    }
  }
}

static inline double dmin(double a, double b) { return a < b ? a : b; }
static inline double dmax(double a, double b) { return a > b ? a : b; }

void tvdb_csg_union_d(const tvdb_dense_grid_d* a, const tvdb_dense_grid_d* b,
                      tvdb_dense_grid_d* out) {
  size_t bytes;
  if (!a || !b || !out || !out->data ||
      !tvdb_grid_valid(a->nx,a->ny,a->nz,a->voxel_size,a->data,sizeof(double)) ||
      !tvdb_grid_valid(b->nx,b->ny,b->nz,b->voxel_size,b->data,sizeof(double)) ||
      a->nx != b->nx || a->ny != b->ny || a->nz != b->nz ||
      a->nx != out->nx || a->ny != out->ny || a->nz != out->nz ||
      !tvdb_grid_bytes(out->nx,out->ny,out->nz,sizeof(double),&bytes)) return;
  size_t n = (size_t)out->nx * out->ny * out->nz;
  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)n; ++i) {
    out->data[i] = dmin(a->data[i], b->data[i]);
  }
}

void tvdb_csg_intersection_d(const tvdb_dense_grid_d* a, const tvdb_dense_grid_d* b,
                             tvdb_dense_grid_d* out) {
  size_t bytes;
  if (!a || !b || !out || !out->data ||
      !tvdb_grid_valid(a->nx,a->ny,a->nz,a->voxel_size,a->data,sizeof(double)) ||
      !tvdb_grid_valid(b->nx,b->ny,b->nz,b->voxel_size,b->data,sizeof(double)) ||
      a->nx != b->nx || a->ny != b->ny || a->nz != b->nz ||
      a->nx != out->nx || a->ny != out->ny || a->nz != out->nz ||
      !tvdb_grid_bytes(out->nx,out->ny,out->nz,sizeof(double),&bytes)) return;
  size_t n = (size_t)out->nx * out->ny * out->nz;
  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)n; ++i) {
    out->data[i] = dmax(a->data[i], b->data[i]);
  }
}

void tvdb_csg_difference_d(const tvdb_dense_grid_d* a, const tvdb_dense_grid_d* b,
                           tvdb_dense_grid_d* out) {
  size_t bytes;
  if (!a || !b || !out || !out->data ||
      !tvdb_grid_valid(a->nx,a->ny,a->nz,a->voxel_size,a->data,sizeof(double)) ||
      !tvdb_grid_valid(b->nx,b->ny,b->nz,b->voxel_size,b->data,sizeof(double)) ||
      a->nx != b->nx || a->ny != b->ny || a->nz != b->nz ||
      a->nx != out->nx || a->ny != out->ny || a->nz != out->nz ||
      !tvdb_grid_bytes(out->nx,out->ny,out->nz,sizeof(double),&bytes)) return;
  size_t n = (size_t)out->nx * out->ny * out->nz;
  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)n; ++i) {
    out->data[i] = dmax(a->data[i], -b->data[i]);
  }
}

double tvdb_volume_d(const tvdb_dense_grid_d* g) {
  /* Guarded like the fp32 twin. These two used to dereference `g` on the first
     line (g->voxel_size) with no null check, so a NULL argument was a segfault
     where the fp32 path returned 0. */
  /* Also reject non-positive/non-finite spacing and overflowing dimensions,
     matching the fp32 twin (NaN spacing used to pass and return NaN). */
  if (!g || !tvdb_grid_valid(g->nx,g->ny,g->nz,g->voxel_size,g->data,sizeof(double))) return 0.0;
  // Sum of voxel cells whose value is < 0.
  double cell = g->voxel_size * g->voxel_size * g->voxel_size;
  double vol = 0.0;
  size_t n = (size_t)g->nx * g->ny * g->nz;
  #pragma omp parallel for reduction(+:vol) schedule(static)
  for (long long i = 0; i < (long long)n; ++i) {
    if (g->data[i] < 0.0) vol += cell;
  }
  return vol;
}

double tvdb_surface_area_d(const tvdb_dense_grid_d* g) {
  /* Same guard as tvdb_volume_d: a NULL grid or NULL data used to fault here
     instead of returning 0, and the fp32 twin returns 0. */
  /* Also reject non-positive/non-finite spacing and overflowing dimensions,
     matching the fp32 twin (NaN spacing used to pass and return NaN). */
  if (!g || !tvdb_grid_valid(g->nx,g->ny,g->nz,g->voxel_size,g->data,sizeof(double))) return 0.0;
  // Count zero-crossings over 6-neighbor edges; weight by voxel_size^2.
  double face = g->voxel_size * g->voxel_size;
  double area = 0.0;
  #pragma omp parallel for collapse(2) reduction(+:area) schedule(static)
  for (int z = 0; z < g->nz; ++z) {
    for (int y = 0; y < g->ny; ++y) {
      for (int x = 0; x < g->nx; ++x) {
        double c = g->data[tvdb_idx_d(g, x, y, z)];
        if (x + 1 < g->nx) {
          double n2 = g->data[tvdb_idx_d(g, x + 1, y, z)];
          if ((c < 0.0) != (n2 < 0.0)) area += face;
        }
        if (y + 1 < g->ny) {
          double n2 = g->data[tvdb_idx_d(g, x, y + 1, z)];
          if ((c < 0.0) != (n2 < 0.0)) area += face;
        }
        if (z + 1 < g->nz) {
          double n2 = g->data[tvdb_idx_d(g, x, y, z + 1)];
          if ((c < 0.0) != (n2 < 0.0)) area += face;
        }
      }
    }
  }
  return area;
}

// FastSweeping: fp64 8-direction Eikonal solver. Logic mirrors the fp32
// path but accumulates everything in double.

static inline double tvdb__godunov_solve_d(double a, double b, double c, double h) {
  double x = a + h;
  if (x <= b) return x;
  double ab = a + b;
  double disc = 2.0 * h * h - (a - b) * (a - b);
  if (disc < 0.0) return x;
  x = 0.5 * (ab + sqrt(disc));
  if (x <= c) return x;
  double abc = a + b + c;
  double sumsq = a * a + b * b + c * c;
  double disc3 = abc * abc - 3.0 * (sumsq - h * h);
  if (disc3 < 0.0) return x;
  return (abc + sqrt(disc3)) / 3.0;
}

int tvdb_fast_sweeping_d(tvdb_dense_grid_d* grid, double frozen_band,
                         int max_iters, double tol) {
  if (!grid || !tvdb_grid_valid(grid->nx,grid->ny,grid->nz,grid->voxel_size,grid->data,sizeof(double)) || !isfinite(frozen_band) || !isfinite(tol) || tol<0) return 0;
  if (max_iters <= 0) max_iters = 1;
  if (frozen_band < 0.0) frozen_band = 0.0;
  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  const double h = grid->voxel_size > 0.0 ? grid->voxel_size : 1.0;
  const size_t N = (size_t)nx * ny * nz;
  uint8_t* sign_pos = (uint8_t*)malloc(N);
  uint8_t* frozen   = (uint8_t*)malloc(N);
  double*  absphi   = (double*)malloc(N * sizeof(double));
  if (!sign_pos || !frozen || !absphi) {
    free(sign_pos); free(frozen); free(absphi); return 0;
  }
  const double HUGE_D = 1e30;
  for (size_t i = 0; i < N; ++i) {
    double v = grid->data[i];
    sign_pos[i] = (v >= 0.0) ? 1u : 0u;
    double av = fabs(v);
    if (av <= frozen_band) { frozen[i] = 1u; absphi[i] = av; }
    else { frozen[i] = 0u; absphi[i] = HUGE_D; }
  }
  const int dirs[8][3] = {
    { 1, 1, 1}, {-1, 1, 1}, { 1,-1, 1}, {-1,-1, 1},
    { 1, 1,-1}, {-1, 1,-1}, { 1,-1,-1}, {-1,-1,-1}
  };
  int iter = 0;
  for (; iter < max_iters; ++iter) {
    double max_change = 0.0;
    for (int d = 0; d < 8; ++d) {
      int sx = dirs[d][0], sy = dirs[d][1], sz = dirs[d][2];
      int x0 = (sx > 0) ? 0 : nx - 1, x1 = (sx > 0) ? nx : -1;
      int y0 = (sy > 0) ? 0 : ny - 1, y1 = (sy > 0) ? ny : -1;
      int z0 = (sz > 0) ? 0 : nz - 1, z1 = (sz > 0) ? nz : -1;
      for (int z = z0; z != z1; z += sz) {
        for (int y = y0; y != y1; y += sy) {
          for (int x = x0; x != x1; x += sx) {
            size_t idx = tvdb_idx_d(grid, x, y, z);
            if (frozen[idx]) continue;
            double ax = HUGE_D;
            if (x > 0)        ax = dmin(ax, absphi[tvdb_idx_d(grid, x - 1, y, z)]);
            if (x + 1 < nx)   ax = dmin(ax, absphi[tvdb_idx_d(grid, x + 1, y, z)]);
            double ay = HUGE_D;
            if (y > 0)        ay = dmin(ay, absphi[tvdb_idx_d(grid, x, y - 1, z)]);
            if (y + 1 < ny)   ay = dmin(ay, absphi[tvdb_idx_d(grid, x, y + 1, z)]);
            double az = HUGE_D;
            if (z > 0)        az = dmin(az, absphi[tvdb_idx_d(grid, x, y, z - 1)]);
            if (z + 1 < nz)   az = dmin(az, absphi[tvdb_idx_d(grid, x, y, z + 1)]);
            double a = ax, b = ay, c = az;
            if (a > b) { double t = a; a = b; b = t; }
            if (b > c) { double t = b; b = c; c = t; }
            if (a > b) { double t = a; a = b; b = t; }
            if (a >= HUGE_D * 0.5) continue;
            double new_v = tvdb__godunov_solve_d(a, b, c, h);
            if (new_v < absphi[idx]) {
              double ch = absphi[idx] - new_v;
              if (ch > max_change) max_change = ch;
              absphi[idx] = new_v;
            }
          }
        }
      }
    }
    if (max_change <= tol) { ++iter; break; }
  }
  for (size_t i = 0; i < N; ++i) {
    if (frozen[i]) continue;
    /* Unreached voxels still hold the HUGE_D sentinel; keep the caller's value
       rather than writing a 1e30 sentinel back. Same rule as the fp32 sweep. */
    if (absphi[i] >= HUGE_D * 0.5) continue;
    grid->data[i] = sign_pos[i] ? absphi[i] : -absphi[i];
  }
  free(sign_pos); free(frozen); free(absphi);
  return iter;
}

// fp64 Poisson (PCG with Jacobi preconditioner; identical structure to the
// fp32 path but doubles throughout).

void tvdb_gradient(const tvdb_dense_grid* in, tvdb_dense_vec_grid* out) {
  size_t ib, ob;
  if (!in || !out || !tvdb_grid_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,1 * sizeof(float)) ||
      !tvdb_grid_bytes(out->nx,out->ny,out->nz,3 * sizeof(float),&ob) || !out->data ||
      in->nx != out->nx || in->ny != out->ny || in->nz != out->nz) return;
  tvdb_grid_bytes(in->nx,in->ny,in->nz,1 * sizeof(float),&ib);
  if (tvdb_buffers_overlap(in->data,ib,out->data,ob)) {
    tvdb_dense_vec_grid tmp = *out; tmp.data = (float*)malloc(ob);
    if (!tmp.data) return;
    tvdb_gradient_impl(in,&tmp); memcpy(out->data,tmp.data,ob); free(tmp.data);
  } else tvdb_gradient_impl(in,out);
}

void tvdb_divergence(const tvdb_dense_vec_grid* in, tvdb_dense_grid* out) {
  size_t ib, ob;
  if (!in || !out || !tvdb_grid_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,3 * sizeof(float)) ||
      !tvdb_grid_bytes(out->nx,out->ny,out->nz,1 * sizeof(float),&ob) || !out->data ||
      in->nx != out->nx || in->ny != out->ny || in->nz != out->nz) return;
  tvdb_grid_bytes(in->nx,in->ny,in->nz,3 * sizeof(float),&ib);
  if (tvdb_buffers_overlap(in->data,ib,out->data,ob)) {
    tvdb_dense_grid tmp = *out; tmp.data = (float*)malloc(ob);
    if (!tmp.data) return;
    tvdb_divergence_impl(in,&tmp); memcpy(out->data,tmp.data,ob); free(tmp.data);
  } else tvdb_divergence_impl(in,out);
}

void tvdb_laplacian(const tvdb_dense_grid* in, tvdb_dense_grid* out) {
  size_t ib, ob;
  if (!in || !out || !tvdb_grid_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,1 * sizeof(float)) ||
      !tvdb_grid_bytes(out->nx,out->ny,out->nz,1 * sizeof(float),&ob) || !out->data ||
      in->nx != out->nx || in->ny != out->ny || in->nz != out->nz) return;
  tvdb_grid_bytes(in->nx,in->ny,in->nz,1 * sizeof(float),&ib);
  if (tvdb_buffers_overlap(in->data,ib,out->data,ob)) {
    tvdb_dense_grid tmp = *out; tmp.data = (float*)malloc(ob);
    if (!tmp.data) return;
    tvdb_laplacian_impl(in,&tmp); memcpy(out->data,tmp.data,ob); free(tmp.data);
  } else tvdb_laplacian_impl(in,out);
}

void tvdb_curl(const tvdb_dense_vec_grid* in, tvdb_dense_vec_grid* out) {
  size_t ib, ob;
  if (!in || !out || !tvdb_grid_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,3 * sizeof(float)) ||
      !tvdb_grid_bytes(out->nx,out->ny,out->nz,3 * sizeof(float),&ob) || !out->data ||
      in->nx != out->nx || in->ny != out->ny || in->nz != out->nz) return;
  tvdb_grid_bytes(in->nx,in->ny,in->nz,3 * sizeof(float),&ib);
  if (tvdb_buffers_overlap(in->data,ib,out->data,ob)) {
    tvdb_dense_vec_grid tmp = *out; tmp.data = (float*)malloc(ob);
    if (!tmp.data) return;
    tvdb_curl_impl(in,&tmp); memcpy(out->data,tmp.data,ob); free(tmp.data);
  } else tvdb_curl_impl(in,out);
}

void tvdb_cpt(const tvdb_dense_grid* in, tvdb_dense_vec_grid* out) {
  size_t ib, ob;
  if (!in || !out || !tvdb_grid_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,1 * sizeof(float)) ||
      !tvdb_grid_bytes(out->nx,out->ny,out->nz,3 * sizeof(float),&ob) || !out->data ||
      in->nx != out->nx || in->ny != out->ny || in->nz != out->nz) return;
  tvdb_grid_bytes(in->nx,in->ny,in->nz,1 * sizeof(float),&ib);
  if (tvdb_buffers_overlap(in->data,ib,out->data,ob)) {
    tvdb_dense_vec_grid tmp = *out; tmp.data = (float*)malloc(ob);
    if (!tmp.data) return;
    tvdb_cpt_impl(in,&tmp); memcpy(out->data,tmp.data,ob); free(tmp.data);
  } else tvdb_cpt_impl(in,out);
}

void tvdb_magnitude(const tvdb_dense_vec_grid* in, tvdb_dense_grid* out) {
  size_t ib, ob;
  if (!in || !out || !tvdb_grid_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,3 * sizeof(float)) ||
      !tvdb_grid_bytes(out->nx,out->ny,out->nz,1 * sizeof(float),&ob) || !out->data ||
      in->nx != out->nx || in->ny != out->ny || in->nz != out->nz) return;
  tvdb_grid_bytes(in->nx,in->ny,in->nz,3 * sizeof(float),&ib);
  if (tvdb_buffers_overlap(in->data,ib,out->data,ob)) {
    tvdb_dense_grid tmp = *out; tmp.data = (float*)malloc(ob);
    if (!tmp.data) return;
    tvdb_magnitude_impl(in,&tmp); memcpy(out->data,tmp.data,ob); free(tmp.data);
  } else tvdb_magnitude_impl(in,out);
}

void tvdb_normalize_vec(const tvdb_dense_vec_grid* in, tvdb_dense_vec_grid* out) {
  size_t ib, ob;
  if (!in || !out || !tvdb_grid_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,3 * sizeof(float)) ||
      !tvdb_grid_bytes(out->nx,out->ny,out->nz,3 * sizeof(float),&ob) || !out->data ||
      in->nx != out->nx || in->ny != out->ny || in->nz != out->nz) return;
  tvdb_grid_bytes(in->nx,in->ny,in->nz,3 * sizeof(float),&ib);
  if(in->data==out->data) { tvdb_normalize_vec_impl(in,out); return; }
  if (tvdb_buffers_overlap(in->data,ib,out->data,ob)) {
    tvdb_dense_vec_grid tmp = *out; tmp.data = (float*)malloc(ob);
    if (!tmp.data) return;
    tvdb_normalize_vec_impl(in,&tmp); memcpy(out->data,tmp.data,ob); free(tmp.data);
  } else tvdb_normalize_vec_impl(in,out);
}

void tvdb_laplacian_d(const tvdb_dense_grid_d* in, tvdb_dense_grid_d* out) {
  size_t ib, ob;
  if (!in || !out || !tvdb_grid_valid(in->nx,in->ny,in->nz,in->voxel_size,in->data,1 * sizeof(double)) ||
      !tvdb_grid_bytes(out->nx,out->ny,out->nz,1 * sizeof(double),&ob) || !out->data ||
      in->nx != out->nx || in->ny != out->ny || in->nz != out->nz) return;
  tvdb_grid_bytes(in->nx,in->ny,in->nz,1 * sizeof(double),&ib);
  if (tvdb_buffers_overlap(in->data,ib,out->data,ob)) {
    tvdb_dense_grid_d tmp = *out; tmp.data = (double*)malloc(ob);
    if (!tmp.data) return;
    tvdb_laplacian_d_impl(in,&tmp); memcpy(out->data,tmp.data,ob); free(tmp.data);
  } else tvdb_laplacian_d_impl(in,out);
}

void tvdb_advect_semi_lagrangian(const tvdb_dense_grid* field, const tvdb_dense_vec_grid* velocity,
 float dt, tvdb_dense_grid* result) {
  size_t fb, vb;
  if (!field || !velocity || !result || !isfinite(dt) ||
      !tvdb_grid_same_shape(field,result) ||
      !tvdb_grid_valid(field->nx,field->ny,field->nz,field->voxel_size,field->data,sizeof(float)) ||
      !tvdb_grid_valid(velocity->nx,velocity->ny,velocity->nz,velocity->voxel_size,velocity->data,3*sizeof(float)) ||
      field->nx != velocity->nx || field->ny != velocity->ny || field->nz != velocity->nz) return;

  tvdb_grid_bytes(field->nx,field->ny,field->nz,sizeof(float),&fb);
  tvdb_grid_bytes(velocity->nx,velocity->ny,velocity->nz,3*sizeof(float),&vb);
  if (tvdb_buffers_overlap(field->data,fb,result->data,fb) ||
      tvdb_buffers_overlap(velocity->data,vb,result->data,fb)) {
    tvdb_dense_grid tmp = *result; tmp.data = (float*)malloc(fb);
    if (!tmp.data) return;
    /* No copy into tmp: tvdb_advect_semi_lagrangian_impl writes every voxel
       unconditionally, so result's prior contents are never read. The copy was a
       full 4N-byte read plus write on the in-place path for nothing. */
    tvdb_advect_semi_lagrangian_impl(field,velocity,dt,&tmp);
    memcpy(result->data,tmp.data,fb); free(tmp.data);
  } else tvdb_advect_semi_lagrangian_impl(field,velocity,dt,result);
}

void tvdb_advect(const tvdb_dense_grid* field, const tvdb_dense_vec_grid* velocity,
 float dt, int scheme, int clamp, tvdb_dense_grid* result) {
  size_t fb, vb;
  if (!field || !velocity || !result || !isfinite(dt) ||
      !tvdb_grid_same_shape(field,result) ||
      !tvdb_grid_valid(field->nx,field->ny,field->nz,field->voxel_size,field->data,sizeof(float)) ||
      !tvdb_grid_valid(velocity->nx,velocity->ny,velocity->nz,velocity->voxel_size,velocity->data,3*sizeof(float)) ||
      field->nx != velocity->nx || field->ny != velocity->ny || field->nz != velocity->nz) return;
  if (scheme < TVDB_ADVECT_RK1 || scheme > TVDB_ADVECT_BFECC) return;

  tvdb_grid_bytes(field->nx,field->ny,field->nz,sizeof(float),&fb);
  tvdb_grid_bytes(velocity->nx,velocity->ny,velocity->nz,3*sizeof(float),&vb);
  if (tvdb_buffers_overlap(field->data,fb,result->data,fb) ||
      tvdb_buffers_overlap(velocity->data,vb,result->data,fb)) {
    tvdb_dense_grid tmp = *result; tmp.data = (float*)malloc(fb);
    if (!tmp.data) return;
    /* As above: the impl writes every voxel, so the incoming value is not read. */
    /* Publish only a complete result: an internal scratch allocation failure
       leaves tmp partly uninitialized, and the contract keeps result intact. */
    if (tvdb_advect_impl(field,velocity,dt, scheme, clamp,&tmp))
      memcpy(result->data,tmp.data,fb);
    free(tmp.data);
  } else (void)tvdb_advect_impl(field,velocity,dt, scheme, clamp,result);
}

tvdb_status_t tvdb_solve_poisson_ex(const tvdb_dense_grid* rhs,tvdb_dense_grid* x,int max_iters,float tolerance,
 tvdb_poisson_result_t* result,tvdb_error_t* err) {
  if(!rhs || !x || rhs->nx!=x->nx || rhs->ny!=x->ny || rhs->nz!=x->nz || rhs->voxel_size!=x->voxel_size) {
    if(result) memset(result,0,sizeof(*result));
    if(err) { memset(err,0,sizeof(*err)); err->status=TVDB_ERROR_INVALID_ARGUMENT; }
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  return tvdb_poisson_solve_core(rhs->data,x->data,rhs->nx,rhs->ny,rhs->nz,rhs->voxel_size,
    false,false,max_iters,tolerance,false,result,err,NULL,NULL);
}
int tvdb_solve_poisson(const tvdb_dense_grid* rhs,tvdb_dense_grid* x,int max_iters,float tolerance) {
  tvdb_poisson_result_t result;
  return tvdb_solve_poisson_ex(rhs,x,max_iters,tolerance,&result,NULL)==TVDB_OK ? result.iterations : 0;
}

tvdb_status_t tvdb_solve_poisson_d_ex(const tvdb_dense_grid* rhs,tvdb_dense_grid* x,int max_iters,double tolerance,
 tvdb_poisson_result_t* result,tvdb_error_t* err) {
  if(!rhs || !x || rhs->nx!=x->nx || rhs->ny!=x->ny || rhs->nz!=x->nz || rhs->voxel_size!=x->voxel_size) {
    if(result) memset(result,0,sizeof(*result));
    if(err) { memset(err,0,sizeof(*err)); err->status=TVDB_ERROR_INVALID_ARGUMENT; }
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  return tvdb_poisson_solve_core(rhs->data,x->data,rhs->nx,rhs->ny,rhs->nz,rhs->voxel_size,
    false,true,max_iters,tolerance,false,result,err,NULL,NULL);
}
int tvdb_solve_poisson_d(const tvdb_dense_grid* rhs,tvdb_dense_grid* x,int max_iters,double tolerance) {
  tvdb_poisson_result_t result;
  return tvdb_solve_poisson_d_ex(rhs,x,max_iters,tolerance,&result,NULL)==TVDB_OK ? result.iterations : 0;
}

tvdb_status_t tvdb_solve_poisson_dd_ex(const tvdb_dense_grid_d* rhs,tvdb_dense_grid_d* x,int max_iters,double tolerance,
 tvdb_poisson_result_t* result,tvdb_error_t* err) {
  if(!rhs || !x || rhs->nx!=x->nx || rhs->ny!=x->ny || rhs->nz!=x->nz || rhs->voxel_size!=x->voxel_size) {
    if(result) memset(result,0,sizeof(*result));
    if(err) { memset(err,0,sizeof(*err)); err->status=TVDB_ERROR_INVALID_ARGUMENT; }
    return TVDB_ERROR_INVALID_ARGUMENT;
  }
  return tvdb_poisson_solve_core(rhs->data,x->data,rhs->nx,rhs->ny,rhs->nz,rhs->voxel_size,
    true,true,max_iters,tolerance,true,result,err,NULL,NULL);
}
int tvdb_solve_poisson_dd(const tvdb_dense_grid_d* rhs,tvdb_dense_grid_d* x,int max_iters,double tolerance) {
  tvdb_poisson_result_t result;
  return tvdb_solve_poisson_dd_ex(rhs,x,max_iters,tolerance,&result,NULL)==TVDB_OK ? result.iterations : 0;
}
