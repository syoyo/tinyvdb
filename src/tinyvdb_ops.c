#include "tinyvdb_ops.h"
#include "tinyvdb_ops_internal.h"
#include "tinyvdb_simd.h"

#include <math.h>
#include <stdlib.h>
#include <string.h>

// -------------------------------------------------------------------------
// dense vec grid lifecycle
// -------------------------------------------------------------------------

void tvdb_dense_vec_grid_init(tvdb_dense_vec_grid* grid, int nx, int ny, int nz) {
  grid->nx = nx;
  grid->ny = ny;
  grid->nz = nz;
  grid->ox = grid->oy = grid->oz = 0.0f;
  grid->voxel_size = 1.0f;
  grid->data = (float*)malloc((size_t)nx * (size_t)ny * (size_t)nz * 3u * sizeof(float));
  if (grid->data) {
    memset(grid->data, 0, (size_t)nx * (size_t)ny * (size_t)nz * 3u * sizeof(float));
  }
}

void tvdb_dense_vec_grid_free(tvdb_dense_vec_grid* grid) {
  if (grid->data) free(grid->data);
  grid->data = NULL;
}

// -------------------------------------------------------------------------
// helpers
// -------------------------------------------------------------------------

static int tvdb_grid_voxels(const tvdb_dense_grid* g) {
  return g->nx * g->ny * g->nz;
}

static int tvdb_grid_same_shape(const tvdb_dense_grid* a, const tvdb_dense_grid* b) {
  return a->nx == b->nx && a->ny == b->ny && a->nz == b->nz;
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
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        float c = in->data[tvdb_idx(in, ix, iy, iz)];
        float xm = tvdb_at(in, ix - 1, iy, iz);
        float xp = tvdb_at(in, ix + 1, iy, iz);
        float ym = tvdb_at(in, ix, iy - 1, iz);
        float yp = tvdb_at(in, ix, iy + 1, iz);
        float zm = tvdb_at(in, ix, iy, iz - 1);
        float zp = tvdb_at(in, ix, iy, iz + 1);
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
        out->data[tvdb_idx(out, ix, iy, iz)] = r;
      }
    }
  }
}

static void tvdb_morph_iter(tvdb_dense_grid* grid, int iterations, int is_dilate) {
  if (iterations <= 0 || grid->data == NULL) return;
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
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        float acc = 0.0f;
        for (int k = -radius; k <= radius; ++k) {
          int sx = ix, sy = iy, sz = iz;
          if (axis == 0) sx = ix + k;
          else if (axis == 1) sy = iy + k;
          else sz = iz + k;
          acc += kernel[k + radius] * tvdb_at(in, sx, sy, sz);
        }
        out->data[tvdb_idx(out, ix, iy, iz)] = acc;
      }
    }
  }
}

static void tvdb_apply_separable(tvdb_dense_grid* grid, const float* kernel,
                                 int radius, int iterations) {
  if (iterations <= 0 || radius <= 0 || grid->data == NULL) return;
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
  if (width <= 0) return;
  const int radius = width;
  const int len = 2 * radius + 1;
  const float sigma = (float)width * 0.5f;
  const float two_s2 = 2.0f * sigma * sigma;
  float* k = (float*)malloc((size_t)len * sizeof(float));
  if (!k) return;
  float sum = 0.0f;
  for (int i = -radius; i <= radius; ++i) {
    float v = expf(-((float)(i * i)) / two_s2);
    k[i + radius] = v;
    sum += v;
  }
  for (int i = 0; i < len; ++i) k[i] /= sum;
  tvdb_apply_separable(grid, k, radius, iterations);
  free(k);
}

void tvdb_mean_filter(tvdb_dense_grid* grid, int width, int iterations) {
  if (width <= 0) return;
  const int radius = width;
  const int len = 2 * radius + 1;
  float* k = (float*)malloc((size_t)len * sizeof(float));
  if (!k) return;
  const float w = 1.0f / (float)len;
  for (int i = 0; i < len; ++i) k[i] = w;
  tvdb_apply_separable(grid, k, radius, iterations);
  free(k);
}

// laplacian_filter: explicit-Euler diffusion step using a 7-point stencil.
// dt = h^2 / 8 (CFL stable for 3-D heat eq, margin below h^2/6).
void tvdb_laplacian_filter(tvdb_dense_grid* grid, int iterations) {
  if (iterations <= 0 || grid->data == NULL) return;
  const size_t nv = (size_t)tvdb_grid_voxels(grid);
  float* tmp = (float*)malloc(nv * sizeof(float));
  if (!tmp) return;

  tvdb_dense_grid scratch = *grid;
  scratch.data = tmp;

  const float dt = 1.0f / 8.0f;  // h^2 cancels in the discrete laplacian below
  // discrete laplacian L = (sum6 - 6 c) / h^2; update u += dt * h^2 * L = dt*(sum6 - 6 c)

  for (int it = 0; it < iterations; ++it) {
    const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
    for (int iz = 0; iz < nz; ++iz) {
      for (int iy = 0; iy < ny; ++iy) {
        for (int ix = 0; ix < nx; ++ix) {
          float c  = grid->data[tvdb_idx(grid, ix, iy, iz)];
          float s  = tvdb_at(grid, ix - 1, iy, iz)
                   + tvdb_at(grid, ix + 1, iy, iz)
                   + tvdb_at(grid, ix, iy - 1, iz)
                   + tvdb_at(grid, ix, iy + 1, iz)
                   + tvdb_at(grid, ix, iy, iz - 1)
                   + tvdb_at(grid, ix, iy, iz + 1);
          tmp[tvdb_idx(grid, ix, iy, iz)] = c + dt * (s - 6.0f * c);
        }
      }
    }
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
  for (size_t i = 0; i < nv; ++i) {
    float va = a->data[i], vb = b->data[i];
    result->data[i] = va < vb ? va : vb;
  }
}

void tvdb_csg_intersection(const tvdb_dense_grid* a, const tvdb_dense_grid* b, tvdb_dense_grid* result) {
  if (!tvdb_grid_same_shape(a, b) || !tvdb_grid_same_shape(a, result)) return;
  const size_t nv = (size_t)tvdb_grid_voxels(a);
  for (size_t i = 0; i < nv; ++i) {
    float va = a->data[i], vb = b->data[i];
    result->data[i] = va > vb ? va : vb;
  }
}

void tvdb_csg_difference(const tvdb_dense_grid* a, const tvdb_dense_grid* b, tvdb_dense_grid* result) {
  if (!tvdb_grid_same_shape(a, b) || !tvdb_grid_same_shape(a, result)) return;
  const size_t nv = (size_t)tvdb_grid_voxels(a);
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
  if (!grid->data) return 0.0f;
  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  size_t crossings = 0;
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        float c = grid->data[tvdb_idx(grid, ix, iy, iz)];
        if (ix + 1 < nx) {
          float n = grid->data[tvdb_idx(grid, ix + 1, iy, iz)];
          if ((c <= 0.0f) != (n <= 0.0f)) ++crossings;
        }
        if (iy + 1 < ny) {
          float n = grid->data[tvdb_idx(grid, ix, iy + 1, iz)];
          if ((c <= 0.0f) != (n <= 0.0f)) ++crossings;
        }
        if (iz + 1 < nz) {
          float n = grid->data[tvdb_idx(grid, ix, iy, iz + 1)];
          if ((c <= 0.0f) != (n <= 0.0f)) ++crossings;
        }
      }
    }
  }
  return (float)crossings * grid->voxel_size * grid->voxel_size;
}

// Volume: integrate inside-region (f < 0). Each voxel contributes voxel_size^3.
float tvdb_volume(const tvdb_dense_grid* grid) {
  if (!grid->data) return 0.0f;
  const size_t nv = (size_t)tvdb_grid_voxels(grid);
  size_t inside = 0;
  for (size_t i = 0; i < nv; ++i) {
    if (grid->data[i] < 0.0f) ++inside;
  }
  const float h = grid->voxel_size;
  return (float)inside * h * h * h;
}

// -------------------------------------------------------------------------
// Phase 2: differential operators
// -------------------------------------------------------------------------

float tvdb_central_diff_x(const tvdb_dense_grid* g, int ix, int iy, int iz) {
  return (tvdb_at(g, ix + 1, iy, iz) - tvdb_at(g, ix - 1, iy, iz)) / (2.0f * g->voxel_size);
}
float tvdb_central_diff_y(const tvdb_dense_grid* g, int ix, int iy, int iz) {
  return (tvdb_at(g, ix, iy + 1, iz) - tvdb_at(g, ix, iy - 1, iz)) / (2.0f * g->voxel_size);
}
float tvdb_central_diff_z(const tvdb_dense_grid* g, int ix, int iy, int iz) {
  return (tvdb_at(g, ix, iy, iz + 1) - tvdb_at(g, ix, iy, iz - 1)) / (2.0f * g->voxel_size);
}

void tvdb_gradient(const tvdb_dense_grid* scalar, tvdb_dense_vec_grid* grad) {
  if (!scalar->data || !grad->data) return;
  const int nx = scalar->nx, ny = scalar->ny, nz = scalar->nz;
  #pragma omp parallel for collapse(2) schedule(static)
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        size_t i = tvdb_idx(scalar, ix, iy, iz) * 3u;
        grad->data[i + 0] = tvdb_central_diff_x(scalar, ix, iy, iz);
        grad->data[i + 1] = tvdb_central_diff_y(scalar, ix, iy, iz);
        grad->data[i + 2] = tvdb_central_diff_z(scalar, ix, iy, iz);
      }
    }
  }
}

static inline float tvdb_vec_at(const tvdb_dense_vec_grid* v, int ix, int iy, int iz, int c) {
  ix = tvdb_clamp_i(ix, 0, v->nx - 1);
  iy = tvdb_clamp_i(iy, 0, v->ny - 1);
  iz = tvdb_clamp_i(iz, 0, v->nz - 1);
  size_t base = (size_t)((iz * v->ny + iy) * v->nx + ix) * 3u;
  return v->data[base + (size_t)c];
}

void tvdb_divergence(const tvdb_dense_vec_grid* vec, tvdb_dense_grid* div) {
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

void tvdb_laplacian(const tvdb_dense_grid* scalar, tvdb_dense_grid* laplacian) {
  if (!scalar->data || !laplacian->data) return;
  const int nx = scalar->nx, ny = scalar->ny, nz = scalar->nz;
  const float h = scalar->voxel_size;
  const float inv_h2 = 1.0f / (h * h);
  #pragma omp parallel for collapse(2) schedule(static)
  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        float c = scalar->data[tvdb_idx(scalar, ix, iy, iz)];
        float s = tvdb_at(scalar, ix - 1, iy, iz)
                + tvdb_at(scalar, ix + 1, iy, iz)
                + tvdb_at(scalar, ix, iy - 1, iz)
                + tvdb_at(scalar, ix, iy + 1, iz)
                + tvdb_at(scalar, ix, iy, iz - 1)
                + tvdb_at(scalar, ix, iy, iz + 1);
        laplacian->data[tvdb_idx(laplacian, ix, iy, iz)] = (s - 6.0f * c) * inv_h2;
      }
    }
  }
}

void tvdb_curl(const tvdb_dense_vec_grid* vec, tvdb_dense_vec_grid* curl) {
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
        size_t i = (size_t)((iz * ny + iy) * nx + ix) * 3u;
        curl->data[i + 0] = dvz_dy - dvy_dz;
        curl->data[i + 1] = dvx_dz - dvz_dx;
        curl->data[i + 2] = dvy_dx - dvx_dy;
      }
    }
  }
}

// -------------------------------------------------------------------------
// Phase 2: trilinear sampler in voxel space (used by advection)
// -------------------------------------------------------------------------

// Sample a dense scalar grid at (vx, vy, vz) given in voxel-index coordinates
// (origin-relative, in units of voxel cells, NOT world-space).
static float tvdb_sample_dense_voxel(const tvdb_dense_grid* g, float vx, float vy, float vz) {
  int ix = (int)floorf(vx), iy = (int)floorf(vy), iz = (int)floorf(vz);
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

// -------------------------------------------------------------------------
// Phase 2: semi-Lagrangian advection
// -------------------------------------------------------------------------

void tvdb_advect_semi_lagrangian(const tvdb_dense_grid* field,
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
        size_t vi = (size_t)((iz * ny + iy) * nx + ix) * 3u;
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
// Phase 2: Poisson solver via Jacobi-preconditioned Conjugate Gradient
// -------------------------------------------------------------------------

// Solves L x = rhs, where L is the 7-point discrete Laplacian on a uniform
// grid with spacing h, using homogeneous Dirichlet (clamp-to-edge) boundaries.
// The diagonal is -6/h^2; off-diagonals are +1/h^2 each.
//
// Convergence on coarse uniform grids with this stencil is generally good;
// use Jacobi (diagonal) preconditioning for a small constant-factor speedup.

static void tvdb_apply_laplacian(const tvdb_dense_grid* x, tvdb_dense_grid* y) {
  // y = L x (7-point, edge-clamped)
  tvdb_laplacian(x, y);
}

static double tvdb_dot(const float* a, const float* b, size_t n) {
#if defined(TINYVDB_SIMD) && defined(__AVX2__) && !defined(TINYVDB_OPENMP_ENABLED)
  // AVX2 reduction (single-threaded). When OpenMP is enabled we keep the
  // OpenMP-reduction path because mixing nested SIMD with omp reduction
  // produces unstable summation order across threads.
  return tvdb_simd_dot_f32(a, b, n);
#else
  double s = 0.0;
  #pragma omp parallel for reduction(+:s) schedule(static)
  for (long long i = 0; i < (long long)n; ++i) s += (double)a[i] * (double)b[i];
  return s;
#endif
}

// fp64 7-point laplacian: out[i] = (sum_6_neighbors - 6*self) / h^2.
// Reads from `in` (fp64 buffer) of shape (nx, ny, nz); writes to `out`.
// Boundary cells use Dirichlet zero (out-of-bounds neighbors treated as 0).
static void apply_laplacian_d(const double* in, double* out,
                              int nx, int ny, int nz, double h) {
  const double inv_h2 = 1.0 / (h * h);
  #pragma omp parallel for collapse(2) schedule(static)
  for (int z = 0; z < nz; ++z) {
    for (int y = 0; y < ny; ++y) {
      for (int x = 0; x < nx; ++x) {
        size_t i = (size_t)((z * ny + y) * nx + x);
        double c = in[i];
        double xn = (x > 0)      ? in[i - 1]                  : 0.0;
        double xp = (x + 1 < nx) ? in[i + 1]                  : 0.0;
        double yn = (y > 0)      ? in[i - nx]                 : 0.0;
        double yp = (y + 1 < ny) ? in[i + nx]                 : 0.0;
        double zn = (z > 0)      ? in[i - (size_t)nx * ny]    : 0.0;
        double zp = (z + 1 < nz) ? in[i + (size_t)nx * ny]    : 0.0;
        out[i] = (xn + xp + yn + yp + zn + zp - 6.0 * c) * inv_h2;
      }
    }
  }
}

static double tvdb_dot_d(const double* a, const double* b, size_t n) {
  double s = 0.0;
  #pragma omp parallel for reduction(+:s) schedule(static)
  for (long long i = 0; i < (long long)n; ++i) s += a[i] * b[i];
  return s;
}

int tvdb_solve_poisson_d(const tvdb_dense_grid* rhs,
                         tvdb_dense_grid* x,
                         int max_iters,
                         double tolerance) {
  if (!rhs->data || !x->data) return 0;
  if (!tvdb_grid_same_shape(rhs, x)) return 0;
  const size_t n = (size_t)tvdb_grid_voxels(rhs);
  if (n == 0) return 0;

  // Allocate fp64 workspace.
  double* xd = (double*)malloc(n * sizeof(double));
  double* rd = (double*)malloc(n * sizeof(double));
  double* pd = (double*)malloc(n * sizeof(double));
  double* Apd = (double*)malloc(n * sizeof(double));
  double* zd = (double*)malloc(n * sizeof(double));
  double* rhsd = (double*)malloc(n * sizeof(double));
  if (!xd || !rd || !pd || !Apd || !zd || !rhsd) {
    free(xd); free(rd); free(pd); free(Apd); free(zd); free(rhsd);
    return 0;
  }
  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)n; ++i) xd[i]   = (double)x->data[i];
  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)n; ++i) rhsd[i] = (double)rhs->data[i];

  const int nx = rhs->nx, ny = rhs->ny, nz = rhs->nz;
  const double h = (double)rhs->voxel_size;
  const double Minv = -(h * h) / 6.0;

  // r = rhs - L x
  apply_laplacian_d(xd, Apd, nx, ny, nz, h);
  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)n; ++i) rd[i] = rhsd[i] - Apd[i];
  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)n; ++i) zd[i] = Minv * rd[i];
  memcpy(pd, zd, n * sizeof(double));

  double rz = tvdb_dot_d(rd, zd, n);
  double r0 = sqrt(tvdb_dot_d(rd, rd, n));
  if (r0 == 0.0) {
    for (size_t i = 0; i < n; ++i) x->data[i] = (float)xd[i];
    free(xd); free(rd); free(pd); free(Apd); free(zd); free(rhsd);
    return 0;
  }
  const double tol2 = tolerance * tolerance * r0 * r0;

  int it = 0;
  for (it = 0; it < max_iters; ++it) {
    apply_laplacian_d(pd, Apd, nx, ny, nz, h);
    double pAp = tvdb_dot_d(pd, Apd, n);
    if (pAp == 0.0) break;
    double alpha = rz / pAp;
    #pragma omp parallel for schedule(static)
    for (long long i = 0; i < (long long)n; ++i) xd[i] += alpha * pd[i];
    #pragma omp parallel for schedule(static)
    for (long long i = 0; i < (long long)n; ++i) rd[i] -= alpha * Apd[i];

    double rr = tvdb_dot_d(rd, rd, n);
    if (rr < tol2) { ++it; break; }

    #pragma omp parallel for schedule(static)
    for (long long i = 0; i < (long long)n; ++i) zd[i] = Minv * rd[i];
    double rz_new = tvdb_dot_d(rd, zd, n);
    double beta = rz_new / rz;
    #pragma omp parallel for schedule(static)
    for (long long i = 0; i < (long long)n; ++i) pd[i] = zd[i] + beta * pd[i];
    rz = rz_new;
  }

  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)n; ++i) x->data[i] = (float)xd[i];
  free(xd); free(rd); free(pd); free(Apd); free(zd); free(rhsd);
  return it;
}

int tvdb_solve_poisson(const tvdb_dense_grid* rhs,
                       tvdb_dense_grid* x,
                       int max_iters,
                       float tolerance) {
  if (!rhs->data || !x->data) return 0;
  if (!tvdb_grid_same_shape(rhs, x)) return 0;

  const size_t n = (size_t)tvdb_grid_voxels(rhs);
  if (n == 0) return 0;

  // workspace
  float* r = (float*)malloc(n * sizeof(float));
  float* p = (float*)malloc(n * sizeof(float));
  float* Ap = (float*)malloc(n * sizeof(float));
  float* z = (float*)malloc(n * sizeof(float));
  if (!r || !p || !Ap || !z) {
    free(r); free(p); free(Ap); free(z);
    return 0;
  }

  tvdb_dense_grid xg = *x;
  tvdb_dense_grid Apg = *x; Apg.data = Ap;
  tvdb_dense_grid pg  = *x; pg.data  = p;

  // r = rhs - L x
  tvdb_apply_laplacian(&xg, &Apg);
  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)n; ++i) r[i] = rhs->data[i] - Ap[i];

  // M^-1 = 1 / diag(L) = -h^2 / 6
  const float h = rhs->voxel_size;
  const float Minv = -(h * h) / 6.0f;

  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)n; ++i) z[i] = Minv * r[i];
  memcpy(p, z, n * sizeof(float));

  double rz = tvdb_dot(r, z, n);
  double r0 = sqrt(tvdb_dot(r, r, n));
  if (r0 == 0.0) {
    free(r); free(p); free(Ap); free(z);
    return 0;
  }
  const double tol2 = (double)tolerance * (double)tolerance * r0 * r0;

  int it = 0;
  for (it = 0; it < max_iters; ++it) {
    tvdb_apply_laplacian(&pg, &Apg);  // Ap = L p
    double pAp = tvdb_dot(p, Ap, n);
    if (pAp == 0.0) break;
    double alpha = rz / pAp;
    #pragma omp parallel for schedule(static)
    for (long long i = 0; i < (long long)n; ++i) x->data[i] += (float)alpha * p[i];
    #pragma omp parallel for schedule(static)
    for (long long i = 0; i < (long long)n; ++i) r[i]      -= (float)alpha * Ap[i];

    double rr = tvdb_dot(r, r, n);
    if (rr < tol2) { ++it; break; }

    #pragma omp parallel for schedule(static)
    for (long long i = 0; i < (long long)n; ++i) z[i] = Minv * r[i];
    double rz_new = tvdb_dot(r, z, n);
    double beta = rz_new / rz;
    #pragma omp parallel for schedule(static)
    for (long long i = 0; i < (long long)n; ++i) p[i] = z[i] + (float)beta * p[i];
    rz = rz_new;
  }

  free(r); free(p); free(Ap); free(z);
  return it;
}
