// Grid statistics and diagnostics. See tinyvdb_stats.h. Dense data is x-fastest:
// idx(i,j,k) = (k*ny + j)*nx + i.

#include "tinyvdb_stats.h"
#include "tinyvdb_checked.h"

#include <math.h>

/* Voxel count of a grid with valid positive dimensions whose float storage
   size is representable; false otherwise (negative/zero dims or overflow). */
static bool stats_voxel_count(const tvdb_dense_grid* grid, size_t* n) {
  size_t bytes;
  if (!grid || !grid->data ||
      !tvdb_grid_bytes(grid->nx, grid->ny, grid->nz, sizeof(float), &bytes)) return false;
  *n = bytes / sizeof(float);
  return true;
}

bool tvdb_grid_statistics(const tvdb_dense_grid* grid, tvdb_grid_stats_t* out) {
  if (!out) return false;
  out->min = out->max = out->mean = out->stddev = out->sum = 0.0;
  out->count = 0;
  size_t n;
  if (!stats_voxel_count(grid, &n)) return false;

  double mn = grid->data[0], mx = grid->data[0], sum = 0.0;
  for (size_t i = 0; i < n; ++i) {
    double v = grid->data[i];
    if (v < mn) mn = v;
    if (v > mx) mx = v;
    sum += v;
  }
  double mean = sum / (double)n;
  // Second pass for a numerically stable variance.
  double var = 0.0;
  for (size_t i = 0; i < n; ++i) {
    double d = (double)grid->data[i] - mean;
    var += d * d;
  }
  var /= (double)n;
  out->min = mn; out->max = mx; out->mean = mean;
  out->stddev = sqrt(var); out->sum = sum; out->count = n;
  return true;
}

bool tvdb_grid_histogram(const tvdb_dense_grid* grid, double range_min,
                         double range_max, int nbins, size_t* out_counts) {
  size_t n;
  if (!out_counts || nbins < 1 || !isfinite(range_min) || !isfinite(range_max) ||
      !(range_max > range_min) || !stats_voxel_count(grid, &n))
    return false;
  for (int b = 0; b < nbins; ++b) out_counts[b] = 0;
  /* Halved operands keep the span finite for ranges near +-DBL_MAX. */
  const double lo = 0.5 * range_min, span = 0.5 * range_max - lo;
  for (size_t i = 0; i < n; ++i) {
    double v = grid->data[i];
    if (isnan(v)) continue;  /* NaN belongs to no bin */
    /* Clamp in double before converting so out-of-range and infinite values
       land in the first/last bin without an out-of-range float->int cast. */
    double x = (0.5 * v - lo) / span * (double)nbins;
    int b;
    if (!(x > 0.0)) b = 0;
    else if (x >= (double)nbins) b = nbins - 1;
    else b = (int)x;
    ++out_counts[b];
  }
  return true;
}

bool tvdb_check_level_set(const tvdb_dense_grid* grid, double band_world,
                          double tol, tvdb_level_set_check_t* out) {
  if (!out) return false;
  out->mean_grad_mag = 0.0; out->max_grad_error = 0.0;
  out->bad_fraction = 0.0; out->band_count = 0;
  if (!grid || !tvdb_grid_valid(grid->nx, grid->ny, grid->nz, grid->voxel_size,
                                grid->data, sizeof(float))) return false;
  int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  if (nx < 3 || ny < 3 || nz < 3) return false;
  double inv2vs = 1.0 / (2.0 * (double)grid->voxel_size);

  size_t band = 0, bad = 0;
  double sum_mag = 0.0, max_err = 0.0;
  for (int k = 1; k < nz - 1; ++k)
    for (int j = 1; j < ny - 1; ++j)
      for (int i = 1; i < nx - 1; ++i) {
        size_t c = ((size_t)k * ny + j) * nx + i;
        if (band_world > 0.0 && fabs((double)grid->data[c]) > band_world) continue;
        double gx = ((double)grid->data[c + 1] - grid->data[c - 1]) * inv2vs;
        double gy = ((double)grid->data[c + nx] - grid->data[c - nx]) * inv2vs;
        size_t sl = (size_t)nx * ny;
        double gz = ((double)grid->data[c + sl] - grid->data[c - sl]) * inv2vs;
        double mag = sqrt(gx * gx + gy * gy + gz * gz);
        double err = fabs(mag - 1.0);
        sum_mag += mag;
        if (err > max_err) max_err = err;
        if (err > tol) ++bad;
        ++band;
      }
  out->band_count = band;
  if (band > 0) {
    out->mean_grad_mag = sum_mag / (double)band;
    out->bad_fraction = (double)bad / (double)band;
    out->max_grad_error = max_err;
  }
  return true;
}

bool tvdb_check_fog_volume(const tvdb_dense_grid* grid, double eps,
                           int* out_valid, double* out_min, double* out_max) {
  size_t n;
  if (!stats_voxel_count(grid, &n)) return false;
  /* NaN is excluded from the reported range; any non-finite voxel makes the
     grid invalid. min/max are NaN only if every voxel is NaN. */
  double mn = INFINITY, mx = -INFINITY;
  bool finite = true, any = false;
  for (size_t i = 0; i < n; ++i) {
    double v = grid->data[i];
    if (!isfinite(v)) finite = false;
    if (isnan(v)) continue;
    any = true;
    if (v < mn) mn = v;
    if (v > mx) mx = v;
  }
  if (!any) mn = mx = NAN;
  if (out_min) *out_min = mn;
  if (out_max) *out_max = mx;
  if (out_valid) *out_valid = (finite && mn >= -eps && mx <= 1.0 + eps) ? 1 : 0;
  return true;
}
