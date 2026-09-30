#pragma once

// Internal helpers shared by tinyvdb_ops.c. Not part of the public API.

#include <stddef.h>
#include "tinyvdb_checked.h"
#include "tinyvdb_mesh.h"  // tvdb_dense_grid

#ifdef __cplusplus
extern "C" {
#endif

static inline int tvdb_clamp_i(int v, int lo, int hi) {
  return v < lo ? lo : (v > hi ? hi : v);
}

static inline size_t tvdb_idx(const tvdb_dense_grid* g, int ix, int iy, int iz) {
  // size_t arithmetic throughout so the index doesn't overflow int for grids
  // with > INT_MAX voxels.
  return ((size_t)iz * g->ny + iy) * g->nx + ix;
}

// Read with edge clamp.
static inline float tvdb_at(const tvdb_dense_grid* g, int64_t ix, int64_t iy, int64_t iz) {
  ix = ix < 0 ? 0 : (ix >= g->nx ? g->nx - 1 : ix);
  iy = iy < 0 ? 0 : (iy >= g->ny ? g->ny - 1 : iy);
  iz = iz < 0 ? 0 : (iz >= g->nz ? g->nz - 1 : iz);
  return g->data[tvdb_idx(g, ix, iy, iz)];
}

// fp64 variants. Declared after `tvdb_dense_grid_d` so we include ops.h.
#include "tinyvdb_ops.h"
static inline size_t tvdb_idx_d(const tvdb_dense_grid_d* g, int ix, int iy, int iz) {
  return ((size_t)iz * g->ny + iy) * g->nx + ix;
}
static inline double tvdb_at_d(const tvdb_dense_grid_d* g, int64_t ix, int64_t iy, int64_t iz) {
  ix = ix < 0 ? 0 : (ix >= g->nx ? g->nx - 1 : ix);
  iy = iy < 0 ? 0 : (iy >= g->ny ? g->ny - 1 : iy);
  iz = iz < 0 ? 0 : (iz >= g->nz ? g->nz - 1 : iz);
  return g->data[tvdb_idx_d(g, ix, iy, iz)];
}

#ifdef __cplusplus
}
#endif
