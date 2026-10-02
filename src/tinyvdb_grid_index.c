// Coordinate utilities and point/coordinate spatial queries. See
// tinyvdb_grid_index.h.

#include "tinyvdb_grid_index.h"
#include "tinyvdb_checked.h"

#include <math.h>
#include <stdlib.h>

/* Every loop below is a per-point gather against a hash that is built once and
 * then only read: each iteration writes exactly one output element that no other
 * iteration touches, so a parallel for needs no synchronization. These were all
 * serial; the hash build is the only serial part and it is O(active).
 * The induction variables are long long because OpenMP before 5.0 does not
 * admit an unsigned induction variable in a canonical loop, and MSVC rejects it. */

#define GI_BIAS (1 << 20)          // 2^20; coords in [-2^20, 2^20-1]
#define GI_MASK21 ((1u << 21) - 1)

static bool gi_world_component(float point, float size, float origin, int32_t *out) {
  if (!isfinite(point) || !isfinite(size) || size <= 0.0f || !isfinite(origin)) return false;
  float value = floorf((point - origin) / size);
  if (!isfinite(value) || (double)value < INT32_MIN || (double)value > INT32_MAX) return false;
  *out = (int32_t)value;
  return true;
}

static bool gi_world_valid(const float *points, size_t n, const float *size, const float *origin) {
  if (!size || !origin || (n && !points) || n > SIZE_MAX / (3 * sizeof(int32_t))) return false;
  for (int a = 0; a < 3; ++a)
    if (!isfinite(size[a]) || size[a] <= 0.0f || !isfinite(origin[a])) return false;
  int32_t component;
  for (size_t i = 0; i < n; ++i)
    for (int a = 0; a < 3; ++a)
      if (!gi_world_component(points[3*i+a], size[a], origin[a], &component)) return false;
  return true;
}

// ---- coordinate <-> world ---------------------------------------------------

void tvdb_world_to_ijk(const float* points, size_t n,
                       const float voxel_size[3], const float origin[3],
                       int32_t* out_ijk) {
  if (!out_ijk || !voxel_size || !origin || (n && !points) || n > SIZE_MAX / (3 * sizeof(int32_t))) return;
  #pragma omp parallel for schedule(static)
  for (long long ii = 0; ii < (long long)n; ++ii) {
    size_t i = (size_t)ii;
    for (int a = 0; a < 3; ++a)
      if (!gi_world_component(points[3*i+a], voxel_size[a], origin[a], &out_ijk[3*i+a]))
        out_ijk[3*i+a] = 0;
  }
}

void tvdb_ijk_to_world(const int32_t* ijk, size_t n,
                       const float voxel_size[3], const float origin[3],
                       float* out_points) {
  /* This had no argument checks at all, so every one of the five pointers was
     dereferenced unconditionally and a huge n walked off both buffers.
     tvdb_world_to_ijk above already guards the same shape of call. */
  if (!out_points || !voxel_size || !origin || (n && !ijk)) return;
  if (n > SIZE_MAX / (3 * sizeof(float))) return;
  #pragma omp parallel for schedule(static)
  for (long long ii = 0; ii < (long long)n; ++ii) {
    size_t i = (size_t)ii;
    for (int a = 0; a < 3; ++a)
      out_points[3*i+a] = origin[a] + ((float)ijk[3*i+a] + 0.5f) * voxel_size[a];
  }
}

// ---- Morton (Z-order) -------------------------------------------------------

static uint64_t gi_split3(uint64_t a) {            // spread 21 low bits to every 3rd
  a &= 0x1fffffULL;
  a = (a | a << 32) & 0x1f00000000ffffULL;
  a = (a | a << 16) & 0x1f0000ff0000ffULL;
  a = (a | a << 8)  & 0x100f00f00f00f00fULL;
  a = (a | a << 4)  & 0x10c30c30c30c30c3ULL;
  a = (a | a << 2)  & 0x1249249249249249ULL;
  return a;
}
static uint64_t gi_compact3(uint64_t a) {          // inverse of gi_split3
  a &= 0x1249249249249249ULL;
  a = (a | a >> 2)  & 0x10c30c30c30c30c3ULL;
  a = (a | a >> 4)  & 0x100f00f00f00f00fULL;
  a = (a | a >> 8)  & 0x1f0000ff0000ffULL;
  a = (a | a >> 16) & 0x1f00000000ffffULL;
  a = (a | a >> 32) & 0x1fffffULL;
  return a;
}

uint64_t tvdb_morton_encode(int32_t x, int32_t y, int32_t z) {
  uint64_t bx = (uint64_t)((int64_t)x + GI_BIAS) & GI_MASK21;
  uint64_t by = (uint64_t)((int64_t)y + GI_BIAS) & GI_MASK21;
  uint64_t bz = (uint64_t)((int64_t)z + GI_BIAS) & GI_MASK21;
  return gi_split3(bx) | (gi_split3(by) << 1) | (gi_split3(bz) << 2);
}

void tvdb_morton_decode(uint64_t code, int32_t* x, int32_t* y, int32_t* z) {
  *x = (int32_t)((int64_t)gi_compact3(code)       - GI_BIAS);
  *y = (int32_t)((int64_t)gi_compact3(code >> 1)  - GI_BIAS);
  *z = (int32_t)((int64_t)gi_compact3(code >> 2)  - GI_BIAS);
}

// ---- int3 -> index hash set -------------------------------------------------

static uint64_t gi_pack(int32_t x, int32_t y, int32_t z) {
  uint64_t ux = (uint64_t)((int64_t)x + GI_BIAS) & GI_MASK21;
  uint64_t uy = (uint64_t)((int64_t)y + GI_BIAS) & GI_MASK21;
  uint64_t uz = (uint64_t)((int64_t)z + GI_BIAS) & GI_MASK21;
  return (ux << 42) | (uy << 21) | uz;             // 63-bit key
}
static uint64_t gi_mix(uint64_t x) {
  x ^= x >> 33; x *= 0xff51afd7ed558ccdULL;
  x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL;
  x ^= x >> 33; return x;
}

typedef struct { uint64_t key; int64_t idx; } gi_entry;  // key stored as packed+1 (0 = empty)
typedef struct { gi_entry* e; size_t mask; const int32_t *coords; } gi_hash;

static bool gi_coord_equal(const gi_hash *h, size_t slot, int32_t x, int32_t y, int32_t z) {
  const int32_t *p = h->coords + 3 * (size_t)h->e[slot].idx;
  return p[0] == x && p[1] == y && p[2] == z;
}

static bool gi_hash_build(gi_hash* h, const int32_t* coords, size_t n) {
  size_t cap;
  if ((n && !coords) || n > INT64_MAX || n > SIZE_MAX / (3 * sizeof(int32_t)) ||
      !tvdb_hash_capacity(n, 2, &cap)) return false;
  h->coords = coords;
  h->e = (gi_entry*)calloc(cap, sizeof(gi_entry));
  h->mask = cap - 1;
  if (!h->e) return false;
  for (size_t i = 0; i < n; ++i) {
    uint64_t key = gi_pack(coords[3*i], coords[3*i+1], coords[3*i+2]) + 1;
    size_t s = (size_t)gi_mix(key) & h->mask;
    while (h->e[s].key) {
      if (h->e[s].key == key && gi_coord_equal(h, s, coords[3*i], coords[3*i+1], coords[3*i+2])) break; // Keep the first exact coordinate match.
      s = (s + 1) & h->mask;
    }
    if (!h->e[s].key) { h->e[s].key = key; h->e[s].idx = (int64_t)i; }
  }
  return true;
}
static int64_t gi_hash_get(const gi_hash* h, int32_t x, int32_t y, int32_t z) {
  uint64_t key = gi_pack(x, y, z) + 1;
  size_t s = (size_t)gi_mix(key) & h->mask;
  while (h->e[s].key) {
    if (h->e[s].key == key && gi_coord_equal(h, s, x, y, z)) return h->e[s].idx;
    s = (s + 1) & h->mask;
  }
  return -1;
}
static void gi_hash_free(gi_hash* h) { free(h->e); h->e = NULL; }

// ---- queries ----------------------------------------------------------------

bool tvdb_coords_in_set(const int32_t* active, size_t na,
                        const int32_t* query, size_t nq, uint8_t* out) {
  if ((nq && (!query || !out)) || nq > SIZE_MAX / (3 * sizeof(int32_t))) return false;
  gi_hash h;
  if (!gi_hash_build(&h, active, na)) return false;
  #pragma omp parallel for schedule(static)
  for (long long ii = 0; ii < (long long)nq; ++ii) {
    size_t i = (size_t)ii;
    out[i] = gi_hash_get(&h, query[3*i], query[3*i+1], query[3*i+2]) >= 0 ? 1 : 0;
  }
  gi_hash_free(&h);
  return true;
}

bool tvdb_points_in_set(const float* points, size_t np,
                        const float voxel_size[3], const float origin[3],
                        const int32_t* active, size_t na, uint8_t* out) {
  if ((np && !out) || !gi_world_valid(points, np, voxel_size, origin)) return false;
  gi_hash h;
  if (!gi_hash_build(&h, active, na)) return false;
  #pragma omp parallel for schedule(static)
  for (long long ii = 0; ii < (long long)np; ++ii) {
    size_t i = (size_t)ii;
    int32_t ijk[3];
    for (int a = 0; a < 3; ++a)
      gi_world_component(points[3*i+a], voxel_size[a], origin[a], &ijk[a]);
    out[i] = gi_hash_get(&h, ijk[0], ijk[1], ijk[2]) >= 0 ? 1 : 0;
  }
  gi_hash_free(&h);
  return true;
}

bool tvdb_ijk_to_index(const int32_t* active, size_t na,
                       const int32_t* query, size_t nq, int64_t* out) {
  if ((nq && (!query || !out)) || nq > SIZE_MAX / (3 * sizeof(int32_t))) return false;
  gi_hash h;
  if (!gi_hash_build(&h, active, na)) return false;
  #pragma omp parallel for schedule(static)
  for (long long ii = 0; ii < (long long)nq; ++ii) {
    size_t i = (size_t)ii;
    out[i] = gi_hash_get(&h, query[3*i], query[3*i+1], query[3*i+2]);
  }
  gi_hash_free(&h);
  return true;
}

bool tvdb_neighbor_counts(const int32_t* active, size_t na,
                          int connectivity, int32_t* out_counts) {
  if ((na && !out_counts) || (connectivity != 6 && connectivity != 26)) return false;
  gi_hash h;
  if (!gi_hash_build(&h, active, na)) return false;
  int off[26][3]; int noff;
  if (connectivity == 26) {
    noff = 0;
    for (int dz = -1; dz <= 1; ++dz) for (int dy = -1; dy <= 1; ++dy) for (int dx = -1; dx <= 1; ++dx) {
      if (dx == 0 && dy == 0 && dz == 0) continue;
      off[noff][0] = dx; off[noff][1] = dy; off[noff][2] = dz; ++noff;
    }
  } else {
    static const int o6[6][3] = { {1,0,0},{-1,0,0},{0,1,0},{0,-1,0},{0,0,1},{0,0,-1} };
    for (int t = 0; t < 6; ++t) { off[t][0]=o6[t][0]; off[t][1]=o6[t][1]; off[t][2]=o6[t][2]; }
    noff = 6;
  }
  #pragma omp parallel for schedule(static)
  for (long long ii = 0; ii < (long long)na; ++ii) {
    size_t i = (size_t)ii;
    int32_t x = active[3*i], y = active[3*i+1], z = active[3*i+2];
    int32_t c = 0;
    for (int t = 0; t < noff; ++t) {
      int nx, ny, nz;
      if (tvdb_coord_offset(x, y, z, off[t][0], off[t][1], off[t][2], &nx, &ny, &nz) &&
          gi_hash_get(&h, nx, ny, nz) >= 0) ++c;
    }
    out_counts[i] = c;
  }
  gi_hash_free(&h);
  return true;
}

bool tvdb_voxelize_points(const float* points, size_t n,
                          const float voxel_size[3], const float origin[3],
                          int32_t** out_coords, size_t* out_count) {
  if (!out_coords || !out_count) return false;
  *out_coords = NULL; *out_count = 0;
  if (!gi_world_valid(points, n, voxel_size, origin)) return false;
  if (n == 0) return true;
  gi_hash h;
  size_t cap, bytes;
  if (n > INT64_MAX || !tvdb_hash_capacity(n, 2, &cap) ||
      !tvdb_size_mul(n, 3 * sizeof(int32_t), &bytes)) return false;
  h.e = (gi_entry*)calloc(cap, sizeof(gi_entry)); h.mask = cap - 1;
  if (!h.e) return false;
  int32_t* coords = (int32_t*)malloc(bytes);
  if (!coords) { free(h.e); return false; }
  h.coords = coords;
  size_t cnt = 0;
  for (size_t i = 0; i < n; ++i) {
    int32_t ijk[3];
    for (int a = 0; a < 3; ++a)
      gi_world_component(points[3*i+a], voxel_size[a], origin[a], &ijk[a]);
    uint64_t key = gi_pack(ijk[0], ijk[1], ijk[2]) + 1;
    size_t s = (size_t)gi_mix(key) & h.mask;
    int found = 0;
    while (h.e[s].key) {
      if (h.e[s].key == key && gi_coord_equal(&h, s, ijk[0], ijk[1], ijk[2])) { found = 1; break; }
      s = (s + 1) & h.mask;
    }
    if (!found) {
      h.e[s].key = key; h.e[s].idx = (int64_t)cnt;
      coords[3*cnt+0] = ijk[0]; coords[3*cnt+1] = ijk[1]; coords[3*cnt+2] = ijk[2];
      ++cnt;
    }
  }
  free(h.e);
  *out_coords = coords;
  *out_count = cnt;
  return true;
}
