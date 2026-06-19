// Analytic level-set primitive generators + SDF utilities. See
// tinyvdb_levelset.h. Pure-C, dependency-free, CPU. The dense data layout is
// x-fastest: idx(i,j,k) = (k*ny + j)*nx + i, matching the rest of tinyvdb.

#include "tinyvdb_levelset.h"

#include <math.h>
#include <stdlib.h>

static inline float lvl_clampf(float v, float lo, float hi) {
  return v < lo ? lo : (v > hi ? hi : v);
}

static inline float lvl_minf(float a, float b) { return a < b ? a : b; }
static inline float lvl_maxf(float a, float b) { return a > b ? a : b; }

// Resolve a half_width argument (<=0 means default), returning the background
// distance bg = half_width * voxel_size and writing the effective half_width.
static inline float lvl_background(float half_width, float voxel_size,
                                   float* eff_half_width) {
  float hw = (half_width > 0.0f) ? half_width : TVDB_LEVEL_SET_HALF_WIDTH;
  if (eff_half_width) *eff_half_width = hw;
  return hw * voxel_size;
}

// Allocate `out` covering world AABB [lo, hi] with isotropic voxel_size, placing
// the origin so voxel-0 center == lo (cell-center convention) and voxel (n-1)
// center >= hi. Returns false on bad args / OOM.
static bool lvl_make_grid(const float lo[3], const float hi[3], float vs,
                          tvdb_dense_grid* out) {
  if (!out || vs <= 0.0f) return false;
  int n[3];
  for (int a = 0; a < 3; ++a) {
    float span = hi[a] - lo[a];
    if (span < 0.0f) return false;
    n[a] = (int)ceilf(span / vs) + 1;  // (n-1)*vs >= span
    if (n[a] < 1) n[a] = 1;
  }
  tvdb_dense_grid_init(out, n[0], n[1], n[2]);  // mallocs + zeroes data
  if (!out->data) return false;
  out->voxel_size = vs;
  out->ox = lo[0] - 0.5f * vs;
  out->oy = lo[1] - 0.5f * vs;
  out->oz = lo[2] - 0.5f * vs;
  return true;
}

// Fill every voxel with sdf(world_center), clamped to [-bg, bg].
typedef float (*lvl_sdf_fn)(float wx, float wy, float wz, const void* params);

static void lvl_fill(tvdb_dense_grid* g, float bg, lvl_sdf_fn fn,
                     const void* params) {
  const float vs = g->voxel_size;
  for (int k = 0; k < g->nz; ++k) {
    float wz = g->oz + ((float)k + 0.5f) * vs;
    for (int j = 0; j < g->ny; ++j) {
      float wy = g->oy + ((float)j + 0.5f) * vs;
      size_t row = (size_t)(k * g->ny + j) * g->nx;
      for (int i = 0; i < g->nx; ++i) {
        float wx = g->ox + ((float)i + 0.5f) * vs;
        float d = fn(wx, wy, wz, params);
        g->data[row + i] = lvl_clampf(d, -bg, bg);
      }
    }
  }
}

// ---- Sphere ----------------------------------------------------------------

typedef struct { float c[3], r; } lvl_sphere_t;

static float lvl_sphere_sdf(float wx, float wy, float wz, const void* p) {
  const lvl_sphere_t* s = (const lvl_sphere_t*)p;
  float dx = wx - s->c[0], dy = wy - s->c[1], dz = wz - s->c[2];
  return sqrtf(dx * dx + dy * dy + dz * dz) - s->r;
}

bool tvdb_level_set_sphere(float radius, const float center[3],
                           float voxel_size, float half_width,
                           tvdb_dense_grid* out) {
  if (!center || radius <= 0.0f || voxel_size <= 0.0f) return false;
  float bg = lvl_background(half_width, voxel_size, NULL);
  float ext = radius + bg;
  float lo[3], hi[3];
  for (int a = 0; a < 3; ++a) { lo[a] = center[a] - ext; hi[a] = center[a] + ext; }
  if (!lvl_make_grid(lo, hi, voxel_size, out)) return false;
  lvl_sphere_t s = { { center[0], center[1], center[2] }, radius };
  lvl_fill(out, bg, lvl_sphere_sdf, &s);
  return true;
}

// ---- Box -------------------------------------------------------------------

typedef struct { float c[3], he[3]; } lvl_box_t;

static float lvl_box_sdf(float wx, float wy, float wz, const void* p) {
  const lvl_box_t* b = (const lvl_box_t*)p;
  float qx = fabsf(wx - b->c[0]) - b->he[0];
  float qy = fabsf(wy - b->c[1]) - b->he[1];
  float qz = fabsf(wz - b->c[2]) - b->he[2];
  float ox = lvl_maxf(qx, 0.0f), oy = lvl_maxf(qy, 0.0f), oz = lvl_maxf(qz, 0.0f);
  float outside = sqrtf(ox * ox + oy * oy + oz * oz);
  float inside = lvl_minf(lvl_maxf(qx, lvl_maxf(qy, qz)), 0.0f);
  return outside + inside;
}

bool tvdb_level_set_box(const float half_extents[3], const float center[3],
                        float voxel_size, float half_width,
                        tvdb_dense_grid* out) {
  if (!half_extents || !center || voxel_size <= 0.0f) return false;
  if (half_extents[0] <= 0.0f || half_extents[1] <= 0.0f || half_extents[2] <= 0.0f)
    return false;
  float bg = lvl_background(half_width, voxel_size, NULL);
  float lo[3], hi[3];
  for (int a = 0; a < 3; ++a) {
    lo[a] = center[a] - half_extents[a] - bg;
    hi[a] = center[a] + half_extents[a] + bg;
  }
  if (!lvl_make_grid(lo, hi, voxel_size, out)) return false;
  lvl_box_t b = { { center[0], center[1], center[2] },
                  { half_extents[0], half_extents[1], half_extents[2] } };
  lvl_fill(out, bg, lvl_box_sdf, &b);
  return true;
}

// ---- Torus (XZ plane, axis Y) ----------------------------------------------

typedef struct { float c[3], R, r; } lvl_torus_t;

static float lvl_torus_sdf(float wx, float wy, float wz, const void* p) {
  const lvl_torus_t* t = (const lvl_torus_t*)p;
  float dx = wx - t->c[0], dy = wy - t->c[1], dz = wz - t->c[2];
  float qx = sqrtf(dx * dx + dz * dz) - t->R;  // distance in XZ from ring
  return sqrtf(qx * qx + dy * dy) - t->r;
}

bool tvdb_level_set_torus(float major_radius, float minor_radius,
                          const float center[3], float voxel_size,
                          float half_width, tvdb_dense_grid* out) {
  if (!center || major_radius <= 0.0f || minor_radius <= 0.0f ||
      voxel_size <= 0.0f)
    return false;
  float bg = lvl_background(half_width, voxel_size, NULL);
  float ext_xz = major_radius + minor_radius + bg;
  float ext_y = minor_radius + bg;
  float lo[3] = { center[0] - ext_xz, center[1] - ext_y, center[2] - ext_xz };
  float hi[3] = { center[0] + ext_xz, center[1] + ext_y, center[2] + ext_xz };
  if (!lvl_make_grid(lo, hi, voxel_size, out)) return false;
  lvl_torus_t t = { { center[0], center[1], center[2] }, major_radius, minor_radius };
  lvl_fill(out, bg, lvl_torus_sdf, &t);
  return true;
}

// ---- Capsule (segment p0->p1, radius) --------------------------------------

typedef struct { float a[3], ba[3], baba, r; } lvl_capsule_t;

static float lvl_capsule_sdf(float wx, float wy, float wz, const void* p) {
  const lvl_capsule_t* c = (const lvl_capsule_t*)p;
  float pax = wx - c->a[0], pay = wy - c->a[1], paz = wz - c->a[2];
  float h = 0.0f;
  if (c->baba > 0.0f) {
    h = (pax * c->ba[0] + pay * c->ba[1] + paz * c->ba[2]) / c->baba;
    h = lvl_clampf(h, 0.0f, 1.0f);
  }
  float dx = pax - c->ba[0] * h;
  float dy = pay - c->ba[1] * h;
  float dz = paz - c->ba[2] * h;
  return sqrtf(dx * dx + dy * dy + dz * dz) - c->r;
}

bool tvdb_level_set_capsule(const float p0[3], const float p1[3], float radius,
                            float voxel_size, float half_width,
                            tvdb_dense_grid* out) {
  if (!p0 || !p1 || radius <= 0.0f || voxel_size <= 0.0f) return false;
  float bg = lvl_background(half_width, voxel_size, NULL);
  float ext = radius + bg;
  float lo[3], hi[3];
  for (int a = 0; a < 3; ++a) {
    lo[a] = lvl_minf(p0[a], p1[a]) - ext;
    hi[a] = lvl_maxf(p0[a], p1[a]) + ext;
  }
  if (!lvl_make_grid(lo, hi, voxel_size, out)) return false;
  lvl_capsule_t c;
  for (int a = 0; a < 3; ++a) { c.a[a] = p0[a]; c.ba[a] = p1[a] - p0[a]; }
  c.baba = c.ba[0] * c.ba[0] + c.ba[1] * c.ba[1] + c.ba[2] * c.ba[2];
  c.r = radius;
  lvl_fill(out, bg, lvl_capsule_sdf, &c);
  return true;
}

// ---- SDF utilities ---------------------------------------------------------

static bool lvl_clone_shape(const tvdb_dense_grid* in, tvdb_dense_grid* out) {
  if (!in || !out || !in->data) return false;
  tvdb_dense_grid_init(out, in->nx, in->ny, in->nz);
  if (!out->data && (size_t)in->nx * in->ny * in->nz > 0) return false;
  out->voxel_size = in->voxel_size;
  out->ox = in->ox; out->oy = in->oy; out->oz = in->oz;
  return true;
}

bool tvdb_sdf_to_fog_volume(const tvdb_dense_grid* sdf, float half_width,
                            tvdb_dense_grid* out) {
  if (!lvl_clone_shape(sdf, out)) return false;
  float gamma = lvl_background(half_width, sdf->voxel_size, NULL);
  if (gamma <= 0.0f) gamma = sdf->voxel_size;
  size_t n = (size_t)sdf->nx * sdf->ny * sdf->nz;
  for (size_t i = 0; i < n; ++i)
    out->data[i] = lvl_clampf(-sdf->data[i] / gamma, 0.0f, 1.0f);
  return true;
}

bool tvdb_sdf_interior_mask(const tvdb_dense_grid* sdf, float isovalue,
                            tvdb_dense_grid* out) {
  if (!lvl_clone_shape(sdf, out)) return false;
  size_t n = (size_t)sdf->nx * sdf->ny * sdf->nz;
  for (size_t i = 0; i < n; ++i)
    out->data[i] = (sdf->data[i] < isovalue) ? 1.0f : 0.0f;
  return true;
}
