#include "tinyvdb_ray.h"
#include "tinyvdb_sample.h"

#include <math.h>
#include <stddef.h>

// Ray-AABB slab test in voxel-index coordinates. Returns whether the ray
// intersects the AABB [0,nx)x[0,ny)x[0,nz), and if so writes the entry/exit
// t values clamped to [tmin, tmax].
static bool tvdb_ray_voxel_aabb(const tvdb_ray* ray, const tvdb_dense_grid* g,
                                float* t_enter, float* t_exit,
                                float vox_origin[3], float vox_dir[3]) {
  // Convert ray origin and dir to voxel-index space.
  float vs = g->voxel_size;
  float inv_vs = 1.0f / vs;
  float ox = (ray->origin.x - g->ox) * inv_vs;
  float oy = (ray->origin.y - g->oy) * inv_vs;
  float oz = (ray->origin.z - g->oz) * inv_vs;
  float dx = ray->dir.x * inv_vs;
  float dy = ray->dir.y * inv_vs;
  float dz = ray->dir.z * inv_vs;
  if (vox_origin) { vox_origin[0] = ox; vox_origin[1] = oy; vox_origin[2] = oz; }
  if (vox_dir) { vox_dir[0] = dx; vox_dir[1] = dy; vox_dir[2] = dz; }

  float t0 = ray->tmin, t1 = ray->tmax;
  for (int axis = 0; axis < 3; ++axis) {
    float o = (axis == 0) ? ox : (axis == 1) ? oy : oz;
    float d = (axis == 0) ? dx : (axis == 1) ? dy : dz;
    float lo = 0.0f;
    float hi = (float)((axis == 0) ? g->nx : (axis == 1) ? g->ny : g->nz);
    if (fabsf(d) < 1e-30f) {
      if (o < lo || o > hi) return false;
      continue;
    }
    float a = (lo - o) / d;
    float b = (hi - o) / d;
    if (a > b) { float t = a; a = b; b = t; }
    if (a > t0) t0 = a;
    if (b < t1) t1 = b;
    if (t0 > t1) return false;
  }
  *t_enter = t0;
  *t_exit = t1;
  return true;
}

size_t tvdb_voxels_along_ray_dense(const tvdb_dense_grid* g,
                                   const tvdb_ray* ray,
                                   tvdb_vec3i* out_voxels,
                                   size_t cap) {
  if (!g || !g->data || !ray || g->nx <= 0 || g->ny <= 0 || g->nz <= 0 ||
      !(g->voxel_size > 0.0f) || !isfinite(g->voxel_size) ||
      !isfinite(ray->origin.x) || !isfinite(ray->origin.y) || !isfinite(ray->origin.z) ||
      !isfinite(ray->dir.x) || !isfinite(ray->dir.y) || !isfinite(ray->dir.z) ||
      isnan(ray->tmin) || isnan(ray->tmax)) return 0;
  float t_enter, t_exit;
  float vox_o[3], vox_d[3];
  if (!tvdb_ray_voxel_aabb(ray, g, &t_enter, &t_exit, vox_o, vox_d)) return 0;

  // Amanatides-Woo DDA in voxel-index space.
  float ox = vox_o[0], oy = vox_o[1], oz = vox_o[2];
  float dx = vox_d[0], dy = vox_d[1], dz = vox_d[2];

  float ex = ox + t_enter * dx;
  float ey = oy + t_enter * dy;
  float ez = oz + t_enter * dz;
  if (!isfinite(ex) || !isfinite(ey) || !isfinite(ez)) return 0;

  // The slab entry point lies on the grid boundary up to rounding, so its
  // floor may be -1 or n; clamp it into the grid before converting to int.
  float fx = floorf(ex), fy = floorf(ey), fz = floorf(ez);
  if (fx < 0.0f) fx = 0.0f; else if (fx > (float)(g->nx - 1)) fx = (float)(g->nx - 1);
  if (fy < 0.0f) fy = 0.0f; else if (fy > (float)(g->ny - 1)) fy = (float)(g->ny - 1);
  if (fz < 0.0f) fz = 0.0f; else if (fz > (float)(g->nz - 1)) fz = (float)(g->nz - 1);
  int ix = (int)fx;
  int iy = (int)fy;
  int iz = (int)fz;

  int sx = (dx > 0) ? 1 : (dx < 0 ? -1 : 0);
  int sy = (dy > 0) ? 1 : (dy < 0 ? -1 : 0);
  int sz = (dz > 0) ? 1 : (dz < 0 ? -1 : 0);

  float t_max_x = (sx != 0) ? (((float)ix + (sx > 0 ? 1.0f : 0.0f)) - ox) / dx : INFINITY;
  float t_max_y = (sy != 0) ? (((float)iy + (sy > 0 ? 1.0f : 0.0f)) - oy) / dy : INFINITY;
  float t_max_z = (sz != 0) ? (((float)iz + (sz > 0 ? 1.0f : 0.0f)) - oz) / dz : INFINITY;
  float t_delta_x = (sx != 0) ? fabsf(1.0f / dx) : INFINITY;
  float t_delta_y = (sy != 0) ? fabsf(1.0f / dy) : INFINITY;
  float t_delta_z = (sz != 0) ? fabsf(1.0f / dz) : INFINITY;

  size_t written = 0;
  size_t total = 0;
  while (ix >= 0 && ix < g->nx && iy >= 0 && iy < g->ny && iz >= 0 && iz < g->nz) {
    if (out_voxels && written < cap) {
      out_voxels[written].x = ix;
      out_voxels[written].y = iy;
      out_voxels[written].z = iz;
      ++written;
    }
    ++total;

    // Stop when the ray segment ends before it crosses into the next voxel.
    // The test uses the crossing time of the current voxel, not the exit
    // time of the voxel being stepped into, so the last voxel is kept.
    if (t_max_x < t_max_y && t_max_x < t_max_z) {
      if (!(t_max_x < t_exit)) break;
      ix += sx; t_max_x += t_delta_x;
    } else if (t_max_y < t_max_z) {
      if (!(t_max_y < t_exit)) break;
      iy += sy; t_max_y += t_delta_y;
    } else {
      if (!(t_max_z < t_exit)) break;
      iz += sz; t_max_z += t_delta_z;
    }
  }
  return out_voxels ? written : total;
}

void tvdb_uniform_ray_samples(const tvdb_ray* ray,
                              size_t n_samples,
                              tvdb_vec3f* out_points,
                              float* out_t) {
  if (!ray || n_samples == 0) return;
  float lo = ray->tmin, hi = ray->tmax;
  float inv_nm1 = (n_samples == 1) ? 0.0f : 1.0f / (float)(n_samples - 1);
  for (size_t i = 0; i < n_samples; ++i) {
    float a = (float)i * inv_nm1;
    float t = lo + (hi - lo) * a;
    if (out_t) out_t[i] = t;
    if (out_points) {
      out_points[i].x = ray->origin.x + t * ray->dir.x;
      out_points[i].y = ray->origin.y + t * ray->dir.y;
      out_points[i].z = ray->origin.z + t * ray->dir.z;
    }
  }
}

size_t tvdb_segments_along_ray(const tvdb_dense_grid* g,
                               const tvdb_ray* ray,
                               float isovalue,
                               size_t step_count,
                               float* out_t_pairs,
                               size_t cap) {
  if (!g || !g->data || !ray || step_count < 2) return 0;
  size_t pairs = 0;
  bool inside = false;
  float t_enter = 0.0f;
  float t_prev = ray->tmin;
  tvdb_sampler sampler;
  if (!tvdb_sampler_init(&sampler, g)) return 0;
  float v_prev = tvdb_sampler_trilinear(&sampler,
      ray->origin.x + t_prev * ray->dir.x,
      ray->origin.y + t_prev * ray->dir.y,
      ray->origin.z + t_prev * ray->dir.z) - isovalue;
  if (v_prev < 0.0f) { inside = true; t_enter = ray->tmin; }

  for (size_t i = 1; i < step_count; ++i) {
    float a = (float)i / (float)(step_count - 1);
    float t = ray->tmin + (ray->tmax - ray->tmin) * a;
    float v = tvdb_sampler_trilinear(&sampler,
        ray->origin.x + t * ray->dir.x,
        ray->origin.y + t * ray->dir.y,
        ray->origin.z + t * ray->dir.z) - isovalue;

    // Classify each sample (inside means v < 0; NaN counts as outside) and
    // emit on a state change. Comparing signs instead of testing
    // v_prev * v < 0 keeps exact-isovalue samples and products that
    // underflow to zero from hiding a crossing.
    const bool now_inside = v < 0.0f;
    if (now_inside != inside) {
      float t_cross;
      if ((v_prev < 0.0f && v > 0.0f) || (v_prev > 0.0f && v < 0.0f)) {
        float frac = v_prev / (v_prev - v);
        t_cross = t_prev + frac * (t - t_prev);
      } else {
        // One endpoint is exactly on the isovalue (or not a number): the
        // crossing is at the sample that sits on the surface.
        t_cross = (v_prev == 0.0f) ? t_prev : t;
      }
      if (now_inside) {
        t_enter = t_cross;
      } else {
        if (out_t_pairs && pairs < cap) {
          out_t_pairs[2 * pairs + 0] = t_enter;
          out_t_pairs[2 * pairs + 1] = t_cross;
        }
        ++pairs;
      }
      inside = now_inside;
    }
    v_prev = v; t_prev = t;
  }
  if (inside) {
    if (out_t_pairs && pairs < cap) {
      out_t_pairs[2 * pairs + 0] = t_enter;
      out_t_pairs[2 * pairs + 1] = ray->tmax;
    }
    ++pairs;
  }
  return pairs;
}

bool tvdb_marching_cubes_batch(const tvdb_dense_grid* grids,
                               size_t n_grids,
                               float isovalue,
                               tvdb_triangle_mesh* meshes,
                               tvdb_arena_allocator_t* arena) {
  if (!grids || !meshes) return false;
  bool all_ok = true;
  if (arena) {
    /* Arena is a bump allocator: not thread-safe, keep serial. */
    for (size_t i = 0; i < n_grids; ++i) {
      tvdb_triangle_mesh_init_arena(&meshes[i], arena);
      bool ok = tvdb_sdf_to_mesh(&grids[i], isovalue, &meshes[i], arena);
      if (!ok) all_ok = false;
    }
    return all_ok;
  }
  /* No arena: each mesh owns its buffers, so the conversions are independent. */
  #pragma omp parallel for schedule(static)
  for (long long i = 0; i < (long long)n_grids; ++i) {
    tvdb_triangle_mesh_init(&meshes[i]);
    bool ok = tvdb_sdf_to_mesh(&grids[i], isovalue, &meshes[i], NULL);
    if (!ok) {
      #pragma omp atomic write
      all_ok = false;
    }
  }
  return all_ok;
}
