#pragma once
//
// tinyvdb_ops.h — Grid operations for SDF processing and physics simulation.
//
// Header-only C++ module providing operations on DenseGrid:
//
// Phase 1 — Manifold mesh quality:
//   - Morphological dilation/erosion (dilate, erode, open, close)
//   - Gaussian and mean SDF filtering
//   - CSG operations (union, intersection, difference) on SDF grids
//   - Surface area and volume measurement from SDF
//
// Phase 2 — Physics simulation foundation:
//   - Differential operators (gradient, divergence, Laplacian, curl)
//   - Finite difference stencils (central, forward, backward)
//   - Semi-Lagrangian advection (RK2)
//   - Poisson solver (preconditioned conjugate gradient)
//
// Phase 3 — Advanced geometry:
//   - Ray-SDF intersection (sphere tracing)
//   - Volume to spheres (greedy adaptive sphere packing)
//   - Particles to SDF (sphere stamping)
//   - Level set fracture (cutter-based volume splitting)
//
// Depends on DenseGrid and Vec3f from tinyvdb_mesh.h.
//
// Usage:
//   In exactly ONE .cc file:
//     #define TINYVDB_OPS_IMPLEMENTATION
//     #include "tinyvdb_ops.h"
//
// License: MIT
//

#include "tinyvdb_mesh.h"
#include <vector>

namespace tvdb_ops {

using tvdb_mesh::DenseGrid;
using tvdb_mesh::Vec3f;

// ============================================================================
// Phase 1: Manifold mesh quality
// ============================================================================

// ---- Morphology ----

/// Dilate active region: expand the narrow band by `iterations` voxels.
/// Voxels at the boundary of the active region (|value| < band) get their
/// values extended outward. For level sets, this thickens the surface.
void Dilate(DenseGrid* grid, int iterations = 1);

/// Erode active region: shrink the narrow band by `iterations` voxels.
void Erode(DenseGrid* grid, int iterations = 1);

/// Morphological open (erode then dilate): removes small protrusions.
void Open(DenseGrid* grid, int iterations = 1);

/// Morphological close (dilate then erode): fills small holes.
void Close(DenseGrid* grid, int iterations = 1);

// ---- Filtering ----

/// Apply Gaussian smoothing to the SDF. `width` is the filter half-width
/// in voxels (typically 1-3). `iterations` controls the number of passes.
void GaussianFilter(DenseGrid* grid, int width = 1, int iterations = 1);

/// Apply mean (box) filter to the SDF.
void MeanFilter(DenseGrid* grid, int width = 1, int iterations = 1);

/// Apply Laplacian smoothing to the SDF.
void LaplacianFilter(DenseGrid* grid, int iterations = 1);

// ---- CSG ----

/// CSG union of two SDF grids: result = min(a, b).
/// Grids must have the same dimensions and voxel size.
void CSGUnion(const DenseGrid& a, const DenseGrid& b, DenseGrid* result);

/// CSG intersection: result = max(a, b).
void CSGIntersection(const DenseGrid& a, const DenseGrid& b, DenseGrid* result);

/// CSG difference: result = max(a, -b).
void CSGDifference(const DenseGrid& a, const DenseGrid& b, DenseGrid* result);

// ---- Measurement ----

/// Compute the surface area of the zero-crossing isosurface in an SDF grid.
float SurfaceArea(const DenseGrid& grid);

/// Compute the volume enclosed by the zero-crossing isosurface.
float Volume(const DenseGrid& grid);

// ============================================================================
// Phase 2: Physics simulation foundation
// ============================================================================

// ---- Dense vector grid (3-component) ----

struct DenseVecGrid {
  int nx, ny, nz;
  float ox, oy, oz;
  float voxel_size;
  std::vector<float> data;  // nx * ny * nz * 3, interleaved [x,y,z,x,y,z,...]

  float* at(int x, int y, int z) {
    return &data[(x + nx * (y + ny * z)) * 3];
  }
  const float* at(int x, int y, int z) const {
    return &data[(x + nx * (y + ny * z)) * 3];
  }
};

// ---- Differential operators ----

/// Compute gradient of scalar field using central differences.
void Gradient(const DenseGrid& scalar, DenseVecGrid* grad);

/// Compute divergence of vector field using central differences.
void Divergence(const DenseVecGrid& vec, DenseGrid* div);

/// Compute Laplacian of scalar field (6-point stencil).
void Laplacian(const DenseGrid& scalar, DenseGrid* laplacian);

/// Compute curl of vector field.
void Curl(const DenseVecGrid& vec, DenseVecGrid* curl);

// ---- Finite differences ----

/// Central difference in X direction at voxel (ix, iy, iz).
inline float CentralDiffX(const DenseGrid& g, int ix, int iy, int iz);
inline float CentralDiffY(const DenseGrid& g, int ix, int iy, int iz);
inline float CentralDiffZ(const DenseGrid& g, int ix, int iy, int iz);

/// Forward difference.
inline float ForwardDiffX(const DenseGrid& g, int ix, int iy, int iz);
inline float ForwardDiffY(const DenseGrid& g, int ix, int iy, int iz);
inline float ForwardDiffZ(const DenseGrid& g, int ix, int iy, int iz);

/// Backward difference.
inline float BackwardDiffX(const DenseGrid& g, int ix, int iy, int iz);
inline float BackwardDiffY(const DenseGrid& g, int ix, int iy, int iz);
inline float BackwardDiffZ(const DenseGrid& g, int ix, int iy, int iz);

/// 6-point Laplacian stencil at voxel (ix, iy, iz).
inline float LaplacianStencil(const DenseGrid& g, int ix, int iy, int iz);

// ---- Advection ----

/// Semi-Lagrangian advection of a scalar field through a velocity field.
/// @param field    Input scalar field (e.g., density, SDF).
/// @param velocity Velocity field.
/// @param dt       Time step.
/// @param result   Output advected field (same dimensions as input).
void AdvectSemiLagrangian(const DenseGrid& field,
                          const DenseVecGrid& velocity,
                          float dt,
                          DenseGrid* result);

// ---- Poisson solver ----

/// Solve Laplacian(x) = b using preconditioned conjugate gradient.
/// @param rhs        Right-hand side (b).
/// @param x          Solution (output, also used as initial guess).
/// @param max_iters  Maximum iterations.
/// @param tolerance  Convergence threshold for residual norm.
/// @return           Number of iterations used (negative if did not converge).
int SolvePoisson(const DenseGrid& rhs,
                 DenseGrid* x,
                 int max_iters = 500,
                 float tolerance = 1e-6f);

// ============================================================================
// Phase 3: Advanced geometry
// ============================================================================

// ---- Ray-SDF intersection ----

struct RayHit {
  float t;              // distance along ray (< 0 if no hit)
  Vec3f position;       // world-space hit point
  Vec3f normal;         // surface normal at hit (gradient of SDF)
};

/// Cast a ray against an SDF grid. Uses sphere tracing (ray marching).
/// @param grid     SDF grid.
/// @param origin   Ray origin in world space.
/// @param dir      Ray direction (must be normalized).
/// @param max_t    Maximum ray distance.
/// @param hit      Output hit result (t < 0 if no hit).
/// @return true if the ray hits the surface (SDF zero-crossing).
bool RayCastSDF(const DenseGrid& grid,
                const Vec3f& origin,
                const Vec3f& dir,
                float max_t,
                RayHit* hit);

// ---- Volume to spheres ----

struct Sphere {
  Vec3f center;
  float radius;
};

/// Fill the interior of an SDF grid with adaptively-sized spheres.
/// Larger spheres are placed first in regions far from the surface.
/// @param grid         SDF grid (negative = interior).
/// @param spheres      Output sphere list.
/// @param min_radius   Minimum sphere radius in world units.
/// @param max_spheres  Maximum number of spheres to generate.
/// @param overlap      Allowed overlap factor (0 = no overlap, 0.5 = 50%).
void VolumeToSpheres(const DenseGrid& grid,
                     std::vector<Sphere>* spheres,
                     float min_radius = 0.0f,
                     int max_spheres = 1000,
                     float overlap = 0.25f);

// ---- Particles to level set ----

struct Particle {
  Vec3f position;
  float radius;
};

/// Rasterize particles (with position and radius) into an SDF grid.
/// Each particle stamps a sphere SDF: min(grid, |p - center| - radius).
/// @param particles    Input particles.
/// @param voxel_size   Grid voxel size.
/// @param band_width   Narrow band half-width in voxels.
/// @param grid         Output SDF grid.
void ParticlesToSDF(const std::vector<Particle>& particles,
                    float voxel_size,
                    float band_width,
                    DenseGrid* grid);

// ---- Level set fracture ----

/// Fracture an SDF volume into pieces by intersecting with cutter SDFs.
/// Each cutter divides the volume into positive/negative halves.
/// @param volume       Input SDF grid.
/// @param cutters      Cutter SDF grids (same dimensions as volume).
/// @param pieces       Output: one SDF grid per piece.
void Fracture(const DenseGrid& volume,
              const std::vector<DenseGrid>& cutters,
              std::vector<DenseGrid>* pieces);

}  // namespace tvdb_ops


// ============================================================================
// Implementation
// ============================================================================

#ifdef TINYVDB_OPS_IMPLEMENTATION

#include <algorithm>
#include <cmath>
#include <cstring>

namespace tvdb_ops {

// ---- Helper: clamp index ----
static inline int clampI(int v, int lo, int hi) {
  return v < lo ? lo : (v > hi ? hi : v);
}

static inline float SampleClamped(const DenseGrid& g, int ix, int iy, int iz) {
  ix = clampI(ix, 0, g.nx - 1);
  iy = clampI(iy, 0, g.ny - 1);
  iz = clampI(iz, 0, g.nz - 1);
  return g.data[ix + g.nx * (iy + g.ny * iz)];
}

static inline float SampleVecClamped(const DenseVecGrid& g, int x, int y, int z, int comp) {
  x = clampI(x, 0, g.nx-1); y = clampI(y, 0, g.ny-1); z = clampI(z, 0, g.nz-1);
  return g.data[(x + g.nx * (y + g.ny * z)) * 3 + comp];
}

// ============================================================================
// Finite differences (inline)
// ============================================================================

inline float CentralDiffX(const DenseGrid& g, int ix, int iy, int iz) {
  assert(g.voxel_size > 0.0f);
  return (SampleClamped(g, ix+1, iy, iz) - SampleClamped(g, ix-1, iy, iz))
         * (0.5f / g.voxel_size);
}
inline float CentralDiffY(const DenseGrid& g, int ix, int iy, int iz) {
  assert(g.voxel_size > 0.0f);
  return (SampleClamped(g, ix, iy+1, iz) - SampleClamped(g, ix, iy-1, iz))
         * (0.5f / g.voxel_size);
}
inline float CentralDiffZ(const DenseGrid& g, int ix, int iy, int iz) {
  assert(g.voxel_size > 0.0f);
  return (SampleClamped(g, ix, iy, iz+1) - SampleClamped(g, ix, iy, iz-1))
         * (0.5f / g.voxel_size);
}

inline float ForwardDiffX(const DenseGrid& g, int ix, int iy, int iz) {
  assert(g.voxel_size > 0.0f);
  return (SampleClamped(g, ix+1, iy, iz) - SampleClamped(g, ix, iy, iz))
         / g.voxel_size;
}
inline float ForwardDiffY(const DenseGrid& g, int ix, int iy, int iz) {
  assert(g.voxel_size > 0.0f);
  return (SampleClamped(g, ix, iy+1, iz) - SampleClamped(g, ix, iy, iz))
         / g.voxel_size;
}
inline float ForwardDiffZ(const DenseGrid& g, int ix, int iy, int iz) {
  assert(g.voxel_size > 0.0f);
  return (SampleClamped(g, ix, iy, iz+1) - SampleClamped(g, ix, iy, iz))
         / g.voxel_size;
}

inline float BackwardDiffX(const DenseGrid& g, int ix, int iy, int iz) {
  assert(g.voxel_size > 0.0f);
  return (SampleClamped(g, ix, iy, iz) - SampleClamped(g, ix-1, iy, iz))
         / g.voxel_size;
}
inline float BackwardDiffY(const DenseGrid& g, int ix, int iy, int iz) {
  assert(g.voxel_size > 0.0f);
  return (SampleClamped(g, ix, iy, iz) - SampleClamped(g, ix, iy-1, iz))
         / g.voxel_size;
}
inline float BackwardDiffZ(const DenseGrid& g, int ix, int iy, int iz) {
  assert(g.voxel_size > 0.0f);
  return (SampleClamped(g, ix, iy, iz) - SampleClamped(g, ix, iy, iz-1))
         / g.voxel_size;
}

inline float LaplacianStencil(const DenseGrid& g, int ix, int iy, int iz) {
  assert(g.voxel_size > 0.0f);
  float c = SampleClamped(g, ix, iy, iz);
  float inv_h2 = 1.0f / (g.voxel_size * g.voxel_size);
  return (SampleClamped(g, ix+1, iy, iz) + SampleClamped(g, ix-1, iy, iz)
        + SampleClamped(g, ix, iy+1, iz) + SampleClamped(g, ix, iy-1, iz)
        + SampleClamped(g, ix, iy, iz+1) + SampleClamped(g, ix, iy, iz-1)
        - 6.0f * c) * inv_h2;
}

// ============================================================================
// Morphology
// ============================================================================

void Dilate(DenseGrid* grid, int iterations) {
  if (!grid) return;
  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  const float bg = grid->voxel_size * 3.0f;  // background value

  for (int iter = 0; iter < iterations; ++iter) {
    std::vector<float> tmp = grid->data;
    for (int iz = 0; iz < nz; ++iz)
      for (int iy = 0; iy < ny; ++iy)
        for (int ix = 0; ix < nx; ++ix) {
          float c = grid->at(ix, iy, iz);
          if (std::abs(c) >= bg) {
            // Background voxel: check if any 6-neighbor is active (|v| < bg)
            float mn = c;
            static const int d[6][3] = {{-1,0,0},{1,0,0},{0,-1,0},{0,1,0},{0,0,-1},{0,0,1}};
            for (const auto& dd : d) {
              float n = SampleClamped(*grid, ix+dd[0], iy+dd[1], iz+dd[2]);
              if (std::abs(n) < std::abs(mn)) mn = n;
            }
            // Expand: set to neighbor value + voxel_size (extend distance)
            if (std::abs(mn) < bg) {
              tmp[ix + nx * (iy + ny * iz)] = mn + (mn >= 0 ? grid->voxel_size : -grid->voxel_size);
            }
          }
        }
    grid->data = std::move(tmp);
  }
}

void Erode(DenseGrid* grid, int iterations) {
  if (!grid) return;
  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  const float bg = grid->voxel_size * 3.0f;

  for (int iter = 0; iter < iterations; ++iter) {
    std::vector<float> tmp = grid->data;
    for (int iz = 0; iz < nz; ++iz)
      for (int iy = 0; iy < ny; ++iy)
        for (int ix = 0; ix < nx; ++ix) {
          float c = grid->at(ix, iy, iz);
          if (std::abs(c) < bg) {
            // Active voxel: check if any 6-neighbor is background
            static const int d[6][3] = {{-1,0,0},{1,0,0},{0,-1,0},{0,1,0},{0,0,-1},{0,0,1}};
            for (const auto& dd : d) {
              float n = SampleClamped(*grid, ix+dd[0], iy+dd[1], iz+dd[2]);
              if (std::abs(n) >= bg) {
                tmp[ix + nx * (iy + ny * iz)] = (c >= 0) ? bg : -bg;
                break;
              }
            }
          }
        }
    grid->data = std::move(tmp);
  }
}

void Open(DenseGrid* grid, int iterations) {
  Erode(grid, iterations);
  Dilate(grid, iterations);
}

void Close(DenseGrid* grid, int iterations) {
  Dilate(grid, iterations);
  Erode(grid, iterations);
}

// ============================================================================
// Filtering
// ============================================================================

void GaussianFilter(DenseGrid* grid, int width, int iterations) {
  if (!grid || width < 1) return;
  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;

  // Precompute 1D Gaussian kernel
  const int ksize = 2 * width + 1;
  std::vector<float> kernel(ksize);
  float sigma = width / 2.0f;
  if (sigma < 0.5f) sigma = 0.5f;
  float sum = 0.0f;
  for (int i = 0; i < ksize; ++i) {
    float d = static_cast<float>(i - width);
    kernel[i] = std::exp(-0.5f * d * d / (sigma * sigma));
    sum += kernel[i];
  }
  for (float& k : kernel) k /= sum;

  // Ping-pong between grid->data and tmp to avoid extra copies.
  std::vector<float> tmp(grid->data.size());
  auto SampleFrom = [&](const std::vector<float>& src, int x, int y, int z) -> float {
    x = clampI(x, 0, nx-1); y = clampI(y, 0, ny-1); z = clampI(z, 0, nz-1);
    return src[x + nx * (y + ny * z)];
  };

  for (int iter = 0; iter < iterations; ++iter) {
    // X pass: grid->data → tmp
    for (int iz = 0; iz < nz; ++iz)
      for (int iy = 0; iy < ny; ++iy)
        for (int ix = 0; ix < nx; ++ix) {
          float v = 0.0f;
          for (int k = -width; k <= width; ++k)
            v += SampleFrom(grid->data, ix+k, iy, iz) * kernel[k + width];
          tmp[ix + nx * (iy + ny * iz)] = v;
        }
    // Y pass: tmp → grid->data
    for (int iz = 0; iz < nz; ++iz)
      for (int ix = 0; ix < nx; ++ix)
        for (int iy = 0; iy < ny; ++iy) {
          float v = 0.0f;
          for (int k = -width; k <= width; ++k)
            v += SampleFrom(tmp, ix, iy+k, iz) * kernel[k + width];
          grid->data[ix + nx * (iy + ny * iz)] = v;
        }
    // Z pass: grid->data → tmp
    for (int iy = 0; iy < ny; ++iy)
      for (int ix = 0; ix < nx; ++ix)
        for (int iz = 0; iz < nz; ++iz) {
          float v = 0.0f;
          for (int k = -width; k <= width; ++k)
            v += SampleFrom(grid->data, ix, iy, iz+k) * kernel[k + width];
          tmp[ix + nx * (iy + ny * iz)] = v;
        }
    grid->data.swap(tmp);
  }
}

void MeanFilter(DenseGrid* grid, int width, int iterations) {
  if (!grid || width < 1) return;
  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  const float inv_k = 1.0f / static_cast<float>(2 * width + 1);

  std::vector<float> tmp(grid->data.size());
  auto SampleFrom = [&](const std::vector<float>& src, int x, int y, int z) -> float {
    x = clampI(x, 0, nx-1); y = clampI(y, 0, ny-1); z = clampI(z, 0, nz-1);
    return src[x + nx * (y + ny * z)];
  };

  for (int iter = 0; iter < iterations; ++iter) {
    for (int iz = 0; iz < nz; ++iz)
      for (int iy = 0; iy < ny; ++iy)
        for (int ix = 0; ix < nx; ++ix) {
          float v = 0.0f;
          for (int k = -width; k <= width; ++k)
            v += SampleFrom(grid->data, ix+k, iy, iz);
          tmp[ix + nx * (iy + ny * iz)] = v * inv_k;
        }
    for (int iz = 0; iz < nz; ++iz)
      for (int ix = 0; ix < nx; ++ix)
        for (int iy = 0; iy < ny; ++iy) {
          float v = 0.0f;
          for (int k = -width; k <= width; ++k)
            v += SampleFrom(tmp, ix, iy+k, iz);
          grid->data[ix + nx * (iy + ny * iz)] = v * inv_k;
        }
    for (int iy = 0; iy < ny; ++iy)
      for (int ix = 0; ix < nx; ++ix)
        for (int iz = 0; iz < nz; ++iz) {
          float v = 0.0f;
          for (int k = -width; k <= width; ++k)
            v += SampleFrom(grid->data, ix, iy, iz+k);
          tmp[ix + nx * (iy + ny * iz)] = v * inv_k;
        }
    grid->data.swap(tmp);
  }
}

void LaplacianFilter(DenseGrid* grid, int iterations) {
  if (!grid) return;
  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;

  const float dt = grid->voxel_size * grid->voxel_size / 6.0f;
  for (int iter = 0; iter < iterations; ++iter) {
    std::vector<float> tmp(grid->data.size());
    for (int iz = 0; iz < nz; ++iz)
      for (int iy = 0; iy < ny; ++iy)
        for (int ix = 0; ix < nx; ++ix) {
          float lap = LaplacianStencil(*grid, ix, iy, iz);
          tmp[ix + nx * (iy + ny * iz)] = grid->at(ix, iy, iz) + dt * lap;
        }
    grid->data = std::move(tmp);
  }
}

// ============================================================================
// CSG
// ============================================================================

static void CSGCopyMeta(const DenseGrid& src, DenseGrid* dst) {
  dst->nx = src.nx; dst->ny = src.ny; dst->nz = src.nz;
  dst->ox = src.ox; dst->oy = src.oy; dst->oz = src.oz;
  dst->voxel_size = src.voxel_size;
  dst->data.resize(src.data.size());
}

void CSGUnion(const DenseGrid& a, const DenseGrid& b, DenseGrid* result) {
  if (!result || a.data.size() != b.data.size()) return;
  CSGCopyMeta(a, result);
  for (size_t i = 0; i < a.data.size(); ++i)
    result->data[i] = std::min(a.data[i], b.data[i]);
}

void CSGIntersection(const DenseGrid& a, const DenseGrid& b, DenseGrid* result) {
  if (!result || a.data.size() != b.data.size()) return;
  CSGCopyMeta(a, result);
  for (size_t i = 0; i < a.data.size(); ++i)
    result->data[i] = std::max(a.data[i], b.data[i]);
}

void CSGDifference(const DenseGrid& a, const DenseGrid& b, DenseGrid* result) {
  if (!result || a.data.size() != b.data.size()) return;
  CSGCopyMeta(a, result);
  for (size_t i = 0; i < a.data.size(); ++i)
    result->data[i] = std::max(a.data[i], -b.data[i]);
}

// ============================================================================
// Measurement
// ============================================================================

float SurfaceArea(const DenseGrid& grid) {
  // Approximate surface area by summing the area of zero-crossing faces.
  // Each pair of adjacent voxels with opposite signs contributes a face
  // of area voxel_size^2.
  const int nx = grid.nx, ny = grid.ny, nz = grid.nz;
  const float face_area = grid.voxel_size * grid.voxel_size;
  float area = 0.0f;

  for (int iz = 0; iz < nz; ++iz)
    for (int iy = 0; iy < ny; ++iy)
      for (int ix = 0; ix < nx; ++ix) {
        float c = grid.at(ix, iy, iz);
        // Check +X, +Y, +Z neighbors for sign change
        if (ix < nx-1) {
          float n = grid.at(ix+1, iy, iz);
          if ((c < 0) != (n < 0)) area += face_area;
        }
        if (iy < ny-1) {
          float n = grid.at(ix, iy+1, iz);
          if ((c < 0) != (n < 0)) area += face_area;
        }
        if (iz < nz-1) {
          float n = grid.at(ix, iy, iz+1);
          if ((c < 0) != (n < 0)) area += face_area;
        }
      }
  return area;
}

float Volume(const DenseGrid& grid) {
  // Volume = count of interior voxels * voxel_volume.
  const float voxel_vol = grid.voxel_size * grid.voxel_size * grid.voxel_size;
  float vol = 0.0f;
  for (float v : grid.data) {
    if (v < 0.0f) vol += voxel_vol;
  }
  return vol;
}

// ============================================================================
// Differential operators
// ============================================================================

void Gradient(const DenseGrid& scalar, DenseVecGrid* grad) {
  if (!grad) return;
  const int nx = scalar.nx, ny = scalar.ny, nz = scalar.nz;
  grad->nx = nx; grad->ny = ny; grad->nz = nz;
  grad->ox = scalar.ox; grad->oy = scalar.oy; grad->oz = scalar.oz;
  grad->voxel_size = scalar.voxel_size;
  grad->data.resize(static_cast<size_t>(nx) * ny * nz * 3);

  for (int iz = 0; iz < nz; ++iz)
    for (int iy = 0; iy < ny; ++iy)
      for (int ix = 0; ix < nx; ++ix) {
        float* g = grad->at(ix, iy, iz);
        g[0] = CentralDiffX(scalar, ix, iy, iz);
        g[1] = CentralDiffY(scalar, ix, iy, iz);
        g[2] = CentralDiffZ(scalar, ix, iy, iz);
      }
}

void Divergence(const DenseVecGrid& vec, DenseGrid* div) {
  if (!div) return;
  const int nx = vec.nx, ny = vec.ny, nz = vec.nz;
  div->nx = nx; div->ny = ny; div->nz = nz;
  div->ox = vec.ox; div->oy = vec.oy; div->oz = vec.oz;
  div->voxel_size = vec.voxel_size;
  div->data.resize(static_cast<size_t>(nx) * ny * nz);

  const float inv_2h = 0.5f / vec.voxel_size;
  auto SV = [&](int x, int y, int z, int c) { return SampleVecClamped(vec, x, y, z, c); };

  for (int iz = 0; iz < nz; ++iz)
    for (int iy = 0; iy < ny; ++iy)
      for (int ix = 0; ix < nx; ++ix) {
        float du_dx = (SV(ix+1,iy,iz,0) - SV(ix-1,iy,iz,0)) * inv_2h;
        float dv_dy = (SV(ix,iy+1,iz,1) - SV(ix,iy-1,iz,1)) * inv_2h;
        float dw_dz = (SV(ix,iy,iz+1,2) - SV(ix,iy,iz-1,2)) * inv_2h;
        div->at(ix, iy, iz) = du_dx + dv_dy + dw_dz;
      }
}

void Laplacian(const DenseGrid& scalar, DenseGrid* lap) {
  if (!lap) return;
  const int nx = scalar.nx, ny = scalar.ny, nz = scalar.nz;
  lap->nx = nx; lap->ny = ny; lap->nz = nz;
  lap->ox = scalar.ox; lap->oy = scalar.oy; lap->oz = scalar.oz;
  lap->voxel_size = scalar.voxel_size;
  lap->data.resize(static_cast<size_t>(nx) * ny * nz);

  for (int iz = 0; iz < nz; ++iz)
    for (int iy = 0; iy < ny; ++iy)
      for (int ix = 0; ix < nx; ++ix)
        lap->at(ix, iy, iz) = LaplacianStencil(scalar, ix, iy, iz);
}

void Curl(const DenseVecGrid& vec, DenseVecGrid* curl) {
  if (!curl) return;
  const int nx = vec.nx, ny = vec.ny, nz = vec.nz;
  curl->nx = nx; curl->ny = ny; curl->nz = nz;
  curl->ox = vec.ox; curl->oy = vec.oy; curl->oz = vec.oz;
  curl->voxel_size = vec.voxel_size;
  curl->data.resize(static_cast<size_t>(nx) * ny * nz * 3);

  const float inv_2h = 0.5f / vec.voxel_size;
  auto SV = [&](int x, int y, int z, int c) { return SampleVecClamped(vec, x, y, z, c); };

  for (int iz = 0; iz < nz; ++iz)
    for (int iy = 0; iy < ny; ++iy)
      for (int ix = 0; ix < nx; ++ix) {
        float dw_dy = (SV(ix,iy+1,iz,2) - SV(ix,iy-1,iz,2)) * inv_2h;
        float dv_dz = (SV(ix,iy,iz+1,1) - SV(ix,iy,iz-1,1)) * inv_2h;
        float du_dz = (SV(ix,iy,iz+1,0) - SV(ix,iy,iz-1,0)) * inv_2h;
        float dw_dx = (SV(ix+1,iy,iz,2) - SV(ix-1,iy,iz,2)) * inv_2h;
        float dv_dx = (SV(ix+1,iy,iz,1) - SV(ix-1,iy,iz,1)) * inv_2h;
        float du_dy = (SV(ix,iy+1,iz,0) - SV(ix,iy-1,iz,0)) * inv_2h;

        float* c = curl->at(ix, iy, iz);
        c[0] = dw_dy - dv_dz;
        c[1] = du_dz - dw_dx;
        c[2] = dv_dx - du_dy;
      }
}

// ============================================================================
// Advection
// ============================================================================

// Trilinear interpolation of a scalar grid at world position (wx, wy, wz).
static float TrilinearSample(const DenseGrid& g, float wx, float wy, float wz) {
  float fx = (wx - g.ox) / g.voxel_size - 0.5f;
  float fy = (wy - g.oy) / g.voxel_size - 0.5f;
  float fz = (wz - g.oz) / g.voxel_size - 0.5f;

  int ix = static_cast<int>(std::floor(fx));
  int iy = static_cast<int>(std::floor(fy));
  int iz = static_cast<int>(std::floor(fz));
  float tx = fx - ix, ty = fy - iy, tz = fz - iz;

  float c000 = SampleClamped(g, ix,   iy,   iz);
  float c100 = SampleClamped(g, ix+1, iy,   iz);
  float c010 = SampleClamped(g, ix,   iy+1, iz);
  float c110 = SampleClamped(g, ix+1, iy+1, iz);
  float c001 = SampleClamped(g, ix,   iy,   iz+1);
  float c101 = SampleClamped(g, ix+1, iy,   iz+1);
  float c011 = SampleClamped(g, ix,   iy+1, iz+1);
  float c111 = SampleClamped(g, ix+1, iy+1, iz+1);

  float c00 = c000 * (1-tx) + c100 * tx;
  float c10 = c010 * (1-tx) + c110 * tx;
  float c01 = c001 * (1-tx) + c101 * tx;
  float c11 = c011 * (1-tx) + c111 * tx;

  float c0 = c00 * (1-ty) + c10 * ty;
  float c1 = c01 * (1-ty) + c11 * ty;

  return c0 * (1-tz) + c1 * tz;
}

// Trilinear interpolation of a vector grid at world position.
static void TrilinearSV(const DenseVecGrid& g, float wx, float wy, float wz,
                               float* out) {
  float fx = (wx - g.ox) / g.voxel_size - 0.5f;
  float fy = (wy - g.oy) / g.voxel_size - 0.5f;
  float fz = (wz - g.oz) / g.voxel_size - 0.5f;

  int ix = static_cast<int>(std::floor(fx));
  int iy = static_cast<int>(std::floor(fy));
  int iz = static_cast<int>(std::floor(fz));
  float tx = fx - ix, ty = fy - iy, tz = fz - iz;

  auto S = [&](int x, int y, int z, int c) -> float {
    x = clampI(x, 0, g.nx-1); y = clampI(y, 0, g.ny-1); z = clampI(z, 0, g.nz-1);
    return g.data[(x + g.nx * (y + g.ny * z)) * 3 + c];
  };

  for (int c = 0; c < 3; ++c) {
    float c00 = S(ix,iy,iz,c)*(1-tx) + S(ix+1,iy,iz,c)*tx;
    float c10 = S(ix,iy+1,iz,c)*(1-tx) + S(ix+1,iy+1,iz,c)*tx;
    float c01 = S(ix,iy,iz+1,c)*(1-tx) + S(ix+1,iy,iz+1,c)*tx;
    float c11 = S(ix,iy+1,iz+1,c)*(1-tx) + S(ix+1,iy+1,iz+1,c)*tx;
    float c0 = c00*(1-ty) + c10*ty;
    float c1 = c01*(1-ty) + c11*ty;
    out[c] = c0*(1-tz) + c1*tz;
  }
}

void AdvectSemiLagrangian(const DenseGrid& field,
                          const DenseVecGrid& velocity,
                          float dt,
                          DenseGrid* result) {
  if (!result) return;
  const int nx = field.nx, ny = field.ny, nz = field.nz;
  result->nx = nx; result->ny = ny; result->nz = nz;
  result->ox = field.ox; result->oy = field.oy; result->oz = field.oz;
  result->voxel_size = field.voxel_size;
  result->data.resize(static_cast<size_t>(nx) * ny * nz);

  for (int iz = 0; iz < nz; ++iz)
    for (int iy = 0; iy < ny; ++iy)
      for (int ix = 0; ix < nx; ++ix) {
        // World position of this voxel center
        float wx = field.ox + (ix + 0.5f) * field.voxel_size;
        float wy = field.oy + (iy + 0.5f) * field.voxel_size;
        float wz = field.oz + (iz + 0.5f) * field.voxel_size;

        // Sample velocity at this position
        float vel[3];
        TrilinearSV(velocity, wx, wy, wz, vel);

        // Trace back: RK2 (midpoint method)
        float mx = wx - 0.5f * dt * vel[0];
        float my = wy - 0.5f * dt * vel[1];
        float mz = wz - 0.5f * dt * vel[2];

        float vel_mid[3];
        TrilinearSV(velocity, mx, my, mz, vel_mid);

        float bx = wx - dt * vel_mid[0];
        float by = wy - dt * vel_mid[1];
        float bz = wz - dt * vel_mid[2];

        // Sample field at back-traced position
        result->at(ix, iy, iz) = TrilinearSample(field, bx, by, bz);
      }
}

// ============================================================================
// Poisson solver (Preconditioned Conjugate Gradient)
// ============================================================================

// Compute Ax = -Laplacian(x) with Dirichlet (zero) boundary conditions.
// Positive definite: diagonal = 6/h^2 > 0.
static void ApplyNegLaplacian(const DenseGrid& x, DenseGrid* out) {
  assert(x.voxel_size > 0.0f);
  const int nx = x.nx, ny = x.ny, nz = x.nz;
  const float inv_h2 = 1.0f / (x.voxel_size * x.voxel_size);

  auto Sample = [&](int ix, int iy, int iz) -> float {
    if (ix < 0 || ix >= nx || iy < 0 || iy >= ny || iz < 0 || iz >= nz) return 0.0f;
    return x.data[ix + nx * (iy + ny * iz)];
  };

  for (int iz = 0; iz < nz; ++iz)
    for (int iy = 0; iy < ny; ++iy)
      for (int ix_ = 0; ix_ < nx; ++ix_) {
        float c = x.at(ix_, iy, iz);
        float sum = Sample(ix_+1,iy,iz) + Sample(ix_-1,iy,iz)
                  + Sample(ix_,iy+1,iz) + Sample(ix_,iy-1,iz)
                  + Sample(ix_,iy,iz+1) + Sample(ix_,iy,iz-1)
                  - 6.0f * c;
        out->at(ix_, iy, iz) = -sum * inv_h2;
      }
}

// Dot product of two grids' data.
static float GridDot(const DenseGrid& a, const DenseGrid& b) {
  float sum = 0.0f;
  for (size_t i = 0; i < a.data.size(); ++i) sum += a.data[i] * b.data[i];
  return sum;
}

int SolvePoisson(const DenseGrid& rhs, DenseGrid* x,
                 int max_iters, float tolerance) {
  if (!x) return -1;
  const size_t N = rhs.data.size();

  // Initialize x if not already sized
  if (x->data.size() != N) {
    x->nx = rhs.nx; x->ny = rhs.ny; x->nz = rhs.nz;
    x->ox = rhs.ox; x->oy = rhs.oy; x->oz = rhs.oz;
    x->voxel_size = rhs.voxel_size;
    x->data.assign(N, 0.0f);
  }

  // r = b - Ax
  DenseGrid r, Ax, p, Ap;
  r.nx = Ax.nx = p.nx = Ap.nx = rhs.nx;
  r.ny = Ax.ny = p.ny = Ap.ny = rhs.ny;
  r.nz = Ax.nz = p.nz = Ap.nz = rhs.nz;
  r.ox = Ax.ox = p.ox = Ap.ox = rhs.ox;
  r.oy = Ax.oy = p.oy = Ap.oy = rhs.oy;
  r.oz = Ax.oz = p.oz = Ap.oz = rhs.oz;
  r.voxel_size = Ax.voxel_size = p.voxel_size = Ap.voxel_size = rhs.voxel_size;
  r.data.resize(N); Ax.data.resize(N); p.data.resize(N); Ap.data.resize(N);

  // Solve (-L)x = (-b) where A = -L is positive definite (diagonal 6/h^2).
  // r = (-b) - A*x
  ApplyNegLaplacian(*x, &Ax);
  for (size_t i = 0; i < N; ++i) r.data[i] = -rhs.data[i] - Ax.data[i];

  // Jacobi preconditioner: M^{-1} = 1/diag(A) = h^2/6
  DenseGrid z;
  z.nx = rhs.nx; z.ny = rhs.ny; z.nz = rhs.nz;
  z.ox = rhs.ox; z.oy = rhs.oy; z.oz = rhs.oz;
  z.voxel_size = rhs.voxel_size;
  z.data.resize(N);

  float precond = (rhs.voxel_size * rhs.voxel_size) / 6.0f;
  for (size_t i = 0; i < N; ++i) z.data[i] = r.data[i] * precond;

  p.data = z.data;
  float rz = GridDot(r, z);
  float tol2 = tolerance * tolerance;

  for (int iter = 0; iter < max_iters; ++iter) {
    float r_norm2 = GridDot(r, r);
    if (r_norm2 < tol2) return iter;

    ApplyNegLaplacian(p, &Ap);
    float pAp = GridDot(p, Ap);
    if (std::abs(pAp) < 1e-30f) return -(iter + 1);

    float alpha = rz / pAp;
    for (size_t i = 0; i < N; ++i) {
      x->data[i] += alpha * p.data[i];
      r.data[i] -= alpha * Ap.data[i];
    }

    for (size_t i = 0; i < N; ++i) z.data[i] = r.data[i] * precond;
    float rz_new = GridDot(r, z);
    float beta = rz_new / rz;
    rz = rz_new;

    for (size_t i = 0; i < N; ++i) p.data[i] = z.data[i] + beta * p.data[i];
  }

  return -max_iters;
}

// ============================================================================
// Ray-SDF intersection (sphere tracing)
// ============================================================================

bool RayCastSDF(const DenseGrid& grid,
                const Vec3f& origin,
                const Vec3f& dir,
                float max_t,
                RayHit* hit) {
  if (!hit) return false;
  hit->t = -1.0f;

  const float eps = 0.5f * grid.voxel_size;  // surface threshold
  const int max_steps = 512;
  float t = 0.0f;

  for (int step = 0; step < max_steps && t < max_t; ++step) {
    float wx = origin.x + t * dir.x;
    float wy = origin.y + t * dir.y;
    float wz = origin.z + t * dir.z;

    float dist = TrilinearSample(grid, wx, wy, wz);

    if (dist < eps) {
      hit->t = t;
      hit->position = {wx, wy, wz};
      // Normal = gradient of SDF at hit point
      float gx = (TrilinearSample(grid, wx + eps, wy, wz) -
                   TrilinearSample(grid, wx - eps, wy, wz));
      float gy = (TrilinearSample(grid, wx, wy + eps, wz) -
                   TrilinearSample(grid, wx, wy - eps, wz));
      float gz = (TrilinearSample(grid, wx, wy, wz + eps) -
                   TrilinearSample(grid, wx, wy, wz - eps));
      float len = std::sqrt(gx*gx + gy*gy + gz*gz);
      if (len > 1e-8f) {
        float inv = 1.0f / len;
        hit->normal = {gx * inv, gy * inv, gz * inv};
      } else {
        hit->normal = {0.0f, 1.0f, 0.0f};
      }
      return true;
    }

    // Advance by the distance to the surface (sphere tracing).
    // Clamp minimum step to avoid getting stuck near the surface.
    t += std::max(std::abs(dist), 0.1f * grid.voxel_size);
  }

  return false;
}

// ============================================================================
// Volume to spheres
// ============================================================================

void VolumeToSpheres(const DenseGrid& grid,
                     std::vector<Sphere>* spheres,
                     float min_radius,
                     int max_spheres,
                     float overlap) {
  if (!spheres) return;
  spheres->clear();
  const int nx = grid.nx, ny = grid.ny, nz = grid.nz;

  // Collect interior voxels with their distance to surface (negative SDF = inside).
  struct Candidate {
    int ix, iy, iz;
    float dist;  // absolute distance to surface (larger = deeper inside)
  };
  std::vector<Candidate> candidates;
  for (int iz = 0; iz < nz; ++iz)
    for (int iy = 0; iy < ny; ++iy)
      for (int ix = 0; ix < nx; ++ix) {
        float d = grid.at(ix, iy, iz);
        if (d < 0.0f && std::abs(d) >= min_radius) {
          candidates.push_back({ix, iy, iz, std::abs(d)});
        }
      }

  // Partial sort: only need the top max_spheres candidates (O(V) vs O(V log V)).
  auto cmp = [](const Candidate& a, const Candidate& b) { return a.dist > b.dist; };
  size_t sort_n = std::min(candidates.size(), static_cast<size_t>(max_spheres) * 4);
  if (sort_n < candidates.size())
    std::partial_sort(candidates.begin(), candidates.begin() + sort_n, candidates.end(), cmp);
  else
    std::sort(candidates.begin(), candidates.end(), cmp);

  // Greedily place spheres, skipping candidates too close to existing spheres.
  for (const auto& c : candidates) {
    if (static_cast<int>(spheres->size()) >= max_spheres) break;

    float wx = grid.ox + (c.ix + 0.5f) * grid.voxel_size;
    float wy = grid.oy + (c.iy + 0.5f) * grid.voxel_size;
    float wz = grid.oz + (c.iz + 0.5f) * grid.voxel_size;
    float radius = c.dist;

    // Check overlap with existing spheres.
    bool too_close = false;
    for (const auto& s : *spheres) {
      float dx = wx - s.center.x, dy = wy - s.center.y, dz = wz - s.center.z;
      float dist = std::sqrt(dx*dx + dy*dy + dz*dz);
      if (dist < (s.radius + radius) * (1.0f - overlap)) {
        too_close = true;
        break;
      }
    }

    if (!too_close) {
      spheres->push_back({{wx, wy, wz}, radius});
    }
  }
}

// ============================================================================
// Particles to SDF
// ============================================================================

void ParticlesToSDF(const std::vector<Particle>& particles,
                    float voxel_size,
                    float band_width,
                    DenseGrid* grid) {
  if (!grid || particles.empty()) return;

  // Compute AABB of all particles
  float bmin_x = 1e30f, bmin_y = 1e30f, bmin_z = 1e30f;
  float bmax_x = -1e30f, bmax_y = -1e30f, bmax_z = -1e30f;
  float max_radius = 0.0f;
  for (const auto& p : particles) {
    bmin_x = std::min(bmin_x, p.position.x - p.radius);
    bmin_y = std::min(bmin_y, p.position.y - p.radius);
    bmin_z = std::min(bmin_z, p.position.z - p.radius);
    bmax_x = std::max(bmax_x, p.position.x + p.radius);
    bmax_y = std::max(bmax_y, p.position.y + p.radius);
    bmax_z = std::max(bmax_z, p.position.z + p.radius);
    max_radius = std::max(max_radius, p.radius);
  }

  float pad = (band_width + 2.0f) * voxel_size;
  bmin_x -= pad; bmin_y -= pad; bmin_z -= pad;
  bmax_x += pad; bmax_y += pad; bmax_z += pad;

  int nx = static_cast<int>(std::ceil((bmax_x - bmin_x) / voxel_size)) + 1;
  int ny = static_cast<int>(std::ceil((bmax_y - bmin_y) / voxel_size)) + 1;
  int nz = static_cast<int>(std::ceil((bmax_z - bmin_z) / voxel_size)) + 1;

  grid->nx = nx; grid->ny = ny; grid->nz = nz;
  grid->ox = bmin_x; grid->oy = bmin_y; grid->oz = bmin_z;
  grid->voxel_size = voxel_size;

  assert(voxel_size > 0.0f);
  float bg = band_width * voxel_size;
  grid->data.assign(static_cast<size_t>(nx) * ny * nz, bg);

  float inv_vs = 1.0f / voxel_size;
  float band_dist = band_width * voxel_size;

  // Stamp each particle as a sphere SDF
  for (const auto& p : particles) {
    float expand = p.radius + band_dist;
    int ix0 = std::max(0, static_cast<int>(std::floor((p.position.x - expand - bmin_x) * inv_vs)));
    int iy0 = std::max(0, static_cast<int>(std::floor((p.position.y - expand - bmin_y) * inv_vs)));
    int iz0 = std::max(0, static_cast<int>(std::floor((p.position.z - expand - bmin_z) * inv_vs)));
    int ix1 = std::min(nx-1, static_cast<int>(std::floor((p.position.x + expand - bmin_x) * inv_vs)));
    int iy1 = std::min(ny-1, static_cast<int>(std::floor((p.position.y + expand - bmin_y) * inv_vs)));
    int iz1 = std::min(nz-1, static_cast<int>(std::floor((p.position.z + expand - bmin_z) * inv_vs)));

    for (int iz = iz0; iz <= iz1; ++iz) {
      float dz = bmin_z + (iz + 0.5f) * voxel_size - p.position.z;
      for (int iy = iy0; iy <= iy1; ++iy) {
        float dy = bmin_y + (iy + 0.5f) * voxel_size - p.position.y;
        for (int ix = ix0; ix <= ix1; ++ix) {
          float dx = bmin_x + (ix + 0.5f) * voxel_size - p.position.x;
          float dist = std::sqrt(dx*dx + dy*dy + dz*dz) - p.radius;
          float& cell = grid->at(ix, iy, iz);
          if (dist < cell) cell = dist;
        }
      }
    }
  }
}

// ============================================================================
// Fracture
// ============================================================================

void Fracture(const DenseGrid& volume,
              const std::vector<DenseGrid>& cutters,
              std::vector<DenseGrid>* pieces) {
  if (!pieces || cutters.empty()) return;
  pieces->clear();

  // Each cutter plane divides the volume into 2 halves.
  // With N cutters, we get up to 2^N pieces.
  // For each combination of cutter signs, intersect volume with
  // all cutter positive/negative halves.

  const int num_cutters = static_cast<int>(cutters.size());
  if (num_cutters > 20) return;  // guard against combinatorial explosion
  for (const auto& c : cutters)
    if (c.data.size() != volume.data.size()) return;

  const int num_combos = 1 << num_cutters;
  const size_t N = volume.data.size();

  for (int combo = 0; combo < num_combos; ++combo) {
    DenseGrid piece;
    CSGCopyMeta(volume, &piece);

    // Single-pass: compute volume ∩ cutter_0^± ∩ cutter_1^± ∩ ...
    bool has_interior = false;
    for (size_t i = 0; i < N; ++i) {
      float val = volume.data[i];
      for (int c = 0; c < num_cutters; ++c) {
        float cv = ((combo >> c) & 1) ? cutters[c].data[i] : -cutters[c].data[i];
        val = std::max(val, cv);
      }
      piece.data[i] = val;
      if (val < 0.0f) has_interior = true;
    }

    if (has_interior) pieces->push_back(std::move(piece));
  }
}

}  // namespace tvdb_ops

#endif  // TINYVDB_OPS_IMPLEMENTATION
