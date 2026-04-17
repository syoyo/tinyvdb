#pragma once
//
// tinyvdb_ops.h — Grid operations for SDF processing and physics simulation.
//
// Public C++ API providing operations on DenseGrid:
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
// Implementation is provided by src/tinyvdb_ops.cc.
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
float CentralDiffX(const DenseGrid& g, int ix, int iy, int iz);
float CentralDiffY(const DenseGrid& g, int ix, int iy, int iz);
float CentralDiffZ(const DenseGrid& g, int ix, int iy, int iz);

/// Forward difference.
float ForwardDiffX(const DenseGrid& g, int ix, int iy, int iz);
float ForwardDiffY(const DenseGrid& g, int ix, int iy, int iz);
float ForwardDiffZ(const DenseGrid& g, int ix, int iy, int iz);

/// Backward difference.
float BackwardDiffX(const DenseGrid& g, int ix, int iy, int iz);
float BackwardDiffY(const DenseGrid& g, int ix, int iy, int iz);
float BackwardDiffZ(const DenseGrid& g, int ix, int iy, int iz);

/// 6-point Laplacian stencil at voxel (ix, iy, iz).
float LaplacianStencil(const DenseGrid& g, int ix, int iy, int iz);

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
