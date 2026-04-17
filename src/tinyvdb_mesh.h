#pragma once
//
// tinyvdb_mesh.h — Mesh-to-SDF and SDF-to-Mesh (marching cubes) utilities.
//
// Public C++ API for:
//   - Triangle mesh → signed distance field (dense 3D grid)
//   - Signed distance field → triangle mesh (marching cubes)
//   - Manifold preprocessing (mesh → SDF → mesh round-trip)
//
// Part of TinyVDB. Compatible with TinyVDB data structures but does not
// depend on the TinyVDB I/O library itself.
//
// Implementation is provided by src/tinyvdb_mesh.cc.
//
// License: MIT
//

#include <cassert>
#include <cstdint>
#include <vector>

namespace tvdb_mesh {

// ---- Data types ----

struct Vec3f {
  float x, y, z;
};

struct Triangle {
  uint32_t v0, v1, v2;
};

struct TriangleMesh {
  std::vector<Vec3f> vertices;
  std::vector<Triangle> faces;
};

// Dense 3D scalar grid (float).
struct DenseGrid {
  int nx, ny, nz;       // dimensions
  float ox, oy, oz;     // origin (world-space min corner)
  float voxel_size;
  std::vector<float> data;  // nx * ny * nz, row-major (x fastest)

  float& at(int x, int y, int z) {
    assert(x >= 0 && x < nx && y >= 0 && y < ny && z >= 0 && z < nz);
    return data[x + nx * (y + ny * z)];
  }
  float at(int x, int y, int z) const {
    assert(x >= 0 && x < nx && y >= 0 && y < ny && z >= 0 && z < nz);
    return data[x + nx * (y + ny * z)];
  }
};

// ---- API ----

/// Convert a triangle mesh to a signed distance field.
/// @param mesh       Input triangle mesh.
/// @param voxel_size Size of each voxel in world units.
///                   Typical: (mesh_max_extent / resolution), e.g. for resolution=50.
/// @param band_width Half-width of the narrow band in voxels (default 3.0).
/// @param grid       Output dense grid.
/// @return true on success.
bool MeshToSDF(const TriangleMesh& mesh,
               float voxel_size,
               float band_width,
               DenseGrid* grid);

/// Extract a triangle mesh from a signed distance field via marching cubes.
/// @param grid     Input dense SDF grid.
/// @param isovalue Isosurface value (default 0.0 for SDF surface; CoACD uses 0.55).
/// @param mesh     Output triangle mesh.
/// @return true on success.
bool SDFToMesh(const DenseGrid& grid,
               float isovalue,
               TriangleMesh* mesh);

/// Manifold preprocessing: mesh → SDF → mesh round-trip.
/// Equivalent to OpenVDB's meshToSignedDistanceField + volumeToMesh
/// as used by CoACD's SDFManifold().
/// @param input      Input (possibly non-manifold) triangle mesh.
/// @param resolution Voxel resolution scale factor (default 50). The mesh is
///                   scaled so that its longest axis spans this many voxels.
/// @param isovalue   Isosurface extraction value (default 0.55).
/// @param output     Output manifold triangle mesh.
/// @return true on success.
bool MakeManifold(const TriangleMesh& input,
                  double resolution,
                  double isovalue,
                  TriangleMesh* output);

/// Sign determination method for SDF computation.
enum SignMethod {
  kSignFloodFill = 0,  // Exterior flood fill (fast, robust for most meshes)
  kSignSweep = 1,      // Directional sweep + iterative propagation (OpenVDB-style)
};

/// Fast SDF computation using triangle AABB rasterization and configurable
/// sign determination.
/// @param sign_method  kSignFloodFill (default) or kSignSweep (OpenVDB-style).
bool MeshToSDF_VDB(const TriangleMesh& mesh,
                   float voxel_size,
                   float band_width,
                   DenseGrid* grid,
                   SignMethod sign_method = kSignFloodFill);

/// Manifold preprocessing using the VDB-accelerated path.
bool MakeManifold_VDB(const TriangleMesh& input,
                      double resolution,
                      double isovalue,
                      TriangleMesh* output,
                      SignMethod sign_method = kSignFloodFill);

}  // namespace tvdb_mesh
