#pragma once
//
// tinyvdbio_mesh.h — Mesh-to-SDF and SDF-to-Mesh (marching cubes) utilities.
//
// This is a self-contained, header-only C++ module that provides:
//   - Triangle mesh → signed distance field (dense 3D grid)
//   - Signed distance field → triangle mesh (marching cubes)
//   - Manifold preprocessing (mesh → SDF → mesh round-trip)
//
// Designed to be compatible with tinyvdbio data structures but does not
// depend on the tinyvdbio I/O library itself.
//
// Usage:
//   In exactly ONE .cc file:
//     #define TINYVDBIO_MESH_IMPLEMENTATION
//     #include "tinyvdbio_mesh.h"
//
// License: MIT
//

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

  float& at(int x, int y, int z) { return data[x + nx * (y + ny * z)]; }
  float  at(int x, int y, int z) const { return data[x + nx * (y + ny * z)]; }
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


// ============================================================================
// Implementation
// ============================================================================

#ifdef TINYVDBIO_MESH_IMPLEMENTATION

#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstring>
#include <limits>
#include <unordered_map>

namespace tvdb_mesh {

// Operators in the tvdb_mesh namespace so ADL finds them for Vec3f.
inline Vec3f operator-(const Vec3f& a, const Vec3f& b) {
  return {a.x - b.x, a.y - b.y, a.z - b.z};
}
inline Vec3f operator+(const Vec3f& a, const Vec3f& b) {
  return {a.x + b.x, a.y + b.y, a.z + b.z};
}
inline Vec3f operator*(const Vec3f& a, float s) {
  return {a.x * s, a.y * s, a.z * s};
}

namespace detail {

// ---- Vector math ----
inline float dot(const Vec3f& a, const Vec3f& b) {
  return a.x * b.x + a.y * b.y + a.z * b.z;
}
inline Vec3f cross(const Vec3f& a, const Vec3f& b) {
  return {a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x};
}
inline float length(const Vec3f& v) {
  return std::sqrt(dot(v, v));
}
inline Vec3f vmin(const Vec3f& a, const Vec3f& b) {
  return {std::min(a.x, b.x), std::min(a.y, b.y), std::min(a.z, b.z)};
}
inline Vec3f vmax(const Vec3f& a, const Vec3f& b) {
  return {std::max(a.x, b.x), std::max(a.y, b.y), std::max(a.z, b.z)};
}

// ---- Point-to-triangle distance ----

// Compute squared distance from point p to triangle (a, b, c).
float PointTriangleDistSq(const Vec3f& p, const Vec3f& a, const Vec3f& b, const Vec3f& c) {
  Vec3f ab = b - a, ac = c - a, ap = p - a;
  float d1 = dot(ab, ap), d2 = dot(ac, ap);
  if (d1 <= 0.0f && d2 <= 0.0f) {
    Vec3f d = p - a;
    return dot(d, d);
  }

  Vec3f bp = p - b;
  float d3 = dot(ab, bp), d4 = dot(ac, bp);
  if (d3 >= 0.0f && d4 <= d3) {
    Vec3f d = p - b;
    return dot(d, d);
  }

  float vc = d1 * d4 - d3 * d2;
  if (vc <= 0.0f && d1 >= 0.0f && d3 <= 0.0f) {
    float v = d1 / (d1 - d3);
    Vec3f closest = a + ab * v;
    Vec3f d = p - closest;
    return dot(d, d);
  }

  Vec3f cp = p - c;
  float d5 = dot(ab, cp), d6 = dot(ac, cp);
  if (d6 >= 0.0f && d5 <= d6) {
    Vec3f d = p - c;
    return dot(d, d);
  }

  float vb = d5 * d2 - d1 * d6;
  if (vb <= 0.0f && d2 >= 0.0f && d6 <= 0.0f) {
    float w = d2 / (d2 - d6);
    Vec3f closest = a + ac * w;
    Vec3f d = p - closest;
    return dot(d, d);
  }

  float va = d3 * d6 - d5 * d4;
  if (va <= 0.0f && (d4 - d3) >= 0.0f && (d5 - d6) >= 0.0f) {
    float w = (d4 - d3) / ((d4 - d3) + (d5 - d6));
    Vec3f closest = b + (c - b) * w;
    Vec3f d = p - closest;
    return dot(d, d);
  }

  float denom = 1.0f / (va + vb + vc);
  float v = vb * denom;
  float w = vc * denom;
  Vec3f closest = a + ab * v + ac * w;
  Vec3f d = p - closest;
  return dot(d, d);
}

// ---- Marching cubes tables ----
// Standard marching cubes edge table and triangle table.

static const int MC_EDGE_TABLE[256] = {
  0x0  , 0x109, 0x203, 0x30a, 0x406, 0x50f, 0x605, 0x70c,
  0x80c, 0x905, 0xa0f, 0xb06, 0xc0a, 0xd03, 0xe09, 0xf00,
  0x190, 0x99 , 0x393, 0x29a, 0x596, 0x49f, 0x795, 0x69c,
  0x99c, 0x895, 0xb9f, 0xa96, 0xd9a, 0xc93, 0xf99, 0xe90,
  0x230, 0x339, 0x33 , 0x13a, 0x636, 0x73f, 0x435, 0x53c,
  0xa3c, 0xb35, 0x83f, 0x936, 0xe3a, 0xf33, 0xc39, 0xd30,
  0x3a0, 0x2a9, 0x1a3, 0xaa , 0x7a6, 0x6af, 0x5a5, 0x4ac,
  0xbac, 0xaa5, 0x9af, 0x8a6, 0xfaa, 0xea3, 0xda9, 0xca0,
  0x460, 0x569, 0x663, 0x76a, 0x66 , 0x16f, 0x265, 0x36c,
  0xc6c, 0xd65, 0xe6f, 0xf66, 0x86a, 0x963, 0xa69, 0xb60,
  0x5f0, 0x4f9, 0x7f3, 0x6fa, 0x1f6, 0xff , 0x3f5, 0x2fc,
  0xdfc, 0xcf5, 0xfff, 0xef6, 0x9fa, 0x8f3, 0xbf9, 0xaf0,
  0x650, 0x759, 0x453, 0x55a, 0x256, 0x35f, 0x55 , 0x15c,
  0xe5c, 0xf55, 0xc5f, 0xd56, 0xa5a, 0xb53, 0x859, 0x950,
  0x7c0, 0x6c9, 0x5c3, 0x4ca, 0x3c6, 0x2cf, 0x1c5, 0xcc ,
  0xfcc, 0xec5, 0xdcf, 0xcc6, 0xbca, 0xac3, 0x9c9, 0x8c0,
  0x8c0, 0x9c9, 0xac3, 0xbca, 0xcc6, 0xdcf, 0xec5, 0xfcc,
  0xcc , 0x1c5, 0x2cf, 0x3c6, 0x4ca, 0x5c3, 0x6c9, 0x7c0,
  0x950, 0x859, 0xb53, 0xa5a, 0xd56, 0xc5f, 0xf55, 0xe5c,
  0x15c, 0x55 , 0x35f, 0x256, 0x55a, 0x453, 0x759, 0x650,
  0xaf0, 0xbf9, 0x8f3, 0x9fa, 0xef6, 0xfff, 0xcf5, 0xdfc,
  0x2fc, 0x3f5, 0xff , 0x1f6, 0x6fa, 0x7f3, 0x4f9, 0x5f0,
  0xb60, 0xa69, 0x963, 0x86a, 0xf66, 0xe6f, 0xd65, 0xc6c,
  0x36c, 0x265, 0x16f, 0x66 , 0x76a, 0x663, 0x569, 0x460,
  0xca0, 0xda9, 0xea3, 0xfaa, 0x8a6, 0x9af, 0xaa5, 0xbac,
  0x4ac, 0x5a5, 0x6af, 0x7a6, 0xaa , 0x1a3, 0x2a9, 0x3a0,
  0xd30, 0xc39, 0xf33, 0xe3a, 0x936, 0x83f, 0xb35, 0xa3c,
  0x53c, 0x435, 0x73f, 0x636, 0x13a, 0x33 , 0x339, 0x230,
  0xe90, 0xf99, 0xc93, 0xd9a, 0xa96, 0xb9f, 0x895, 0x99c,
  0x69c, 0x795, 0x49f, 0x596, 0x29a, 0x393, 0x99 , 0x190,
  0xf00, 0xe09, 0xd03, 0xc0a, 0xb06, 0xa0f, 0x905, 0x80c,
  0x70c, 0x605, 0x50f, 0x406, 0x30a, 0x203, 0x109, 0x0
};

static const int MC_TRI_TABLE[256][16] = {
  {-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,8,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,1,9,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,8,3,9,8,1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,8,3,1,2,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,2,10,0,2,9,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {2,8,3,2,10,8,10,9,8,-1,-1,-1,-1,-1,-1,-1},
  {3,11,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,11,2,8,11,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,9,0,2,3,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,11,2,1,9,11,9,8,11,-1,-1,-1,-1,-1,-1,-1},
  {3,10,1,11,10,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,10,1,0,8,10,8,11,10,-1,-1,-1,-1,-1,-1,-1},
  {3,9,0,3,11,9,11,10,9,-1,-1,-1,-1,-1,-1,-1},
  {9,8,10,10,8,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,7,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,3,0,7,3,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,1,9,8,4,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,1,9,4,7,1,7,3,1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,8,4,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,4,7,3,0,4,1,2,10,-1,-1,-1,-1,-1,-1,-1},
  {9,2,10,9,0,2,8,4,7,-1,-1,-1,-1,-1,-1,-1},
  {2,10,9,2,9,7,2,7,3,7,9,4,-1,-1,-1,-1},
  {8,4,7,3,11,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {11,4,7,11,2,4,2,0,4,-1,-1,-1,-1,-1,-1,-1},
  {9,0,1,8,4,7,2,3,11,-1,-1,-1,-1,-1,-1,-1},
  {4,7,11,9,4,11,9,11,2,9,2,1,-1,-1,-1,-1},
  {3,10,1,3,11,10,7,8,4,-1,-1,-1,-1,-1,-1,-1},
  {1,11,10,1,4,11,1,0,4,7,11,4,-1,-1,-1,-1},
  {4,7,8,9,0,11,9,11,10,11,0,3,-1,-1,-1,-1},
  {4,7,11,4,11,9,9,11,10,-1,-1,-1,-1,-1,-1,-1},
  {9,5,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,5,4,0,8,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,5,4,1,5,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {8,5,4,8,3,5,3,1,5,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,9,5,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,0,8,1,2,10,4,9,5,-1,-1,-1,-1,-1,-1,-1},
  {5,2,10,5,4,2,4,0,2,-1,-1,-1,-1,-1,-1,-1},
  {2,10,5,3,2,5,3,5,4,3,4,8,-1,-1,-1,-1},
  {9,5,4,2,3,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,11,2,0,8,11,4,9,5,-1,-1,-1,-1,-1,-1,-1},
  {0,5,4,0,1,5,2,3,11,-1,-1,-1,-1,-1,-1,-1},
  {2,1,5,2,5,8,2,8,11,4,8,5,-1,-1,-1,-1},
  {10,3,11,10,1,3,9,5,4,-1,-1,-1,-1,-1,-1,-1},
  {4,9,5,0,8,1,8,10,1,8,11,10,-1,-1,-1,-1},
  {5,4,0,5,0,11,5,11,10,11,0,3,-1,-1,-1,-1},
  {5,4,8,5,8,10,10,8,11,-1,-1,-1,-1,-1,-1,-1},
  {9,7,8,5,7,9,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,3,0,9,5,3,5,7,3,-1,-1,-1,-1,-1,-1,-1},
  {0,7,8,0,1,7,1,5,7,-1,-1,-1,-1,-1,-1,-1},
  {1,5,3,3,5,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,7,8,9,5,7,10,1,2,-1,-1,-1,-1,-1,-1,-1},
  {10,1,2,9,5,0,5,3,0,5,7,3,-1,-1,-1,-1},
  {8,0,2,8,2,5,8,5,7,10,5,2,-1,-1,-1,-1},
  {2,10,5,2,5,3,3,5,7,-1,-1,-1,-1,-1,-1,-1},
  {7,9,5,7,8,9,3,11,2,-1,-1,-1,-1,-1,-1,-1},
  {9,5,7,9,7,2,9,2,0,2,7,11,-1,-1,-1,-1},
  {2,3,11,0,1,8,1,7,8,1,5,7,-1,-1,-1,-1},
  {11,2,1,11,1,7,7,1,5,-1,-1,-1,-1,-1,-1,-1},
  {9,5,8,8,5,7,10,1,3,10,3,11,-1,-1,-1,-1},
  {5,7,0,5,0,9,7,11,0,1,0,10,11,10,0,-1},
  {11,10,0,11,0,3,10,5,0,8,0,7,5,7,0,-1},
  {11,10,5,7,11,5,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {10,6,5,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,8,3,5,10,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,0,1,5,10,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,8,3,1,9,8,5,10,6,-1,-1,-1,-1,-1,-1,-1},
  {1,6,5,2,6,1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,6,5,1,2,6,3,0,8,-1,-1,-1,-1,-1,-1,-1},
  {9,6,5,9,0,6,0,2,6,-1,-1,-1,-1,-1,-1,-1},
  {5,9,8,5,8,2,5,2,6,3,2,8,-1,-1,-1,-1},
  {2,3,11,10,6,5,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {11,0,8,11,2,0,10,6,5,-1,-1,-1,-1,-1,-1,-1},
  {0,1,9,2,3,11,5,10,6,-1,-1,-1,-1,-1,-1,-1},
  {5,10,6,1,9,2,9,11,2,9,8,11,-1,-1,-1,-1},
  {6,3,11,6,5,3,5,1,3,-1,-1,-1,-1,-1,-1,-1},
  {0,8,11,0,11,5,0,5,1,5,11,6,-1,-1,-1,-1},
  {3,11,6,0,3,6,0,6,5,0,5,9,-1,-1,-1,-1},
  {6,5,9,6,9,11,11,9,8,-1,-1,-1,-1,-1,-1,-1},
  {5,10,6,4,7,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,3,0,4,7,3,6,5,10,-1,-1,-1,-1,-1,-1,-1},
  {1,9,0,5,10,6,8,4,7,-1,-1,-1,-1,-1,-1,-1},
  {10,6,5,1,9,7,1,7,3,7,9,4,-1,-1,-1,-1},
  {6,1,2,6,5,1,4,7,8,-1,-1,-1,-1,-1,-1,-1},
  {1,2,5,5,2,6,3,0,4,3,4,7,-1,-1,-1,-1},
  {8,4,7,9,0,5,0,6,5,0,2,6,-1,-1,-1,-1},
  {7,3,9,7,9,4,3,2,9,5,9,6,2,6,9,-1},
  {3,11,2,7,8,4,10,6,5,-1,-1,-1,-1,-1,-1,-1},
  {5,10,6,4,7,2,4,2,0,2,7,11,-1,-1,-1,-1},
  {0,1,9,4,7,8,2,3,11,5,10,6,-1,-1,-1,-1},
  {9,2,1,9,11,2,9,4,11,7,11,4,5,10,6,-1},
  {8,4,7,3,11,5,3,5,1,5,11,6,-1,-1,-1,-1},
  {5,1,11,5,11,6,1,0,11,7,11,4,0,4,11,-1},
  {0,5,9,0,6,5,0,3,6,11,6,3,8,4,7,-1},
  {6,5,9,6,9,11,4,7,9,7,11,9,-1,-1,-1,-1},
  {10,4,9,6,4,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,10,6,4,9,10,0,8,3,-1,-1,-1,-1,-1,-1,-1},
  {10,0,1,10,6,0,6,4,0,-1,-1,-1,-1,-1,-1,-1},
  {8,3,1,8,1,6,8,6,4,6,1,10,-1,-1,-1,-1},
  {1,4,9,1,2,4,2,6,4,-1,-1,-1,-1,-1,-1,-1},
  {3,0,8,1,2,9,2,4,9,2,6,4,-1,-1,-1,-1},
  {0,2,4,4,2,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {8,3,2,8,2,4,4,2,6,-1,-1,-1,-1,-1,-1,-1},
  {10,4,9,10,6,4,11,2,3,-1,-1,-1,-1,-1,-1,-1},
  {0,8,2,2,8,11,4,9,10,4,10,6,-1,-1,-1,-1},
  {3,11,2,0,1,6,0,6,4,6,1,10,-1,-1,-1,-1},
  {6,4,1,6,1,10,4,8,1,2,1,11,8,11,1,-1},
  {9,6,4,9,3,6,9,1,3,11,6,3,-1,-1,-1,-1},
  {8,11,1,8,1,0,11,6,1,9,1,4,6,4,1,-1},
  {3,11,6,3,6,0,0,6,4,-1,-1,-1,-1,-1,-1,-1},
  {6,4,8,11,6,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {7,10,6,7,8,10,8,9,10,-1,-1,-1,-1,-1,-1,-1},
  {0,7,3,0,10,7,0,9,10,6,7,10,-1,-1,-1,-1},
  {10,6,7,1,10,7,1,7,8,1,8,0,-1,-1,-1,-1},
  {10,6,7,10,7,1,1,7,3,-1,-1,-1,-1,-1,-1,-1},
  {1,2,6,1,6,8,1,8,9,8,6,7,-1,-1,-1,-1},
  {2,6,9,2,9,1,6,7,9,0,9,3,7,3,9,-1},
  {7,8,0,7,0,6,6,0,2,-1,-1,-1,-1,-1,-1,-1},
  {7,3,2,6,7,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {2,3,11,10,6,8,10,8,9,8,6,7,-1,-1,-1,-1},
  {2,0,7,2,7,11,0,9,7,6,7,10,9,10,7,-1},
  {1,8,0,1,7,8,1,10,7,6,7,10,2,3,11,-1},
  {11,2,1,11,1,7,10,6,1,6,7,1,-1,-1,-1,-1},
  {8,9,6,8,6,7,9,1,6,11,6,3,1,3,6,-1},
  {0,9,1,11,6,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {7,8,0,7,0,6,3,11,0,11,6,0,-1,-1,-1,-1},
  {7,11,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {7,6,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,0,8,11,7,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,1,9,11,7,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {8,1,9,8,3,1,11,7,6,-1,-1,-1,-1,-1,-1,-1},
  {10,1,2,6,11,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,3,0,8,6,11,7,-1,-1,-1,-1,-1,-1,-1},
  {2,9,0,2,10,9,6,11,7,-1,-1,-1,-1,-1,-1,-1},
  {6,11,7,2,10,3,10,8,3,10,9,8,-1,-1,-1,-1},
  {7,2,3,6,2,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {7,0,8,7,6,0,6,2,0,-1,-1,-1,-1,-1,-1,-1},
  {2,7,6,2,3,7,0,1,9,-1,-1,-1,-1,-1,-1,-1},
  {1,6,2,1,8,6,1,9,8,8,7,6,-1,-1,-1,-1},
  {10,7,6,10,1,7,1,3,7,-1,-1,-1,-1,-1,-1,-1},
  {10,7,6,1,7,10,1,8,7,1,0,8,-1,-1,-1,-1},
  {0,3,7,0,7,10,0,10,9,6,10,7,-1,-1,-1,-1},
  {7,6,10,7,10,8,8,10,9,-1,-1,-1,-1,-1,-1,-1},
  {6,8,4,11,8,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,6,11,3,0,6,0,4,6,-1,-1,-1,-1,-1,-1,-1},
  {8,6,11,8,4,6,9,0,1,-1,-1,-1,-1,-1,-1,-1},
  {9,4,6,9,6,3,9,3,1,11,3,6,-1,-1,-1,-1},
  {6,8,4,6,11,8,2,10,1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,3,0,11,0,6,11,0,4,6,-1,-1,-1,-1},
  {4,11,8,4,6,11,0,2,9,2,10,9,-1,-1,-1,-1},
  {10,9,3,10,3,2,9,4,3,11,3,6,4,6,3,-1},
  {8,2,3,8,4,2,4,6,2,-1,-1,-1,-1,-1,-1,-1},
  {0,4,2,4,6,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,9,0,2,3,4,2,4,6,4,3,8,-1,-1,-1,-1},
  {1,9,4,1,4,2,2,4,6,-1,-1,-1,-1,-1,-1,-1},
  {8,1,3,8,6,1,8,4,6,6,10,1,-1,-1,-1,-1},
  {10,1,0,10,0,6,6,0,4,-1,-1,-1,-1,-1,-1,-1},
  {4,6,3,4,3,8,6,10,3,0,3,9,10,9,3,-1},
  {10,9,4,6,10,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,9,5,7,6,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,8,3,4,9,5,11,7,6,-1,-1,-1,-1,-1,-1,-1},
  {5,0,1,5,4,0,7,6,11,-1,-1,-1,-1,-1,-1,-1},
  {11,7,6,8,3,4,3,5,4,3,1,5,-1,-1,-1,-1},
  {9,5,4,10,1,2,7,6,11,-1,-1,-1,-1,-1,-1,-1},
  {6,11,7,1,2,10,0,8,3,4,9,5,-1,-1,-1,-1},
  {7,6,11,5,4,10,4,2,10,4,0,2,-1,-1,-1,-1},
  {3,4,8,3,5,4,3,2,5,10,5,2,11,7,6,-1},
  {7,2,3,7,6,2,5,4,9,-1,-1,-1,-1,-1,-1,-1},
  {9,5,4,0,8,6,0,6,2,6,8,7,-1,-1,-1,-1},
  {3,6,2,3,7,6,1,5,0,5,4,0,-1,-1,-1,-1},
  {6,2,8,6,8,7,2,1,8,4,8,5,1,5,8,-1},
  {9,5,4,10,1,6,1,7,6,1,3,7,-1,-1,-1,-1},
  {1,6,10,1,7,6,1,0,7,8,7,0,9,5,4,-1},
  {4,0,10,4,10,5,0,3,10,6,10,7,3,7,10,-1},
  {7,6,10,7,10,8,5,4,10,4,8,10,-1,-1,-1,-1},
  {6,9,5,6,11,9,11,8,9,-1,-1,-1,-1,-1,-1,-1},
  {3,6,11,0,6,3,0,5,6,0,9,5,-1,-1,-1,-1},
  {0,11,8,0,5,11,0,1,5,5,6,11,-1,-1,-1,-1},
  {6,11,3,6,3,5,5,3,1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,10,9,5,11,9,11,8,11,5,6,-1,-1,-1,-1},
  {0,11,3,0,6,11,0,9,6,5,6,9,1,2,10,-1},
  {11,8,5,11,5,6,8,0,5,10,5,2,0,2,5,-1},
  {6,11,3,6,3,5,2,10,3,10,5,3,-1,-1,-1,-1},
  {5,8,9,5,2,8,5,6,2,3,8,2,-1,-1,-1,-1},
  {9,5,6,9,6,0,0,6,2,-1,-1,-1,-1,-1,-1,-1},
  {1,5,8,1,8,0,5,6,8,3,8,2,6,2,8,-1},
  {1,5,6,2,1,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,3,6,1,6,10,3,8,6,5,6,9,8,9,6,-1},
  {10,1,0,10,0,6,9,5,0,5,6,0,-1,-1,-1,-1},
  {0,3,8,5,6,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {10,5,6,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {11,5,10,7,5,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {11,5,10,11,7,5,8,3,0,-1,-1,-1,-1,-1,-1,-1},
  {5,11,7,5,10,11,1,9,0,-1,-1,-1,-1,-1,-1,-1},
  {10,7,5,10,11,7,9,8,1,8,3,1,-1,-1,-1,-1},
  {11,1,2,11,7,1,7,5,1,-1,-1,-1,-1,-1,-1,-1},
  {0,8,3,1,2,7,1,7,5,7,2,11,-1,-1,-1,-1},
  {9,7,5,9,2,7,9,0,2,2,11,7,-1,-1,-1,-1},
  {7,5,2,7,2,11,5,9,2,3,2,8,9,8,2,-1},
  {2,5,10,2,3,5,3,7,5,-1,-1,-1,-1,-1,-1,-1},
  {8,2,0,8,5,2,8,7,5,10,2,5,-1,-1,-1,-1},
  {9,0,1,5,10,3,5,3,7,3,10,2,-1,-1,-1,-1},
  {9,8,2,9,2,1,8,7,2,10,2,5,7,5,2,-1},
  {1,3,5,3,7,5,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,8,7,0,7,1,1,7,5,-1,-1,-1,-1,-1,-1,-1},
  {9,0,3,9,3,5,5,3,7,-1,-1,-1,-1,-1,-1,-1},
  {9,8,7,5,9,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {5,8,4,5,10,8,10,11,8,-1,-1,-1,-1,-1,-1,-1},
  {5,0,4,5,11,0,5,10,11,11,3,0,-1,-1,-1,-1},
  {0,1,9,8,4,10,8,10,11,10,4,5,-1,-1,-1,-1},
  {10,11,4,10,4,5,11,3,4,9,4,1,3,1,4,-1},
  {2,5,1,2,8,5,2,11,8,4,5,8,-1,-1,-1,-1},
  {0,4,11,0,11,3,4,5,11,2,11,1,5,1,11,-1},
  {0,2,5,0,5,9,2,11,5,4,5,8,11,8,5,-1},
  {9,4,5,2,11,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {2,5,10,3,5,2,3,4,5,3,8,4,-1,-1,-1,-1},
  {5,10,2,5,2,4,4,2,0,-1,-1,-1,-1,-1,-1,-1},
  {3,10,2,3,5,10,3,8,5,4,5,8,0,1,9,-1},
  {5,10,2,5,2,4,1,9,2,9,4,2,-1,-1,-1,-1},
  {8,4,5,8,5,3,3,5,1,-1,-1,-1,-1,-1,-1,-1},
  {0,4,5,1,0,5,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {8,4,5,8,5,3,9,0,5,0,3,5,-1,-1,-1,-1},
  {9,4,5,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,11,7,4,9,11,9,10,11,-1,-1,-1,-1,-1,-1,-1},
  {0,8,3,4,9,7,9,11,7,9,10,11,-1,-1,-1,-1},
  {1,10,11,1,11,4,1,4,0,7,4,11,-1,-1,-1,-1},
  {3,1,4,3,4,8,1,10,4,7,4,11,10,11,4,-1},
  {4,11,7,9,11,4,9,2,11,9,1,2,-1,-1,-1,-1},
  {9,7,4,9,11,7,9,1,11,2,11,1,0,8,3,-1},
  {11,7,4,11,4,2,2,4,0,-1,-1,-1,-1,-1,-1,-1},
  {11,7,4,11,4,2,8,3,4,3,2,4,-1,-1,-1,-1},
  {2,9,10,2,7,9,2,3,7,7,4,9,-1,-1,-1,-1},
  {9,10,7,9,7,4,10,2,7,8,7,0,2,0,7,-1},
  {3,7,10,3,10,2,7,4,10,1,10,0,4,0,10,-1},
  {1,10,2,8,7,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,9,1,4,1,7,7,1,3,-1,-1,-1,-1,-1,-1,-1},
  {4,9,1,4,1,7,0,8,1,8,7,1,-1,-1,-1,-1},
  {4,0,3,7,4,3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {4,8,7,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {9,10,8,10,11,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,0,9,3,9,11,11,9,10,-1,-1,-1,-1,-1,-1,-1},
  {0,1,10,0,10,8,8,10,11,-1,-1,-1,-1,-1,-1,-1},
  {3,1,10,11,3,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,2,11,1,11,9,9,11,8,-1,-1,-1,-1,-1,-1,-1},
  {3,0,9,3,9,11,1,2,9,2,11,9,-1,-1,-1,-1},
  {0,2,11,8,0,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {3,2,11,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {2,3,8,2,8,10,10,8,9,-1,-1,-1,-1,-1,-1,-1},
  {9,10,2,0,9,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {2,3,8,2,8,10,0,1,8,1,10,8,-1,-1,-1,-1},
  {1,10,2,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {1,3,8,9,1,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,9,1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {0,3,8,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
  {-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1}
};

// ---- Vertex interpolation on a cube edge ----
inline Vec3f VertexInterp(float iso, const Vec3f& p1, const Vec3f& p2, float v1, float v2) {
  if (std::abs(v1 - v2) < 1e-10f) return p1;
  float mu = (iso - v1) / (v2 - v1);
  return {p1.x + mu * (p2.x - p1.x),
          p1.y + mu * (p2.y - p1.y),
          p1.z + mu * (p2.z - p1.z)};
}

// Exterior flood fill: negate interior voxels.
// Seed from grid boundary, propagate through voxels with dist > 0.75*vs.
inline void FloodFillSign(DenseGrid* grid) {
  const int nx = grid->nx, ny = grid->ny, nz = grid->nz;
  const float thresh = 0.75f * grid->voxel_size;
  std::vector<uint8_t> exterior(grid->data.size(), 0);
  std::vector<int32_t> queue;
  auto Idx = [&](int x, int y, int z) -> size_t {
    return static_cast<size_t>(x) + nx * (static_cast<size_t>(y) + ny * static_cast<size_t>(z));
  };
  for (int iz = 0; iz < nz; ++iz)
    for (int iy = 0; iy < ny; ++iy)
      for (int ix = 0; ix < nx; ++ix)
        if (ix==0||ix==nx-1||iy==0||iy==ny-1||iz==0||iz==nz-1) {
          exterior[Idx(ix,iy,iz)] = 1;
          queue.push_back(static_cast<int32_t>(Idx(ix,iy,iz)));
        }
  size_t head = 0;
  while (head < queue.size()) {
    int32_t ci = queue[head++];
    int iz = ci / (nx * ny), iy = (ci / nx) % ny, ix = ci % nx;
    static const int dirs[6][3] = {{-1,0,0},{1,0,0},{0,-1,0},{0,1,0},{0,0,-1},{0,0,1}};
    for (const auto& d : dirs) {
      int x2=ix+d[0], y2=iy+d[1], z2=iz+d[2];
      if (x2<0||x2>=nx||y2<0||y2>=ny||z2<0||z2>=nz) continue;
      size_t ni = Idx(x2, y2, z2);
      if (exterior[ni] || grid->data[ni] <= thresh) continue;
      exterior[ni] = 1;
      queue.push_back(static_cast<int32_t>(ni));
    }
  }
  for (size_t i = 0; i < grid->data.size(); ++i)
    if (!exterior[i]) grid->data[i] = -grid->data[i];
}

}  // namespace detail

// ============================================================================
// MeshToSDF
// ============================================================================

bool MeshToSDF(const TriangleMesh& mesh,
               float voxel_size,
               float band_width,
               DenseGrid* grid) {
  if (!grid || mesh.vertices.empty() || mesh.faces.empty()) return false;

  // Compute AABB
  Vec3f bmin = mesh.vertices[0], bmax = mesh.vertices[0];
  for (const auto& v : mesh.vertices) {
    bmin = detail::vmin(bmin, v);
    bmax = detail::vmax(bmax, v);
  }

  // Expand by band_width voxels + 1 for safety
  float pad = (band_width + 2.0f) * voxel_size;
  bmin = bmin - Vec3f{pad, pad, pad};
  bmax = bmax + Vec3f{pad, pad, pad};

  int nx = static_cast<int>(std::ceil((bmax.x - bmin.x) / voxel_size)) + 1;
  int ny = static_cast<int>(std::ceil((bmax.y - bmin.y) / voxel_size)) + 1;
  int nz = static_cast<int>(std::ceil((bmax.z - bmin.z) / voxel_size)) + 1;

  grid->nx = nx;
  grid->ny = ny;
  grid->nz = nz;
  grid->ox = bmin.x;
  grid->oy = bmin.y;
  grid->oz = bmin.z;
  grid->voxel_size = voxel_size;

  float background = band_width * voxel_size;  // large positive distance
  grid->data.assign(static_cast<size_t>(nx) * ny * nz, background);

  // Phase 1: compute unsigned distance to nearest triangle for each voxel
  // within the narrow band.
  float band_dist = band_width * voxel_size;

  for (int iz = 0; iz < nz; ++iz) {
    for (int iy = 0; iy < ny; ++iy) {
      for (int ix = 0; ix < nx; ++ix) {
        Vec3f p = {bmin.x + (ix + 0.5f) * voxel_size,
                   bmin.y + (iy + 0.5f) * voxel_size,
                   bmin.z + (iz + 0.5f) * voxel_size};

        float min_dist_sq = band_dist * band_dist;
        for (const auto& tri : mesh.faces) {
          float dsq = detail::PointTriangleDistSq(
              p, mesh.vertices[tri.v0], mesh.vertices[tri.v1], mesh.vertices[tri.v2]);
          if (dsq < min_dist_sq) min_dist_sq = dsq;
        }

        float dist = std::sqrt(min_dist_sq);
        grid->at(ix, iy, iz) = dist;
      }
    }
  }

  detail::FloodFillSign(grid);
  return true;
}

// ============================================================================
// SDFToMesh (Marching Cubes)
// ============================================================================

bool SDFToMesh(const DenseGrid& grid,
               float isovalue,
               TriangleMesh* mesh) {
  if (!mesh) return false;
  mesh->vertices.clear();
  mesh->faces.clear();

  const int nx = grid.nx, ny = grid.ny, nz = grid.nz;
  if (nx < 2 || ny < 2 || nz < 2) return false;

  // Edge-to-vertex cache: key = edge encoding, value = vertex index
  std::unordered_map<uint64_t, uint32_t> edge_cache;

  auto VoxelPos = [&](int ix, int iy, int iz) -> Vec3f {
    return {grid.ox + (ix + 0.5f) * grid.voxel_size,
            grid.oy + (iy + 0.5f) * grid.voxel_size,
            grid.oz + (iz + 0.5f) * grid.voxel_size};
  };

  auto VoxelIdx = [&](int ix, int iy, int iz) -> uint64_t {
    return static_cast<uint64_t>(ix) +
           static_cast<uint64_t>(iy) * nx +
           static_cast<uint64_t>(iz) * nx * ny;
  };

  auto EdgeKey = [&](uint64_t v0, uint64_t v1) -> uint64_t {
    if (v0 > v1) std::swap(v0, v1);
    return (v0 << 32) | v1;
  };

  auto GetOrCreateEdgeVertex = [&](int x0, int y0, int z0,
                                   int x1, int y1, int z1) -> uint32_t {
    uint64_t key = EdgeKey(VoxelIdx(x0, y0, z0), VoxelIdx(x1, y1, z1));
    auto it = edge_cache.find(key);
    if (it != edge_cache.end()) return it->second;

    Vec3f p0 = VoxelPos(x0, y0, z0);
    Vec3f p1 = VoxelPos(x1, y1, z1);
    float v0 = grid.at(x0, y0, z0);
    float v1 = grid.at(x1, y1, z1);
    Vec3f p = detail::VertexInterp(isovalue, p0, p1, v0, v1);

    uint32_t idx = static_cast<uint32_t>(mesh->vertices.size());
    mesh->vertices.push_back(p);
    edge_cache[key] = idx;
    return idx;
  };

  // Cube corners:
  //    4----5
  //   /|   /|
  //  7----6 |
  //  | 0--|-1
  //  |/   |/
  //  3----2
  // Corner offsets (x,y,z) relative to (ix,iy,iz):
  static const int corner[8][3] = {
    {0,0,0},{1,0,0},{1,1,0},{0,1,0},
    {0,0,1},{1,0,1},{1,1,1},{0,1,1}
  };

  // Edge endpoints (corner indices):
  static const int edge_conn[12][2] = {
    {0,1},{1,2},{2,3},{3,0},
    {4,5},{5,6},{6,7},{7,4},
    {0,4},{1,5},{2,6},{3,7}
  };

  for (int iz = 0; iz < nz - 1; ++iz) {
    for (int iy = 0; iy < ny - 1; ++iy) {
      for (int ix = 0; ix < nx - 1; ++ix) {
        // Get corner values
        float val[8];
        int cx[8], cy[8], cz[8];
        for (int i = 0; i < 8; ++i) {
          cx[i] = ix + corner[i][0];
          cy[i] = iy + corner[i][1];
          cz[i] = iz + corner[i][2];
          val[i] = grid.at(cx[i], cy[i], cz[i]);
        }

        // Compute cube index
        int cubeindex = 0;
        for (int i = 0; i < 8; ++i) {
          if (val[i] < isovalue) cubeindex |= (1 << i);
        }

        if (detail::MC_EDGE_TABLE[cubeindex] == 0) continue;

        // Compute edge vertices
        uint32_t vertlist[12] = {};
        int edges = detail::MC_EDGE_TABLE[cubeindex];
        for (int e = 0; e < 12; ++e) {
          if (edges & (1 << e)) {
            int c0 = edge_conn[e][0], c1 = edge_conn[e][1];
            vertlist[e] = GetOrCreateEdgeVertex(
                cx[c0], cy[c0], cz[c0], cx[c1], cy[c1], cz[c1]);
          }
        }

        // Generate triangles
        for (int i = 0; detail::MC_TRI_TABLE[cubeindex][i] != -1; i += 3) {
          uint32_t a = vertlist[detail::MC_TRI_TABLE[cubeindex][i]];
          uint32_t b = vertlist[detail::MC_TRI_TABLE[cubeindex][i + 1]];
          uint32_t c = vertlist[detail::MC_TRI_TABLE[cubeindex][i + 2]];
          mesh->faces.push_back({a, b, c});
        }
      }
    }
  }

  return !mesh->faces.empty();
}

// ============================================================================
// MakeManifold
// ============================================================================

// Forward declaration — MakeManifold delegates to MakeManifold_VDB.
bool MakeManifold_VDB(const TriangleMesh& input,
                      double resolution,
                      double isovalue,
                      TriangleMesh* output,
                      SignMethod sign_method);

bool MakeManifold(const TriangleMesh& input,
                  double resolution,
                  double isovalue,
                  TriangleMesh* output) {
  // Simple path uses brute-force MeshToSDF; still uses flood fill for sign.
  if (!output || input.vertices.empty() || input.faces.empty()) return false;

  Vec3f bmin = input.vertices[0], bmax = input.vertices[0];
  for (const auto& v : input.vertices) {
    bmin = detail::vmin(bmin, v);
    bmax = detail::vmax(bmax, v);
  }
  float extent = std::max({bmax.x - bmin.x, bmax.y - bmin.y, bmax.z - bmin.z});
  if (extent < 1e-12f) return false;

  float voxel_size = extent / static_cast<float>(resolution);

  DenseGrid sdf;
  if (!MeshToSDF(input, voxel_size, 3.0f, &sdf)) return false;

  // Extract mesh at isovalue (in world-space distance units)
  float iso_dist = static_cast<float>(isovalue) * voxel_size;
  if (!SDFToMesh(sdf, iso_dist, output)) return false;

  return true;
}

// ============================================================================
// MeshToSDF_VDB — Flood-fill voxelization + sweep-based sign classification
// ============================================================================

bool MeshToSDF_VDB(const TriangleMesh& mesh,
                   float voxel_size,
                   float band_width,
                   DenseGrid* grid,
                   SignMethod sign_method) {
  if (!grid || mesh.vertices.empty() || mesh.faces.empty()) return false;

  // Compute AABB
  Vec3f bmin = mesh.vertices[0], bmax = mesh.vertices[0];
  for (const auto& v : mesh.vertices) {
    bmin = detail::vmin(bmin, v);
    bmax = detail::vmax(bmax, v);
  }

  float pad = (band_width + 2.0f) * voxel_size;
  bmin = bmin - Vec3f{pad, pad, pad};
  bmax = bmax + Vec3f{pad, pad, pad};

  int nx = static_cast<int>(std::ceil((bmax.x - bmin.x) / voxel_size)) + 1;
  int ny = static_cast<int>(std::ceil((bmax.y - bmin.y) / voxel_size)) + 1;
  int nz = static_cast<int>(std::ceil((bmax.z - bmin.z) / voxel_size)) + 1;

  grid->nx = nx;
  grid->ny = ny;
  grid->nz = nz;
  grid->ox = bmin.x;
  grid->oy = bmin.y;
  grid->oz = bmin.z;
  grid->voxel_size = voxel_size;

  // Store squared distances during Phase 1; sqrt at end.
  float background_sq = (band_width * voxel_size) * (band_width * voxel_size);
  grid->data.assign(static_cast<size_t>(nx) * ny * nz, background_sq);

  float band_dist = band_width * voxel_size;

  // --- Phase 1: Triangle AABB rasterization ---
  // For each triangle, compute its expanded AABB in voxel space,
  // then iterate only those voxels and compute squared distance.
  // No hash tables, no BFS — just simple nested loops.

  float inv_vs = 1.0f / voxel_size;

  for (const auto& tri : mesh.faces) {
    const Vec3f& a = mesh.vertices[tri.v0];
    const Vec3f& b = mesh.vertices[tri.v1];
    const Vec3f& c = mesh.vertices[tri.v2];

    // Triangle AABB in world space, expanded by band_dist
    float tmin_x = std::min({a.x, b.x, c.x}) - band_dist;
    float tmin_y = std::min({a.y, b.y, c.y}) - band_dist;
    float tmin_z = std::min({a.z, b.z, c.z}) - band_dist;
    float tmax_x = std::max({a.x, b.x, c.x}) + band_dist;
    float tmax_y = std::max({a.y, b.y, c.y}) + band_dist;
    float tmax_z = std::max({a.z, b.z, c.z}) + band_dist;

    // Convert to voxel indices, clamped to grid
    int ix0 = std::max(0, static_cast<int>(std::floor((tmin_x - bmin.x) * inv_vs)));
    int iy0 = std::max(0, static_cast<int>(std::floor((tmin_y - bmin.y) * inv_vs)));
    int iz0 = std::max(0, static_cast<int>(std::floor((tmin_z - bmin.z) * inv_vs)));
    int ix1 = std::min(nx - 1, static_cast<int>(std::floor((tmax_x - bmin.x) * inv_vs)));
    int iy1 = std::min(ny - 1, static_cast<int>(std::floor((tmax_y - bmin.y) * inv_vs)));
    int iz1 = std::min(nz - 1, static_cast<int>(std::floor((tmax_z - bmin.z) * inv_vs)));

    for (int iz = iz0; iz <= iz1; ++iz) {
      float pz = bmin.z + (iz + 0.5f) * voxel_size;
      for (int iy = iy0; iy <= iy1; ++iy) {
        float py = bmin.y + (iy + 0.5f) * voxel_size;
        for (int ix = ix0; ix <= ix1; ++ix) {
          Vec3f p = {bmin.x + (ix + 0.5f) * voxel_size, py, pz};
          float dsq = detail::PointTriangleDistSq(p, a, b, c);
          float& cell = grid->at(ix, iy, iz);
          if (dsq < cell) cell = dsq;
        }
      }
    }
  }

  // Convert squared distances to actual distances (unsigned).
  for (float& v : grid->data) {
    v = std::sqrt(v);
  }

  // --- Phase 2: Sign determination ---
  // The surface threshold (0.75 voxels, matching OpenVDB) defines voxels
  // that are "on the surface" and block sign propagation.
  const float surface_thresh = 0.75f * voxel_size;

  auto FlatIdx = [&](int x, int y, int z) -> size_t {
    return static_cast<size_t>(x) + nx * (static_cast<size_t>(y) + ny * static_cast<size_t>(z));
  };

  if (sign_method == kSignSweep) {
    // --- OpenVDB-style: directional sweep + iterative propagation ---
    // Phase 2a: Sweep from grid boundaries along each axis.
    // Exterior voxels (distance > 0.75*vs) get negated.
    // Surface voxels (distance <= 0.75*vs) stop propagation.
    float* data = grid->data.data();

    // Sweep along each axis: for each scanline, start from both ends.
    // Negate exterior voxels (make them negative = "outside" in OpenVDB convention).
    auto sweepLine = [&](size_t start, int step, int count) {
      // Forward sweep
      bool outside = true;
      for (int i = 0; i < count; ++i) {
        float& d = data[start + static_cast<size_t>(i) * step];
        if (d < 0.0f) {
          outside = true;  // already signed
        } else {
          if (!(d > surface_thresh)) outside = false;  // surface blocks
          if (outside) d = -d;  // mark as exterior (negative)
        }
      }
      // Backward sweep
      outside = true;
      for (int i = count - 1; i >= 0; --i) {
        float& d = data[start + static_cast<size_t>(i) * step];
        if (d < 0.0f) {
          outside = true;
        } else {
          if (!(d > surface_thresh)) outside = false;
          if (outside) d = -d;
        }
      }
    };

    // Sweep Z
    for (int iy = 0; iy < ny; ++iy)
      for (int ix = 0; ix < nx; ++ix)
        sweepLine(FlatIdx(ix, iy, 0), nx * ny, nz);
    // Sweep Y
    for (int iz = 0; iz < nz; ++iz)
      for (int ix = 0; ix < nx; ++ix)
        sweepLine(FlatIdx(ix, 0, iz), nx, ny);
    // Sweep X
    for (int iz = 0; iz < nz; ++iz)
      for (int iy = 0; iy < ny; ++iy)
        sweepLine(FlatIdx(0, iy, iz), 1, nx);

    // Phase 2b: BFS propagation from negated voxels.
    // Collect all voxels negated by the sweep, then propagate to
    // positive neighbors with distance > threshold. O(V) total.
    {
      std::vector<int32_t> prop_queue;
      for (size_t i = 0; i < grid->data.size(); ++i)
        if (data[i] < 0.0f) prop_queue.push_back(static_cast<int32_t>(i));

      size_t head = 0;
      static const int dirs[6][3] = {{-1,0,0},{1,0,0},{0,-1,0},{0,1,0},{0,0,-1},{0,0,1}};
      while (head < prop_queue.size()) {
        int32_t ci = prop_queue[head++];
        int iz = ci / (nx * ny), iy = (ci / nx) % ny, ix = ci % nx;
        for (const auto& d : dirs) {
          int x2=ix+d[0], y2=iy+d[1], z2=iz+d[2];
          if (x2<0||x2>=nx||y2<0||y2>=ny||z2<0||z2>=nz) continue;
          size_t ni = FlatIdx(x2, y2, z2);
          if (data[ni] > surface_thresh) {  // positive & far from surface
            data[ni] = -data[ni];
            prop_queue.push_back(static_cast<int32_t>(ni));
          }
        }
      }
    }

    // Phase 2c: Flip convention. OpenVDB uses negative=exterior for
    // the sweep, but the final SDF convention is negative=interior.
    // After sweeping, exterior voxels are negative, interior are positive.
    // We need to flip all signs so negative=interior.
    for (float& v : grid->data) {
      v = -v;
    }
  } else {
    detail::FloodFillSign(grid);
  }

  return true;
}

// ============================================================================
// MakeManifold_VDB
// ============================================================================

bool MakeManifold_VDB(const TriangleMesh& input,
                      double resolution,
                      double isovalue,
                      TriangleMesh* output,
                      SignMethod sign_method) {
  if (!output || input.vertices.empty() || input.faces.empty()) return false;

  Vec3f bmin = input.vertices[0], bmax = input.vertices[0];
  for (const auto& v : input.vertices) {
    bmin = detail::vmin(bmin, v);
    bmax = detail::vmax(bmax, v);
  }
  float extent = std::max({bmax.x - bmin.x, bmax.y - bmin.y, bmax.z - bmin.z});
  if (extent < 1e-12f) return false;

  float scale = static_cast<float>(resolution);
  float voxel_size = extent / scale;

  DenseGrid sdf;
  if (!MeshToSDF_VDB(input, voxel_size, 3.0f, &sdf, sign_method)) return false;

  float iso_dist = static_cast<float>(isovalue) * voxel_size;
  if (!SDFToMesh(sdf, iso_dist, output)) return false;

  return true;
}

}  // namespace tvdb_mesh

#endif  // TINYVDBIO_MESH_IMPLEMENTATION
