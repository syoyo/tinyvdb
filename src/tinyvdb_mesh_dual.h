/* Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
   SPDX-License-Identifier: Apache-2.0 */

#pragma once

#ifdef __cplusplus
extern "C" {
#endif

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "tinyvdb_mesh.h"          /* tvdb_vec3f, tvdb_dense_grid, status/error types */
#include "tinyvdb_sparse_tree.h"   /* tvdb_grid_t */
#include "tinyvdb_thread.h"        /* tvdb_thread_pool_t */

/* A quadrilateral of corner indices into tvdb_quad_mesh::vertices. */
typedef struct {
    uint32_t v0, v1, v2, v3;
} tvdb_quad;

/* Owning quad mesh, laid out like tvdb_triangle_mesh. `vertices` and `quads`
 * are heap buffers unless the mesh was produced with an arena. */
typedef struct {
    tvdb_vec3f *vertices;
    size_t vertex_count;
    size_t vertex_capacity;
    tvdb_quad *quads;
    size_t quad_count;
    size_t quad_capacity;
} tvdb_quad_mesh;

void tvdb_quad_mesh_init(tvdb_quad_mesh *mesh);
void tvdb_quad_mesh_free(tvdb_quad_mesh *mesh);
void tvdb_quad_mesh_init_arena(tvdb_quad_mesh *mesh, tvdb_arena_allocator_t *arena);

/* ---- cube-local MC patch decomposition (DMC-1 first slice) -------------
 *
 * Internal, allocation-free helper for the per-cube connected components of
 * an MC triangle soup over the 12 cube edges. This mirrors the Lean oracle
 * `Vdb.DmcOne` (`mcPatchCount`, `mcTriPatch`, `patchesUsing`): a union-find
 * over the case's triangles merges the three edge ids of each triangle, and
 * the resulting components are the DMC-1 patches of that cube.
 *
 * This is ONLY the cube-local decomposition. It does not place patch
 * vertices, does not stitch quads across cube faces, and does not change the
 * public dual-mesh output above (which remains DMC-0). No DMC-1 topology is
 * claimed by these functions.
 */

#define TVDB_DUAL_PATCH_MAX_TRIS 5    /* MC_TRI_TABLE holds at most 5 triangles */
#define TVDB_DUAL_PATCH_MAX_PATCHES 4 /* machine-checked bound of Vdb.DmcOne */

typedef struct {
    uint8_t tri_count;  /* number of triangles in the case's soup, 0..5 */
    uint8_t patch_count; /* connected components of the soup, 0..4 (0 iff empty) */
    uint8_t tri_patch[TVDB_DUAL_PATCH_MAX_TRIS]; /* patch id of each triangle */
    uint8_t edge_patch_count[12];  /* number of distinct patches owning a cube edge (0 or 1) */
    uint8_t edge_patch[12][TVDB_DUAL_PATCH_MAX_PATCHES]; /* deduplicated patch ids per edge */
    uint16_t cross_mask; /* 12-bit sign-change mask of the case, from the corner bits */
} tvdb_dual_patch_info;

/* Fill `info` for MC case `case_id` (0..255) from the shipped MC triangle
 * table. Returns false if `info` is NULL or `case_id > 255` (in both cases
 * `info` is left untouched); a table row outside the machine-checked bounds
 * of 5 triangles / 4 patches also yields false. Otherwise true. Pure and
 * allocation-free: the result depends only on `case_id` and the static MC
 * table. */
bool tvdb_dual_patch_compute(unsigned case_id, tvdb_dual_patch_info *info);

/* Dense-grid dual marching cubes, first slice: DMC-0 / naive surface nets.
 *
 * Construction. One dual vertex per crossed lattice cell (an MC cube whose
 * eight corner samples straddle `isovalue`), placed at the centroid of the
 * edge crossings of that cell. One quad per sign-changing *primal* lattice
 * edge, joining the dual vertices of the four cells incident to that edge.
 * Quads are ordered counter-clockwise about the positive edge axis, then
 * reversed when the sample decreases along that axis, which gives an outward
 * oriented, consistently wound mesh (for a negative-inside SDF).
 *
 * This is NOT DMC-1 / Nielson dual marching cubes: there is no per-cube MC
 * patch decomposition and no patch-vertex stitching. The quads therefore do
 * not reproduce the Lean DMC-1 index vectors, and ambiguous faces are resolved
 * by the surface-nets centroid rule rather than a per-face sign rule.
 *
 * Contract (same family as tvdb_sdf_to_mesh_ex): `out` must be an initialized
 * owning mesh and must not overlap the input grid or itself. The grid must be
 * valid with finite samples/origin/spacing and at least 2 voxels per axis;
 * `isovalue` must be finite. Success replaces `out` (freeing old heap data;
 * with an arena, old output storage must belong to that same arena and stays
 * retained until the caller resets it); failure preserves `out` and restores
 * the arena offset. Output buffers must
 * not overlap the input grid or each other. Emission is serial in a fixed
 * raster order, so the result is bit-identical for any `pool` (including
 * NULL): `pool` is used only for the independent per-plane counting pass.
 *
 * No boundary padding is performed. Watertightness and outward orientation
 * require the crossing surface to be strictly inside the lattice (all
 * boundary samples on the outside of `isovalue`); sign-changing primal edges
 * on the lattice boundary have fewer than four incident cells and are skipped.
 * Single-cell scratch is an O(surface) open-addressing hash, not a dense
 * nx*ny*nz array.
 */
tvdb_status_t tvdb_sdf_to_mesh_dual_ex(const tvdb_dense_grid *grid, float isovalue,
                                       tvdb_thread_pool_t *pool, tvdb_quad_mesh *out,
                                       tvdb_arena_allocator_t *arena, tvdb_error_t *err);

/* Convenience wrapper: serial pool, no error context. */
bool tvdb_sdf_to_mesh_dual(const tvdb_dense_grid *grid, float isovalue, tvdb_quad_mesh *out,
                           tvdb_arena_allocator_t *arena);

/* ---- dense DMC-1 (Nielson dual marching cubes), first slice ---------------
 *
 * This is the DMC-1 counterpart of tvdb_sdf_to_mesh_dual_ex. It reuses the
 * cube-local patch decomposition (tvdb_dual_patch_compute) and the same
 * emission/winding/alias/commit machinery, but changes the vertex model:
 *
 *   - One dual vertex per (cell, MC patch) rather than per crossed cell. A
 *     cell whose MC soup has k connected components emits k vertices; most
 *     cells have k = 1, but ambiguous cases have k = 2, 3 or 4 (the exact
 *     distribution is machine-checked in Lean's Vdb.DmcOne).
 *   - One quad per sign-changing primal lattice edge with four incident
 *     cells, joining the four patch-vertices of those cells that own the
 *     crossed edge (the Nielson dual / DmcOne quad construction). Each
 *     crossed cube edge belongs to exactly one patch, so the owner is
 *     unambiguous. The four corners are ordered counter-clockwise about the
 *     positive edge axis and reversed when the sample decreases along it,
 *     exactly as in DMC-0; this yields a consistently wound, watertight
 *     surface for a strictly-interior crossing.
 *
 * Vertex placement minimises the quadratic error function (QEF) of the
 * patch's edge-crossing planes: each crossing contributes the plane through
 * its interpolated position with the interpolated central-difference gradient
 * as normal; the 3x3 normal equations are solved by Cramer's rule in double.
 * A singular system falls back to the centroid of the crossings, and the
 * result is clamped to the owning cell. Combinatorial watertightness is
 * independent of placement (Lean's `watertight_of_ix`): quads are closed in
 * the index mesh under any placement.
 *
 * Scope / limits: dense grids only. This function does not pad the lattice,
 * so a crossing surface that meets the boundary yields an open mesh; use
 * `tvdb_sdf_to_mesh_dual_one_padded_ex` below for a shell-pinned, watertight
 * result in that case. Degenerate cells (empty/oversized soups) are handled
 * defensively and never yield invalid indices. No sparse/tree variant, no
 * C<->Lean topology vector dump, and no claim of exact index parity with the
 * `lean/Vdb/DmcOne*` constructions here.
 *
 * Contract: identical to tvdb_sdf_to_mesh_dual_ex -- `out` must be an
 * initialized owning mesh, must not overlap the input grid or itself; the
 * grid must be valid with finite samples/origin/spacing and at least 2 voxels
 * per axis; `isovalue` must be finite. Success replaces `out`; failure
 * preserves `out` and restores the arena offset. Emission is serial in a
 * fixed raster order, so the result is bit-identical for any `pool` (used
 * only for the independent per-plane counting pass, including NULL).
 */
tvdb_status_t tvdb_sdf_to_mesh_dual_one_ex(const tvdb_dense_grid *grid, float isovalue,
                                            tvdb_thread_pool_t *pool, tvdb_quad_mesh *out,
                                            tvdb_arena_allocator_t *arena, tvdb_error_t *err);

/* Convenience wrapper: serial pool, no error context. */
bool tvdb_sdf_to_mesh_dual_one(const tvdb_dense_grid *grid, float isovalue, tvdb_quad_mesh *out,
                               tvdb_arena_allocator_t *arena);

/* Dense DMC-1 with a shell-pinned boundary. One voxel of samples on each face
 * of the lattice is pinned to the outside phase before the standard DMC-1
 * construction, so sign-changing primal edges on the original boundary get
 * their four incident cells and are emitted. The result is therefore
 * combinatorially watertight even when the crossing surface meets the domain
 * boundary (the padded surface is closed by the outside shell). The added
 * shell is materialised on the heap and freed before return; output positions
 * stay in the original grid's world coordinates. The contract is identical to
 * tvdb_sdf_to_mesh_dual_one_ex; grids with an axis of 2046 voxels or more are
 * rejected (the padded lattice would exceed this implementation's dimension
 * cap). Sparse/tree DMC-1 and C<->Lean index parity are still out of scope. */
tvdb_status_t tvdb_sdf_to_mesh_dual_one_padded_ex(const tvdb_dense_grid *grid, float isovalue,
                                                   tvdb_thread_pool_t *pool, tvdb_quad_mesh *out,
                                                   tvdb_arena_allocator_t *arena,
                                                   tvdb_error_t *err);

bool tvdb_sdf_to_mesh_dual_one_padded(const tvdb_dense_grid *grid, float isovalue,
                                      tvdb_quad_mesh *out, tvdb_arena_allocator_t *arena);

/* Sparse-tree dual marching cubes, first slice (DMC-0 / naive surface nets).
 *
 * The tree is scanned over the active index box plus a one-voxel margin using
 * a cached accessor; stored values are read as they are (active state does not
 * clip the surface). Cell corners are placed in world space with the grid's
 * complete affine transform. As in the dense variant there is one dual vertex
 * per crossed cell (edge-crossing centroid) and one outward-wound quad per
 * sign-changing primal edge with four crossed incident cells; edges on the
 * scanned boundary are skipped. This is NOT DMC-1: no MC patch decomposition
 * or patch stitching, so the Lean DMC-1 index vectors are not reproduced.
 *
 * Contract (same family as tvdb_sdf_to_mesh_dual_ex and the sparse tools):
 * `out` must be an initialized owning mesh; success replaces it (freeing old
 * heap data; with an arena, old storage must belong to that arena and is
 * retained until the caller resets it). Failure preserves `out` and restores
 * the arena offset. Output buffers must not overlap tree node storage or each
 * other. Nonfinite samples/origin or a non-invertible transform are rejected.
 * max_cells bounds crossed cells (0 selects 1,000,000); the bounding-box scan
 * is capped at 32*max_cells+4096 cells. Emission is serial in raster order, so
 * the mesh is bit-identical for any `pool` (accepted for ABI parity only).
 *
 * Scope limit: surfaces formed solely by stored values outside the active box
 * are not visited; non-uniform/scaled transforms are supported (unlike a
 * dense materialization) but inactive values outside the active box are not.
 */
tvdb_status_t tvdb_grid_volume_to_mesh_dual_ex(const tvdb_grid_t *grid, float isovalue,
                                               size_t max_cells, tvdb_thread_pool_t *pool,
                                               tvdb_quad_mesh *out,
                                               tvdb_arena_allocator_t *arena, tvdb_error_t *err);

/* Convenience wrapper: serial, no error context. */
bool tvdb_grid_volume_to_mesh_dual(const tvdb_grid_t *grid, float isovalue, size_t max_cells,
                                   tvdb_quad_mesh *out, tvdb_arena_allocator_t *arena);

/* Sparse-tree DMC-1 (Nielson dual marching cubes), shell-pinned.
 *
 * This is the tree counterpart of tvdb_sdf_to_mesh_dual_one_ex /
 * tvdb_sdf_to_mesh_dual_one_padded_ex. It reuses the cube-local MC patch
 * decomposition (tvdb_dual_patch_compute) and the sparse-tree DMC-0 traversal
 * and quad rule, but changes the vertex model to one dual vertex per
 * (cell, MC patch): a cell whose MC soup has k connected components emits k
 * vertices, and a sign-changing primal edge emits one quad joining the four
 * patch-vertices of its four incident cells that own the crossed cube edge.
 *
 * Shell pinning is ALWAYS on (there is no unpadded tree variant). The scanned
 * cell box is the DMC-0 box extended by one cell on every side
 * (`lo-1 .. hi+1` in each axis). Any cell corner sample whose index lies
 * outside the original DMC-0 sample domain `[lo, hi+1]` is treated as the
 * outside phase (a value >= isovalue, `isovalue+1` when finite), regardless of
 * what the accessor would return there. Consequently a crossing surface that
 * meets the domain boundary acquires its four incident cells and is closed by
 * the pinned shell; the result is combinatorially watertight in that case.
 * No extra dense lattice is materialised.
 *
 * Vertex placement minimises the QEF of the patch's edge-crossing planes,
 * solved in INDEX space (no inverse affine transform is required): the
 * plane normals use the per-cell central-difference index-space gradient
 * (the mean of the four axis-parallel edge differences per axis), each owned
 * crossed edge contributes its interpolated index-space crossing point, the
 * 3x3 normal equations are solved with Cramer's rule in double, a singular
 * system falls back to the crossing centroid, the result is clamped to the
 * cell's index box `[c, c+1]`, and finally mapped to world coordinates with
 * the grid's complete affine transform. This is a placement heuristic: it is
 * not the dense DMC-1 world-space gradient, so tree and dense DMC-1 vertex
 * positions need not coincide; only their topology/counts are comparable.
 *
 * Contract: identical to tvdb_grid_volume_to_mesh_dual_ex -- `out` must be an
 * initialized owning mesh; success replaces it (freeing old heap data; with
 * an arena, old storage must belong to that arena and is retained until the
 * caller resets it). Failure preserves `out` and restores the arena offset.
 * Output buffers must not overlap tree node storage or each other. Nonfinite
 * samples/origin or a non-invertible transform are rejected. `max_cells`
 * bounds crossed cells (0 selects 1,000,000); the bounding-box scan is capped
 * at 32*max_cells+4096 cells (the extended shell is included in both budgets).
 * Emission is serial in raster order, so the mesh is bit-identical for any
 * `pool` (accepted for ABI parity only). As in DMC-0, surfaces formed solely
 * by stored values outside the active box are not visited. No C<->Lean index
 * vector dump or exact parity claim is made here.
 */
tvdb_status_t tvdb_grid_volume_to_mesh_dual_one_ex(const tvdb_grid_t *grid, float isovalue,
                                                   size_t max_cells, tvdb_thread_pool_t *pool,
                                                   tvdb_quad_mesh *out,
                                                   tvdb_arena_allocator_t *arena, tvdb_error_t *err);

/* Convenience wrapper: serial, no error context. */
bool tvdb_grid_volume_to_mesh_dual_one(const tvdb_grid_t *grid, float isovalue, size_t max_cells,
                                       tvdb_quad_mesh *out, tvdb_arena_allocator_t *arena);

#ifdef __cplusplus
}
#endif
