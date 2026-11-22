# API reference and contracts

> Extracted from the [TinyVDB README](../README.md) for detailed reference.

## Modules

All public APIs are pure-C11 with `extern "C"` linkage (consumable from
C and C++).

| Header | Description |
|--------|-------------|
| `tinyvdb_io.h` | OpenVDB read/write with custom allocator + mmap support |
| `tinyvdb_nanovdb.h` | NanoVDB read/write, VDB → NanoVDB conversion (float, double, int32, int64, vec3f, vec3d, mask), hierarchical accessor, trilinear sampler, CRC32, Gaussian-splat rasterizer (CPU forward+backward) |
| `tinyvdb_volume.h` | Volume access for renderers and UsdVol: grid info (class, type, transform, exact or header-only bounds), typed dense extraction with a voxel budget, nearest/trilinear sparse sampling in world or index space |
| `tinyvdb_to_nanovdb.c` | VDB → NanoVDB FloatGrid converter (byte-compatible with libnanovdb) |
| `tinyvdb_mesh.h` | Mesh ↔ SDF, marching cubes, manifold preprocessing |
| `tinyvdb_ops.h` | Dense ops: morphology, filtering, CSG, differential operators, Poisson PCG, advection, fast sweeping, fp64 variants |
| `tinyvdb_sample.h` / `tinyvdb_tsdf.h` | Trilinear sampling/splatting; depth-frame TSDF fusion (single-frame and in-place multi-frame) |
| `tinyvdb_topology.h` / `tinyvdb_ray.h` | Coarsen / refine / prune / clip / merge / pool; Amanatides–Woo DDA, ray-cast SDF, segments-along-ray, batched marching cubes |
| `tinyvdb_sparse.h` / `tinyvdb_sparse_tree.h` | Flat sparse-grid representation (hash-based CSG/morphology, sparse 3D conv); operations on a loaded `tvdb_grid_t` (leaf iter, dilate/erode active or topology, tree-aware CSG, from-scratch rebuilders) |
| `tinyvdb_tree.h` | Checked float-tree diagnostics, signed flood fill, exact pruning and sparse/dense bridges |
| `tinyvdb_sparse_tools.h` | Sparse level-set tracking/rebuild, mesh → narrow-band level set (winding-number signs), affine resampling, indexed/adaptive meshing and Poisson/PDE domains |
| `tinyvdb_winding.h` | Generalized winding numbers of triangle meshes, exact and fast (AABB tree with dipole far field) |
| `tinyvdb_tetmesh.h` | Tetrahedral meshes of an SDF interior by isosurface stuffing (BCC lattice), from a level-set grid or a field callback; dihedral-angle quality report |
| `tinyvdb_sdf_tree.h` | In-place hierarchical SDF fast sweeping, filtering, morphology and offsets with compact active-voxel workspaces |
| `tinyvdb_thread.h` | Reusable synchronous task pool: C11, GCD, pthread or serial backend |
| `tinyvdb_autograd.h` | Per-op CPU VJPs (sample, splat, CSG, sparse_conv3d) — framework-free |
| `tinyvdb_simd.h` | Optional SSE4.2/AVX2/F16C primitives gated on `TINYVDB_SIMD` |
| `tinyvdb_gpu.h` | Optional runtime-loaded GPU backend: Vulkan, CUDA and HIP kernels for analytic sphere/box/torus SDF generation, dense CSG, dense trilinear batch sampling, and same-topology sparse conv3d |
| `tinyvdb_gpu_compute.h` | Lean CUDA/HIP device (runtime-loaded, no SDK) running mesh-to-level-set, level-set sampling and isosurface stuffing; needs only the CPU modules it accelerates |

### VDB operations contracts

CPU dense stencils and advection require valid dimensions, allocated matching
output shapes, and positive finite input spacing. CPU void APIs leave outputs unchanged
on invalid input; checked GPU APIs report `INVALID_ARGUMENT`. Shape-preserving
stencils, advection, and sparse operations support same-handle in-place output
through scratch storage. Pointwise CPU operations keep their allocation-free
in-place path. Topology constructors require distinct input/output handles.
`test_threads` and `test_hardening` cover the in-place forms of the stencils,
advection schemes, composite and morphological ops, topology constructors and the
sparse ops; the sampled, batch and mesh-entry points are not covered for aliasing.

Sparse outputs must be initialized owning containers, including empty outputs.
Failures preserve the prior output. Coordinate comparisons use all three int32
components, with first-occurrence lookup semantics for duplicates. Sparse CSG
uses union topology for union, intersection, and difference; missing coordinates
contribute the supplied background. GPU offsets outside int32 are absent/padded,
and morphology clips generated coordinates at the representable limits.

Poisson `_ex` APIs report status, iterations, convergence, and true residual norms.
All precisions use the edge-clamped Laplacian and preserve the initial solution
mean. A nonzero RHS mean beyond `64 * input_epsilon * sum(abs(rhs)) / count` is
rejected; rounding-sized means are removed. Relative tolerance applies to float
storage (including double internal arithmetic), and absolute tolerance to double
storage. CPU solvers refresh residuals every 32 iterations and before accepting
convergence. Convergence uses a true residual in the returned storage precision.
Budget exhaustion returns a finite iterate with an honest convergence flag;
invalid input, allocation failure, or numerical breakdown leaves the solution
unchanged. Legacy APIs return zero on failure; use `_ex` for an unambiguous status.

On fp64-capable devices, GPU Poisson retains vectors, projection, PCG updates,
and double reductions on the device. Host decisions read reduced scalars and
dependent kernels share submissions. The float host API on devices without
fp64 retains its vector-transfer implementation.

### Checked tree maintenance

`tinyvdb_tree.h` provides `tvdb_grid_diagnose`,
`tvdb_grid_signed_flood_fill`, and `tvdb_grid_prune` for loaded float trees.
Maintenance constructors take distinct initialized owning outputs (`{0}` is
valid), preserve source and destination on failure, and produce independent
libc-owned grids freed with `tvdb_grid_destroy_owned`. Source workspaces and
borrowed views remain valid when a separate result is constructed. Metadata,
transforms and active values/states are copied; maintenance accepts no custom
output allocator. Point grids and other value types are unsupported.

Diagnostics validate hierarchy, masks, child indices, buffers and coordinates
before inspecting values. Numeric defects return a report with `valid=0`;
structural/type/allocation errors return an error status and preserve the prior
report. Generic diagnostics require finite stored values and a finite invertible
affine transform. Level-set checks additionally require a positive symmetric
background, orthogonal uniform scale, no active tiles, valid band values and
string `class="level set"` metadata. Fog checks require zero background/inactive
values, active values in `[0,1]`, and `class="fog volume"`. Optional central
world-distance gradient checks apply to active level-set voxels inside the band;
tolerance is absolute and also applies to value checks.

Signed flood fill propagates signs through inactive voxels and tiles in a
**closed narrow-band level set**. It preserves active values and masks, accepts
positive exterior and negative interior widths in world units, and rejects
active tiles/nonfinite values. It does not validate watertightness or rebuild
distances. Exact pruning collapses only identical float bit patterns and active
states, preserving mixed signs and signed zero distinctions. It compacts nodes
and child arrays and may produce active tiles.

Active counts include tile volumes; bounds describe the exact active region
with an exclusive maximum. Legacy int32 bounds return false when that maximum
is unrepresentable; diagnostic bounds use int64. Flat extraction explicitly
rejects active-tile expansion. Flat sparse/dense bridges and morphology require
positive axis-aligned isotropic spacing representable in their float geometry.
Dense materialization fills inactive cells with the caller's background, while
morphology/CSG sample each source's stored inactive values. Morphology uses fixed
inactive boundaries in every iteration and accepts zero iterations as identity.
All tree CSG operations use union active topology and require identical complete
transforms. `_ex` bridges report errors and replace initialized owning outputs
only on success; the legacy dense constructor accepts an uninitialized output.

CPU Gaussian rasterization now sorts complete symmetric tile footprints by
tile, depth and input index. It has no per-splat tile cap, composites the
background with final transmittance, validates finite inputs/positive semidefinite
conics, and keeps failed outputs safely destructible. Backward replays the same
ordering and termination decisions, supports opaque splats, and preserves gradient
accumulators on failure. GPU hash voxelization publishes all three coordinates
before allowing duplicate comparisons; threads skip slots still being written.

Optional OpenVDB maintenance comparisons need a matching installed header/library
pair and C++17, TBB and Imath. The default library has no OpenVDB dependency:

```sh
cmake -S . -B /tmp/tinyvdb-oracle -G Ninja \
  -DTINYVDB_BUILD_TESTS=ON -DTINYVDB_BUILD_OPENVDB_TESTS=ON \
  -DTINYVDB_BUILD_GPU=OFF -DTINYVDB_BUILD_EXAMPLES=OFF \
  -DTINYVDB_BUILD_VDBRENDER=OFF
cmake --build /tmp/tinyvdb-oracle
ctest --test-dir /tmp/tinyvdb-oracle -R openvdb --output-on-failure
```

### Sparse tools inspired by OpenVDB

`tinyvdb_sparse_tools.h` adds all four feature groups identified in the OpenVDB
source review at `86b5ea9e` (13.1.1 configuration). The library remains C11 and has
no OpenVDB dependency. Optional reference tests use matching installed OpenVDB
10.0.1 headers/libraries, comparing interpolation, rebuild distances, surface
geometry and immediate-neighbor Poisson solutions.

| API | Behavior |
|---|---|
| `tvdb_grid_level_set_rebuild` / `tvdb_grid_level_set_track` | Reconstruct a piecewise-linear isosurface, compute closest-triangle world distances with a BVH, expand/trim the narrow band, fill inactive signs and prune. Tracking rebuilds the zero isosurface after edits. |
| `tvdb_grid_resample` | Resample scalar values into a complete affine target transform with nearest/trilinear interpolation. Includes inactive stored values and tiles; a sample is active when a nonzero-weight tap is active. |
| `tvdb_grid_volume_to_mesh` | Indexed classic marching cubes over sparse stored regions and tile boundaries. Shared edges and reflection-aware outward winding; optional global vertex clustering bounded by a world-space displacement. |
| `tvdb_grid_solve_poisson` | Solve `-div(k grad u)=rhs` on active topology, with double Jacobi-preconditioned CG, positive face conductivity callbacks and Dirichlet/Neumann boundary callbacks. |

All outputs must be distinct initialized owning containers (`{0}` is valid).
Success replaces the old output; errors preserve source, output and result
reports. Grid results own libc storage and use the standard float 5/4/3 hierarchy;
mesh results own heap vertex/face arrays. Metadata/transforms are copied, obsolete
serialized-file statistics are removed, and PDE results get `class="unknown"`.
Only float scalar trees are supported. These APIs run on the CPU.

Working sets use complete int32 coordinate hashes, never a dense global bounding
box. A zero coordinate/cell budget selects 1,000,000 entries. Resampling can expand
constant tiles into individual samples before exact pruning; large transformed
regions can exceed the budget. Meshing visits only constant-tile boundary slabs,
with a scan limit of 32 times the cell budget. Budget, allocation, nonfinite and
coordinate-overflow failures are explicit errors.

Rebuild requires a closed, resolved narrow-band surface, positive exterior
background relative to the isovalue, and orthogonal isotropic affine axes. Both
band widths are **positive world-distance magnitudes**, unlike the negative
interior argument to signed flood fill. It preserves the sampled surface rather
than the old active values/topology. Asymmetric bands are supported, while the
level-set diagnostic mode still requires symmetric bands. Distances are to the float mesh's
piecewise-linear surface. It does not repair holes, advect the interface or use
OpenVDB's iterative tracker. It has no iterative convergence parameter.
Resampling accepts rotations, anisotropic scales and shear; scalar values retain
their units and are not redistanced. Vector transformation policies remain future
work.

Meshing samples stored inactive values as well as active values; activity does
not clip the surface. `adaptivity=0` disables reduction; positive adaptivity is a
**world-space vertex-displacement bound**, not OpenVDB's `[0,1]` parameter.
Globally shared clusters avoid separate leaf seams and remove faces with repeated
indices. Classic MC ambiguity/exact-isovalue degeneracy and clustering can affect
manifoldness or merge nearby components; topology preservation is not guaranteed.

PDE axes must be orthogonal, but may have different spacing; shear requires a
coupled stencil and is rejected. Dirichlet values are at missing neighbor centers.
Neumann values are outward `k*du/dn` at half-cell faces, contributing `flux/h` to
the RHS. Conductivity is evaluated once per undirected edge and used symmetrically.
Each disconnected pure-Neumann component must have compatible summed RHS/flux
(with a `1e-10` relative L1 rounding allowance) and receives a zero-mean solution.
Mixed/Dirichlet components are anchored. Active tiles expand within the voxel
budget. Inactive output values are zero; callbacks define boundary values.
Iteration exhaustion returns a finite iterate with `converged=false`; residuals
include final float storage rounding. Convergence uses relative L2 tolerance.

The optional oracle command above runs both suites with `-R openvdb`. OpenVDB's
Poisson comparison uses its staggered option to match immediate six-neighbor
sampling; its default collocated stencil uses two-voxel offsets.

Further parity work includes advection/iterative tracking, vector resampling,
conservative adaptive meshing and stronger PDE preconditioners/GPU kernels.
Reference interfaces:
[LevelSetTracker](https://www.openvdb.org/documentation/doxygen/LevelSetTracker_8h.html),
[GridTransformer](https://www.openvdb.org/documentation/doxygen/GridTransformer_8h.html),
[VolumeToMesh](https://www.openvdb.org/documentation/doxygen/VolumeToMesh_8h.html), and
[PoissonSolver](https://www.openvdb.org/documentation/doxygen/PoissonSolver_8h.html).

### Hierarchical SDF processing

`tinyvdb_sdf_tree.h` operates directly on float `tvdb_grid_t` leaves. It provides
fast sweeping, mean/Gaussian/Laplacian filtering, seven-point min/max morphology,
and world-distance offsets. Operations preserve active masks, inactive values,
leaf buffers and tiles; failures leave grid values unchanged. Isotropic spacing
is required, including rotated uniform affine transforms without shear.

Create one workspace per grid and reuse it across operations:

```c
#include "tinyvdb_sdf_tree.h"

/* grid is an existing owning float grid; check each returned status. */
tvdb_sdf_tree_t *sdf = NULL;
tvdb_error_t error = {0};
tvdb_status_t status = tvdb_sdf_tree_create(&grid, NULL, NULL, &sdf, &error);
if (status == TVDB_OK) {
    tvdb_sdf_sweep_result_t result;
    status = tvdb_sdf_tree_fast_sweep(sdf, 1.5f * voxel_size, 8, 1e-5f,
                                      &result, &error);
    if (status == TVDB_OK)
        status = tvdb_sdf_tree_filter(sdf, TVDB_SDF_FILTER_GAUSSIAN, 2, &error);
    tvdb_sdf_tree_destroy(sdf);
}
```

Sweeping uses the active leaf voxels as its domain. Values with
`abs(phi) <= frozen_band` are frozen seeds; unseeded disconnected components keep
their original values and are reported as unreached. Eight directional sweeps
use leaf wavefronts, with a barrier between occupied planes. Filters read stored
inactive leaf values and signed internal/root tiles as fixed boundary data.
Offsets and morphology keep the existing band topology.

Scratch storage starts at `4 * active_voxels` bytes. Sweeping adds two packed
flag bits per active voxel; filters lazily allocate a second float buffer.
Per-leaf masks, neighbor caches and sweep order metadata are additional. No
bounding-box volume or intermediate coordinate array is allocated.
`tvdb_sdf_tree_info` reports retained metadata and scratch bytes, excluding the
grid, pool/OS resources and temporary constructor/sort allocations. The workspace
accepts a custom allocator. Keep topology, transforms, tiles and leaf allocations
fixed while it is alive; leaf values may change between calls. Serialize operations
on each grid/workspace.

Configure task scheduling with `-DTINYVDB_THREAD_BACKEND=AUTO` (the default):
C11 threads where available, GCD on macOS/iOS, pthreads if C11 is unavailable,
and a serial fallback when no supported runtime is found. Explicit choices are
`C11`, `GCD`, `PTHREAD`, and `NONE`; unavailable explicit backends fail configuration.
GCD uses the synchronous C `dispatch_apply_f` interface and needs no Blocks or
Objective-C code. Native Apple tests are registered in CI.

A NULL pool creates an owned pool with the detected CPU count capped at eight and
at the leaf count. Pass a reusable `tvdb_thread_pool_t` to choose a worker count
or share scheduling resources across workspaces. C11/pthread workers persist
between passes and the calling thread participates. OpenMP remains optional for
other existing kernels; hierarchical SDF processing uses this task module even
with `TINYVDB_OPENMP=OFF`.

### Mesh and volume conversion

`tinyvdb_mesh_conversion.h` adds checked dense mesh/SDF conversion and a reusable
`tvdb_mesh_sdf_t` closest-triangle workspace. Keep the borrowed mesh geometry,
counts and arrays fixed while the workspace is alive. Reuse its BVH and normals
for different voxel spacings or band widths; generation into distinct outputs
may share a task pool. Mesh voxelization uses the same C11/GCD/pthread/serial
module as hierarchical SDF processing, including with OpenMP disabled. A NULL
pool chooses up to eight workers and runs small inputs serially.

`tvdb_grid_volume_to_mesh` collects the surface-adjacent regions of the tree in
tree order, classifies their cells on a pool (one cell map and one lookup cache
per slice) and then sorts the merged cells, so the mesh and the `max_cells`
budget do not depend on the worker count. `tvdb_grid_volume_to_mesh_pooled`
takes a caller's pool; the plain form creates its own for inputs with at least
32k active voxels.

```c
#include "tinyvdb_mesh_conversion.h"

tvdb_status_t convert_mesh(const tvdb_triangle_mesh *input, float spacing,
                          float band, tvdb_triangle_mesh *surface,
                          tvdb_error_t *error) {
    tvdb_mesh_sdf_t *workspace = NULL;
    tvdb_dense_grid volume = {0, 0, 0, 0, 0, 0, 0, NULL};
    tvdb_status_t status = tvdb_mesh_sdf_create(input, &workspace, error);
    if (status == TVDB_OK)
        status = tvdb_mesh_sdf_generate(workspace, spacing, band, NULL,
                                       &volume, NULL, error);
    /* Retain workspace between generations to reuse its acceleration. */
    if (status == TVDB_OK)
        status = tvdb_sdf_to_mesh_ex(&volume, 0.0f, TVDB_MESH_WINDING_OUTWARD,
                                    NULL, surface, NULL, error);
    tvdb_dense_grid_free(&volume);
    tvdb_mesh_sdf_destroy(workspace);
    return status;
}
```

The example appends to an initialized owning `surface`. Checked mesh-to-SDF
generation replaces an initialized owning grid and releases its old heap data
on success. `tvdb_mesh_to_sdf_ex` provides the one-shot equivalent. Failures
preserve existing outputs and restore arena offsets. Arena allocations are
checked for input/output overlap before the allocator zeroes them. Temporary
acceleration and marching-cubes caches use the heap, leaving only output storage
in the arena; replaced arena output remains retained until reset.

Indexed marching cubes counts in parallel, sizes output exactly, and emits in
stable raster/edge order with shared-edge deduplication. Its edge scratch chooses
the smaller of a two-plane rolling cache (about `20 * nx * ny` bytes) and a
surface-sized hash, plus one count record per z plane. Interpolation handles tiny
field magnitudes and overflowing float differences on CPU, Vulkan and CUDA.

`TVDB_MESH_WINDING_OUTWARD` points outward for negative-inside SDFs. Legacy
`tvdb_sdf_to_mesh` keeps its original table winding toward the negative phase;
`tvdb_make_manifold` now produces outward faces and keeps its intermediate grid
off the output arena. Conversion still uses classic marching cubes, including
ambiguous cases and degenerate triangles at exact-isovalue samples. Mesh-to-SDF
sign uses the closest feature: the face normal in a face interior, the summed
normals of the two incident faces on an edge, and on a vertex the incident face
whose normal pairs positively with the offset to the query point. Open surfaces
and inconsistent face orientation can still cause sign artifacts, and degenerate
faces have zero normals contributing unsigned distances. The `_vdb` sign-method
argument remains advisory. Neither API promises a watertight manifold
reconstruction.

`tvdb_sdf_to_mesh_dual_ex` (and its `tvdb_sdf_to_mesh_dual` wrapper) is a staged
**DMC-0 / surface-nets** alternative: one dual vertex per crossed cell at the
centroid of its edge crossings, one quad per sign-changing primal edge. It
follows the same `_ex` contract as the marching-cubes conversion and is
deterministic across worker counts. It is not Nielson DMC-1 (no per-cube patch
decomposition), and it performs no boundary padding, so watertightness requires
the crossing surface to be strictly inside the lattice; it does not yet match
the Lean DMC-1 vectors.

