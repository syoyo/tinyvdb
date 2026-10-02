# TinyVDB, lightweight C/C++ VDB library

[![PyPI](https://img.shields.io/pypi/v/tinyvdb)](https://pypi.org/project/tinyvdb/)

TinyVDB provides lightweight C/C++ libraries for working with OpenVDB data. It includes VDB file I/O, mesh-to-SDF conversion, grid operations, and more — without depending on the full OpenVDB library.

TinyVDB is suitable for genAI, graphics applications, HPC visualization tools, physics simulation, and any project that needs lightweight VDB functionality.

The 0.10.0 release candidate adds checked tree maintenance and sparse volume
tools. See the [release notes](CHANGELOG.md) for new APIs, behavior changes, and
migration details. Python bindings require Python 3.11 or newer.

## Modules

All public APIs are pure-C11 with `extern "C"` linkage (consumable from
C and C++).

| Header | Description |
|--------|-------------|
| `tinyvdb_io.h` | OpenVDB read/write with custom allocator + mmap support |
| `tinyvdb_nanovdb.h` | NanoVDB read/write, hierarchical accessor, trilinear sampler, CRC32, Gaussian-splat rasterizer (CPU forward+backward) |
| `tinyvdb_to_nanovdb.c` | VDB → NanoVDB FloatGrid converter (byte-compatible with libnanovdb) |
| `tinyvdb_mesh.h` | Mesh ↔ SDF, marching cubes, manifold preprocessing |
| `tinyvdb_ops.h` | Dense ops: morphology, filtering, CSG, differential operators, Poisson PCG, advection, fast sweeping, fp64 variants |
| `tinyvdb_sample.h` / `tinyvdb_tsdf.h` | Trilinear sampling/splatting; depth-frame TSDF fusion (single-frame and in-place multi-frame) |
| `tinyvdb_topology.h` / `tinyvdb_ray.h` | Coarsen / refine / prune / clip / merge / pool; Amanatides–Woo DDA, ray-cast SDF, segments-along-ray, batched marching cubes |
| `tinyvdb_sparse.h` / `tinyvdb_sparse_tree.h` | Flat sparse-grid representation (hash-based CSG/morphology, sparse 3D conv); operations on a loaded `tvdb_grid_t` (leaf iter, dilate/erode active or topology, tree-aware CSG, from-scratch rebuilders) |
| `tinyvdb_tree.h` | Checked float-tree diagnostics, signed flood fill, exact pruning and sparse/dense bridges |
| `tinyvdb_sparse_tools.h` | Sparse level-set tracking/rebuild, affine resampling, indexed/adaptive meshing and Poisson/PDE domains |
| `tinyvdb_sdf_tree.h` | In-place hierarchical SDF fast sweeping, filtering, morphology and offsets with compact active-voxel workspaces |
| `tinyvdb_thread.h` | Reusable synchronous task pool: C11, GCD, pthread or serial backend |
| `tinyvdb_autograd.h` | Per-op CPU VJPs (sample, splat, CSG, sparse_conv3d) — framework-free |
| `tinyvdb_simd.h` | Optional SSE4.2/AVX2/F16C primitives gated on `TINYVDB_SIMD` |
| `tinyvdb_gpu.h` | Optional runtime-loaded GPU backend: Vulkan and CUDA kernels for analytic sphere/box/torus SDF generation, dense CSG, dense trilinear batch sampling, and same-topology sparse conv3d |

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
sign comes from the closest face normal; sharp corners, open surfaces and
inconsistent face orientation can cause sign artifacts. Degenerate faces have
zero normals and contribute unsigned distances. The `_vdb` sign-method argument
remains advisory. Neither API promises a watertight manifold reconstruction.

## Features

### I/O (`tinyvdb_io.h`)

* [x] Dependency-free C11 code (header-only, single file)
* [x] Custom memory allocator interface (arena/pool allocator friendly)
* [x] mmap-based file access with heap-buffer fallback
* [x] UTF-8 path support on all platforms (Windows WideChar + long path `\\?\` prefix)
* [x] Cross-platform (Linux, macOS, Windows)
* [x] Big endian support (e.g., Power, SPARC)
* [x] Read and write OpenVDB files (version 220 to 225)
* [x] Multiple grid/tree topologies (not limited to `Tree_float_5_4_3`)
* [x] ZIP compression (via bundled miniz or system zlib)
* [x] BLOSC compression (built-in for OpenVDB `.vdb` files via bundled LZ4; NanoVDB BLOSC needs system libblosc — see `TINYVDB_USE_SYSTEM_BLOSC`)
* [x] Active mask compression (per-node flags 0-6)
* [x] Half-float (FP16) grid support
* [x] PointIndexGrid (`Tree_ptidx32_*`) leaf payload read/write
* [x] PointDataGrid (`Tree_ptdataidx32_*`) topology read + opaque point payload round-trip

### NanoVDB I/O (`tinyvdb_nanovdb.h`)

* [x] Read and write NanoVDB files (version 32+)
* [x] All standard grid types (Float, Double, Vec3f, Int32, …)
* [x] Compressed files: ZIP via miniz/zlib; **BLOSC** via system libblosc
  (opt-in `TINYVDB_USE_SYSTEM_BLOSC=ON`) — verified on
  `nanovdb_convert --blosc` output
* [x] Real Root → Upper → Lower → Leaf hierarchical accessor
  (`tvdb_nanovdb_get_voxel_f` / `_d`) — backed by vendored
  `nanovdb::PNanoVDB.h` (Apache-2.0)
* [x] Trilinear sampler (`tvdb_nanovdb_sample_trilinear_f`,
  cell-center convention)
* [x] Active-voxel test (`tvdb_nanovdb_is_voxel_active`) consults the
  real leaf value mask
* [x] CRC32 checksum compute / validate
  (`tvdb_nanovdb_compute_head_checksum`, `_compute_tail_checksum`,
  `_validate_checksum`) — head + 4KB-blocked tail, matches
  `nanovdb::tools::GridChecksum` byte-for-byte
* [x] **VDB → NanoVDB FloatGrid builder** (`tvdb_grid_to_nanovdb_float`)
  — converts a loaded `Tree_float_5_4_3` `tvdb_grid_t` into an
  in-memory NanoVDB byte buffer that passes `nanovdb_validate`
* [x] World ↔ index transforms (`tvdb_nanovdb_index_to_world` /
  `_world_to_index`) with adjugate-determinant inverse for
  rotation+scale+translation maps
* [x] Endianness handling, memory buffer I/O, node-size utilities

### Mesh (`tinyvdb_mesh.h`)

* [x] Triangle mesh to signed distance field (dense 3D grid)
* [x] SDF to triangle mesh (marching cubes)
* [x] Manifold preprocessing (mesh to SDF to mesh round-trip)
* [x] Configurable sign determination (flood fill or sweep)

### Grid operations (`tinyvdb_ops.h` + sibling headers)

* [x] Morphological dilation / erosion / open / close (dense, sparse,
  and tree-aware variants — `dilate_active` / `dilate_topology`)
* [x] Gaussian, mean, and Laplacian SDF filtering (dense + sparse)
* [x] CSG union / intersection / difference (dense, sparse, tree-aware)
* [x] Surface area and volume measurement
* [x] Differential operators: gradient, divergence, Laplacian, curl
* [x] Finite-difference stencils: central / forward / backward
* [x] Semi-Lagrangian advection (RK2)
* [x] Poisson solver (preconditioned conjugate gradient; fp32 + fp64)
* [x] Fast sweeping (Eikonal redistance, sign-preserving)
* [x] Ray-SDF intersection (sphere tracing); voxel-walk DDA;
  segments-along-ray; uniform ray samples
* [x] Trilinear sampling and splatting (single + batched, world↔voxel
  transforms); TSDF fusion (depth + RGB)
* [x] Topology ops: coarsen / refine / prune / clip / merge / max-pool /
  avg-pool
* [x] Sparse 3D convolution (single + multi-channel, hash-based O(1)
  neighbor lookup)
* [x] Volume to spheres (greedy adaptive sphere packing)
* [x] Particles to SDF (sphere stamping)
* [x] Level-set fracture (cutter-based volume splitting)
* [x] CPU autograd: per-op VJPs for sample, splat, CSG, and
  sparse_conv3d — gradient-checked against finite differences

### GPU backend (`tinyvdb_gpu.h`)

* [x] Optional `tinyvdb_gpu` C target (`TINYVDB_BUILD_GPU=ON`) with no
  compile-time Vulkan SDK, CUDA SDK, `vulkan.h`, `cuda.h`, `nvcc`, or SDK
  library requirement.
* [x] Runtime-loaded Vulkan compute backend (`libvulkan` / `vulkan-1.dll`)
  using local ABI definitions and SPIR-V kernels generated at build time when
  `glslangValidator` and `xxd` are available.
* [x] Runtime-loaded CUDA Driver API + NVRTC backend (`libcuda`/`nvcuda.dll`
  plus `libnvrtc`) that compiles kernels to PTX at runtime.
* [x] Blocking high-level C entrypoints for analytic sphere/box/torus SDF generation,
  dense CSG, dense trilinear batch sampling, and same-topology
  `tvdb_sparse_conv3d` on Vulkan and CUDA.
* [x] Vulkan sparse 3D image capability is reported in the context info field.
  Dense sampling has experimental regular and sparse-resident Vulkan
  `sampler3D` paths benchmarked against the default SSBO sampler, plus a
  persistent partial-residency path that binds only pages containing active
  sparse voxels, reuses sampler dispatch resources across queries, and supports
  device-resident query batches with batch-owned async submit/poll/wait.

The resident API in [`src/tinyvdb_gpu_resident.h`](src/tinyvdb_gpu_resident.h)
(included by `tinyvdb_gpu.h`) keeps volume data on the device across operations.
Create a dense handle with its shape, channels, precision, and geometry; upload
once, chain operations, and download explicitly. Dense composition, CSG,
filters, scalar/vector stencils, advection, morphology, resampling, reductions,
measurement, marching cubes, and Poisson have resident entrypoints. Sparse
handles support convolution, morphology, dense conversion, and point
voxelization. Topology-preserving sparse results share immutable coordinate
maps; topology-changing operations build and compact their maps on the device.

Typed processing operations preserve the previous output on failure and allow the aliasing
specified in their declarations. Calls are synchronous; serialize calls on a
context and destroy its handles before destroying the context. The raw
`tvdb_gpu_dispatch_resident` API accepts existing buffers and copied uniform
parameters, including a batch of dependent dispatches. Its outputs may be
partially written if a dispatch fails. Transfer/allocation counters report
logical resident-buffer bytes, not driver allocation sizes or total VRAM use.

Marching cubes classifies cells, scans triangle counts, then allocates and emits
only the compact triangle soup in CPU cell/table order. It reads back a single
four-byte triangle count before allocation. The former 180-byte-per-cell vertex
temporary is gone; offsets require four bytes per cell, plus the scan hierarchy
and actual output. Procedural tests cover all 256 cases, empty surfaces, exact
zeros, sparse surfaces, noisy fields, and multiple scan levels.

Resident Poisson supports float arithmetic, double arithmetic with float
storage at the API boundary, and double input/output. All three require device
fp64 for reductions. It retains solver vectors on the device and reads only
reduced scalars, preserving Neumann compatibility, the warm-start mean, and
residual reporting in the returned precision. Iteration counts can differ from
CPU reduction order. Solver workspace uses 40, 64, or 72 bytes per voxel for
the three modes, respectively; true residuals and reductions remain doubles.
Dependent kernels share a submission until a scalar readback is needed.
The float host API retains its existing path on devices without fp64.

Sparse resident convolution supports full signed coordinates and first-input
lookup semantics; transpose sums contributions from duplicate input points.
Transpose rejects candidate-coordinate overflow transactionally. The host
transpose API uses the resident path for representable candidates and retains
its existing clipped-boundary fallback for overflowing candidates. Resident point
voxelization currently uses isotropic spacing. Missing generated SPIR-V returns
`TVDB_ERROR_UNIMPLEMENTED` on Vulkan; CUDA remains usable through NVRTC.

Grid contents can be released with `tvdb_grid_destroy(grid, allocator)`, which
also releases metadata and point-data payloads. Use the allocator that owns the
descriptor strings and payload (`NULL` for the default allocator); tree and
metadata allocations retain their own allocators. `tvdb_grid_destroy_owned`
remains the convenience wrapper for grids built with the default allocator.

### Gaussian-splat rasterizer (`tinyvdb_nanovdb.h`)

* [x] CPU forward (`tvdb_gaussian_rasterize_forward`): per-tile
  depth-sorted alpha blend with fast tile binning
* [x] CPU backward (`tvdb_gaussian_rasterize_backward`): analytic
  gradients w.r.t. each gaussian's projected x/y, conic_a/b/c,
  opacity, and per-feature color — reverses the alpha blend without
  saving per-pixel intersection lists. Gradient-checked against
  central FD for all parameters
* [x] PLY I/O for splat scenes (load + save)

## Validation

tinyvdb is cross-validated against libopenvdb 13.0 + libnanovdb 32.9 in
the test suite (build with `-DTINYVDB_BUILD_TESTS=ON` and run `ctest`):

* **VDB**: 6-type reference corpus generated by libopenvdb
  (`scripts/gen_openvdb_reference.cc`) — `bool`, `float`, `double`,
  `int32`, `int64`, `vec3s` — round-trips through tinyvdb's
  reader/writer and the tinyvdb-written output reads back successfully
  in libopenvdb's `vdb_print`. Real `.vdb` corpus (sphere v224 BLOSC,
  bunny/cube/smoke v222 half-precision FLOAT) round-trips bit-exact
  (drift < 1e-10 for 5.5M-voxel bunny).
* **NanoVDB**: corpus generated by `nanovdb_convert` round-trips
  through tinyvdb's hierarchical accessor, trilinear sampler, and
  CRC32 head + 4KB-blocked tail validator (matches
  `nanovdb::tools::GridChecksum` byte-for-byte).
* **VDB → NanoVDB**: `tvdb_grid_to_nanovdb_float` produces NanoVDB
  buffers that `nanovdb_validate` accepts (exit 0) and
  `nanovdb_convert` reads back into a valid `Tree_float_5_4_3` `.vdb`
  with matching topology and value range.
* **Gaussian-splat rasterizer**: backward-pass gradients are
  gradient-checked against central finite differences for every
  parameter.
* **GPU backend**: when a Vulkan runtime/device is available,
  `test_gpu_backend` compares GPU analytic sphere/box/torus SDF generation, dense CSG,
  dense sampling, and sparse conv3d against the CPU implementations. The test
  skips cleanly when no runtime backend is available. Set
  `TVDB_GPU_TEST_VRAM_MB=1024` or `2048` for the opt-in larger Vulkan
  sparse-image benchmark; the planner treats this as a hard ceiling and uses a
  conservative fraction of it to avoid exhausting shared 8 GiB GPUs.

The test suite registers 24 ctest targets, or 48 when the optional GPU tests are
enabled — see `tasks.md` for the full table. `test_threads` runs every parallel op
at one thread and again at the widest team and requires bit-identical results, so
a kernel whose output came to depend on how the work was split fails rather than
passing on whichever thread count the host happened to default to.

## Supported VDB versions

| Version | Feature |
|---------|---------|
| 220 | Selective compression |
| 221 | Float frustum bbox |
| 222 | Node mask compression, per-grid compression flags |
| 223 | BLOSC compression, point index grid |
| 224 | Multipass I/O |
| 225 | Half-float grid type |

## How to use

### I/O library

Copy `src/tinyvdb_io.h`, `src/miniz.c`, `src/miniz.h`, `src/lz4.c`, and `src/lz4.h` to your project. BLOSC compression (LZ4) is built-in — no external dependency needed.

```c
/* In exactly one .c or .cc file: */
#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_io.h"
```

#### Reading a VDB file

```c
tvdb_file_t file;
tvdb_error_t err = {0};

tvdb_status_t st = tvdb_file_open(&file, "input.vdb", NULL, &err);
if (st != TVDB_OK) { /* handle error */ }

st = tvdb_read_all_grids(&file, &err);
if (st != TVDB_OK) { /* handle error */ }

for (size_t i = 0; i < tvdb_grid_count(&file); i++) {
    printf("Grid: %s  Type: %s\n",
           tvdb_grid_name(&file, i),
           tvdb_grid_type_name(&file, i));
}

tvdb_file_close(&file);
```

#### Writing a VDB file

```c
/* After reading/modifying a file, write it back: */
tvdb_status_t st = tvdb_file_save(&file, "output.vdb",
                                  TVDB_COMPRESS_BLOSC | TVDB_COMPRESS_ACTIVE_MASK,
                                  /*use_mmap=*/0, &err);
```

Or write to a memory buffer:

```c
uint8_t *data = NULL;
size_t data_size = 0;
tvdb_status_t st = tvdb_write_to_memory(&file,
                                        TVDB_COMPRESS_ZIP | TVDB_COMPRESS_ACTIVE_MASK,
                                        &data, &data_size, &err);
/* ... use data ... */
free(data);
```

### NanoVDB I/O library

```c
/* In exactly one .c or .cc file: */
#define TINYVDB_NANOVDB_IMPLEMENTATION
#include "tinyvdb_nanovdb.h"
```

#### Reading a NanoVDB file

```c
tvdb_nanovdb_file_t file;
tvdb_error_t err;
memset(&err, 0, sizeof(err));

tvdb_status_t st = tvdb_nanovdb_file_open(&file, "input.nvdb", NULL, &err);
if (st != TVDB_OK) { /* handle error */ }

for (size_t i = 0; i < tvdb_nanovdb_grid_count(&file); i++) {
    printf("Grid: %s  Type: %s\n",
           tvdb_nanovdb_grid_name(&file, i),
           tvdb_nanovdb_grid_type_name(tvdb_nanovdb_grid_type(&file, i)));
}

tvdb_nanovdb_file_close(&file);
```

#### Custom allocator

```c
tvdb_allocator_t alloc = {
    .malloc_fn  = my_malloc,
    .realloc_fn = my_realloc,
    .free_fn    = my_free,
    .user_ctx   = my_arena
};

tvdb_file_open(&file, "input.vdb", &alloc, &err);
```

The allocator passes `old_size` to `realloc_fn` and `size` to `free_fn`, enabling arena/pool allocators that don't track allocation sizes internally.

### Mesh library

Include `tinyvdb_mesh.h` and compile/link `src/tinyvdb_mesh.c`.

```cpp
// Mesh to SDF
tvdb_mesh::DenseGrid grid;
tvdb_mesh::MeshToSDF(mesh, voxel_size, band_width, &grid);

// SDF to mesh (marching cubes)
tvdb_mesh::TriangleMesh output;
tvdb_mesh::SDFToMesh(grid, 0.0f, &output);

// Manifold preprocessing (mesh -> SDF -> mesh round-trip)
tvdb_mesh::MakeManifold(input, resolution, isovalue, &output);
```

### Grid operations

Include `tinyvdb_ops.h` and compile/link `src/tinyvdb_ops.c` (plus the
sibling `.c` files for the ops you use; see CMake's
`tinyvdb_mesh_ops` target for the canonical list).

```cpp
// CSG union of two SDF grids
tvdb_ops::CSGUnion(grid_a, grid_b, &result);

// Gaussian smoothing
tvdb_ops::GaussianFilter(&grid, /*width=*/1, /*iterations=*/3);

// Ray-SDF intersection
tvdb_ops::RayHit hit;
if (tvdb_ops::RayCastSDF(grid, origin, dir, max_t, &hit)) {
    // hit.position, hit.normal, hit.t
}
```

## Compile-time defines

| Define | Description |
|--------|-------------|
| `TVDB_USE_SYSTEM_ZLIB` | Use system zlib instead of bundled miniz |
| `TVDB_HAVE_BLOSC` | Route NanoVDB BLOSC decompression through system libblosc (set automatically by `TINYVDB_USE_SYSTEM_BLOSC=ON`) |
| `TVDB_USE_ZSTD` | Enable ZSTD inside BLOSC frames |
| `TVDB_NO_MMAP` | Disable mmap; always read into heap buffer |

## CMake build

CMake build is provided for example/test builds.

### Setup

```
$ git submodule update --init --recursive --depth 1
```

### Build

```
$ mkdir build
$ cd build
$ cmake ..
$ make
```

### CMake options

| Option | Default | Description |
|--------|---------|-------------|
| `TINYVDB_BUILD_TESTS` | `OFF` | Build the test suite (24 CPU tests, or 48 with GPU tests enabled) |
| `TINYVDB_BUILD_BENCH` | `OFF` | Build `bench_tinyvdb`, the measurement harness behind `doc/bench-baseline.md` |
| `TINYVDB_BUILD_EXAMPLES` | `ON` | Build `vdbdump`, `nanovdbdump`, etc. |
| `TINYVDB_BUILD_VDBRENDER` | `ON` | Build the vdbrender volume path tracer |
| `TINYVDB_BUILD_PYTHON` | `OFF` | Build Python extension |
| `TINYVDB_USE_SYSTEM_ZLIB` | `OFF` | Use system zlib instead of bundled miniz |
| `TINYVDB_USE_ZSTD` | `ON` | Enable ZSTD inside BLOSC frames (bundled or system) |
| `TINYVDB_USE_SYSTEM_ZSTD` | `OFF` | Link system libzstd instead of `deps/zstd.c` |
| `TINYVDB_USE_SYSTEM_BLOSC` | `OFF` | Link system libblosc — required to read NanoVDB BLOSC files produced by libnanovdb |
| `TINYVDB_OPENMP` | `OFF` | Enable OpenMP parallelism in dense ops, Poisson CG, sparse conv, sample batches, TSDF fusion |
| `TINYVDB_SIMD` | `ON` | Enable SSE4.2/AVX2/F16C (x86-64 only; scalar fallback otherwise) |
| `TINYVDB_BUILD_GPU` | `ON` | Build the runtime-loaded Vulkan/CUDA backend (no SDK needed at build time) |
| `TINYVDB_BUILD_TVDBVIEW` | `ON` | Build the `tvdbview` viewer |
| `TINYVDB_USE_CCACHE` | `ON` | Use ccache when available |

`TINYVDB_BUILD_GPU` generates SPIR-V with `glslangValidator` when it is on `PATH`
and falls back to a build with no shaders otherwise; point
`TINYVDB_GLSLANG_VALIDATOR` at the binary to override the search. Without shaders a
context still creates and every GPU op returns `UNIMPLEMENTED`, so a caller can
tell "not built for this" from "genuinely unsupported" via
`tvdb_gpu_spirv_available()`.

## vdbdump example

A command-line tool that reads a VDB file and prints its structure:

```
$ ./vdbdump input.vdb --verbose
File: input.vdb
  VDB version: 224  (lib 6.2)
  UUID: 1569c382-d056-4c66-aa3e-9b0ca351fe91
  Grids: 1

Grid[0]: "surface"
  Type: Tree_float_5_4_3
  Tree: 4 levels [Root, Internal(log2dim=5), Internal(log2dim=4), Leaf(log2dim=3)]
  Background: 0.3
  Root: 0 tiles, 8 children
  Nodes: 25 total (16 internal, 8 leaf)
  Active voxels: 2.08K
  Transform: UniformScale
    Voxel size: (0.1, 0.1, 0.1)
  Compression: blosc+active_mask (0x6)
```

Write a copy with `--write` or `--write-mmap`:

```
$ ./vdbdump input.vdb --write output.vdb
$ ./vdbdump input.vdb --write-mmap output_mmap.vdb
```

## nanovdbdump example

A command-line tool that reads a NanoVDB file and prints its structure:

```
$ ./nanovdbdump input.nvdb --verbose
File: input.nvdb
  NanoVDB version: 32
  Grids: 1
  Codec: blosc

Grid[0]: "surface"
  Type: Float
  Class: LevelSet
  Grid size: 123456 bytes
  Voxel size: (0.1, 0.1, 0.1)
  World bbox: [(0, 0, 0), (100, 100, 100)]
  Index bbox: [(0, 0, 0), (999, 999, 999)]
  Active voxels: 123456
  Nodes: 10 leaf, 5 lower, 2 upper
  Tiles: 0 level0, 0 level1, 0 level2
```

## Python bindings

Install the Python extension:

```bash
pip install tinyvdb
```

Or build from source:

```bash
pip install .  # from the repository root
```

Usage:

```python
import tinyvdb

from contextlib import closing
from tinyvdb import nanovdb

# Open a NanoVDB file
with closing(nanovdb.NanoVDBFile("input.nvdb")) as f:
    print(f"Grids: {f.grid_count()}")
    for i in range(f.grid_count()):
        print(f"Grid {i}: {f.grid_name(i)}")
        print(f"  Type: {f.grid_type(i)}")
        print(f"  BBox: {f.bbox(i)}")
        print(f"  Voxel size: {f.voxel_size(i, 0)}")
    val = f.get(0, 100, 100, 100)
    print(f"Value at (100, 100, 100): {val}")
```

Writing:

```python
# Save to file
f.save("output.nvdb", codec=tinyvdb.CODEC_BLOSC)

# Write to bytes
data = f.to_bytes(codec=tinyvdb.CODEC_ZIP)
```

Writing a dense grid to `.vdb` (value type chosen from the numpy dtype —
`float32`/`float64`/`int32`/`int64`/`bool` scalar grids, or a `(nx, ny, nz, 3)`
`float32` array for a `vec3f` grid):

```python
import numpy as np, tinyvdb

sdf = np.random.randn(32, 32, 24).astype(np.float32)
tinyvdb.write_dense_grid("sdf.vdb", sdf, voxel_size=0.05)     # Tree_float_5_4_3
arr, voxel_size, origin = tinyvdb.read_dense_grid("sdf.vdb")  # dtype preserved
```

See `python/README.md` for the full dtype table and the `bool` caveat (tinyvdb's
1-byte-per-voxel BOOL layout is not byte-compatible with OpenVDB's bit-packed
format).

Utility functions:

```python
import tinyvdb

# Get node sizes
leaf_size = tinyvdb.leaf_node_size()      # Default: Float
leaf_size = tinyvdb.leaf_node_size(tinyvdb.GRID_TYPE_DOUBLE)

# Get value size
val_size = tinyvdb.value_size()            # 4 for Float
val_size = tinyvdb.value_size(tinyvdb.GRID_TYPE_VEC3F)  # 12
```

## Notes

### Terms

`background` is a uniform constant value used when there is no voxel data.

`Node` is composed of Root, Internal, and Leaf.
Leaf contains actual voxel data.

Root and Internal nodes have `Value` or a pointer to a child node, where `Value` is a constant value for the node.

There are two bit masks, `child mask` and `value mask`, for each internal node.

## License

TinyVDB is licensed under the [Apache License, Version 2.0](http://www.apache.org/licenses/LICENSE-2.0).

```
Copyright 2026 - Present Syoyo Fujita

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
```

### Third party licenses

| Library | License |
|---------|---------|
| OpenVDB (original I/O logic) | Apache 2.0 |
| LZ4 | BSD 2-Clause |
| miniz | MIT |
| tinyexr (vdbrender example) | BSD 3-Clause |
