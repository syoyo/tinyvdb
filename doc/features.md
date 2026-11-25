# Features

> Extracted from the [TinyVDB README](../README.md) for detailed reference.

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
* [x] MaskGrid (`Tree_mask_*`) read/write (bool trees whose values are the active state)
* [x] Per-grid reads: `tvdb_read_grid` decodes one grid, `tvdb_read_grid_header`
  only its metadata, transform and layout (class, file bounding box, voxel
  count) without touching voxel data
* [x] Grid metadata access: `tvdb_grid_find_metadata`, `tvdb_grid_set_metadata`
  (bool, int32, int64, float, double, vec3i, vec3s, vec3d, string)
* [x] AffineMap transforms in OpenVDB's row-vector layout, held in memory as
  column-vector matrices (`world = matrix * (i, j, k, 1)`); checked against
  libopenvdb in both directions (`test_io_openvdb`)

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
* [x] Runtime-loaded HIP backend (`TVDB_GPU_BACKEND_HIP`: `libamdhip64` plus
  `libhiprtc`, found on the loader path or under `$ROCM_PATH`, `/opt/rocm`)
  for AMD GPUs. The HIP driver API has the CUDA one's C ABI, so a HIP context
  fills the CUDA loader table and runs every CUDA code path, with the same
  kernel source compiled by hiprtc. The CUDA parity tests run on HIP as
  `*_hip` ctest variants. ROCm is never unloaded once loaded (unloading it
  leaves LLVM options registered and a reload crashes).
* [x] Blocking high-level C entrypoints for analytic sphere/box/torus SDF generation,
  dense CSG, dense trilinear batch sampling, and same-topology
  `tvdb_sparse_conv3d` on Vulkan and CUDA.
* [x] Vulkan sparse 3D image capability is reported in the context info field.
  Dense sampling has experimental regular and sparse-resident Vulkan
  `sampler3D` paths benchmarked against the default SSBO sampler, plus a
  persistent partial-residency path that binds only pages containing active
  sparse voxels, reuses sampler dispatch resources across queries, and supports
  device-resident query batches with batch-owned async submit/poll/wait.

The resident API in [`src/tinyvdb_gpu_resident.h`](../src/tinyvdb_gpu_resident.h)
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

#### Sparse level sets and tetrahedral meshes on CUDA/HIP

`tinyvdb_gpu_compute.h` runs `tvdb_mesh_to_level_set`, level-set sampling and
`tvdb_level_set_to_tet_mesh` on a CUDA or HIP device (`tvdb_gpu_compute_create`,
or the `tvdb_gpu_mesh_to_level_set` family on a `tvdb_gpu_context_t`). The
device does the per-point work: closest-face distance and winding number per
candidate voxel, and the stuffing lattice samples. The host keeps the sparse
bookkeeping, through hooks on the CPU options (`evaluate`, `batch_sample`), so
outputs follow the CPU rules and are deterministic.

The kernels compile with floating-point contraction off and repeat the CPU's
arithmetic:
- distances use the same BVH, closest-point code and tie-break (in float, then
  double);
- winding numbers walk the same tree in float (the CPU uses double), so signs
  can differ only at voxels on the surface, where the distance is zero to
  rounding;
- lattice samples are the CPU's double trilinear interpolation.

On an RX 9070 XT the level sets of the test meshes were byte-identical to the
CPU's except for such on-surface voxels, and stuffing meshes were identical.
Timings against the CPU on 8 Threadripper 1950X threads:

| Input | CPU | HIP (RX 9070 XT) |
|---|---|---|
| Mug, 24,544 faces, voxel extent/160 (0.98M candidates) | 8.2 s | 0.34 s |
| Mug, voxel extent/320 (4.9M candidates) | 40.8 s | 1.28 s |
| Bunny, 4,968 faces, voxel extent/256 (2.3M candidates) | 11.6 s | 0.46 s |
| Stuffing the extent/160 mug at spacing extent/192 (6.35M tets) | 7.0 s | 2.0 s |

The first call on a device compiles the kernels (0.1 s with a warm hiprtc
cache). `tests/bench_volumetric` reproduces these (`--gpu cuda|hip
--compare`); `test_gpu_volumetric` checks parity. Vulkan contexts return
`TVDB_ERROR_UNIMPLEMENTED`. CUDA shares the kernel source and code paths with
HIP; NVRTC compiles it, but no NVIDIA device was available to run it.

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
* [x] CPU projection (`tvdb_gaussian_project`): EWA conic from the full 3x3
  covariance and pinhole Jacobian (including the z variance), three-sigma
  radius from the major axis, culled splats zeroed
* [x] PLY I/O for splat scenes (load + save)
