# Changelog

## Unreleased

### Added

- A staged dense dual marching cubes API: `tvdb_sdf_to_mesh_dual_ex` (plus the
  `tvdb_sdf_to_mesh_dual` wrapper) emits one dual vertex per crossed cell and
  one quad per sign-changing primal edge into a new owning `tvdb_quad_mesh`
  (`src/tinyvdb_mesh_dual.h`). This first slice is **DMC-0 / surface nets**, not
  Nielson DMC-1: it has no per-cube MC patch decomposition, so its topology does
  not match the Lean DMC-1 vectors yet. It follows the `_ex` contract (status +
  error, output preserved on failure, arena rollback, alias rejection,
  deterministic emission), counts in parallel and emits in a fixed raster
  order. `tvdb_grid_volume_to_mesh_dual_ex` adds the sparse/tree variant with
  the same contract, using the grid transform and an active-bbox + margin scan
  (with a cell budget). It is still DMC-0, not Nielson DMC-1, and does not
  reproduce the Lean DMC-1 index vectors. `tests/test_mesh_dual.c` and
  `tests/test_mesh_dual_tree.c` check independent counts, watertightness,
  outward winding, determinism across worker pools and failure preservation.
  `tests/test_mesh_degenerate_sdf.c` adds mesh→SDF robustness coverage for
  degenerate/collinear faces, large coordinates and failure preservation; the
  double-precision closest-point fallback remains a documented limit of the
  Lean differential twin. An internal cube-local MC patch decomposition helper
  (`tvdb_dual_patch_compute`) and `tests/test_mesh_dual_patch.c` verify the
  256-case patch facts. A staged dense DMC-1 API
  (`tvdb_sdf_to_mesh_dual_one_ex`, `tvdb_sdf_to_mesh_dual_one`) now emits one
  vertex per (cell, MC patch) and one quad per crossed primal edge. Vertex
  placement minimises the QEF of the crossing planes (interpolated gradients,
  Cramer solve, centroid fallback and in-cell clamp).
  `tvdb_sdf_to_mesh_dual_one_padded_ex` (and its wrapper) adds a shell-pinned
  outside voxel around the lattice, so watertightness no longer requires the
  crossing surface to be strictly interior; the CTest regression shows an
  open 2,352-quad mesh becoming a closed 2,688-quad mesh on a boundary-touching
  sphere. `tvdb_grid_volume_to_mesh_dual_one_ex` (and its wrapper) adds the
  sparse/tree DMC-1 variant with index-space QEF placement and unconditional
  shell pinning; `tests/test_mesh_dual_tree_one.c` checks counts, watertightness
  (interior and boundary-touching spheres), determinism and the `_ex` contract.
  A C↔Lean DMC-1 topology differential (`lean/scripts/check_dmc1_topology.sh`)
  compares crossed-edge count, vertex count, quad count, component count,
  directed-edge closure and χ on all 256 shell-pinned fields; vertex indices,
  positions and patch ids are deliberately not compared.
  `tests/test_mesh_dual_one.c`
  checks counts, watertightness, winding and determinism on four analytic
  fields. The original DMC-0 functions are byte-identical.

### Changed

- **Breaking (C API/ABI and Python):** removed the dead
  `tvdb_header_t.half_precision` member and the matching `half_precision`
  key of the Python `VDBFile.header` dict. It was never set on read or write:
  the file header has no such byte, and half precision is a per-grid property
  (the `_HalfFloat` grid-type suffix and `is_saved_as_half_float` metadata),
  which is unchanged.
- The reader is stricter and now rejects inputs it used to accept:
  - file versions above 225 (`TVDB_FILE_VERSION_HALF_GRID`) fail with
    `TVDB_ERROR_UNSUPPORTED_VERSION` (only versions below 220 were rejected
    before), and a grid descriptor whose `block_byte_offset` is not between
    `grid_byte_offset` and `end_byte_offset` fails with
    `TVDB_ERROR_INVALID_DATA`;
  - grid-type strings must follow a strict grammar. Each `Tree_<type>_a_b_c`
    level is one or two digits in `0..10`, separated by single `_`.
    `Tree_float_5_4_3junk`, `5_4_`, `5__4_3` and `5_4_33` used to parse as
    zero-sized extra levels and now fail with
    `TVDB_ERROR_UNSUPPORTED_GRID_TYPE`;
  - node masks are no longer allocated at the size the grid type claims before
    checking it against the file: a claimed mask larger than the bytes left
    below the grid's `end_byte_offset` is rejected, so a crafted
    `Tree_float_10_10_10` can no longer force gigabyte-scale allocations, and
    tree reads can no longer run past the grid's declared end.
- Dense elementwise operations (`tvdb_csg_union`, `tvdb_csg_intersection`,
  `tvdb_csg_difference`, `tvdb_comp_max/min/sum/mult`, morphology and
  advection) now require both grids to have the same dimensions **and** the
  same `voxel_size` and origin (exact float equality). Grids that only
  matched in dimensions used to be blended voxel by voxel as if they
  occupied the same space, which gave silently misaligned results; a
  mismatch is now the documented no-op (the result grid is left untouched,
  consistent with the void return of these functions). The contract is spelled
  out in `tinyvdb_ops.h`.

### Fixed

- Half-precision float writing is now round-to-nearest-even and NaN-preserving
  in every build. The scalar `tvdb__float_to_half` used to truncate the
  mantissa, flush values below 2^-24 to zero and map NaN to Inf, while the
  F16C path (`_mm256_cvtps_ph`) rounded; the same grid therefore produced
  different bytes in SIMD and scalar builds. Both paths now agree with each
  other and with OpenVDB's `truncateRealToHalf`. `tests/test_half_rounding.c`
  covers rounding, subnormal flushing, signed zero, Inf and NaN round trips
  and fails on the old scalar encoder when `TINYVDB_SIMD=OFF`.
  The same encoder also evaluated an undefined 32-bit shift for floats with
  binary exponent 94 (`[2^-33, 2^-32)`), which on x86-64 produced a bogus
  non-zero half instead of +0; it is fixed and covered by the same test.
- Writing a boolean leaf after loading a file wrote `{0,0,0}` as the leaf
  origin, because the reader does not store node origins (they are implicit
  in the child-mask slot) and the writer emitted the stored field. The
  buffer-write traversal now computes the true origin, so load -> save keeps
  boolean leaves at their voxel position (`tests/test_bool_leaf_origin.c`).
- `tvdb_grid_to_nanovdb` and `tvdb_grid_to_nanovdb_float` now validate the
  source tree (root and node types and levels, child indices, mask storage,
  duplicated or cyclic children, leaf data) and return
  `TVDB_ERROR_INVALID_DATA` for a malformed tree. Previously a corrupt
  `child_indices` array could cause an out-of-bounds read, and children of
  an unexpected node type were silently dropped from the output
  (`tests/test_to_nanovdb_validation.c`).
- The sign of dense mesh -> SDF values (CPU, and the Vulkan, CUDA and HIP
  kernels) was taken from the closest *face's* normal. When the closest point
  of the mesh was on an edge or vertex, the adjacent faces can disagree, so
  voxels outside even a convex mesh could be signed negative, depending on the
  traversal tie-break. The sign now uses the closest feature: the face normal
  in a face interior, the sum of the two incident face normals on an edge, and
  on a vertex the incident face whose normal pairs positively with the
  offset to the query point (`tests/test_mesh_pseudo_normal.c`,
  `tests/test_mesh_vertex_sign.c`). Output values change only where the old
  sign was wrong.
- Finite differences at the boundary of a dense grid used a clamped-neighbour
  difference divided by `2h`, i.e. a one-cell difference at half strength.
  `tvdb_gradient`, `tvdb_central_diff_x/y/z`, divergence, curl and the
  closest-point transform now use a one-sided difference over `h` at boundary
  voxels (and 0 along an axis of size 1); interior voxels are unchanged. The
  Vulkan stencil shaders and the CUDA/HIP kernels match. Boundary voxel values
  of these operators change, and are now exact for linear fields.
- Builds with clang (including Apple clang and clang-cl) now pass
  `-ffp-contract=off` for C and C++. GCC's default is already off under the
  project's strict `-std=c11`, but clang's is on, so clang fused scalar
  `a*b+c` into FMAs in the SIMD sources (built with `-mfma`) and nowhere else.
  The same expression then rounded differently depending on which file it
  lived in: `tvdb_merge_grids` and `tvdb_gpu_merge_grids` computed merged grids
  one voxel apart (25 versus 26 in x for the `test_merge` case), which failed
  `test_gpu_backend` under clang. Numeric results of clang builds now match
  GCC's. Explicit FMA intrinsics are unchanged.
- The WASM module (`web/tinyvdb_embind.cc` via `web/CMakeLists.txt`) now builds
  with `CMAKE_CXX_STANDARD 17` instead of 11. Emscripten 5.x rejects C++11 for
  embind; 4.x (the CI pin) accepts C++17 too, so the bump is compatible both
  ways. The local Emscripten 5.0.1 build passes the Node smoke test
  (`web/test_wasm_smoke.js`, 183/183 checks).

## 0.9.1 — 2026-10-28

### Added

- `tvdb_mesh_to_level_set` (`tinyvdb_sparse_tools.h`): sparse narrow-band
  level set of a triangle mesh with exact closest-face distances, signs from
  generalized winding numbers (robust to open, inside-out and inconsistently
  oriented meshes), flood-filled interior and pruning; deterministic for any
  worker count.
- `tinyvdb_winding.h`: exact and fast generalized winding numbers.
- `tinyvdb_tetmesh.h`: isosurface stuffing tetrahedral meshes of SDF
  interiors (`tvdb_level_set_to_tet_mesh`, `tvdb_sdf_to_tet_mesh`) with
  watertight outward boundaries, positive orientation and
  `tvdb_tet_mesh_quality`.
- `tvdb_file_init_for_write`: set up a header and allocator for writing
  caller-owned grids without reading a file first.
- HIP backend (`TVDB_GPU_BACKEND_HIP`): AMD GPUs through runtime-loaded
  `libamdhip64` and `libhiprtc`, running the CUDA backend's kernels and code
  paths; `*_hip` variants of the CUDA tests.
- `tinyvdb_gpu_compute.h`: a lean CUDA/HIP device and GPU
  `tvdb_mesh_to_level_set`, level-set sampling and
  `tvdb_level_set_to_tet_mesh` (also on `tvdb_gpu_context_t`), with CPU-equal
  results; 24-32x faster level sets on an RX 9070 XT than 8 CPU threads.
  `tvdb_mesh_level_set_options_t.evaluate` and
  `tvdb_stuffing_options_t.batch_sample` let other batch evaluators plug in.
- `tinyvdb_winding.h` exposes the fast tree (`tvdb_winding_nodes`,
  `tvdb_winding_order`) for device ports.
- `tvdb_read_grid` / `tvdb_read_grid_header`: decode one grid, or only its
  header (metadata, transform, layout), instead of the whole file.
- `tvdb_grid_find_metadata`, `tvdb_grid_set_metadata(_string)`; vec3s
  metadata is read and written.
- OpenVDB MaskGrids (`Tree_mask_*`) read and write.
- `tinyvdb_volume.h`: `tvdb_grid_get_info` (class, value type, components,
  index-to-world, exact bounds from the tree or the file's bounding-box
  metadata), `tvdb_grid_to_dense_volume` (any value type, stride/budget box
  filter, windows, inactive-as-background) and `tvdb_volume_sampler_*`
  (nearest/trilinear, world or index space). `tvdb_tree_lookup` returns any
  type's stored value.
- `tvdb_grid_to_nanovdb`: float, double, int32, int64, vec3f, vec3d and mask
  grids, with the full affine map, the grid class, root tiles and exact node
  bounding boxes (`tvdb_grid_to_nanovdb_float` now wraps it).
- `test_io_openvdb` (OpenVDB oracle): affine maps both ways, lazy reads,
  typed grids through dense, sampler, info and NanoVDB (read back with
  PNanoVDB); `test_volume`.

- Checked float-tree diagnostics, signed flood fill, exact pruning, and sparse
  and dense bridges in `tinyvdb_tree.h`.
- Sparse level-set rebuild/tracking, affine nearest/trilinear resampling,
  indexed isosurface meshing, and active-domain Poisson/PDE solving in
  `tinyvdb_sparse_tools.h`, with corresponding `VDBGrid` Python methods.
- Optional comparisons against an installed OpenVDB library, allocation-failure
  regressions, and procedural fixtures for clean-checkout and wheel tests.

### Fixed and hardened

- Sparse tool coordinate maps rehashed on almost every insert once their
  table reached its 4/3 sizing (the half-load trigger sat right behind the
  new size), making large rebuilds, resamples and meshing quadratic; tables
  now double (186x faster on a 13k-voxel band).
- The OpenVDB oracle tests did not compile since exceptions and RTTI were
  disabled project-wide; they now enable both for their own targets.
- Mesh level sets build their candidate band from 8^3 bitmask bricks instead
  of a coordinate hash map and emit leaf order, so the tree builder skips its
  sort (`tvdb_grid_from_sparse*` now checks for sorted input): 5.7x less host
  time at 4.9M candidates, byte-identical output.
- Stuffing found boundary faces through a hash table of 8 slots per
  tetrahedron (1.8 GB and 3.6 s at 6.3M tets); a bucket pass by smallest
  vertex takes 16 bytes per face and ~0.4 s. Outside lattice cells are
  skipped and warp neighbors come from index arithmetic. Byte-identical
  output.
- `tvdb_gaussian_project` (3D Gaussian splatting) wrote a full 3x3 rotated
  covariance into a six-float stack array (indices 6-8 overflowed) and scaled
  the 2D covariance by `1/fx^2` instead of `(fx/z)^2`, dropped the z variance
  and read the xy term for the yy entry, so a radius-1 splat at depth 2 with
  `fx=800` projected to 0.004 px instead of ~1200 px and anisotropic rotations
  could yield a non-positive-definite conic. The projection now builds
  `J (R S R^T) J^T` with `J = [[fx/z, 0, -dx/z], [0, fy/z, -dy/z]]` and takes
  the radius from the covariance's major axis; the Vulkan shader and the
  embedded CUDA/HIP kernel use the same arithmetic. Culled splats are zeroed
  (they previously kept uninitialised conic/x/y/feature fields). New
  `test_gaussian_project` compares the conic and radius against an independent
  reference, checks the 90-degree view-axis symmetry, culling, opacity and
  features. Rendered splat sizes change; the device parity test needs a GPU.
- Surface meshing looked every edge up in one ~100 MB hash table per axis, so
  the polygonize pass was DRAM-latency bound (0.65 s of the teapot level-set
  run). Edges are now bucketed into three live x slabs per axis: a cell can
  only reference an edge whose lower corner sits at its own x or the next one,
  so a three-slot ring of small maps (a few hundred KB, cache resident) covers
  any border, cleared per slab. Vertex numbering and output are unchanged;
  teapot 1.99 s -> 1.65 s, bunny 1.58 s -> 1.30 s.
- The merged cell list was one global qsort. Each slice now sorts its own cells
  as it finishes and the merge is a k-way heap merge with the repeats dropped
  on the fly: teapot 1.65 s -> 1.36 s, bunny 1.30 s -> 1.10 s, icosahedron
  0.09 s -> 0.07 s, byte-identical.
- The stuffing warp pass scanned all 14 lattice edges of every vertex. A
  vertex farther than sqrt(3) spacings from the isovalue cannot be crossed by
  any edge (a signed distance field changes by at most that over the longest
  edge), so the scan is skipped for it: teapot level set at 1.0 spacing
  0.45 s -> 0.29 s at eight workers, byte-identical. The sampler contract now
  states the 1-Lipschitz requirement this relies on.
- Surface-cell classification recomputed a box index per corner
  (`(z*n + y)*n + x` eight times a cell); it now computes the cell's base
  index once and adds precomputed per-corner offsets (teapot level set
  1.36 s -> 1.27 s, bunny 1.10 s -> 1.02 s), and adaptive clustering computes
  its per-vertex cluster keys on the pool.
- Grid buffers written by `tvdb_grid_to_nanovdb*` carried the legacy
  `NanoVDB0` number as `GridData::magic`; NanoVDB's C++ `GridHandle` and
  `nanovdb::io` expect `NanoVDB1` (tinyvdb's own reader accepts both). They
  now write `NanoVDB1`, matching what `test_nanovdb_roundtrip` builds by hand.
- The GPU level-set sampler (CUDA/HIP) flattened the float tree into host
  arrays on every call - per-node origin/type/log2dim/value+child offsets,
  every slot value, per-slot child indices and a root hash - and uploaded them,
  which capped grids at `INT32_MAX` entries and made small edits re-upload the
  whole tree. It now converts the grid once with `tvdb_grid_to_nanovdb` and the
  kernel reads NanoVDB's own layout (root tiles, upper/lower internal nodes,
  leaves) through `src/tinyvdb_nanovdb_device.h`: one buffer, no size cap. The
  accessor is an ordinary header, so NVRTC and hiprtc compile the same text the
  new host test `test_nanovdb_device` compares against the CPU tree lookup
  (214k voxels over a generated 5-4-3 sphere, including internal tiles, root
  tiles, the background and negative coordinates). On the RTX 5060 Ti
  `test_gpu_volumetric cuda` samples 200k points with 0 differences and builds
  the same 18757 tets as the CPU; HIP compiles with hipcc.
- Isosurface stuffing extracted the watertight boundary with a single-threaded
  counting sort plus a fused sort/singleton pass (1.65 s of the 2.9 s teapot
  level-set run). The counting sort now runs on the pool: each slice counts
  into a private per-bucket cursor table, a prefix sum lays the cursors out in
  slice order, the slices scatter, and bucket ranges are sorted and emitted in
  parallel with exact output offsets. Byte-identical meshes for any worker
  count; teapot level set 2.90 s -> 1.64 s, bunny 0.30 s -> 0.20 s on eight
  threads, single-thread unchanged.
- Surface meshing classified every crossing cell from each of its voxels in
  the narrow band, i.e. up to eight times, and scanned all six slabs of every
  interior tile. A cell is now classified once, by the lowest-numbered voxel
  the walk visits (its `tool_scan` cost drops to one per cell), and an interior
  tile whose whole shell stays on its side of the isovalue skips the slab scan.
  Byte-identical meshes; teapot level set 2.18 s -> 2.01 s, bunny 1.72 s ->
  1.61 s, bunny_cloud at 0.1 4.96 s -> 4.12 s. `max_cells * 32` still bounds
  cell classifications, so it now bounds slightly more real work than before
  (redundant repeats no longer consume it).
- Level-set stuffing sampled every lattice vertex with an uncached tree
  descent (8 lookups per vertex). Each 4096-vertex pool slice now opens its
  own tree accessor, so the leaf lookup is cached: the teapot level set at
  0.5 spacing went from 1.40 s to 0.90 s of sampling on one thread (3.14 s to
  3.03 s for the whole mesh at four). Byte-identical output.
- Sparse tree CSG looked up both inputs uncached per output voxel; it now
  keeps one accessor per input (3.24 s to 2.60 s for the teapot level set
  unioned with itself, 7.0M voxels; identical output).
- `tvdb_grid_volume_to_mesh` classified surface cells on one thread with one
  global cell hash. It now collects the surface-adjacent regions in tree order
  and classifies them on the task pool, with one cell map and one tree
  accessor per slice, merging by sort so the mesh is byte-identical for any
  worker count: teapot level set 7.2 s to 2.2 s, bunny 5.2 s to 1.7 s on eight
  threads, at a lower peak footprint (the per-slice probe tables are released
  before the merged copy). The cell budget is counted across slices, so
  `max_cells` still bounds memory globally. `tvdb_grid_volume_to_mesh_pooled`
  accepts a caller's pool.
- Sparse-tool coordinate maps store coordinates in their slots (one cache
  line per probe).
- AffineMap matrices were read and written verbatim, i.e. transposed: real
  OpenVDB affine grids were rejected by every tool (`tvdb_tree_matrix`) and
  tinyvdb-written ones were misplaced in OpenVDB.
- VDB → NanoVDB dropped root tiles (large flood-filled interiors read the
  background), wrote only the diagonal of the map and no grid class.

- Preserve initialized outputs on constructor failure and reject malformed
  trees, invalid transforms, nonfinite inputs, and unsupported active tiles.
- Count active tile volumes and detect coordinate-bound overflow. Sparse tree
  CSG checks complete transforms and uses stored inactive values; morphology
  uses fixed inactive boundaries on every iteration.
- Make repeated grid reads transactional and independently owned. Python views
  reject access after close, reload, or replacement and during native work;
  maintenance results remain valid after their source file closes. Revalidate
  views after argument conversion that can invoke Python callbacks. Preserve
  `None` reference ownership when wheels built with newer Python headers run
  on Python 3.11.
- Remove CPU Gaussian rasterization's tile cap, use complete symmetric
  footprints and stable depth ordering, and correctly composite backgrounds.
  Backward evaluation supports opaque splats and preserves failed accumulators.
- Publish GPU hash coordinates before duplicate comparisons, fixing races in
  Vulkan and CUDA insertion/compaction.

### Packaging and migration

- Python requires **3.11+**, matching the existing `cp311-abi3` extensions.
  CMake, package metadata, and `tinyvdb.__version__` now agree on 0.9.1.
- Default Python wheels build scalar CPU kernels without AVX2, OpenMP, or GPU
  dependencies. Optimized native/source builds can explicitly enable these
  options. NumPy remains optional at runtime for array convenience functions.
- Source archives exclude local state, nested worktrees, build products, and
  unused upstream TinyEXR examples/test assets while retaining dependency
  licenses and the maintained VDB fixtures. The build backend requires
  scikit-build-core 0.11+ for the SPDX license metadata.
- Expose the bundled NanoVDB binding as `tinyvdb.nanovdb`; correct examples
  to use its method-based grid count and `contextlib.closing`.
- New C constructors require distinct initialized owning outputs; release grids
  with `tvdb_grid_destroy_owned`. Flat extraction rejects active tiles instead
  of silently losing topology. Flood-fill inside widths are negative; rebuild
  inside widths are positive magnitudes. Meshing adaptivity is a world-distance
  displacement bound, rather than OpenVDB's normalized adaptivity parameter.

The new sparse tools run on the CPU. Rebuild/tracking reconstructs geometric
distance from a resolved closed surface; it does not provide OpenVDB's iterative
advection tracker. Classic marching cubes and vertex clustering do not guarantee
manifold topology. Poisson uses immediate neighbors on orthogonal grid axes;
see the public header and README for boundary conditions and convergence reports.
