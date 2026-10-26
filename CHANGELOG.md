# Changelog

## 0.10.0 — release candidate

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
  CMake, package metadata, and `tinyvdb.__version__` now agree on 0.10.0.
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
