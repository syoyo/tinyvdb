# tinyvdb tasks

Outstanding work and known gaps in tinyvdb's reader/writer, as discovered while
integrating it into the lightgeom_gui VDB viewer. Items are ordered roughly by
priority for general-purpose VDB I/O parity with libopenvdb.

## Status legend

- [x] done in `fix/half-and-vec-types` branch
- [ ] open

## Reader fixes (already landed)

- [x] **Vec3 value reader** — `tvdb__sr_read_value` now handles `VEC3I/F/D`,
  so a grid whose root or inactive-tile background is a vec3 (e.g. velocity
  `Tree_vec3s_5_4_3`) loads instead of failing with
  "Failed to read root background value".
- [x] **Vec3 negate** — `tvdb__negate_value` negates the three components for
  vec3 types, used to derive `inactive_val0 = -background` on signed-flood-
  filled vec3 level sets.
- [x] **Half-precision empty-node read** — `tvdb__read_mask_values` now
  matches OpenVDB's `HalfReader::read` early-return: when `is_half &&
  read_count == 0` no blosc size header is read. Without this, every
  all-inactive half-precision internal node drifted 8 bytes and exploded
  downstream.
- [x] **Root background propagation** — `tvdb__read_root_topology` builds a
  local `child_params` with the just-read `root->background` and passes it
  into the recursive descent. Previously every internal-tile inactive value
  came back as 0 because the caller-supplied `params.background` was still
  zero-initialised when child topology started.
- [x] **PointDataGrid (`ptdataidx32_*`) recognition** — `tvdb__parse_grid_type`
  maps the prefix to `INT32` for topology parsing, and `tvdb__read_grid`
  detects any grid type containing `ptdataidx` and seeks to
  `end_byte_offset` after topology, so the embedded `AttributeSet` blob does
  not misalign subsequent grids.

## Writer fixes (already landed)

- [x] **Interleaved grid layout** — `tvdb_write_to_memory` now emits each grid
  as `[descriptor][grid data]` immediately, instead of writing all
  descriptors up front and grid data after. OpenVDB and tinyvdb's own
  reader both expect the interleaved form; the old layout corrupted every
  multi-grid file. Single-grid files happened to work and hid the bug.
- [x] **Uncompressed-fallback sentinel** — when blosc/zip cannot shrink a
  block, the writer used to emit `-1` as the size header. OpenVDB's
  `bloscFromStream` interprets `numCompressedBytes <= 0` as
  "uncompressed of length `-numCompressedBytes`", so `-1` is read as
  "expected 0-byte chunk, got 1-byte chunk" and throws. The writer now
  emits `-(int64_t)total_size`, matching openvdb's `bloscToStream`. Fixed
  in all three (BLOSC, system zlib, miniz) fallback branches.
- [x] **Zero-length sentinel** — for `total_size == 0` the writer used to
  emit `-1` (same problem). It now emits `0`, matching openvdb.
- [x] **Half-precision write empty-node guard** — mirror of the read-side
  fix. When `is_half && write_count == 0`, `tvdb__write_mask_values` skips
  `tvdb__compress_and_write` entirely so we don't emit a header that
  `HalfWriter::write` never would have written.
- [x] **`MASK_AND_NO_INACTIVE_VALS` selection-mask convention** — the
  writer's analysis swaps `inactive_val0/val1` to put the "special" value
  first for storage, but the reader has a fixed convention for that flag
  (`val0 = -bg, val1 = +bg`). The local swap silently flipped the meaning
  and turned interior tiles into +bg on round-trip. The writer now re-pins
  `val0 = -bg, val1 = +bg` for that flag and the mask-build loop tests
  only `v == inactive_val1` (no longer ORed with `bg_bytes`, which was
  marking every cell ON for the no-inactive-vals case).
- [x] **Vec3 value writer** — `tvdb__sw_write_value` emits VEC3I/F/D as
  three components. Without this the root background of a vec3 grid was
  silently skipped, the stream went out of alignment, and subsequent
  reads saw "0 children" — dropping the entire tree.
- [x] **Vec3 inactive value negate on write** — already covered by the
  vec3 negate read fix; the writer's analysis loop now sees the right
  bytes for the `-background` comparison.

## Verified round-trips

All checked bit-exact through libopenvdb's `pyopenvdb`:

| file | grids | type(s) | result |
| --- | --- | --- | --- |
| `suzanne.vdb` | 1 | `Tree_float_5_4_3` (fog volume) | bit-exact |
| `fire.vdb` | 2 | `Tree_float_5_4_3` density + temperature | bit-exact |
| `explosion.vdb` | 3 | `Tree_float_5_4_3` density+temperature, `Tree_vec3s_5_4_3` velocity | bit-exact |
| `bunny_half.vdb` | 1 | `Tree_float_5_4_3` (level set, `save_float_as_half=true`) | within 1 ULP at half precision (lossless modulo half quantisation) |

## Open tasks

## Open Tasks

### High Priority (Integration & Stability)

- [x] **Public regression suite for openvdb interop.** Added `scripts/regression_test.sh` which performs round-trips using `vdbdump --write` and verifies grid topology/stats parity using `vdb_print`. Verified on 12 test files from `data/`.
- [x] **Full PointDataGrid Attribute support.** Implemented `AttributeSet` and paged stream reading logic. Supports MultiPass I/O, attribute descriptor/metadata parsing, and loading of uniform/non-uniform attribute data (including Blosc decompression of pages). Point grids are now **fully loadable** (not just topology-only).
- [x] **Compression flag preservation across grids.** Ensure per-grid compression modes (e.g. blosc vs zip) are preserved during multi-grid `tvdb_file_save`.

### Medium Priority (Features & Interop)

- [x] **Affine & Vector Transformations.** Implemented full write path support for `UniformScaleMap`, `ScaleMap`, `UniformScaleTranslateMap`, `ScaleTranslateMap`, and `TranslationMap`, ensuring parity with the reader's transform parsing.
- [x] **Advanced VDB Tools.** Port foundational OpenVDB tools.
    *   **Foundation (High):** [x] `SignedFloodFill` (sign consistency), [x] `Mask` (topology ops), [x] `Prune` (`tvdb_prune_grid` snaps near-background voxels), [x] `ChangeBackground`, [x] `FindActiveValues`.
    *   **Processing (Medium):** [x] `Morphology` (dilation/erosion, `tvdb_dilate`/`tvdb_erode`/`tvdb_open`/`tvdb_close` plus sparse + tree-aware variants `dilate_active`/`erode_active`/`dilate_topology`/`erode_topology`), [x] `Composite` (`tvdb_csg_union`/`intersection`/`difference` for dense; sparse + tree-aware variants), [x] `Filter` (`tvdb_gaussian_filter`/`mean_filter`/`laplacian_filter`), [x] `TopologyToLevelSet`.
    *   **Advanced (Low):** [ ] `FastSweeping` (deferred), [x] `LevelSetAdvect` (`tvdb_advect_semi_lagrangian`), [x] `VolumeToMesh` (`tvdb_sdf_to_mesh` marching cubes + batched variant `tvdb_marching_cubes_batch`), [x] `RayTracer` (`tvdb_ray_cast_sdf`, `tvdb_voxels_along_ray` Amanatides-Woo DDA, `tvdb_segments_along_ray`, `tvdb_uniform_ray_samples`).

- [x] **MeshToVolume / mesh → SDF voxeliser.** Implemented as a lightweight, header-only utility in `src/tinyvdb_mesh.h`, supporting triangle mesh to SDF conversion, marching cubes extraction, and manifold preprocessing.
- [x] **Advanced Mathematical Solvers.** Implemented a preconditioned conjugate gradient (PCG) solver for Poisson's equation (`SolvePoisson`) in `src/tinyvdb_ops.h`. Also added `tvdb_solve_poisson_d` (fp64 internal CG) for ill-conditioned problems where the fp32 path stalls.
- [x] **SIMD-accelerated grid operations.** `src/tinyvdb_simd.h` provides AVX2 fp32 dot/AXPY and F16C bulk fp16↔fp32 conversion, gated on `TINYVDB_SIMD` CMake option (default ON). All paths have scalar fallbacks via `#ifdef`. Wired into Poisson CG dot kernel. Measured ~2.25× speedup on 8M-elem dot, ~3× on 16M-elem fp16 conversion. Verified parity in `tests/test_simd.c`.
- [x] **OpenMP threading with build flag.** `TINYVDB_OPENMP` CMake option (default OFF). When ON, `#pragma omp parallel for` annotates per-voxel loops in dense ops (gradient/divergence/laplacian/curl/advection), Poisson CG (fp32+fp64), sparse_conv3d, sample batches, and TSDF integration. Scalar path bit-identical when OFF. ~5.9× speedup on 64³ Poisson at 8 threads.

### CPU-friendly fvdb feature port (landed)

The following capabilities were ported from `fvdb-core` for CPU use, sized to
fit tinyvdb's "header-first, dependency-free, pure C public API" design.
Implementations live in `src/tinyvdb_*.{h,c}` and are wired through
`python/tinyvdb/__init__.py` via Py_LIMITED_API bindings.

- [x] **Sampling / splat.** `tvdb_sample_trilinear_dense` (single + batched),
  `tvdb_sample_trilinear_vec_dense`, `tvdb_splat_trilinear_dense` (cell-center
  convention; world↔voxel via `tvdb_apply_xform`).
- [x] **TSDF fusion.** `tvdb_integrate_tsdf` (depth-only) and
  `tvdb_integrate_tsdf_with_color` (depth + RGB) with single-frame and
  multi-frame in-place variants (`*_into`). `tvdb_invert_rigid_pose` helper.
- [x] **Topology ops.** `tvdb_coarsen_grid` / `tvdb_refine_grid` (factor-N
  block average / trilinear), `tvdb_clip_grid`, `tvdb_prune_grid`,
  `tvdb_merge_grids` (SDF union).
- [x] **Pooling.** `tvdb_max_pool` and `tvdb_avg_pool` over kx×ky×kz blocks.
- [x] **Ray ops.** Amanatides-Woo DDA (`tvdb_voxels_along_ray`),
  `tvdb_uniform_ray_samples`, isosurface segments (`tvdb_segments_along_ray`),
  batched marching cubes (`tvdb_marching_cubes_batch`).
- [x] **Sparse grid representation.** Flat (coords[], values[]) layout
  (`tvdb_sparse_grid`) with hash-based CSG and morphology
  (`tvdb_csg_*_sparse`, `tvdb_dilate_sparse`, `tvdb_erode_sparse`),
  dense↔sparse materializers, and active-coord enumeration.
- [x] **Sparse 3D convolution.** `tvdb_sparse_conv3d`: same-topology
  fp32 convolution with arbitrary kx×ky×kz kernel, anchor at floor(k/2),
  hash-based O(1) neighbor lookup.
- [x] **OpenVDB-tree sparse bridge.** `src/tinyvdb_sparse_tree.{h,c}`
  operates directly on a loaded `tvdb_grid_t`:
    *   `tvdb_grid_visit_leaves_float` (DFS leaf iterator)
    *   `tvdb_grid_active_voxel_count` / `tvdb_grid_active_bbox`
    *   `tvdb_grid_to_sparse` / `tvdb_grid_materialize_dense`
    *   `tvdb_grid_dilate_active` / `tvdb_grid_erode_active`
      (leaf-stamp, topology-preserving)
    *   `tvdb_grid_dilate_topology` / `tvdb_grid_erode_topology`
      (topology-changing)
    *   `tvdb_grid_csg_union` / `intersection` / `difference`
      (tree-aware CSG)
    *   `tvdb_grid_update_from_sparse` (write sparse coords back into
      existing leaves; topology-preserving)
- [x] **From-scratch VDB tree builder.** `tvdb_grid_from_sparse_using_template`
  rebuilds a `tvdb_grid_t` (Tree_float_5_4_3) from a flat sparse_grid using
  another grid as the layout template. The built grid round-trips through
  `tvdb_file_save` / `tvdb_file_open`. Wired to Python as
  `VDBFile.replace_grid_from_sparse`. Enables saving topology-changing op
  results (dilate_topology, sparse CSG, sparse_conv3d) to .vdb.
- [x] **Particle-to-SDF / volume-to-spheres / fracture.** Implemented in
  the Python C wrapper (`particles_to_sdf`, `volume_to_spheres` greedy
  medial-axis cover, `fracture` N+1 piece split).
- [x] **Numpy zero-copy buffer protocol.** PEP 3118 buffers on
  `DenseGrid` (3D, float32), `DenseVecGrid` (4D, float32), and
  `TriangleMesh` (vertices: 2D float32, faces: 2D uint32). No pybind /
  nanobind dependency.
- [x] **End-to-end capstone demo.** `scripts/capstone_demo.py`: particles
  → SDF → gradient/laplacian → 8-pose 360° depth fly-around →
  multi-frame TSDF fusion → volume_to_spheres medial cover →
  marching-cubes mesh → OBJ output. Produced 4568 verts / 16270 faces.

### Test coverage

CTest registers 11 tests under `build/`:

| target | what |
| --- | --- |
| `test_ops` | Phase 1-6 dense ops smoke (volume, surface_area, dilate, csg, gradient, Poisson recovery, advection, sampling, TSDF, topology, ray, sparse) |
| `test_sparse_tree` | OpenVDB-tree bridge on `sphere.vdb`: counts, bbox, sparse extraction, dense materialization, leaf-stamp dilate/erode |
| `test_grid_from_sparse` | Sphere round-trip + synthetic 27-leaf cross-parent test for `tvdb_grid_from_sparse_using_template` |
| `test_simd` | SIMD vs scalar parity for dot, AXPY, fp16 round-trip, fp16 encoder ≤1 ULP |
| `test_fast_sweeping` | Sphere SDF redistance: 8-sweep Eikonal recovery against analytic distance, max-error within voxel_size |
| `test_vec3_extend` | Vec3 builder via `tvdb_grid_from_sparse_vec3_using_template` (round-trip 8-voxel leaf, root background type-tagged VEC3F); `tvdb_grid_extend_from_sparse` topology growth (sphere + 4 far-off coords → +3 leaves, +4 active) |
| `test_dense_d` | fp64 dense grid: lifecycle, fp32↔fp64 round-trip, trilinear sample exactness at lattice points, CSG, lap(x²)=2 interior, sphere volume/area within 5%, fast_sweeping_d to <1×voxel, Poisson_dd recovery to ~3e-15 RMS (machine precision) |
| `test_autograd` | Per-op VJPs (`tinyvdb_autograd.{h,c}`): trilinear sample VJP w.r.t. grid + points, splat VJP w.r.t. values, CSG union/intersection/difference VJPs, sparse_conv3d VJP w.r.t. values + kernel — every analytic gradient checked against finite differences |
| `test_nanovdb_transform` | NanoVDB `world_to_index` / `index_to_world` round-trip on uniform-scale + rotation+scale+translation; singular-matrix error path |
| `test_scalar_writer_audit` | INT32 / INT64 / DOUBLE / BOOL grids built via the typed sparse-tree builder, saved, reloaded, and verified voxel-by-voxel. Caught two real bugs: wrong `grid_type` descriptor string for non-float values (writer said `Tree_float_5_4_3` regardless of type) and missing `int64_` parser in the reader. BOOL is self-consistency-only (1 byte per voxel) — not byte-compatible with OpenVDB's bit-packed BOOL leaf format |
| `test_bridge_ops_py` | Python end-to-end on `sphere.vdb`: dilate_active/erode_active/dilate_topology/erode_topology counts, self-CSG idempotence, update_from_sparse → save → reload |

### Low Priority / Larger Features (fVDB / GPU)

- [ ] **Jagged Tensor API.** Sparse variable-length data container (parallels `fvdb::JaggedTensor`).
- [ ] **GridBatch abstraction.** Spatial indexing container for high-performance batched GPU operations (parallels `fvdb::GridBatch`).
- [ ] **Differentiable Operators (Autograd).** PyTorch autograd integration for spatial operations.
- [ ] **High-performance GPU Dispatch system.** Generic kernel dispatch mechanism for sparse grid topology/types (parallels `fvdb::dispatch`).
- [ ] **Sparse Gaussian Splatting Rasterizer.** Differentiable forward/backward rasterization (parallels `fvdb::detail::autograd`).

### Misc Fixes

- [x] **Audit scalar writer paths for `INT32` / `INT64` / `DOUBLE` /
  `BOOL` grids.** Built via the public
  `tvdb_grid_from_sparse_typed_using_template` (typed core promoted from
  internal); saved with `tvdb_file_save`; reloaded and verified
  voxel-by-voxel in `test_scalar_writer_audit`. Two bugs found and
  fixed for the int/double path: (a) typed builder set
  `descriptor.grid_type` to the template's string regardless of actual
  value type, so a DOUBLE grid was advertised as `Tree_float_5_4_3` and
  read back with 4-byte values; (b) reader's grid-type-string parser
  had no case for `int64_`, so any INT64 grid we wrote refused to
  reload. BOOL also round-trips through our reader/writer, but with
  the self-consistency caveat: tinyvdb stores BOOL voxels as 1 byte
  each (0/1) on disk and in memory, while OpenVDB stores them as a
  64-byte bit-packed buffer per leaf. Files we write with BOOL grids
  will not load in DCCs (Houdini / Blender) until that gap is closed,
  which needs a reference OpenVDB-produced BOOL .vdb to validate the
  on-disk packing against.
- [ ] **Reader: integrate-and-test with delayed-load metadata grids.**
- [x] **`tvdb_value_type_size(BOOL) = 1` fix.** BOOL grids are now handled as bit-packed masks in leaf nodes, matching OpenVDB's serialization format (dedicated path in `tvdb__read_leaf_buffer` and `tvdb__write_leaf_buffer`).
- [ ] **`MultiPassIO` ≥ v224** handler.
- [ ] **Half-precision file format prior to v225** backward compatibility.

## Remaining items (fvdb-port scope)

Honest list of what's still missing or scope-limited from the CPU-friendly
fvdb feature port. These are non-blockers for the documented workflows but
worth knowing.

### Open

- [x] **Tree builder generalized to typed values.** Refactored
  `tvdb_grid_from_sparse_using_template` to a typed core; the float entry
  is now a thin wrapper. New `tvdb_grid_from_sparse_vec3_using_template`
  accepts `(coords[], values[count*3], background[3])` and builds a
  `Tree_vec3s_5_4_3` grid from a vec3-typed template. Root background is
  type-tagged correctly. Other 4-level layouts (DOUBLE, INT32, INT64,
  VEC3I, VEC3D) are all routed through the same core; adding their
  public wrappers is mechanical. Still 4-level only (`num_levels == 4`,
  matching the standard `5_4_3` hierarchy).
- [x] **Topology-extending `update_from_sparse`.**
  `tvdb_grid_extend_from_sparse(existing, sg, name, bg, out)` rebuilds
  an owned grid containing every active voxel in `existing` plus every
  coord in `sg` (sg wins on overlap, new leaves are created where
  needed). Uses hash-based dedup over sg's coords against the
  extracted-existing sparse set, then dispatches to the typed builder.
  Float layouts only.
- [x] **Multi-channel sparse convolution.** `tvdb_sparse_conv3d_mc`:
  c_in input channels, c_out output channels, kernel laid out
  `kernel[(((dk*ky+dj)*kx+di)*c_out+co)*c_in+ci]`. Wired to Python as
  `tinyvdb.sparse_conv3d_mc`. Verified with identity + channel-mix
  kernels.
- [x] **F16C wiring inside `tinyvdb_io.h` half-precision path.**
  `tvdb__demote_float_to_half` and `tvdb__promote_half_to_float` now
  use AVX2/F16C 8-wide intrinsics when `TINYVDB_SIMD` is on, with
  scalar fallback. Brings the ~3× SIMD speedup to all half-precision
  .vdb load/save paths.
- [x] **Splat parallelization.** `tvdb_splat_trilinear_dense` now
  uses `#pragma omp parallel for` with `omp atomic update` on per-tap
  scatter writes. Bit-identical to scalar when OpenMP is off; safe
  under contention when on.
- [x] **Filters on sparse grids (Python).**
  `tinyvdb.gaussian_filter_sparse`, `mean_filter_sparse`, and
  `laplacian_filter_sparse`. Each builds a kernel and dispatches to
  `sparse_conv3d`. Accept either a sparse-grid dict or a `VDBGrid`.
  Same-topology output (out-of-active-set taps contribute 0).
- [x] **fp64 dense grid type (subset).** `tvdb_dense_grid_d` in
  `tinyvdb_ops.{h,c}` with double-precision storage and matching
  ops: lifecycle (`init`/`free`), fp32↔fp64 converters
  (`tvdb_dense_grid_f_to_d` / `tvdb_dense_grid_d_to_f`), trilinear
  sampling, 7-point Laplacian, CSG (union/intersection/difference),
  surface_area / volume measurements, FastSweeping (`fast_sweeping_d`),
  and a fully fp64-in/out Poisson PCG solver (`tvdb_solve_poisson_dd`,
  distinct from the existing `tvdb_solve_poisson_d` which is fp32-in/out
  with fp64 internals). All ops are OpenMP-parallel where the fp32 path
  is. Ops not yet ported to fp64: morphology, separable filters,
  advection, gradient/divergence/curl, ray ops, splatting (convert via
  `_d_to_f` and use the fp32 path until needed). Adding any of these
  follows the same mechanical pattern.
- [x] **`FastSweeping` (Eikonal redistance).** `tvdb_fast_sweeping`
  in `tinyvdb_ops.{h,c}`: 8-direction 3D fast sweeping (Zhao 2005)
  with Godunov upwind quadratic, sign-preserving. Voxels with
  `|phi| <= frozen_band` are kept fixed as boundary conditions; the
  rest are redistanced. Wired to Python as `tinyvdb.fast_sweeping`.
  Verified: sphere-SDF redistance produces max-error < 1×voxel_size.

- [x] **CPU autograd (per-op VJPs).** `tinyvdb_autograd.{h,c}` — explicit
  vector-Jacobian-product functions for the differentiable ops, mirroring
  fvdb's PyTorch custom Function backwards but framework-free. Landed:
  - `tvdb_sample_trilinear_dense_vjp_grid` / `_vjp_pts`
  - `tvdb_splat_trilinear_dense_vjp_values`
  - `tvdb_csg_{union,intersection,difference}_vjp`
  - `tvdb_sparse_conv3d_vjp_values` / `_vjp_kernel`
  All accumulate into output buffers (caller zeros for absolute gradients);
  CSG VJPs split ties 50/50 to remain a valid subgradient. Python
  bindings exposed for sparse_conv VJPs (`tinyvdb.sparse_conv3d_vjp_values`
  / `_vjp_kernel`); dense VJPs are C-only for now. Every analytic gradient
  is gradient-checked against finite differences in `test_autograd`.

- [x] **NanoVDB world↔index transform helpers.**
  `tvdb_nanovdb_index_to_world` / `tvdb_nanovdb_world_to_index` apply
  the grid's 3x4 row-major affine `map[12]` (now exposed on the
  user-facing `tvdb_nanovdb_grid_t`). Inverse is computed by adjugate /
  determinant for general 3x3 (uniform-scale, rotation+scale+translation
  all handled). Singular matrices return `TVDB_ERROR_INVALID_DATA`.
  Loaded grids inherit the map from `gd.map`; freshly-created grids get
  identity. Verified: round-trip preserves coords to 1e-10 on rotated +
  non-uniformly scaled + translated grids.

### NanoVDB gaps still open (need reference `.nvdb` files)

The rest of the NanoVDB punch list cannot land cleanly without a real
`.nvdb` produced by official OpenVDB tools to validate against. Without
that, any implementation is self-consistent but can't be confirmed
byte-compatible with Houdini / the official `nanovdb::validateGrid`. The
gaps:

- [ ] Real `tvdb_nanovdb_get_voxel_f` (Root → Upper → Lower → Leaf
      traversal). Today it reads `leaf_data_offset+64` as a flat array,
      which only works for the synthetic test grid.
- [ ] VDB → NanoVDB Float SDF builder. `tvdb_nanovdb_create_grid` builds
      metadata only; `examples/openvdb2nanovdb/openvdb2nanovdb.cc` is
      empty.
- [ ] `tvdb_nanovdb_sample_trilinear_f`. Trivial once the accessor
      lands.
- [ ] CRC32 checksum compute / validate. Algorithm is documented but
      bit-compatibility needs a reference `.nvdb` to verify which byte
      ranges are hashed.
- [ ] Real BLOSC framing (replace fake LZ4-with-fake-header).
- [ ] Backward pass for the Gaussian-splat rasterizer.

To unblock: add a small `data/*.nvdb` corpus produced by
`openvdb_print --addnv` or NanoVDB's `nanovdb_make_grid_test`, and these
items become straightforward to implement and test.

### Out of scope (deferred)

- All of the **fVDB / GPU** items below — JaggedTensor, GridBatch,
  autograd, GPU dispatch, Gaussian splatting rasterizer — require a
  tensor framework + CUDA, both fundamentally out of tinyvdb's design.


## Notes for downstream consumers

- After applying the writer fixes above, any tinyvdb-produced VDB should
  open in DCCs that use libopenvdb (Houdini, Blender, Maya, Hydra). If you
  hit a "blosc decompression failed" or "expected an N-byte uncompressed
  chunk" message from openvdb, the most likely culprit is the
  `total_size` sentinel on the write side — verify you have all four
  fixes from the "Writer fixes" section.

- For the lightgeom_gui debug-roundtrip flow: the current
  `tvdb_file_save` reuses the file-level compression flags from grid 0
  and re-emits the data uncompressed if blosc cannot shrink it, so the
  output file may be larger than the input. Bit-exact data round-trip is
  preserved (verified above).
