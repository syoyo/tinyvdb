# tinyvdb tasks

This file tracks open work. Completed items have been pruned; their
history is in `git log` (and the test-suite enumeration below documents
what's covered).

## Open

### In-scope (pure-C, CPU, dependency-free)

Gap analysis vs OpenVDB `openvdb/tools/` and fvdb-core ops (reviewed
2026-06-19). All items below are algorithmically CPU-portable and
consistent with tinyvdb's header-first, no-CUDA design; each was
grep-verified absent from `src/*.h`. Ordered high→low value within
each theme. Notes point at the nearest existing primitive to reuse.

**A. Level-set primitives & SDF utilities**

- [x] **Level-set primitive generators.** `tvdb_level_set_sphere/box/
      torus/capsule` + `tvdb_level_set_platonic` (tetra/cube/octa/dodeca/
      icosa) (parallels OpenVDB `LevelSetSphere`/`LevelSetTubes`/
      `LevelSetPlatonic`). Analytic narrow-band dense SDFs in
      `tinyvdb_levelset.{h,c}`; Python `level_set_sphere/box/torus/capsule/
      platonic` + named `level_set_tetrahedron/cube/octahedron/dodecahedron/
      icosahedron`. Covered by `test_levelset` (C + py).
- [x] **SDF utilities (LevelSetUtil).** `tvdb_sdf_to_fog_volume`,
      `tvdb_sdf_interior_mask`, `tvdb_sdf_segmentation` (interior connected
      components → one SDF grid each) and `tvdb_sdf_extract_enclosed_regions`
      (cavity mask). Python `sdf_to_fog_volume` / `sdf_interior_mask` /
      `sdf_segmentation` / `sdf_extract_enclosed_regions`. Covered by
      `test_levelset` (C + py).
- [x] **Level-set measure extensions.** `tvdb_level_set_euler_characteristic`
      & `tvdb_level_set_genus` (parallels OpenVDB `LevelSetMeasure`) — exact
      cubical-complex χ of the interior, χ(surface)=2·χ(solid), genus =
      components − χ(solid). Python `level_set_euler_characteristic` /
      `level_set_genus`. Covered by `test_levelset` (C + py).
      `tvdb_surface_area` / `tvdb_volume` already existed.
- [x] **Level-set rebuild from isosurface.** `tvdb_level_set_rebuild`
      (parallels OpenVDB `LevelSetRebuild`): marching-cubes the isovalue
      surface then mesh-to-SDF into a clean narrow band, with optional
      resampling and re-signing from the input. Python `level_set_rebuild`.
      Covered by `test_levelset` (C + py). NOTE: inherits `mesh_to_sdf`'s
      brute-force O(voxels·triangles) cost — keep voxel sizes coarse.

**B. Statistics, diagnostics & operators**

- [ ] **Active-voxel statistics.** min/max/mean/stddev/extrema +
      histogram over active voxels (parallels OpenVDB
      `Statistics`/`Extrema`/`Histogram`). Walk via `tvdb_grid_visit_leaves`.
- [ ] **Diagnostics / validators.** `check_level_set`, `check_fog_volume`
      (parallels OpenVDB `Diagnostics`).
- [ ] **Vector-grid operators.** `magnitude`, `normalize`,
      closest-point-transform `cpt` (parallels OpenVDB `GridOperators`);
      gradient/divergence/laplacian/curl already done.
- [ ] **Additional filters.** Median filter, mean-curvature flow
      (parallels OpenVDB `Filter`/`LevelSetFilter`); gaussian/mean/
      laplacian already done.
- [ ] **General composite.** `comp_max`/`comp_min`/`comp_sum`/`comp_mult`
      over value grids (parallels OpenVDB `Composite`); SDF CSG min/max
      already done.

**C. Resampling & advection**

- [ ] **Arbitrary-transform resampling.** `resample_to_match` with
      point/box/quadratic sampler order (parallels OpenVDB
      `GridTransformer::resampleToMatch`); only integer `coarsen_grid` /
      `refine_grid` exist today.
- [ ] **Higher-order advection.** RK3/RK4, MacCormack, BFECC + flux
      limiters (CLAMP/REVERT) (parallels OpenVDB `VolumeAdvect`); RK2
      semi-Lagrangian already done.
- [ ] **Signed flood fill.** Narrow-band sign propagation (parallels
      OpenVDB `SignedFloodFill`); currently only implicit inside the
      `mesh_to_sdf` sign methods.

**D. fvdb-style spatial queries & sampling**

- [ ] **Coordinate utilities.** `ijk_to_index` (active-set linear index),
      world↔voxel batch transforms, morton/hilbert codes (parallels fvdb
      `IjkToIndex`, `MortonHilbertFromIjk`); `tvdb_apply_xform` is the
      existing transform primitive.
- [ ] **Spatial queries.** `points_in_grid`, `coords_in_grid`,
      `cubes_in_grid`, neighbor enumeration (parallels fvdb
      `PointsInGrid`/`CoordsInGrid`/`NeighborIndexes`).
- [ ] **Grid-from-points voxelization.** Occupancy grid from a point
      cloud (parallels fvdb `from_points` /
      `from_nearest_voxels_to_points`); `mesh_to_sdf` done, point-cloud
      voxelization not.
- [ ] **Higher-order sampling.** Bezier/quadratic sample + splat with
      VJPs (parallels fvdb `SampleBezier`, OpenVDB `QuadraticSampler`);
      trilinear sample/splat + VJPs already done.
- [ ] **Volume-render helper.** Alpha-compositing ray-march as a library
      function (parallels fvdb `VolumeRender`); currently lives only in
      the `vdbrender` example.
- [ ] **Point rasterization & scatter.** `points_to_mask`, uniform point
      scatter inside an SDF (parallels OpenVDB `PointsToMask`/`PointScatter`).

### Out of scope (CUDA / tensor framework)

Fundamentally outside tinyvdb's "header-first, dependency-free, pure-C
public API" design — listed for visibility, not on the near-term roadmap.

- [ ] **Jagged Tensor API.** Sparse variable-length data container
      (parallels `fvdb::JaggedTensor`).
- [ ] **GridBatch abstraction.** Spatial indexing container for
      high-performance batched GPU operations
      (parallels `fvdb::GridBatch`).
- [ ] **PyTorch autograd integration** for spatial operations.
      (CPU per-op VJPs are already in `tinyvdb_autograd.{h,c}`; this
      task is specifically about wiring them into PyTorch's autograd
      graph as `torch.autograd.Function` subclasses.)
- [ ] **High-performance GPU dispatch system.** Generic kernel dispatch
      mechanism for sparse grid topology/types (parallels
      `fvdb::dispatch`).
- [ ] **GPU Gaussian-splat rasterizer.** A CUDA forward+backward to
      complement the CPU forward (`tvdb_gaussian_rasterize_forward`)
      and the CPU backward (`tvdb_gaussian_rasterize_backward`,
      gradient-checked in `test_gaussian_backward`).

## Test coverage (current)

16 ctests register under `build/`:

| target | what |
| --- | --- |
| `test_ops` | Phase 1-6 dense ops smoke (volume, surface_area, dilate, csg, gradient, Poisson recovery, advection, sampling, TSDF, topology, ray, sparse) |
| `test_levelset` | Level-set primitive generators (sphere/box/torus/capsule): analytic SDF recomputed and matched at every voxel; platonic solids (tetra/cube/octa/dodeca/icosa) bracketed between inscribed/circumscribed spheres; `sdf_to_fog_volume` range/empty-exterior, `sdf_interior_mask` sign-consistency, `sdf_segmentation` (two spheres → exact 2-way interior partition), `sdf_extract_enclosed_regions` (spherical-shell cavity mask) and `level_set_euler_characteristic`/`level_set_genus` (sphere 2/0, torus 0/1, two spheres 4/0, two tori 0/2) and `level_set_rebuild` (damaged sphere renormalized: euler 2, zero crossing ~R; torus resampled keeps genus 1) |
| `test_sparse_tree` | OpenVDB-tree bridge on `sphere.vdb`: counts, bbox, sparse extraction, dense materialization, leaf-stamp dilate/erode |
| `test_grid_from_sparse` | Sphere round-trip + synthetic 27-leaf cross-parent test for `tvdb_grid_from_sparse_using_template` |
| `test_simd` | SIMD vs scalar parity for dot, AXPY, fp16 round-trip, fp16 encoder ≤1 ULP |
| `test_fast_sweeping` | Sphere SDF redistance: 8-sweep Eikonal recovery against analytic distance, max-error within voxel_size |
| `test_vec3_extend` | Vec3 builder via `tvdb_grid_from_sparse_vec3_using_template`; `tvdb_grid_extend_from_sparse` topology growth |
| `test_dense_d` | fp64 dense grid: lifecycle, fp32↔fp64 round-trip, trilinear sample exactness, CSG, lap(x²)=2 interior, Poisson_dd recovery to ~3e-15 RMS |
| `test_autograd` | Per-op VJPs (sample, splat, CSG, sparse_conv3d): every analytic gradient checked against finite differences |
| `test_nanovdb_transform` | NanoVDB world↔index round-trip on uniform-scale + rotation+scale+translation; singular-matrix error path |
| `test_scalar_writer_audit` | INT32 / INT64 / DOUBLE / BOOL grids built via the typed sparse-tree builder, saved, reloaded, voxel-by-voxel verified |
| `test_corpus_roundtrip` | `.vdb` corpus: sphere v224 BLOSC, bunny/cube/smoke v222 half-precision FLOAT, sphere-div1/div2 v224 BLOSC. Round-trip through reader/writer; counts + value sums compared |
| `test_reference_roundtrip` | libopenvdb-generated reference grids (bool/float/double/int32/int64/vec3s) round-trip through tinyvdb. Cross-tool byte-format guard |
| `test_gaussian_backward` | Gaussian-splat rasterizer backward pass: 16×16 image from 4 random gaussians, all 36 analytic gradients checked against central FD |
| `test_nanovdb_reference` | nanovdb_convert-produced `.nvdb` corpus: hierarchical accessor + trilinear sampler + CRC32 checksum validation + VDB→NanoVDB conversion exactness |
| `test_bridge_ops_py` | Python end-to-end on `sphere.vdb`: dilate/erode/CSG/update_from_sparse → save → reload |
| `test_dense_writer` (py) | Dense + sparse `.vdb` writer/reader: float SDF (raw + numpy), all compression modes, multi-leaf, analytic sphere, plus typed `write_dense_grid`/`read_dense_grid` and `write_sparse_grid`/`read_sparse_grid` round-trips for `float64`/`int32`/`int64`/`vec3f`/`bool` with grid-type-string checks |

## Notes for downstream consumers

- Any tinyvdb-produced `.vdb` should open in DCCs that use libopenvdb
  (Houdini, Blender, Maya, Hydra). If you hit a "blosc decompression
  failed" or "expected an N-byte uncompressed chunk" message from
  openvdb, the most likely culprit is the `total_size` sentinel on the
  write side — confirm you're at or above the commit that fixed BLOSC,
  ZIP, and miniz fallback branches.

- For the lightgeom_gui debug-roundtrip flow: `tvdb_file_save` reuses
  the file-level compression flags from grid 0 and re-emits the data
  uncompressed if BLOSC cannot shrink it, so the output file may be
  larger than the input. Bit-exact data round-trip is preserved.

- NanoVDB BLOSC-compressed files require building with
  `TINYVDB_USE_SYSTEM_BLOSC=ON` (links libblosc); the legacy
  fake-LZ4 fallback is retained only for backwards compatibility with
  previously-written tinyvdb files.

- The reference corpora under `data/reference/` (`.vdb`) and
  `data/reference_nvdb/` (`.nvdb`) are gitignored — regenerate via
  `scripts/gen_openvdb_reference.cc` and `nanovdb_convert` respectively
  (recipes in `tests/test_reference_roundtrip.c` and
  `tests/test_nanovdb_reference.c`).
