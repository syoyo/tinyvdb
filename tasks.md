# tinyvdb tasks

This file tracks open work. Completed items have been pruned; their
history is in `git log` (and the test-suite enumeration below documents
what's covered).

## Open

### In-scope (pure-C, CPU, dependency-free)

Gap analysis vs OpenVDB `openvdb/tools/` and fvdb-core ops (reviewed
2026-06-19). All items below are algorithmically CPU-portable and
consistent with tinyvdb's header-first, CPU-core design; each was
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

- [x] **Grid statistics.** `tvdb_grid_statistics` (min/max/mean/stddev/sum)
      + `tvdb_grid_histogram` (parallels OpenVDB `Statistics`/`Histogram`) in
      `tinyvdb_stats.{h,c}`; Python `grid_statistics` / `grid_histogram`.
      Covered by `test_stats_ops` (C + py).
- [x] **Diagnostics / validators.** `tvdb_check_level_set` (band |grad|≈1
      health) + `tvdb_check_fog_volume` (values in [0,1]) (parallels OpenVDB
      `Diagnostics`); Python `check_level_set` / `check_fog_volume`.
- [x] **Vector-grid operators.** `tvdb_magnitude`, `tvdb_normalize_vec`,
      closest-point-transform `tvdb_cpt` (parallels OpenVDB `GridOperators`)
      in `tinyvdb_ops.{h,c}`; Python `magnitude` / `normalize` / `cpt`.
      Covered by `test_stats_ops` (C + py).
- [x] **Additional filters.** `tvdb_median_filter` + `tvdb_mean_curvature_flow`
      (parallels OpenVDB `Filter`/`LevelSetFilter`); Python `median_filter` /
      `mean_curvature_flow`. Gaussian/mean/laplacian already existed.
- [x] **General composite.** `tvdb_comp_max`/`min`/`sum`/`mult` over value
      grids (parallels OpenVDB `Composite`); Python `comp_max`/`comp_min`/
      `comp_sum`/`comp_mult`. SDF CSG min/max already existed.

**C. Resampling & advection**

- [x] **Arbitrary-transform resampling.** `tvdb_resample_grid` to any
      `voxel_size` over the same world AABB, with `order` 0 nearest / 1
      trilinear / 2 triquadratic (parallels OpenVDB
      `GridTransformer::resampleToMatch`). Python `resample_grid`. Covered by
      `test_resample_advect` (C + py); generalizes integer coarsen/refine.
- [x] **Higher-order advection.** `tvdb_advect` with RK1-4 semi-Lagrangian
      backtrace + MacCormack + BFECC error compensation and a stencil clamp
      limiter (parallels OpenVDB `VolumeAdvect`). Python `advect(field, vel,
      dt, scheme=, clamp=)` + `ADVECT_RK1..ADVECT_BFECC` constants. Covered by
      `test_resample_advect` (C + py).
- [x] **Signed flood fill.** `tvdb_signed_flood_fill` (parallels OpenVDB
      `SignedFloodFill`): flood far voxels (|value|>=band) from the grid
      boundary → +band exterior / -band interior, restoring interior signs.
      Python `signed_flood_fill`. Covered by `test_resample_advect` (C + py).

**D. fvdb-style spatial queries & sampling**

- [x] **Coordinate utilities.** `world_to_ijk`/`ijk_to_world` batch
      transforms, `morton_encode`/`morton_decode` (Z-order), and `ijk_to_index`
      (index into an active coord set) in `tinyvdb_grid_index.{h,c}` (parallels
      fvdb `IjkToIndex`/`MortonHilbertFromIjk`). Covered by `test_grid_index`
      (C + py). (Hilbert codes not implemented.)
- [x] **Spatial queries.** `coords_in_grid`, `points_in_grid`, and
      `neighbor_counts` (6/26) via an int3→index hash (parallels fvdb
      `PointsInGrid`/`CoordsInGrid`/`NeighborIndexes`). Python `coords_in_grid`
      / `points_in_grid` / `neighbor_counts`.
- [x] **Grid-from-points voxelization.** `tvdb_voxelize_points` — world point
      cloud → unique occupied voxel coords (parallels fvdb `from_points`).
      Python `voxelize_points`.
- [x] **Higher-order sampling.** `tvdb_sample_quadratic_dense` (+ batch)
      triquadratic sampling (parallels OpenVDB `QuadraticSampler`); Python
      `sample_quadratic`. Covered by `test_grid_index` (py). *Still open:*
      quadratic splat + sampling VJPs (trilinear sample/splat + VJPs done).
- [x] **Volume-render helper.** `tvdb_volume_render` in `tinyvdb_render.{h,c}`:
      emission-absorption alpha compositing of a density grid with a pinhole
      camera (ray-AABB clip + front-to-back march), parallels fvdb
      `VolumeRender`. Python `volume_render` -> (H,W) float image. Covered by
      `test_grid_index` (C + py).
- [x] **Point rasterization & scatter.** `points_to_mask` (rasterize a point
      cloud to a dense occupancy grid) and `scatter_points_in_sdf` (rejection-
      sample points inside an SDF interior) — Python helpers over
      `voxelize_points` / `sample_trilinear` (parallels OpenVDB
      `PointsToMask`/`PointScatter`). Covered by `test_grid_index` (py).

### Optional GPU backend (runtime-loaded, no SDK dependency)

- [x] **Vulkan compute backend v1.** `tinyvdb_gpu.{h,c}` adds an optional
      `tinyvdb_gpu` target and C API for runtime-loaded GPU contexts with no
      compile-time Vulkan SDK/CUDA SDK headers or link libraries. Vulkan uses
      local ABI definitions, `dlopen`/`LoadLibrary`, `vkGetInstanceProcAddr`,
      `vkGetDeviceProcAddr`, and SPIR-V compute kernels for analytic sphere/box/torus
      SDF generation, dense CSG, dense trilinear batch sampling,
      same-topology sparse conv3d, and an experimental sampled-image dense
      trilinear path with both regular and
      sparse-resident image allocation benchmarked against the SSBO sampler.
      Covered by `test_gpu_backend` (skips with code 77 when no Vulkan
      runtime/device is available).
- [x] **CUDA driver-loader API.** `tvdb_gpu_enumerate_devices` detects
      `libcuda`/`nvcuda.dll` plus `libnvrtc`, and the public backend enum/context
      API supports CUDA contexts.
- [x] **CUDA kernels.** Runtime-loaded CUDA Driver API + NVRTC kernels matching
      the Vulkan v1 operation set: analytic sphere/box/torus SDF generation, dense CSG,
      dense trilinear batch sampling, and same-topology sparse conv3d. Covered
      by `test_gpu_backend` when CUDA device access is available.
- [x] **GPU analytic SDF primitive generation.**
      `tvdb_gpu_level_set_sphere`, `tvdb_gpu_level_set_box`, and
      `tvdb_gpu_level_set_torus` mirror the CPU grid sizing/origin conventions
      and fill dense narrow-band SDFs on Vulkan compute or CUDA/NVRTC. Covered
      by `test_gpu_backend` against CPU metadata and voxel-value parity.
- [x] **Vulkan sparse 3D image binding path.** Context info exposes a
      sparse-image capability field and dense sampling has a
      `sparseBinding` + `sparseResidencyImage3D` path that binds all pages
      resident, uploads through a staging buffer, samples through `sampler3D`,
      and benchmarks against the SSBO fallback.
- [x] **Partial sparse 3D residency for active sparse voxels.** Sparse-grid
      upload binds only pages touched by active coordinates, copies only those
      page regions from staging, samples through `sampler3D`, and benchmarks
      against dense SSBO upload on the same logical grid.
- [x] **Persistent Vulkan sparse image resources.** Public opaque
      `tvdb_gpu_vulkan_sparse_image3d_t` objects keep sparse image allocation,
      page binds, upload, image view, and sampler alive across repeated sample
      calls; benchmark covers one-shot partial sparse upload versus persistent
      sparse image sampling.
- [x] **Persistent Vulkan dispatch resources.** Persistent sparse-image objects
      reuse sample point/output/uniform buffers, descriptor set bindings,
      command buffer, fence, and compute pipeline across repeated sample calls,
      growing the workspace only when sample count exceeds capacity.
- [x] **Device-resident query batches.** Public
      `tvdb_gpu_vulkan_sample_batch_t` objects keep point/result/param buffers
      resident across repeated sparse-image sample dispatches, with explicit
      readback separated from dispatch timing.
- [x] **VRAM-budgeted GPU benchmarks.** `test_gpu_backend` keeps default GPU
      memory use small and supports opt-in `TVDB_GPU_TEST_VRAM_MB=1024` or
      `2048` stress runs. The planner treats the value as a hard ceiling,
      clamps requests to 2 GiB, and uses a conservative fraction of the budget
      to avoid disrupting other processes on 8 GiB cards.
- [x] **Async/nonblocking Vulkan queue API.** Persistent sparse-image batch
      sampling has submit/poll/wait variants using runtime-loaded
      `vkGetFenceStatus`, so callers can separate queue submission from
      synchronization and readback.
- [x] **Multi-in-flight Vulkan query batches.** Async state now lives on
      `tvdb_gpu_vulkan_sample_batch_t`: each batch owns descriptor/command/fence
      state, so multiple batches can be submitted against the same persistent
      sparse image and polled/waited independently.

**Reference GPU op inventory (OpenVDB / NanoVDB / fvdb-core, reviewed
2026-06-20)**

- **OpenVDB core:** no CUDA/GPU implementation found under
      `openvdb/openvdb/openvdb`; GPU-facing work in the local checkout lives in
      NanoVDB and fvdb-core.
- **NanoVDB CUDA:** device buffers/handles, grid upload/download,
      points/voxels-to-grid, multi-GPU points-to-grid, index-to-grid,
      topology builder, dilate/prune/refine/coarsen/merge, signed flood fill,
      checksum/stats/validator, blind data append, and voxel block manager.
- **fvdb-core CUDA/PyTorch:** grid construction/topology, sampling/splatting,
      transforms, pooling, dense/sparse inject, spatial queries, ray ops, TSDF,
      marching cubes, sparse convolution, volume render, Gaussian splatting,
      fused SSIM, and JaggedTensor/GridBatch operations.

**Prioritized GPU backend roadmap**

- [ ] **P0: device-to-device buffer interop.** Sample batches are currently
      host-visible Vulkan buffers owned by tinyvdb. Add import/export or
      caller-provided buffer hooks for Vulkan and CUDA so sample/query results
      can stay on device.
- [~] **P0: GPU sparse topology ops.** Dense `tvdb_gpu_dilate`/`tvdb_gpu_erode`
      (6-neighbor min/max morphology), `tvdb_gpu_prune`, `tvdb_gpu_coarsen`
      (block average), and `tvdb_gpu_refine` (trilinear upsample) on Vulkan and
      CUDA/NVRTC, mirroring `tinyvdb_ops.c`/`tinyvdb_topology.c`. Covered by
      `test_gpu_backend` (`test_topology`). *Still open:* sparse topology-growth
      dilate/erode and merge (output-size-unknown → needs compaction).
- [~] **P0: GPU spatial queries.** `tvdb_gpu_coords_in_grid`,
      `tvdb_gpu_points_in_grid`, `tvdb_gpu_ijk_to_index`, and
      `tvdb_gpu_neighbor_counts` (6/26) over a flat active-coord set, on Vulkan
      and CUDA/NVRTC, mirroring the CPU `tinyvdb_grid_index.{h,c}` helpers via
      brute-force linear-scan kernels (one thread per query/active voxel).
      Covered by `test_gpu_backend` (GPU-vs-CPU parity). *Still open:* GPU
      active-coordinate extraction from a dense grid (needs stream compaction /
      prefix-sum).
- [x] **P0: GPU ray and volume queries.** `tvdb_gpu_volume_render`
      (emission-absorption, one thread/pixel), `tvdb_gpu_uniform_ray_samples`,
      `tvdb_gpu_voxels_along_ray` (Amanatides-Woo DDA), and
      `tvdb_gpu_segments_along_ray` (SDF crossings; ray-SDF intersection = first
      pair) on Vulkan and CUDA/NVRTC, mirroring `tinyvdb_render.c`/`tinyvdb_ray.c`.
      Covered by `test_gpu_backend` (`test_volume_render`, `test_ray_queries`);
      DDA termination/entry are float-sensitive so the test allows a ±1
      boundary diff with exact-prefix agreement. VRAM-trivial test data.
- [ ] **P0: GPU TSDF integration and marching cubes.** Port the existing CPU
      TSDF fusion and marching-cubes surface extraction to the runtime-loaded
      GPU backend.
- [ ] **P1: GPU grid construction.** Build sparse grids on GPU from points,
      voxel/ijk lists, dense masks, and triangle meshes, taking inspiration from
      NanoVDB `pointsToGrid`/`voxelsToGrid` and fvdb GridBatch factories.
- [ ] **P1: sparse convolution upgrades.** Add transposed convolution,
      arbitrary stride, output-grid builders, and a faster near-dense backend
      beyond the current same-topology sparse conv3d.
- [ ] **P1: GPU sampling/splatting gradients.** Add trilinear/Bezier-style
      sample and splat gradient kernels without requiring PyTorch autograd.
- [ ] **P1: GPU diagnostics.** Add NanoVDB-style stats, checksum, and validator
      kernels for device-resident dense/sparse data.
- [ ] **P1: signed flood fill and sparse background robustness.** Add GPU
      signed flood fill plus portable inactive-page/background fallback for
      sparse-image sampling near unbound regions.
- [ ] **P2: GPU Gaussian-splat rasterizer.** Add CUDA/Vulkan forward and
      backward rasterization to complement the existing CPU Gaussian splat
      implementation.
- [ ] **P2: batched sparse data abstractions.** Evaluate a tinyvdb-native
      subset of fvdb `JaggedTensor`/`GridBatch` for batched GPU workloads while
      preserving the dependency-free C API.
- [ ] **P2: PyTorch integration.** Expose selected GPU ops through PyTorch
      tensors/autograd only as an optional layer outside the core C API.
- [ ] **P2: Gaussian training helpers.** Consider fused SSIM, Gaussian
      projection/SH/MCMC helpers after the rasterizer and batching layers exist.
- [ ] **P2: multi-GPU construction/scheduling.** Defer NanoVDB/fvdb-style
      multi-GPU grid construction until single-GPU construction and device
      interop are stable.

### Out of scope (tensor framework)

Framework-level integrations remain outside tinyvdb's dependency-free C API
core — listed for visibility, not on the near-term roadmap.

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
      `fvdb::dispatch`) beyond the small v1 runtime-loaded backend.
- [ ] **GPU Gaussian-splat rasterizer.** A CUDA forward+backward to
      complement the CPU forward (`tvdb_gaussian_rasterize_forward`)
      and the CPU backward (`tvdb_gaussian_rasterize_backward`,
      gradient-checked in `test_gaussian_backward`).

## Test coverage (current)

19 ctests register under `build/` when `TINYVDB_BUILD_GPU=ON`:

| target | what |
| --- | --- |
| `test_ops` | Phase 1-6 dense ops smoke (volume, surface_area, dilate, csg, gradient, Poisson recovery, advection, sampling, TSDF, topology, ray, sparse) |
| `test_grid_index` | Coordinate utilities (`world_to_ijk`/`ijk_to_world` and `morton_encode`/`decode` round-trips incl. negatives), spatial queries (`voxelize_points` dedup; `coords_in_grid`/`points_in_grid`/`ijk_to_index`; `neighbor_counts` on a 2³ block = 3 face / 7 vertex), quadratic sampling (exact on a linear field), point rasterization/scatter, and `volume_render` (sphere-fog center brighter than corner; empty grid = background) |
| `test_resample_advect` | Resampling (`resample_grid` reproduces a linear field exactly for trilinear/triquadratic; preserves a sphere SDF zero-crossing), signed flood fill (restores a wiped sphere interior to -band), and advection (all schemes RK1-4/MacCormack/BFECC shift a linear field exactly; MacCormack less diffusive than RK1 on a bump round-trip) |
| `test_stats_ops` | Statistics (`grid_statistics`/`grid_histogram` on a known linear field), diagnostics (`check_level_set` clean ≈1 vs damaged ≈3; `check_fog_volume` fog-valid vs raw-SDF-invalid), vector operators (`magnitude`=5 on (3,4,0); `normalize`; `cpt` maps a sphere band onto the sphere), composite (`comp_max/min/sum/mult`), and filters (`median_filter` removes an impulse; `mean_curvature_flow` shrinks a sphere) |
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
| `test_gpu_backend` | Optional runtime-loaded GPU backend parity for Vulkan and CUDA when available: analytic sphere/box/torus SDF generation, dense CSG union/difference, dense trilinear batch sampling, Vulkan regular/full-sparse/partial-sparse/persistent-sparse sampled-image benchmarks against SSBO sampling, same-topology sparse conv3d against CPU, and spatial queries (`coords_in_grid`/`points_in_grid`/`ijk_to_index`/`neighbor_counts` 6&26 parity vs CPU on a 4³ active block + outside coords); skips with code 77 if no runtime backend/device is available |
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
