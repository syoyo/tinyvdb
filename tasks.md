# tinyvdb tasks

This file tracks open work. Completed items have been pruned; their
history is in `git log` (and the test-suite enumeration below documents
what's covered).

## Open

The remaining items all require a tensor framework + CUDA and are
fundamentally out of tinyvdb's "header-first, dependency-free, pure-C
public API" design. They are listed for visibility but not on the
near-term roadmap.

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

15 ctests register under `build/`:

| target | what |
| --- | --- |
| `test_ops` | Phase 1-6 dense ops smoke (volume, surface_area, dilate, csg, gradient, Poisson recovery, advection, sampling, TSDF, topology, ray, sparse) |
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
