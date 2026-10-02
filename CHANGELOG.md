# Changelog

## 0.10.0 — release candidate

### Added

- Checked float-tree diagnostics, signed flood fill, exact pruning, and sparse
  and dense bridges in `tinyvdb_tree.h`.
- Sparse level-set rebuild/tracking, affine nearest/trilinear resampling,
  indexed isosurface meshing, and active-domain Poisson/PDE solving in
  `tinyvdb_sparse_tools.h`, with corresponding `VDBGrid` Python methods.
- Optional comparisons against an installed OpenVDB library, allocation-failure
  regressions, and procedural fixtures for clean-checkout and wheel tests.

### Fixed and hardened

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
