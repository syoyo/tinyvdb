# Lean 4 formalization and validation status

TinyVDB ships a Lean 4 verified model of the `.vdb` format and the volume
operators used by the C library. The model is proven; the C code is checked
against it by differential harnesses (same philosophy as the tinyexr
formalization). This page is a short status overview. The authoritative
theorem inventory, boundaries, findings and gate results are in
[`lean/VERIFICATION.md`](lean/VERIFICATION.md); the scope and phase plan are in
[`plan-lean.md`](plan-lean.md).

**Last verified: 2026-11-23 (local, no CI job by decision).**

## At a glance

| Item | Status |
| --- | --- |
| Toolchain | Lean / mathlib **v4.36.0** (`lean/lean-toolchain`, `lean/lakefile.lean`) |
| Modules | **178** Lean files (171 under `lean/Vdb/`), `warningAsError` on |
| `sorry` / `admit` | **0** in landed modules |
| `lake build` | **18,594 jobs**, success |
| CTest | **91/91** (27 Lean differential gates + `lean_axioms` + 63 C tests; `TINYVDB_BUILD_EXAMPLES=ON` for `vdbdump`, out-of-tree runs pass `VDBDUMP=<build>/vdbdump`) |
| Axiom audit | 5,206 `Vdb.*` declarations; only `propext`, `Classical.choice`, `Quot.sound` plus `native_decide`/`bv_decide` certificates |
| C matrix | scalar ASan/UBSan **60/60**, SIMD+OpenMP and clang **59/59** full suite (new `test_mesh_simplify` additionally passed at OMP 1/8 and under clang), GPU fallback passes with skips |

## What is covered

- **VDB file format** (P1): total decoder/encoder, sparse-tree semantics and
  lookup equivalence, mask compression, half floats, chunk framing, canonical
  file round trip; bit-exact C↔Lean dumps over samples and generated corpora.
- **Level-set ops** (P2): exact SDFs, CSG, Godunov/Eikonal/fast sweeping,
  signed flood fill, measures, trilinear sampling; seeded differential
  harnesses (Godunov, fill, Euler, fast sweep, CSG).
- **Voxel–surface processing** (P3/P4/P5): marching cubes (table theorems,
  welding, ownership, adaptivity), dual marching cubes DMC-0 and DMC-1
  (cube-local patch table, general-`n` watertightness, Nodup criterion, Euler
  and duality), dense/tree C DMC implementations with QEF placement and
  shell-pinned padding, mesh→volume distance/BVH/sign/winding theory, narrow
  band and seed coverage, and C↔Lean topology/value differentials.
- **Advanced results**: staircase-estimator inconsistency families, winding
  dipole/far-field theory, comparison-principle tier for fast sweeping,
  general-`n` angle-weighted sign seam reduced to local convexity data.
- **Physics processing (PH track, in progress)**: shared index-mesh foundation
  with watertightness/Euler counting and a quad→triangle bridge; fog/interior
  masks, SDF component/cavity decomposition, genus/χ arithmetic and closest-
  point projection. Collision-proxy simplification, convex decomposition and
  contact/manifold queries are planned (see `plan-lean.md` §5 and the coverage
  matrix in `lean/VERIFICATION.md`).

## Boundaries and known walls

These are documented precisely in [`lean/VERIFICATION.md`](lean/VERIFICATION.md),
not silently tolerated:

- Spherical-triangle fan existence / Stokes for the full n-face sign seam
  (n=3,4,5 and the general induction step are proved).
- Topological degree for general closed meshes: the far-field zero step is
  circular without independent degree theory.
- Cubical genus / Poincaré–Lefschetz duality needs homology infrastructure
  absent from mathlib 4.36.
- Full Zhao 2005 8-sweep convergence; universal native `Float32` agreement;
  aggregate Barnes–Hut tree claim.
- GPU device coverage: CUDA verified on an RTX 5060 Ti; HIP skipped (no AMD
  device); generated-shader leg needs `glslangValidator` (absent in the last
  run). CTest exit 77 means skipped, not passed.

## Reproduce locally

```sh
cd lean
lake exe cache get && lake build
grep -rn '\bsorry\b' Vdb/            # must be empty
lake env lean AxiomAudit.lean         # axiom profile
# from the repository root, with a freshly built vdbdump:
ctest --test-dir <build> -R 'lean_' --output-on-failure
```

Individual C↔Lean gates are opt-in via `-DTINYVDB_BUILD_LEAN_DIFF=ON`; see
[`lean/README.md`](lean/README.md) for the full gate list.
