# `lean/` — Lean 4 formalization of the OpenVDB (`.vdb`) format and TinyVDB ops

This package is the **verified model** used to validate (and where it disagrees,
fix) the TinyVDB C implementation in `src/`. It is not a proof *about* the C
code: the Lean model is proven, and the C code is checked against it by
differential harnesses (see `plan-lean.md` in the repository root).

The scope, phase plan, theorem targets and current findings are tracked in
[VERIFICATION.md](VERIFICATION.md).

* Lean `v4.36.0` (`lean-toolchain`), mathlib pinned at `v4.36.0` (upgraded from v4.35.0 on 2026-11-20; `lake update mathlib` + `lake exe cache get`).
* Every file carries the Apache-2.0 SPDX header (this repository's license).
* No `sorry` in landed modules. The axiom profile is audited mechanically.

## Build

```sh
cd lean
lake exe cache get     # mathlib oleans (once)
lake build
```

Mathlib is only needed from the coordinate/geometry modules onward; the byte,
value and mask modules only use Lean core.

## Status (current)

The library, the oracle generator and the differential tools are all landed
and building (`warningAsError` on, no `sorry`/`admit` in landed modules). The
file round trip, tree model, mask-compression round trip, half-float
encoding, winding-number and dipole far-field theory, narrow-band composition,
geometry/SDF layer, CSG, Godunov/fast-sweeping/flood-fill/Euler theory, MC/DMC
welding and ownership, the general-`n` padded-grid DMC-0 edge-closure
theorem (`balanced_general` / `edgeClosed_general`), and the dense-sampling
coordinate change are all proved. The general-`n` DMC-0 mesh also has
`E = 2F` and `χ = V − F` (`QuadEuler`, `QuadEulerPad`), a classification of the
no-repeated-edge hypothesis as "no checkerboard face" (`DmcNodup`), a
machine-checked `χ = 3` family for every `n ≥ 3` (`QuadEulerEmbed`), and the
dual-vertex-pinch mechanism behind it (`DmcPinch`): the four anti-diagonal
body-diagonal-pair fields decompose as two one-cell bumps (`χ = 2` each)
sharing exactly the central dual vertex, so `χ = 3` by the abstract glue
lemma (`euler_glue`) — so "edge-manifold" and "`χ = 2`" are *false* in
general, not merely unproved. The
staircase face-count overshoot on the octahedron is proved for every radius
(`StaircaseClosed`); general-set statements about the estimator
(`StaircaseBoundary`) and the MC adaptivity Float-key layer (verified by a
C↔Lean differential harness over millions of adversarial doubles,
`McAdaptKey`) are landed. In Lean, the winding-dipole residual in the
landed identity is shown identically zero and the generic triple-product
bound is attained (`WindingDipoleSharp`), and the closest-point cone
expansion is machine-checked in closure form (`ConeExpansion`: `p − q` lies
in the closure of the cone of tight face normals — the Farkas content of
`p − q = Σ λᵢ nᵢ`) and in exact form (`ConeClosed`: a finitely generated
pointed cone is closed, so `p − q = Σ λᵢ nᵢ` with `λᵢ ≥ 0` over the tight
faces), and the angle-weighted (Bærentzen–Aanæs) apex normal pairs strictly
positively at the F16 trap point (`AnglePseudoNormal`), whose general convex
theorem is now proved conditional on the named per-face positivity seam (with
unconditional non-obtuse and two-face planar instances), and the far-field
asymptotic consistency of the dipole estimator is
machine-checked (`WindingFarField`: `t² · (solidAngle − faceDipole) → 0`
along a ray), and the cube-local DMC-1 (Nielson dual marching cubes) patch
decomposition is machine-checked over all 256 cases (`DmcOne`: patch counts
`(2, 162, 82, 8, 2)`; every cube edge owned by at most one patch), and the
assembled DMC-1 mesh is machine-checked watertight for all 256 shell-pinned
fields of the bounded `n = 3` padded grid (`DmcOnePad`: every quad has four
distinct corners, mesh edge list is `EdgeClosed` and duplicate-free), its
component count and `χ = 2 × #components` are machine-checked against the
MC soup (`DmcOneDual`), and a seeded `n = 4` sample verifies the same
invariants (`DmcOnePad4`) — and the general-`n`
stitching machinery is landed: the face framework
(`DmcOneStitch`), the symbolic orientation law for all 24 boundary-edge
instances (`DmcOneStitchOrient`), and the cube-local face-pairing
enumerations machine-checked over all 256 cases × 3 normal axes × 2 sides
(`DmcOneStitchEnum`: paired edges emit opposite-oriented F-sides; pairs are
owned by one patch) — with the general-`n` watertight theorem **proved**
(`DmcOneAssemble.edgeClosed_general`: the shell-pinned DMC-1 mesh is
`EdgeClosed` for every `n`) and the general Euler characteristic
`χ = V − F` proven under the checkable no-repeat criterion
(`DmcOneEuler.euler_general_dmc1_of_nodup` plus
`DmcOneNodupCriterion.euler_general_dmc1_of_noBadFace`; quads machine-checked
well-formed, mesh loop-free, `|mesh| = 4·|crossed|`, fully proven; surrogate
axioms only). No-repeat is **not automatic** — a concrete shell-pinned `n = 4`
field with repeated edges and failing χ is machine-checked in
`Vdb/DmcOneNodupFailure.lean` (finding F19), so the criterion is essential.
Findings F1–F19 are
tracked in the ledger (F17–F19 are
Lean-side: the cell-sign torus model does not transfer to bounded grids,
an off-by-one in the bounded sign enumeration, and the DMC-1 `Nodup`
counterexample). The global DMC-1 criterion is now proven in
`Vdb/DmcOneNodupCriterion.lean`: `mesh_nodup_iff_noBadFace` and
`euler_general_dmc1_of_noBadFace` discharge the no-repeat hypothesis for every
`n`. `T-DMC1-DUAL` is fully proved for every `n`: MC-vertex↔DMC-quad and
patch↔vertex bijections, incidence preservation and χ duality (the cube-local
ingredients are machine-checked over all 256 cases, the lifting is kernel-proof).
The seam (S) additionally holds for isosceles three-face vertices
(`AngleVertexFigure`, machine-checked over the algebraic spherical-triangle
argument); the three-face case is now completely unconditional
(`sphericalProj_unconditional`, including the `p+r=0`/cyclic slices via a
continuity argument); arbitrary `n > 3` face figures are proved conditionally on `sphericalBarycenter`
(`AngleNFace`), now shown equivalent to (S) itself, with unconditional simplicial
and non-obtuse instances and a non-vacuous `n = 4` fan-cancellation theorem
(`AngleNFaceTangent` additionally records why the fixed-tangent strategy fails
and reduces (S) to a co-normal flux identity). Winding degree theory is landed
as a conditional reduction with unconditional continuity/constancy facts
(`WindingDegree`). The C↔Lean DMC-1 topology differential matches all six invariants
(crossed/verts/quads/comps/closed/χ) on all 256 shell-pinned fields.
The module tally is 176 (169 under `Vdb/`); the C code is checked against the
model by differential harnesses (bit-exact for CSG and mesh→SDF). Remaining work
is reorganized into voxel-surface lanes VS-0…VS-4a and the physics-processing
lanes PH-0…PH-5 in `../plan-lean.md` (mesh foundation and SDF/part-decomposition
modules landed; collision-proxy simplification, convex decomposition and
contact/manifold queries planned); each proof group has a 10-minute wall-clock
cap with a split-or-document escalation ladder. See `VERIFICATION.md` for the
theorem inventory, the voxel-surface and physics coverage matrices, the
differential-harness results and the explicit list of walls (general
Poincaré–Lefschetz, staircase-estimator consistency for general sets, Zhao 2005
/ Phase C, the general-n sign seam (S)).

## Conventions

* Readers are total (`Option`/`Except`), never panic; out-of-bounds reads fail.
* Emitters are `ByteArray → ByteArray` difference lists; `pushBytes` is the
  single primitive every multi-byte writer goes through, so round-trip proofs
  are one induction over a `List UInt8`.
* Bit patterns are kept raw (`UInt32`/`UInt64` IEEE bits); float semantics live
  only in `Vdb/Half.lean` and the geometry modules.
* A node mask is a `Nat` whose low `2^(3L)` bits are the slots; the byte
  serialization is its base-256 little-endian digit expansion, so the round
  trip follows from `Nat.ofDigits_digits`.
* Two coordinate conventions must never be conflated: dense grids in
  `src/tinyvdb_*.c` are cell-centred (`o + (i+0.5)h`, x-fastest storage),
  sparse VDB trees are vertex-centred (`M·(i,j,k,1)`, leaf slot
  `(x<<2L)|(y<<L)|z`).

## Gates

Local-only for now (no CI job):

```sh
lake build                     # zero errors (warningAsError is on)
grep -rn '\bsorry\b' Vdb/      # must be empty
./lean/scripts/check_samples.sh          # 13/13 .vdb files: official samples parsed & round-tripped
./lean/scripts/check_mask_classify.sh    # 1,679,616/1,679,616 nodes byte-exact
./lean/scripts/check_half.sh             # h2f + 192,940 f2h witnesses byte-exact
./lean/scripts/check_godunov.sh          # 200,000/200,000 (1e-12)
./lean/scripts/check_euler.sh            # 400/400 (c == 2·χ)
./lean/scripts/check_fill.sh             # 400/400 byte-exact
./lean/scripts/check_fastsweep.sh        # 102,400/102,400 (1e-5·h, exact sign)
./lean/scripts/check_csg.sh              # 614,400/614,400 op outputs bit-exact
./lean/scripts/check_meshsdf.sh          # 6,488/6,488 voxels bit-exact (mesh→SDF arm)
./lean/scripts/check_meshsdf_bvh.sh     # 280 cell-centre queries: C BVH vs exact-Q pruned search
./lean/scripts/check_treemeshsdf.sh      # 2 meshes x 729 voxels, bounded tree path + negative control
./lean/scripts/check_winding.sh          # 194/194 points, degree 1 on closed meshes
./lean/scripts/check_mc_adapt.sh         # 3,000,000 axis evals, C/Lean Float-key twin bit-exact
./lean/scripts/check_mc_topology.sh     # 258 fields x 2 windings: welded MC topology exact
./lean/scripts/check_dmc1_topology.sh   # 256 shell-pinned DMC-1 fields: six topology invariants exact
./lean/scripts/check_mc_sparse_topology.sh # sparse/tree tool_mesh topology vs exact-Q twin
./lean/scripts/check_meshsdf_double.sh  # 16 fallback cases: exact RNE binary64->binary32 cast
./lean/scripts/check_mc_face.py          # 192 ambiguous MC face instances face-consistent
./lean/scripts/check_vdbgen.sh           # 2,500/2,500 corpus files: vdbcheck vs vdbdump
```

All harnesses above are wired into CTest under `-DTINYVDB_BUILD_LEAN_DIFF=ON`
as `lean_diff` and `lean_diff_*` (twenty tests, including `lean_diff_meshsdf_bvh`,
`lean_diff_meshsdf_bvh_ties`,
`lean_diff_meshsdf_double`, `lean_diff_mc_sparse_topology`,
`lean_diff_dmc1_topology`, `lean_diff_mc_topology`, `lean_diff_treemeshsdf`
and `lean_diff_mc_face`).
Each shell harness exits **77** ("skipped", not "passed") when `lake` is absent;
a real checker failure still fails the test. Every harness also exports
`ELAN_TOOLCHAIN` from `lean/lean-toolchain` so CTest (which runs from the build
directory) uses the pinned Lean 4.36 rather than an ambient toolchain. With the
Lean toolchain present, run `ctest --test-dir <build> --output-on-failure
-R '^lean_diff'`.
