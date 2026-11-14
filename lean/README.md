# `lean/` — Lean 4 formalization of the OpenVDB (`.vdb`) format and TinyVDB ops

This package is the **verified model** used to validate (and where it disagrees,
fix) the TinyVDB C implementation in `src/`. It is not a proof *about* the C
code: the Lean model is proven, and the C code is checked against it by
differential harnesses (see `plan-lean.md` in the repository root).

The scope, phase plan, theorem targets and current findings are tracked in
[VERIFICATION.md](VERIFICATION.md).

* Lean `v4.35.0` (`lean-toolchain`), mathlib pinned at `v4.35.0`.
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
welding and ownership, and the dense-sampling coordinate change are all
proved; the C code is checked against the model by differential harnesses
(bit-exact for CSG and mesh→SDF). See `VERIFICATION.md` for the theorem
inventory, the differential-harness results and the explicit list of what
remains open or was abandoned with reasons.

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
./lean/scripts/check_winding.sh          # 194/194 points, degree 1 on closed meshes
./lean/scripts/check_vdbgen.sh           # 2,500/2,500 corpus files: vdbcheck vs vdbdump
```

None of the harnesses are wired into CTest — run them directly.
