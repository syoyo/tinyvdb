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

## Status (this drop)

Landed and building: `Vdb/Bytes.lean`, `Vdb/Value.lean`, `Vdb/Mask.lean`,
`Vdb/Coord.lean`, `Vdb/Tree.lean`, `Vdb/MaskCompress.lean`, `Vdb/Half.lean`,
`Vdb/Header.lean`, `Vdb/Layout.lean`.
The tree model reads a worked `5_4_3` tree (three lookups checked by `decide`),
the **general mask-compression round trip is proven** (all seven codes,
including the background swap and the code-6 full-list path).

See `VERIFICATION.md` for the theorem inventory and the explicit list of
remaining P1 work (mask byte round trip, slot bijection, tree model, format
layer, oracle harness).

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
```
