/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  The **Float `floor` / int64-key layer** of MC adaptivity
  (`tool_adapt`, `src/tinyvdb_sparse_tools.c`), which the ℝ-level model
  (`Vdb/McAdapt.lean`) deliberately does not see.

  The C computes, per vertex coordinate `v[a]`:

  ```
  double q = floor(v[a] / step);
  if (!isfinite(q) || q < -9223372036854775808.0 || q >= 9223372036854775808.0)
      overflow = 1;              // "cluster coordinate overflow"
  else
      c[a] = (int64_t)q;         // exact: q is integral and |q| < 2^63
  ```

  with `step = tolerance / sqrt(3.0)` (the `step ≤ 0`/non-finite check is
  done upstream, not here). Vertices are sorted by `(c[0], c[1], c[2])`
  (`memcmp` on three `int64_t`s, equality only — never a numeric order)
  and same-key groups are clustered.

  What this module provides:

  * `mcKeyAxis` — an executable twin of the C per-axis key computation,
    over Lean's native `Float` (IEEE binary64, compiled to the same
    `floor`/arithmetic the C runs). `none` = the C's overflow condition
    (`!isfinite(q) || q < -2^63 || q >= 2^63`); `some q` = the integral
    double `q` (the packed int64 — `(int64_t)q` — is exact for integral
    in-range `q`, so `q` is a faithful stand-in; sign of zero and NaN
    never reach the `some` branch).
  * `mcKeyStats` — runs a seeded xorshift64 corpus of `(v, step)` pairs
    (sign-symmetric magnitudes, the exact `±2^63` boundary doubles and
    their neighbours via `Float.ofBits`, `±0.0`, `±Inf`, `NaN` (several
    payloads), subnormals, the `2^53` integer boundary) and returns
    `(ok, overflow, checksum)` where `checksum` is the XOR of
    `Float.toBits` of accepted keys. `mc_key_main [n]` prints the
    summary; `check_mc_adapt.sh` compares it against the C twin
    (`lean/scripts/mc_adapt_c.c`, a line-for-line transcription of the C
    guard driven by the same corpus).

  What is **not** claimed (and cannot be without an IEEE-754 model with
  rounding lemmas, which Lean core does not provide): theorems about the
  Float computation. `Float.Model` provides an executable binary64 model
  (`Init.Data.Float.Model`) but no `floor` and no rounding lemmas, so the
  twin uses native `Float`; the harness is the evidence. The ℝ-level
  guarantees of `Vdb/McAdapt.lean` (same-cell distance ≤ tolerance,
  midpoint distortion ≤ tolerance/2) remain the normative model.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
namespace Vdb

/-! ### The twin -/

/-- The exact double `2^63` (both bounds of the C's guard are powers of
    two, hence exactly representable in binary64). -/
def twoPow63 : Float := 9223372036854775808.0

/-- `-2^63`, as in the C's `-9223372036854775808.0` literal. -/
def negTwoPow63 : Float := -9223372036854775808.0

/-- Per-axis key twin of the C's `tool_cluster_range` inner loop.
    `none` mirrors the overflow path; `some q` is the integral double `q`
    (exact stand-in for the packed int64 key; `(int64_t)q` is exact for
    integral in-range `q` in both languages). -/
def mcKeyAxis (v step : Float) : Option Float :=
  let q := Float.floor (v / step)
  if !q.isFinite || q < negTwoPow63 || q >= twoPow63 then none
  else some q

/-! ### Adversarial corpus (seeded xorshift64, mirrored in `mc_adapt_c.c`) -/

/-- Xorshift64*, one step. -/
def xs64 (s : UInt64) : UInt64 :=
  let s := s ^^^ (s >>> 12)
  let s := s ^^^ (s <<< 25)
  let s := s ^^^ (s >>> 27)
  s * (0x2545F4914F6CDD1D : UInt64)

/-- Reinterpret the folded xorshift bits as a double of bounded magnitude
    with the input sign bit. -/
def mixDouble (bits : UInt64) : Float :=
  let sign := bits &&& 0x8000000000000000
  let mantissa := bits &&& 0x000FFFFFFFFFFFFF
  let exp := (0x3F00000000000000 : UInt64) + (bits >>> 12) % (0x7F0000000000 : UInt64)
  Float.ofBits (sign ||| exp ||| mantissa)

/-- Adversarial coordinates (all axes, indexed by the low bits of `j`). -/
def adversarialV (j : UInt64) : Float :=
  match j.toNat % 24 with
  | 0 => 0.0
  | 1 => -0.0
  | 2 => 1.0 / 0.0
  | 3 => -(1.0 / 0.0)
  | 4 => 0.0 / 0.0
  | 5 => 5e-324
  | 6 => -5e-324
  | 7 => Float.ofBits 0x43E0000000000000   -- exactly 2^63
  | 8 => Float.ofBits 0x43DFFFFFFFFFFFFF   -- largest double below 2^63
  | 9 => Float.ofBits 0x43E0000000000001   -- smallest double above 2^63
  | 10 => Float.ofBits 0xC3E0000000000000  -- exactly -2^63
  | 11 => Float.ofBits 0xC3DFFFFFFFFFFFFF  -- -(2^63 - 512)
  | 12 => Float.ofBits 0xC3E0000000000001  -- -(2^63 + 1024)
  | 13 => 9007199254740992.0               -- 2^53
  | 14 => -9007199254740992.0
  | 15 => 1e308
  | 16 => -1e308
  | 17 => 4.5e15
  | 18 => -4.5e15
  | 19 => Float.ofBits 0x7FF8000000000001  -- NaN, payload 1
  | 20 => Float.ofBits 0x7FFFFFFFFFFFFFFF  -- NaN, all payload bits
  | 21 => Float.ofBits 0xFFFF000000000001  -- negative NaN, payload
  | _ => Float.ofBits 0xFFF0000000000000   -- -inf via bits

/-- Adversarial steps (all clusters of indices `% 8 == 0`). -/
def corpusStepAdv (j : UInt64) : Float :=
  match j.toNat % 8 with
  | 0 => 3.7e-4
  | 1 => 1.0
  | 2 => 1e3
  | 3 => 1e-6
  | 4 => 1e300
  | 5 => 5e-324
  | 6 => 0.0 / 0.0              -- NaN step (upstream guard territory; twin path taken anyway)
  | _ => 1.0 / 0.0              -- +inf step

/-- The coordinate for corpus slot `j` (vertex index `i = j / 3`, axis `j % 3`):
    adversarial on `% 4 == 0`, otherwise the xorshift stream. -/
def corpusV (j : UInt64) : Float :=
  if j % 4 == 0 then adversarialV j
  else mixDouble (xs64 ((0x243F6A8885A308D3 : UInt64) + j * (0x9E3779B97F4A7C15 : UInt64)))

/-- The step for vertex `i`: adversarial on `% 4 == 0`, otherwise the
    xorshift stream. -/
def corpusStepAt (i : UInt64) : Float :=
  if i % 4 == 0 then corpusStepAdv i
  else mixDouble (xs64 ((0xBB67AE8584CAA73B : UInt64) + i * (0xC2B2AE3D27D4EB4F : UInt64)))

/-- Twin runner: folds `(ok, overflow, checksum)` over `n` vertices × 3 axes;
    `checksum` is the wrapping `UInt64` sum of the raw bits of the accepted keys. -/
def mcKeyStats (n : Nat) : Nat × Nat × UInt64 :=
  (List.range n).foldl (fun acc i =>
    let s := corpusStepAt i.toUInt64
    [0, 1, 2].foldl (fun (acc : Nat × Nat × UInt64) a =>
      let (ok, ov, bits) := acc
      match mcKeyAxis (corpusV ((3 : UInt64) * i.toUInt64 + a.toUInt64)) s with
      | some q => (ok + 1, ov, bits + q.toBits)
      | none => (ok, ov + 1, bits)) acc) (0, 0, 0)

end Vdb

/-- Twin executable: prints `ok <n> overflow <n> checksum <n>` (checksum is
    decimal). The `main` lives in the root namespace, as the Lake
    executable entry point resolves it there. -/
def main (args : List String) : IO UInt32 := do
  let n := (args.head?.getD "1000000").toNat!
  let (ok, ov, acc) := Vdb.mcKeyStats n
  IO.println s!"ok {ok} overflow {ov} checksum {acc}"
  return 0
