/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Binary16 (half) model: the exact reader (`tvdb__half_to_float`) and the two
  encoders in the code base, the scalar truncating one
  (`tvdb__float_to_half`) and the round-to-nearest-even one used by the F16C
  path and by OpenVDB (`_mm256_cvtps_ph`, `truncateRealToHalf`).

  All functions are over raw bit patterns (`UInt16`/`UInt32`); no float
  semantics are assumed. The key facts recorded here are the F1 finding
  boundary: the truncating encoder maps NaN to Inf and rounds toward zero,
  so scalar and SIMD writers disagree.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Bytes

namespace Vdb

/-! ### Decoding a half to a binary32 bit pattern -/

/-- Shift a subnormal mantissa left until the implicit bit is set, returning
    the normalized mantissa (top bit removed by the caller) and the exponent
    adjustment. Bounded by 11 iterations, like the C `while` loop. -/
def normalizeSubnormal (mant : Nat) : Nat × Nat :=
  (List.range 11).foldl
    (fun acc _ => if acc.1 &&& 0x400 ≠ 0 then acc else (acc.1 <<< 1, acc.2 + 1))
    (mant, 0)

/-- `tvdb__half_to_float` as a binary32 bit pattern (exact, including
    subnormals and NaN payloads). -/
def halfToFloatBits (h : UInt16) : UInt32 :=
  let u := h.toNat
  let sign := (u >>> 15) &&& 1
  let e := (u >>> 10) &&& 0x1F
  let mant := u &&& 0x3FF
  if e = 0 then
    if mant = 0 then
      UInt32.ofNat (sign <<< 31)
    else
      let nm := normalizeSubnormal mant
      let adj := nm.2
      let m := nm.1 &&& 0x3FF
      UInt32.ofNat (sign <<< 31 ||| ((127 - 15 + 1 - adj) <<< 23) ||| (m <<< 13))
  else if e = 31 then
    UInt32.ofNat (sign <<< 31 ||| 0x7F800000 ||| (mant <<< 13))
  else
    UInt32.ofNat (sign <<< 31 ||| ((e + 127 - 15) <<< 23) ||| (mant <<< 13))

/-! ### Encoding: the scalar (truncating) encoder -/

/-- `tvdb__float_to_half`: truncates instead of rounding, flushes values
    below `2^-24` to zero, and maps NaN to Inf (`exp >= 31`). -/
def floatToHalfTrunc (u : UInt32) : UInt16 :=
  let un := u.toNat
  let sign := (un >>> 31) &&& 1
  let e := (un >>> 23) &&& 0xFF
  let mant := un &&& 0x7FFFFF
  if e ≤ 112 then
    if e < 102 then
      UInt16.ofNat (sign <<< 15)
    else
      let mant' := mant ||| 0x800000
      let shift := 113 - e
      UInt16.ofNat (sign <<< 15 ||| (mant' >>> (13 + shift)))
  else if e ≥ 143 then
    UInt16.ofNat (sign <<< 15 ||| 0x7C00)
  else
    UInt16.ofNat (sign <<< 15 ||| ((e - 112) <<< 10) ||| (mant >>> 13))

/-! ### Encoding: round-to-nearest-even (F16C / OpenVDB) -/

/-- Shift right with round-to-nearest, ties to even. -/
def shrRNE (x k : Nat) : Nat :=
  if k = 0 then x
  else
    let q := x >>> k
    let rem := x &&& ((1 <<< k) - 1)
    let half := 1 <<< (k - 1)
    if half < rem ∨ (rem = half ∧ q &&& 1 = 1) then q + 1 else q

/-- Round-to-nearest-even demotion, matching `_mm256_cvtps_ph` with
    `_MM_FROUND_TO_NEAREST_INT` and OpenVDB's `truncateRealToHalf`.
    Infinity stays infinity, NaN stays NaN (quiet, payload truncated). -/
def floatToHalfRNE (u : UInt32) : UInt16 :=
  let un := u.toNat
  let sign := (un >>> 31) &&& 1
  let e := (un >>> 23) &&& 0xFF
  let mant := un &&& 0x7FFFFF
  let signBit := sign <<< 15
  if e = 0xFF then
    if mant = 0 then
      UInt16.ofNat (signBit ||| 0x7C00)
    else
      UInt16.ofNat (signBit ||| 0x7E00 ||| (mant >>> 13))
  else if e ≥ 143 then
    UInt16.ofNat (signBit ||| 0x7C00)
  else if e ≥ 113 then
    -- normal half: 13 dropped bits, exponent `e - 112`
    let h := shrRNE (0x800000 ||| mant) 13
    let eh := e - 112
    if h ≥ 0x800 then
      UInt16.ofNat (signBit ||| ((eh + 1) <<< 10))
    else
      UInt16.ofNat (signBit ||| (eh <<< 10) ||| (h &&& 0x3FF))
  else
    -- subnormal half (or zero): value `(1.f) * 2^(e-127)` in units of `2^-24`
    let h := shrRNE (0x800000 ||| mant) (126 - e)
    UInt16.ofNat (signBit ||| (h &&& 0x7FF))

/-! ### Concrete F1 evidence -/

/-- The truncating encoder maps NaN to Inf. -/
theorem floatToHalfTrunc_nan : floatToHalfTrunc 0x7FC00000 = 0x7C00 := by
  native_decide

/-- The round-to-nearest encoder keeps NaN as NaN. -/
theorem floatToHalfRNE_nan : (floatToHalfRNE 0x7FC00000 >>> 10) &&& 0x1F = 0x1F := by
  native_decide

/-- Truncation drops the low mantissa bit where RNE rounds it up:
    `1 + 2^-12 + 2^-23` truncates to `1.0` and rounds to `1 + 2^-10`. -/
theorem trunc_vs_rne_differ :
    floatToHalfTrunc 0x3F801001 = 0x3C00 ∧ floatToHalfRNE 0x3F801001 = 0x3C01 := by
  native_decide

/-- Values below `2^-24` flush to zero under the truncating encoder. -/
theorem floatToHalfTrunc_tiny_flush : floatToHalfTrunc 0x00000001 = 0x0000 := by
  native_decide

/-- Signed zeros are preserved by both encoders. -/
theorem floatToHalfTrunc_negzero : floatToHalfTrunc 0x80000000 = 0x8000 := by
  native_decide

theorem floatToHalfRNE_negzero : floatToHalfRNE 0x80000000 = 0x8000 := by
  native_decide

/-! ### Round trips on representable halves -/

/-- Every normal half value round trips through the truncating encoder. -/
theorem floatToHalfTrunc_halfToFloat_normal (h : Fin 65536) :
    let e := (h.val >>> 10) &&& 0x1F
    e ≠ 0 → e ≠ 31 → floatToHalfTrunc (halfToFloatBits (UInt16.ofNat h.val)) = UInt16.ofNat h.val := by
  revert h
  native_decide

/-- Every normal half value round trips through the round-to-nearest encoder. -/
theorem floatToHalfRNE_halfToFloat_normal (h : Fin 65536) :
    let e := (h.val >>> 10) &&& 0x1F
    e ≠ 0 → e ≠ 31 → floatToHalfRNE (halfToFloatBits (UInt16.ofNat h.val)) = UInt16.ofNat h.val := by
  revert h
  native_decide

/-- Subnormal halves round trip through the round-to-nearest encoder too. -/
theorem floatToHalfRNE_halfToFloat_subnormal (h : Fin 65536) :
    let e := (h.val >>> 10) &&& 0x1F
    e = 0 → floatToHalfRNE (halfToFloatBits (UInt16.ofNat h.val)) = UInt16.ofNat h.val := by
  revert h
  native_decide

end Vdb
