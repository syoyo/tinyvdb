/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Chunk framing for node buffers (`tvdb__read_and_decompress` /
  `tvdb__compress_and_write`):

  * an `i64` size word, then
  * when the size is positive, `n` compressed bytes (Blosc/ZIP), which the
    codec expands to the expected element count; or
  * when the size is nonpositive, `-n` raw bytes and `-n` must equal the
    expected byte count (the writer uses `-total` when compression does not
    help, and `0` for an empty payload).

  The codec itself is a parameter (`Bytes → Nat → Option Bytes`), because
  Blosc/ZIP are outside the model; the framing around it is proven.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Chunks

set_option linter.unusedSimpArgs false

namespace Vdb

/-- The `i64` size word followed by a raw payload (`-N`, then `N` bytes). -/
def Chunk.rawChunks (raw : Bytes) : List Bytes :=
  [putI64LE (-(Int64.ofNat raw.size)) ByteArray.empty, raw]

/-- The `i64` size word followed by a compressed payload (`+N`, then `N`
    compressed bytes). -/
def Chunk.compressedChunks (c : Bytes) : List Bytes :=
  [putI64LE (Int64.ofNat c.size) ByteArray.empty, c]

/-- Parse a chunk sized for `expected` bytes: `nonpositive n` means `-n` raw
    bytes follow and must equal `expected`; positive `n` means `n` compressed
    bytes follow, which `decompress` must expand to `expected` bytes. -/
def Chunk.parse (decompress : Bytes → Nat → Option Bytes)
    (b : Bytes) (off expected : Nat) : Option (Bytes × Nat) :=
  match getI64LE b off with
  | none => none
  | some n =>
    if n ≤ 0 then
      if n.toInt = -(expected : Int) then
        (getBytes? b (off + 8) expected).map fun d => (d, off + 8 + expected)
      else none
    else
      (getBytes? b (off + 8) n.toNatClampNeg).bind fun c =>
        (decompress c expected).map fun d => (d, off + 8 + n.toNatClampNeg)

/-- A raw (uncompressed) chunk parses back to its payload. -/
theorem Chunk.parse_raw (decompress : Bytes → Nat → Option Bytes)
    (pre rest : List Bytes) (raw : Bytes) (hsz : raw.size < 2 ^ 63) :
    Chunk.parse decompress
      (concatChunks (pre ++ [putI64LE (-(Int64.ofNat raw.size)) ByteArray.empty, raw] ++ rest))
      (concatChunks pre).size raw.size =
    some (raw, (concatChunks (pre ++ [putI64LE (-(Int64.ofNat raw.size)) ByteArray.empty,
      raw])).size) := by
  have hneg : Int64.toInt (-(Int64.ofNat raw.size)) = -(raw.size : Int) :=
    Int64.toInt_neg_ofNat_of_le (by omega)
  have hle : (-(Int64.ofNat raw.size)) ≤ 0 := by
    rw [show (-(Int64.ofNat raw.size)) ≤ 0 ↔
        Int64.toInt (-(Int64.ofNat raw.size)) ≤ Int64.toInt 0 from
      Int64.le_iff_toInt_le]
    rw [hneg, Int64.toInt_zero]
    omega
  unfold Chunk.parse
  rw [show concatChunks (pre ++ [putI64LE (-(Int64.ofNat raw.size)) ByteArray.empty, raw] ++ rest) =
      concatChunks (pre ++ putI64LE (-(Int64.ofNat raw.size)) ByteArray.empty :: (raw :: rest)) from by simp]
  rw [getI64LE_chunk]
  dsimp only
  rw [ite_eq_left hle]
  rw [hneg]
  simp only [neg_inj, Int.cast_inj]
  simp only [ite_true]
  rw [show (concatChunks pre).size + 8 =
      (concatChunks (pre ++ [putI64LE (-(Int64.ofNat raw.size)) ByteArray.empty])).size from by
    conv_rhs => rw [concatChunks_append_map]
    simp [putI64LE_size]]
  rw [show concatChunks (pre ++ putI64LE (-(Int64.ofNat raw.size)) ByteArray.empty :: (raw :: rest)) =
      concatChunks ((pre ++ [putI64LE (-(Int64.ofNat raw.size)) ByteArray.empty]) ++ (raw :: rest)) from by simp]
  rw [getBytes?_chunk]
  simp only [Option.map_some]
  have h8 : (concatChunks (pre ++ [putI64LE (-(Int64.ofNat raw.size)) ByteArray.empty])).size =
      (concatChunks pre).size + 8 := by
    conv_lhs => rw [concatChunks_append_map]
    simp [putI64LE_size]
  rw [show (concatChunks (pre ++ [putI64LE (-(Int64.ofNat raw.size)) ByteArray.empty])).size + raw.size =
      (concatChunks (pre ++ [putI64LE (-(Int64.ofNat raw.size)) ByteArray.empty, raw])).size from by
    conv_rhs => rw [concatChunks_append_map]
    rw [h8]
    simp [putI64LE_size]
    omega]

/-- A compressed chunk parses back through the codec. -/
theorem Chunk.parse_compressed (decompress : Bytes → Nat → Option Bytes)
    (pre rest : List Bytes) (c raw : Bytes)
    (hsz : c.size < 2 ^ 63) (hpos : 0 < c.size)
    (hdec : decompress c raw.size = some raw) :
    Chunk.parse decompress
      (concatChunks (pre ++ [putI64LE (Int64.ofNat c.size) ByteArray.empty, c] ++ rest))
      (concatChunks pre).size raw.size =
    some (raw, (concatChunks (pre ++ [putI64LE (Int64.ofNat c.size) ByteArray.empty,
      c])).size) := by
  have hto : Int64.toInt (Int64.ofNat c.size) = (c.size : Int) :=
    Int64.toInt_ofNat_of_lt hsz
  have hpos' : ¬ (Int64.ofNat c.size) ≤ 0 := by
    rw [show (Int64.ofNat c.size) ≤ 0 ↔
        Int64.toInt (Int64.ofNat c.size) ≤ Int64.toInt 0 from Int64.le_iff_toInt_le]
    rw [hto, Int64.toInt_zero]
    omega
  unfold Chunk.parse
  rw [show concatChunks (pre ++ [putI64LE (Int64.ofNat c.size) ByteArray.empty, c] ++ rest) =
      concatChunks (pre ++ putI64LE (Int64.ofNat c.size) ByteArray.empty :: (c :: rest)) from by simp]
  rw [getI64LE_chunk]
  dsimp only
  rw [ite_eq_right hpos']
  rw [Int64.toNatClampNeg_ofNat_of_lt hsz]
  rw [show (concatChunks pre).size + 8 =
      (concatChunks (pre ++ [putI64LE (Int64.ofNat c.size) ByteArray.empty])).size from by
    conv_rhs => rw [concatChunks_append_map]
    simp [putI64LE_size]]
  rw [show concatChunks (pre ++ putI64LE (Int64.ofNat c.size) ByteArray.empty :: (c :: rest)) =
      concatChunks ((pre ++ [putI64LE (Int64.ofNat c.size) ByteArray.empty]) ++ (c :: rest)) from by simp]
  rw [getBytes?_chunk]
  simp only [Option.bind_some]
  rw [hdec]
  simp only [Option.map_some]
  have h8 : (concatChunks (pre ++ [putI64LE (Int64.ofNat c.size) ByteArray.empty])).size =
      (concatChunks pre).size + 8 := by
    conv_lhs => rw [concatChunks_append_map]
    simp [putI64LE_size]
  rw [show (concatChunks (pre ++ [putI64LE (Int64.ofNat c.size) ByteArray.empty])).size + c.size =
      (concatChunks (pre ++ [putI64LE (Int64.ofNat c.size) ByteArray.empty, c])).size from by
    conv_rhs => rw [concatChunks_append_map]
    rw [h8]
    simp [putI64LE_size]
    omega]

end Vdb
