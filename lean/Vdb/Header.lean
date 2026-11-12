/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  File header and the string/blob wire primitives shared by metadata, grid
  descriptors and the transform.

  Layout (`tvdb__write_header` / `tvdb__read_header`):

  | field                 | bytes | notes                                   |
  |-----------------------|-------|-----------------------------------------|
  | magic                 | 8     | i64 `0x56444220` (`" BVD\0\0\0\0"`)     |
  | file version          | 4     | u32, 220 … 225 in the C reader          |
  | library major version | 4     | u32                                     |
  | library minor version | 4     | u32 (minor of 0 prints as 10.0)         |
  | has grid offsets      | 1     | u8; the reader rejects 0                |
  | legacy compression    | 1     | u8, only for 220 ≤ version < 222         |
  | UUID                  | 36    | ASCII bytes, no NUL terminator           |

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Chunks
import Vdb.Value

namespace Vdb

/-! ### String and blob primitives -/

/-- A VDB string: `u32` length followed by that many bytes (no terminator). -/
def putString (s : Bytes) : Emit :=
  fun acc => (putU32LE (UInt32.ofNat s.size)) acc ++ s

/-- Parse a VDB string; returns the bytes and the next offset. -/
def getString? (b : Bytes) (off : Nat) : Option (Bytes × Nat) :=
  match getU32LE b off with
  | none => none
  | some n =>
    match getBytes? b (off + 4) n.toNat with
    | none => none
    | some payload => some (payload, off + 4 + n.toNat)

/-! ### Round trips for the primitives -/

theorem getBytes?_append (s acc : Bytes) :
    getBytes? (acc ++ s) acc.size s.size = some s := by
  unfold getBytes?
  have h : acc.size + s.size ≤ (acc ++ s).size := by
    rw [ByteArray.size_append]
  rw [ite_eq_left h]
  exact congrArg some extract_append_right_eq

/-- The same read with the `putBytes` spelling. -/
theorem getBytes?_putBytes (s acc : Bytes) :
    getBytes? (putBytes s acc) acc.size s.size = some s := getBytes?_append s acc

theorem getString?_putString (s acc : Bytes) (hsize : s.size < 2 ^ 32) :
    getString? (putString s acc) acc.size = some (s, acc.size + 4 + s.size) := by
  unfold getString? putString
  have hlen4 : (putU32LE.u32Bytes (UInt32.ofNat s.size)).length = 4 := rfl
  have hoff : (putU32LE (UInt32.ofNat s.size) acc).size = acc.size + 4 := by
    unfold putU32LE
    rw [pushBytes_size, hlen4]
  rw [getU32LE_append_left (a := (putU32LE (UInt32.ofNat s.size)) acc) (b := s)
    (i := acc.size) (by rw [hoff])]
  rw [getU32LE_putU32LE]
  dsimp only
  have htoNat : (UInt32.ofNat s.size).toNat = s.size := by
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt hsize
  rw [htoNat, show acc.size + 4 = (putU32LE (UInt32.ofNat s.size) acc).size from hoff.symm]
  rw [getBytes?_append]

theorem putString_size (s acc : Bytes) :
    (putString s acc).size = acc.size + 4 + s.size := by
  unfold putString
  rw [ByteArray.size_append]
  have h : (putU32LE (UInt32.ofNat s.size) acc).size = acc.size + 4 := by
    unfold putU32LE
    rw [pushBytes_size]
    rfl
  rw [h]

/-! ### Header -/

/-- The VDB magic as a signed 64-bit integer (`0x56444220`). -/
def headerMagic : Int64 := 0x56444220

/-- Highest file version the model accepts (OpenVDB 10.x / 224, with 225
    defined for half grids). -/
def maxFileVersion : UInt32 := 225

/-- Lowest file version the model accepts. -/
def minFileVersion : UInt32 := 220

/-- File header fields (after the magic). -/
structure Header where
  fileVersion : UInt32
  majorVersion : UInt32
  minorVersion : UInt32
  hasGridOffsets : Bool
  /-- Legacy global compression byte, only present for 220 ≤ version < 222. -/
  legacyCompressed : Bool := false
  uuid : Bytes
  deriving Repr, DecidableEq

/-- Whether the legacy compression byte is on the wire (versions 220, 221). -/
def Header.hasLegacyByte (h : Header) : Bool :=
  decide (minFileVersion ≤ h.fileVersion ∧ h.fileVersion < 222)

/-- Canonical headers: supported version range, grid offsets on, 36-byte
    UUID, and the legacy byte value consistent with its presence. -/
def Header.Canonical (h : Header) : Prop :=
  minFileVersion ≤ h.fileVersion ∧ h.fileVersion ≤ maxFileVersion ∧
  h.hasGridOffsets = true ∧ h.uuid.size = 36 ∧
  (h.hasLegacyByte = false → h.legacyCompressed = false)

/-- The header's wire chunks, in order. The legacy byte chunk is empty when
    the version does not carry it. -/
def Header.chunks (h : Header) : List Bytes :=
  [ putI64LE headerMagic ByteArray.empty
  , putU32LE h.fileVersion ByteArray.empty
  , putU32LE h.majorVersion ByteArray.empty
  , putU32LE h.minorVersion ByteArray.empty
  , putU8 (if h.hasGridOffsets then 1 else 0) ByteArray.empty
  , (if h.hasLegacyByte then
       putU8 (if h.legacyCompressed then 1 else 0) ByteArray.empty
     else ByteArray.empty)
  , h.uuid ]

/-- Emit a header after `acc`. -/
def Header.emitFrom (h : Header) (acc : Bytes) : Bytes :=
  acc ++ concatChunks (h.chunks)

/-- Emit a header. -/
def Header.emit (h : Header) : Bytes := h.emitFrom ByteArray.empty

/-- Size of an emitted header. -/
theorem Header.emit_size (h : Header) (acc : Bytes) :
    (h.emitFrom acc).size = acc.size + 21 + (if h.hasLegacyByte then 1 else 0) + h.uuid.size := by
  unfold Header.emitFrom Header.chunks
  rw [ByteArray.size_append, concatChunks_size]
  cases h.hasLegacyByte <;> simp <;> omega

/-- Parse a header starting at `off`; returns it and the first free offset. -/
def Header.parseFrom (b : Bytes) (off : Nat) : Option (Header × Nat) :=
  match getI64LE b off with
  | none => none
  | some magic =>
    if magic ≠ headerMagic then none
    else match getU32LE b (off + 8) with
    | none => none
    | some ver =>
      if ver < minFileVersion then none
      else match getU32LE b (off + 12) with
      | none => none
      | some major =>
        match getU32LE b (off + 16) with
        | none => none
        | some minor =>
          match getU8? b (off + 20) with
          | none => none
          | some hasOff =>
            if hasOff = 0 then none
            else if 220 ≤ ver ∧ ver < 222 then
              match getU8? b (off + 21) with
              | none => none
              | some legacy =>
                match getBytes? b (off + 22) 36 with
                | none => none
                | some uuid =>
                  some (⟨ver, major, minor, true, legacy != 0, uuid⟩, off + 58)
            else
              match getBytes? b (off + 21) 36 with
              | none => none
              | some uuid =>
                some (⟨ver, major, minor, true, false, uuid⟩, off + 57)

/-- Parse a header at offset 0. -/
def Header.parse (b : Bytes) : Option (Header × Nat) := Header.parseFrom b 0

/-- Reading the header back: canonical files round trip exactly. -/
theorem Header.parseFrom_emitFrom (h : Header) (hc : h.Canonical) (acc : Bytes) :
    Header.parseFrom (h.emitFrom acc) acc.size =
      some (h, acc.size + 21 + (if h.hasLegacyByte then 1 else 0) + 36) := by
  obtain ⟨hv1, hv2, hoff, huuid, hleg⟩ := hc
  rcases h with ⟨ver, maj, min, hasOff, legacy, uuid⟩
  simp only at hv1 hv2 hoff huuid hleg ⊢
  subst hoff
  -- chunk expressions
  set c0 : Bytes := putI64LE headerMagic ByteArray.empty with hc0
  set c1 : Bytes := putU32LE ver ByteArray.empty with hc1
  set c2 : Bytes := putU32LE maj ByteArray.empty with hc2
  set c3 : Bytes := putU32LE min ByteArray.empty with hc3
  set c4 : Bytes := putU8 1 ByteArray.empty with hc4
  set c6 : Bytes := uuid with hc6
  cases hb : decide (minFileVersion ≤ ver ∧ ver < 222)
  · -- no legacy byte on the wire
    have hleg' : legacy = false := by
      have := hleg hb
      simpa [Header.hasLegacyByte] using this
    subst hleg'
    have hcond : ¬ (220 ≤ ver ∧ ver < 222) := of_decide_eq_false hb
    -- field reads
    have hm : getI64LE (acc ++ concatChunks [c0, c1, c2, c3, c4, ByteArray.empty, c6])
        acc.size = some headerMagic := by
      rw [acc_append_concatChunks]
      rw [show (acc :: [c0, c1, c2, c3, c4, ByteArray.empty, c6]) =
        [acc] ++ c0 :: [c1, c2, c3, c4, ByteArray.empty, c6] from rfl]
      rw [concatChunks_split, concatChunks_singleton]
      rw [show acc.size = acc.size + 0 from (Nat.add_zero acc.size).symm]
      rw [getI64LE_append_right']
      rw [getI64LE_append_left (by rw [hc0]; simp)]
      rw [hc0, show (0 : Nat) = ByteArray.empty.size from rfl]
      rw [getI64LE_putI64LE]
    have hv : getU32LE (acc ++ concatChunks [c0, c1, c2, c3, c4, ByteArray.empty, c6])
        (acc.size + 8) = some ver := by
      rw [acc_append_concatChunks]
      rw [show (acc :: [c0, c1, c2, c3, c4, ByteArray.empty, c6]) =
        [acc, c0] ++ c1 :: [c2, c3, c4, ByteArray.empty, c6] from rfl]
      rw [concatChunks_split]
      rw [show acc.size + 8 = (concatChunks [acc, c0]).size + 0 by
        simp [concatChunks_size, hc0]]
      rw [getU32LE_append_right']
      rw [getU32LE_append_left (by rw [hc1]; simp)]
      rw [hc1, show (0 : Nat) = ByteArray.empty.size from rfl]
      rw [getU32LE_putU32LE]
    have hma : getU32LE (acc ++ concatChunks [c0, c1, c2, c3, c4, ByteArray.empty, c6])
        (acc.size + 12) = some maj := by
      rw [acc_append_concatChunks]
      rw [show (acc :: [c0, c1, c2, c3, c4, ByteArray.empty, c6]) =
        [acc, c0, c1] ++ c2 :: [c3, c4, ByteArray.empty, c6] from rfl]
      rw [concatChunks_split]
      rw [show acc.size + 12 = (concatChunks [acc, c0, c1]).size + 0 by
        simp [concatChunks_size, hc0, hc1]]
      rw [getU32LE_append_right']
      rw [getU32LE_append_left (by rw [hc2]; simp)]
      rw [hc2, show (0 : Nat) = ByteArray.empty.size from rfl]
      rw [getU32LE_putU32LE]
    have hmi : getU32LE (acc ++ concatChunks [c0, c1, c2, c3, c4, ByteArray.empty, c6])
        (acc.size + 16) = some min := by
      rw [acc_append_concatChunks]
      rw [show (acc :: [c0, c1, c2, c3, c4, ByteArray.empty, c6]) =
        [acc, c0, c1, c2] ++ c3 :: [c4, ByteArray.empty, c6] from rfl]
      rw [concatChunks_split]
      rw [show acc.size + 16 = (concatChunks [acc, c0, c1, c2]).size + 0 by
        simp [concatChunks_size, hc0, hc1, hc2]]
      rw [getU32LE_append_right']
      rw [getU32LE_append_left (by rw [hc3]; simp)]
      rw [hc3, show (0 : Nat) = ByteArray.empty.size from rfl]
      rw [getU32LE_putU32LE]
    have ho : getU8? (acc ++ concatChunks [c0, c1, c2, c3, c4, ByteArray.empty, c6])
        (acc.size + 20) = some 1 := by
      rw [acc_append_concatChunks]
      rw [show (acc :: [c0, c1, c2, c3, c4, ByteArray.empty, c6]) =
        [acc, c0, c1, c2, c3] ++ c4 :: [ByteArray.empty, c6] from rfl]
      rw [concatChunks_split]
      rw [show acc.size + 20 = (concatChunks [acc, c0, c1, c2, c3]).size + 0 by
        simp [concatChunks_size, hc0, hc1, hc2, hc3]]
      rw [getU8?_append_right']
      rw [getU8?_append_left (by rw [hc4]; simp)]
      rw [hc4]
      exact getU8_putU8 ByteArray.empty 1
    have hu : getBytes? (acc ++ concatChunks [c0, c1, c2, c3, c4, ByteArray.empty, c6])
        (acc.size + 21) 36 = some uuid := by
      rw [acc_append_concatChunks]
      rw [show (acc :: [c0, c1, c2, c3, c4, ByteArray.empty, c6]) =
        [acc, c0, c1, c2, c3, c4, ByteArray.empty] ++ c6 :: ([] : List Bytes) from rfl]
      rw [show acc.size + 21 = (concatChunks [acc, c0, c1, c2, c3, c4, ByteArray.empty]).size by
        simp [concatChunks_size, hc0, hc1, hc2, hc3, hc4]]
      rw [show (36 : Nat) = c6.size from huuid.symm]
      rw [getBytes?_chunk]
    unfold Header.parseFrom Header.emitFrom Header.chunks
    simp only [hb, Header.hasLegacyByte, Bool.false_eq_true, ite_true, ite_false]
    rw [← hc0, ← hc1, ← hc2, ← hc3, ← hc4]
    rw [hm, hv, hma, hmi, ho, hu]
    dsimp only
    have hmagicNe : ¬ (headerMagic ≠ headerMagic) := by simp
    have hverlt : ¬ (ver < minFileVersion) := by
      intro hlt
      have h1 : ver.toNat < minFileVersion.toNat := hlt
      have h2 : minFileVersion.toNat ≤ ver.toNat := hv1
      omega
    have hoffNe : ¬ ((1 : UInt8) = 0) := by decide
    simp only [hmagicNe, hverlt, hoffNe, hcond, ite_false]
    simp only [Option.some.injEq]
    refine Prod.ext rfl ?_
    omega
  · -- legacy byte present
    have hcond : 220 ≤ ver ∧ ver < 222 := of_decide_eq_true hb
    set c5 : Bytes := putU8 (if legacy then 1 else 0) ByteArray.empty with hc5
    have hm : getI64LE (acc ++ concatChunks [c0, c1, c2, c3, c4, c5, c6])
        acc.size = some headerMagic := by
      rw [acc_append_concatChunks]
      rw [show (acc :: [c0, c1, c2, c3, c4, c5, c6]) =
        [acc] ++ c0 :: [c1, c2, c3, c4, c5, c6] from rfl]
      rw [concatChunks_split, concatChunks_singleton]
      rw [show acc.size = acc.size + 0 from (Nat.add_zero acc.size).symm]
      rw [getI64LE_append_right']
      rw [getI64LE_append_left (by rw [hc0]; simp)]
      rw [hc0, show (0 : Nat) = ByteArray.empty.size from rfl]
      rw [getI64LE_putI64LE]
    have hv : getU32LE (acc ++ concatChunks [c0, c1, c2, c3, c4, c5, c6])
        (acc.size + 8) = some ver := by
      rw [acc_append_concatChunks]
      rw [show (acc :: [c0, c1, c2, c3, c4, c5, c6]) =
        [acc, c0] ++ c1 :: [c2, c3, c4, c5, c6] from rfl]
      rw [concatChunks_split]
      rw [show acc.size + 8 = (concatChunks [acc, c0]).size + 0 by
        simp [concatChunks_size, hc0]]
      rw [getU32LE_append_right']
      rw [getU32LE_append_left (by rw [hc1]; simp)]
      rw [hc1, show (0 : Nat) = ByteArray.empty.size from rfl]
      rw [getU32LE_putU32LE]
    have hma : getU32LE (acc ++ concatChunks [c0, c1, c2, c3, c4, c5, c6])
        (acc.size + 12) = some maj := by
      rw [acc_append_concatChunks]
      rw [show (acc :: [c0, c1, c2, c3, c4, c5, c6]) =
        [acc, c0, c1] ++ c2 :: [c3, c4, c5, c6] from rfl]
      rw [concatChunks_split]
      rw [show acc.size + 12 = (concatChunks [acc, c0, c1]).size + 0 by
        simp [concatChunks_size, hc0, hc1]]
      rw [getU32LE_append_right']
      rw [getU32LE_append_left (by rw [hc2]; simp)]
      rw [hc2, show (0 : Nat) = ByteArray.empty.size from rfl]
      rw [getU32LE_putU32LE]
    have hmi : getU32LE (acc ++ concatChunks [c0, c1, c2, c3, c4, c5, c6])
        (acc.size + 16) = some min := by
      rw [acc_append_concatChunks]
      rw [show (acc :: [c0, c1, c2, c3, c4, c5, c6]) =
        [acc, c0, c1, c2] ++ c3 :: [c4, c5, c6] from rfl]
      rw [concatChunks_split]
      rw [show acc.size + 16 = (concatChunks [acc, c0, c1, c2]).size + 0 by
        simp [concatChunks_size, hc0, hc1, hc2]]
      rw [getU32LE_append_right']
      rw [getU32LE_append_left (by rw [hc3]; simp)]
      rw [hc3, show (0 : Nat) = ByteArray.empty.size from rfl]
      rw [getU32LE_putU32LE]
    have ho : getU8? (acc ++ concatChunks [c0, c1, c2, c3, c4, c5, c6])
        (acc.size + 20) = some 1 := by
      rw [acc_append_concatChunks]
      rw [show (acc :: [c0, c1, c2, c3, c4, c5, c6]) =
        [acc, c0, c1, c2, c3] ++ c4 :: [c5, c6] from rfl]
      rw [concatChunks_split]
      rw [show acc.size + 20 = (concatChunks [acc, c0, c1, c2, c3]).size + 0 by
        simp [concatChunks_size, hc0, hc1, hc2, hc3]]
      rw [getU8?_append_right']
      rw [getU8?_append_left (by rw [hc4]; simp)]
      rw [hc4]
      exact getU8_putU8 ByteArray.empty 1
    have hl : getU8? (acc ++ concatChunks [c0, c1, c2, c3, c4, c5, c6])
        (acc.size + 21) = some (if legacy then 1 else 0) := by
      rw [acc_append_concatChunks]
      rw [show (acc :: [c0, c1, c2, c3, c4, c5, c6]) =
        [acc, c0, c1, c2, c3, c4] ++ c5 :: [c6] from rfl]
      rw [concatChunks_split]
      rw [show acc.size + 21 = (concatChunks [acc, c0, c1, c2, c3, c4]).size + 0 by
        simp [concatChunks_size, hc0, hc1, hc2, hc3, hc4]]
      rw [getU8?_append_right']
      rw [getU8?_append_left (by rw [hc5]; simp)]
      rw [hc5]
      exact getU8_putU8 ByteArray.empty (if legacy then 1 else 0)
    have hu : getBytes? (acc ++ concatChunks [c0, c1, c2, c3, c4, c5, c6])
        (acc.size + 22) 36 = some uuid := by
      rw [acc_append_concatChunks]
      rw [show (acc :: [c0, c1, c2, c3, c4, c5, c6]) =
        [acc, c0, c1, c2, c3, c4, c5] ++ c6 :: ([] : List Bytes) from rfl]
      rw [show acc.size + 22 = (concatChunks [acc, c0, c1, c2, c3, c4, c5]).size by
        simp [concatChunks_size, hc0, hc1, hc2, hc3, hc4, hc5]]
      rw [show (36 : Nat) = c6.size from huuid.symm]
      rw [getBytes?_chunk]
    unfold Header.parseFrom Header.emitFrom Header.chunks
    simp only [hb, Header.hasLegacyByte, ite_true]
    rw [← hc0, ← hc1, ← hc2, ← hc3, ← hc4, ← hc5]
    rw [hm, hv, hma, hmi, ho, hl, hu]
    dsimp only
    have hmagicNe : ¬ (headerMagic ≠ headerMagic) := by simp
    have hverlt : ¬ (ver < minFileVersion) := by
      intro hlt
      have h1 : ver.toNat < minFileVersion.toNat := hlt
      have h2 : minFileVersion.toNat ≤ ver.toNat := hv1
      omega
    have hoffNe : ¬ ((1 : UInt8) = 0) := by decide
    simp only [hmagicNe, hverlt, hoffNe, hcond]
    cases legacy <;> simp <;> omega

end Vdb
