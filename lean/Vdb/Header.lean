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
import Vdb.Bytes
import Vdb.Value

namespace Vdb

/-! ### String and blob primitives -/

/-- Append raw bytes (the "difference list" counterpart of `getBytes?`). -/
def putBytes (s : Bytes) : Emit := fun acc => acc ++ s

/-- Bounds-checked slice: `n` bytes at `off`. -/
def getBytes? (b : Bytes) (off n : Nat) : Option Bytes :=
  if off + n ≤ b.size then some (b.extract off (off + n)) else none

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
    rw [ByteArray.size_append]; omega
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
    (i := acc.size) (by rw [hoff]; omega)]
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
    defined for half grids). The C reader currently accepts newer versions. -/
def maxFileVersion : UInt32 := 225

/-- Lowest file version the model accepts. -/
def minFileVersion : UInt32 := 220

/-- File header fields (after the magic). -/
structure Header where
  fileVersion : UInt32
  majorVersion : UInt32
  minorVersion : UInt32
  hasGridOffsets : Bool
  /-- Legacy global compression byte, only present for 220 ≤ version < 222.
      It is absent for later versions; the model keeps it `false` there. -/
  legacyCompressed : Bool := false
  uuid : Bytes
  deriving Repr, DecidableEq

/-- Whether the legacy compression byte is on the wire for this version. -/
def Header.hasLegacyByte (h : Header) : Bool :=
  h.fileVersion ≥ 220 && h.fileVersion < 222

/-- Canonical headers: supported version range, 36-byte UUID, and no legacy
    byte value for versions that do not encode it. -/
def Header.Canonical (h : Header) : Prop :=
  minFileVersion ≤ h.fileVersion ∧ h.fileVersion ≤ maxFileVersion ∧
  h.uuid.size = 36 ∧ (h.hasLegacyByte = false → h.legacyCompressed = false)

/-- Emit a header. -/
def Header.emit (h : Header) : Bytes :=
  let acc := putI64LE headerMagic ByteArray.empty
  let acc := putU32LE h.fileVersion acc
  let acc := putU32LE h.majorVersion acc
  let acc := putU32LE h.minorVersion acc
  let acc := putU8 (if h.hasGridOffsets then 1 else 0) acc
  let acc := if h.hasLegacyByte then putU8 (if h.legacyCompressed then 1 else 0) acc else acc
  putBytes h.uuid acc

/-- Parse a header; returns it and the number of bytes consumed. The magic
    and version range are checked. -/
def Header.parse (b : Bytes) : Option (Header × Nat) := do
  let magic ← getI64LE b 0
  if magic ≠ headerMagic then none else do
  let ver ← getU32LE b 8
  if ver < minFileVersion then none else do
  let major ← getU32LE b 12
  let minor ← getU32LE b 16
  let hasOff ← getU8? b 20
  if hasOff = 0 then none else do
  let (legacy, off) ←
    if ver ≥ 220 ∧ ver < 222 then do
      let l ← getU8? b 21
      pure (l != 0, 22)
    else pure (false, 21)
  let uuid ← getBytes? b off 36
  pure (⟨ver, major, minor, true, legacy, uuid⟩, off + 36)

end Vdb
