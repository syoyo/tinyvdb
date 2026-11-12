/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Node masks: a node at level `l` with `L = log2dim l` owns `2^(3L)` voxel
  slots; the C code stores them as `1 << (3L)` bits, bit `i` in
  `byte[i / 8]` at position `i % 8` (`mask_on`, `tvdb_tree_mask_rank`).

  We model a mask as a `Vector Bool (2^(3L))`, so index bounds are free, and
  keep the byte serialization as a separate total function.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Bytes

namespace Vdb

/-! ### Geometry of a node -/

/-- Number of voxel slots in a node with `log2dim = L`. -/
def nodeSlots (L : Nat) : Nat := 2 ^ (3 * L)

/-- Number of serialized bits (`1 << (3L)` in the C code). -/
def nodeBits (L : Nat) : Nat := nodeSlots L

/-- Serialized byte count, `ceil(bits / 8)` (the C `(bits + 7) / 8`). -/
def nodeMaskBytes (L : Nat) : Nat := (nodeBits L + 7) / 8

theorem nodeSlots_pos (L : Nat) : 0 < nodeSlots L := by
  unfold nodeSlots; exact Nat.two_pow_pos _

theorem nodeMaskBytes_pos (L : Nat) : 0 < nodeMaskBytes L := by
  unfold nodeMaskBytes nodeBits nodeSlots
  have h : 0 < 2 ^ (3 * L) := Nat.two_pow_pos _
  omega

/-- Standard layouts: leaf `L = 3` (512 slots, 64 bytes), lower internal
    `L = 4` (4096 slots, 512 bytes), upper internal `L = 5` (32768 slots,
    4096 bytes). -/
theorem nodeMaskBytes_three : nodeMaskBytes 3 = 64 := by decide
theorem nodeMaskBytes_four : nodeMaskBytes 4 = 512 := by decide
theorem nodeMaskBytes_five : nodeMaskBytes 5 = 4096 := by decide

/-- The spacing between leaf voxels in a `5_4_3` tree, i.e. the number of
    voxels per lower-internal node (`1 << 12`). -/
theorem nodeSlots_three : nodeSlots 3 = 512 := by decide

/-! ### Masks -/

/-- A node mask: one bit per slot. -/
abbrev NodeMask (L : Nat) := Vector Bool (nodeSlots L)

/-- Bit `i` of a mask (out-of-range reads are `false`). -/
def NodeMask.bit {L : Nat} (m : NodeMask L) (i : Nat) : Bool :=
  m[i]?.getD false

theorem NodeMask.bit_of_lt {L : Nat} (m : NodeMask L) {i : Nat}
    (h : i < nodeSlots L) : m.bit i = m[i] := by
  unfold NodeMask.bit
  rw [Vector.getElem?_eq_getElem (by simpa [nodeSlots] using h)]
  rfl

theorem NodeMask.bit_of_ge {L : Nat} (m : NodeMask L) {i : Nat}
    (h : nodeSlots L ≤ i) : m.bit i = false := by
  have : m[i]? = none := by
    apply Vector.getElem?_eq_none
    simpa [nodeSlots] using h
  simp [NodeMask.bit, this]

/-- Population count of a mask. -/
def NodeMask.popCount {L : Nat} (m : NodeMask L) : Nat := m.toList.countP id

/-- Number of set bits strictly below slot `i` (the C `tvdb_tree_mask_rank`). -/
def NodeMask.rank {L : Nat} (m : NodeMask L) (i : Nat) : Nat :=
  (m.toList.take i).countP id

/-- Rank of slot 0 is 0. -/
@[simp] theorem NodeMask.rank_zero {L : Nat} (m : NodeMask L) : m.rank 0 = 0 := rfl

/-- Rank at the end of the node equals the population count. -/
theorem NodeMask.rank_full {L : Nat} (m : NodeMask L) :
    m.rank (nodeSlots L) = m.popCount := by
  unfold NodeMask.rank NodeMask.popCount
  rw [List.take_of_length_le (by simp)]

/-- A prefix never has more `true` bits than the whole list. -/
theorem List.count_take_le (l : List α) (p : α → Bool) (i : Nat) :
    (l.take i).countP p ≤ l.countP p := by
  induction l generalizing i with
  | nil => simp
  | cons a t ih =>
    cases i with
    | zero => simp
    | succ k =>
      have h := ih k
      cases hp : p a <;> simp [hp] <;> omega

theorem NodeMask.rank_le_popCount {L : Nat} (m : NodeMask L) (i : Nat) :
    m.rank i ≤ m.popCount := by
  unfold NodeMask.rank NodeMask.popCount
  exact List.count_take_le m.toList id i

/-- Child compaction index: the number of set bits below `i`, used to index
    the compacted `child_indices` array. -/
def NodeMask.childRank {L : Nat} (m : NodeMask L) (i : Nat) : Nat := m.rank i

/-- A mask whose child compaction is consistent with a child count. -/
def NodeMask.childCountOK {L : Nat} (m : NodeMask L) (children : Nat) : Prop :=
  m.popCount = children

/-! ### Serialization -/

/-- The 8 bits starting at `8 * j`, as a little-endian byte (bit `k` of the
    byte is slot `8 * j + k`). -/
def NodeMask.byteAt {L : Nat} (m : NodeMask L) (j : Nat) : UInt8 :=
  UInt8.ofNat <| (List.range 8).foldl
    (fun acc k => acc + (if m.bit (8 * j + k) then 2 ^ k else 0)) 0

/-- Serialize a mask: `ceil(bits/8)` bytes, low bits first. -/
def NodeMask.serialize {L : Nat} (m : NodeMask L) : Bytes :=
  pushBytes ((List.range (nodeMaskBytes L)).map (fun j => m.byteAt j)) ByteArray.empty

theorem NodeMask.serialize_size {L : Nat} (m : NodeMask L) :
    (m.serialize).size = nodeMaskBytes L := by
  unfold NodeMask.serialize
  rw [pushBytes_size]
  simp

/-- Read byte `j` at `off + j` (0 past the end). -/
def readByteOrZero (b : Bytes) (off j : Nat) : Nat :=
  (getU8? b (off + j)).map UInt8.toNat |>.getD 0

/-- Assemble a mask from little-endian bytes at `off`. Bits past the serialized
    range read as `false`. -/
def NodeMask.parse {L : Nat} (b : Bytes) (off : Nat) : NodeMask L :=
  Vector.ofFn (fun (i : Fin (nodeSlots L)) =>
    let j := i.val / 8
    let k := i.val % 8
    Nat.testBit (readByteOrZero b off j) k)

end Vdb
