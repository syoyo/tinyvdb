/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Node masks. A node at level `l` with `L = log2dim l` owns `2^(3L)` voxel
  slots; the C code stores them as `1 << (3L)` bits, bit `i` in
  `byte[i / 8]` at position `i % 8` (`mask_on`, `tvdb_tree_mask_rank`).

  We model a mask as a `Nat` (its low `2^(3L)` bits are the slots). That is
  the same information as the C bit array and makes the byte serialization a
  base-256 digit decomposition, which mathlib already proves correct
  (`Nat.ofDigits_digits`).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
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

/-- The standard layouts: leaf `L = 3` (512 slots, 64 bytes), lower internal
    `L = 4` (4096 slots, 512 bytes), upper internal `L = 5` (32768 slots,
    4096 bytes). -/
theorem nodeMaskBytes_three : nodeMaskBytes 3 = 64 := by decide
theorem nodeMaskBytes_four : nodeMaskBytes 4 = 512 := by decide
theorem nodeMaskBytes_five : nodeMaskBytes 5 = 4096 := by decide

theorem nodeSlots_three : nodeSlots 3 = 512 := by decide

/-! ### Masks -/

/-- A node mask: the low `2^(3L)` bits of the number are the slots. -/
abbrev NodeMask (_L : Nat) := Nat

/-- Bit `i` of a mask. -/
def NodeMask.bit (m : Nat) (i : Nat) : Bool := m.testBit i

/-- Population count over the node's slots. -/
def NodeMask.popCount {L : Nat} (m : NodeMask L) : Nat :=
  (List.range (nodeSlots L)).countP (fun i => m.testBit i)

/-- Number of set bits strictly below slot `i` (the C `tvdb_tree_mask_rank`). -/
def NodeMask.rank (m : Nat) (i : Nat) : Nat :=
  (List.range i).countP (fun j => m.testBit j)

@[simp] theorem NodeMask.rank_zero (m : Nat) : NodeMask.rank m 0 = 0 := rfl

/-- Adding one slot adds its bit to the rank. -/
theorem NodeMask.rank_succ (m : Nat) (i : Nat) :
    NodeMask.rank m (i + 1) = NodeMask.rank m i + (if NodeMask.bit m i then 1 else 0) := by
  unfold NodeMask.rank NodeMask.bit
  rw [List.range_succ, List.countP_append]
  cases h : m.testBit i <;> simp [h]

/-- Rank at the end of the node equals the population count. -/
theorem NodeMask.rank_full {L : Nat} (m : NodeMask L) :
    NodeMask.rank m (nodeSlots L) = NodeMask.popCount m := rfl

/-- Rank is bounded by the bit index. -/
theorem NodeMask.rank_le_index (m : Nat) (i : Nat) : NodeMask.rank m i ≤ i := by
  unfold NodeMask.rank
  have h : (List.range i).countP (fun j => m.testBit j) ≤ (List.range i).length :=
    List.countP_le_length
  simpa using h

/-- Child compaction index: the number of set bits below `i`, used to index
    the compacted `child_indices` array. -/
def NodeMask.childRank (m : Nat) (i : Nat) : Nat := NodeMask.rank m i

/-! ### Serialization

The C writer emits `ceil(bits/8)` bytes little-endian, bit `i` into byte
`i/8` at position `i%8`, which is exactly the base-256 little-endian digit
expansion of the mask. -/

/-- Base-`256` digits of `m`, zero-padded (on the high side) to `n` digits.
    Requires `m < 256^n`; longer digit lists are truncated (never happens for
    well-formed masks). -/
def paddedDigits (m n : Nat) : List Nat :=
  let d := Nat.digits 256 m
  d ++ List.replicate (n - d.length) 0

theorem paddedDigits_length {m n : Nat} (hm : m < 256 ^ n) :
    (paddedDigits m n).length = n := by
  unfold paddedDigits
  have hb : 1 < 256 := by decide
  have hle : (Nat.digits 256 m).length ≤ n :=
    (Nat.digits_length_le_iff hb m).2 hm
  rw [List.length_append, List.length_replicate]
  omega

/-- The padded digits still evaluate to the mask. -/
theorem ofDigits_paddedDigits (m n : Nat) :
    Nat.ofDigits 256 (paddedDigits m n) = m := by
  unfold paddedDigits
  rw [Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]

/-- Serialize `m` as `n` little-endian bytes. -/
def serializeNat (m n : Nat) : Bytes :=
  pushBytes ((paddedDigits m n).map (fun d => UInt8.ofNat d)) ByteArray.empty

theorem serializeNat_size {m n : Nat} (hm : m < 256 ^ n) : (serializeNat m n).size = n := by
  unfold serializeNat
  rw [pushBytes_size]
  simp [paddedDigits_length hm]

theorem le_two_pow (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega

theorem mask_lt_pow {L : Nat} (m : NodeMask L) (hm : m < nodeSlots L) :
    m < 256 ^ nodeMaskBytes L := by
  unfold nodeMaskBytes nodeBits nodeSlots at *
  have h : 2 ^ (3 * L) ≤ 256 ^ ((2 ^ (3 * L) + 7) / 8) := by
    have h8 : 256 = 2 ^ 8 := by decide
    rw [h8, ← Nat.pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    have hq : 2 ^ (3 * L) ≤ 8 * ((2 ^ (3 * L) + 7) / 8) := by
      have hdm := Nat.div_add_mod (2 ^ (3 * L) + 7) 8
      omega
    have hx : 3 * L ≤ 2 ^ (3 * L) := by
      have := le_two_pow (3 * L)
      omega
    omega
  exact Nat.lt_of_lt_of_le hm h

/-- Serialize a mask to its `nodeMaskBytes L` bytes. -/
def NodeMask.serialize {L : Nat} (m : NodeMask L) : Bytes :=
  serializeNat m (nodeMaskBytes L)

theorem NodeMask.serialize_size {L : Nat} (m : NodeMask L) (hm : m < nodeSlots L) :
    (m.serialize).size = nodeMaskBytes L :=
  serializeNat_size (mask_lt_pow m hm)

/-- Read byte `j` at `off + j` (0 past the end). -/
def readByteOrZero (b : Bytes) (off j : Nat) : Nat :=
  (getU8? b (off + j)).map UInt8.toNat |>.getD 0

/-- Assemble a mask from `n` little-endian bytes at `off`. -/
def parseNat (b : Bytes) (off n : Nat) : Nat :=
  Nat.ofDigits 256 ((List.range n).map (fun j => readByteOrZero b off j))

/-- Every digit of `paddedDigits` fits in a byte. -/
theorem mem_paddedDigits_lt {m n d : Nat} (hd : d ∈ paddedDigits m n) : d < 256 := by
  unfold paddedDigits at hd
  rcases List.mem_append.1 hd with h | h
  · exact Nat.digits_lt_base (by decide) h
  · have : d = 0 := List.eq_of_mem_replicate h
    omega

/-- Reading byte `j` of a serialized mask returns digit `j`. -/
theorem readByteOrZero_serializeNat {m n j d : Nat}
    (hd : (paddedDigits m n)[j]? = some d) :
    readByteOrZero (serializeNat m n) 0 j = d := by
  unfold readByteOrZero
  rw [Nat.zero_add]
  unfold serializeNat
  rw [show j = ByteArray.empty.size + j by simp]
  rw [getU8?_pushBytes_add]
  rw [List.getElem?_map, hd]
  simp only [Option.map_some, Option.getD_some]
  rw [UInt8.toNat_ofNat']
  have hlt : d < 256 := mem_paddedDigits_lt (List.mem_of_getElem? hd)
  exact Nat.mod_eq_of_lt hlt

/-- Serialize/parse round trip: the mask comes back exactly. -/
theorem parseNat_serializeNat {m n : Nat} (hm : m < 256 ^ n) :
    parseNat (serializeNat m n) 0 n = m := by
  unfold parseNat
  have hlen : (paddedDigits m n).length = n := paddedDigits_length hm
  have hlist : (List.range n).map (fun j => readByteOrZero (serializeNat m n) 0 j) =
      paddedDigits m n := by
    apply List.ext_getElem?
    intro j
    by_cases hj : j < n
    · rw [List.getElem?_map, List.getElem?_range hj]
      simp only [Option.map_some]
      cases hd : (paddedDigits m n)[j]? with
      | none =>
        have hsome : (paddedDigits m n)[j]? =
            some ((paddedDigits m n)[j]'(by omega)) :=
          List.getElem?_eq_getElem (by omega)
        rw [hsome] at hd
        cases hd
      | some d => rw [readByteOrZero_serializeNat hd]
    · have hrange : (List.range n).length ≤ j := by simp; omega
      have hpad : (paddedDigits m n).length ≤ j := by rw [hlen]; omega
      rw [List.getElem?_map, List.getElem?_eq_none hrange,
        List.getElem?_eq_none hpad]
      simp only [Option.map_none]
  rw [hlist, ofDigits_paddedDigits]

/-- The mask byte round trip for any layout: a mask below `2^(3L)` serializes
    and parses back unchanged. -/
theorem NodeMask.parse_serialize {L : Nat} (m : NodeMask L) (hm : m < nodeSlots L) :
    parseNat (NodeMask.serialize m) 0 (nodeMaskBytes L) = m :=
  parseNat_serializeNat (mask_lt_pow m hm)

end Vdb
