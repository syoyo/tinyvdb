/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Per-node value records: the mask-compression code byte, the inactive values,
  the selection mask and the value chunk (`tvdb__read_mask_values` /
  `tvdb__write_mask_values`). The classification itself is in
  `Vdb/MaskCompress.lean`; this module proves that the wire record parses back
  exactly. The value chunk is modelled as a raw chunk (compression is a codec
  parameter in `Vdb/Chunk.lean`), so the emit side is deterministic.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Mask
import Vdb.MaskCompress
import Vdb.Chunk

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Vdb

/-- The wire flag byte of a mask-compression code. -/
def MaskCode.flag : MaskCode → UInt8
  | .noMaskOrInactiveVals => 0
  | .noMaskAndMinusBg => 1
  | .noMaskAndOneInactiveVal => 2
  | .maskAndNoInactiveVals => 3
  | .maskAndOneInactiveVal => 4
  | .maskAndTwoInactiveVals => 5
  | .noMaskAndAllVals => 6

@[simp] theorem MaskCode.flag_toNat : ∀ c : MaskCode, c.flag.toNat = c.toNat
  | .noMaskOrInactiveVals => rfl
  | .noMaskAndMinusBg => rfl
  | .noMaskAndOneInactiveVal => rfl
  | .maskAndNoInactiveVals => rfl
  | .maskAndOneInactiveVal => rfl
  | .maskAndTwoInactiveVals => rfl
  | .noMaskAndAllVals => rfl

@[simp] theorem MaskCode.ofNat?_flag (c : MaskCode) :
    MaskCode.ofNat? c.flag.toNat = some c := by
  cases c <;> rfl

end Vdb
namespace Vdb

theorem Chunk.parse_rawChunks (decompress : Bytes → Nat → Option Bytes)
    (pre post : List Bytes) (raw : Bytes) (hsz : raw.size < 2 ^ 63) :
    Chunk.parse decompress (concatChunks (pre ++ Chunk.rawChunks raw ++ post))
      (concatChunks pre).size raw.size =
    some (raw, (concatChunks (pre ++ Chunk.rawChunks raw)).size) := by
  simpa [Chunk.rawChunks] using Chunk.parse_raw decompress pre post raw hsz

end Vdb
namespace Vdb

/-- One node's mask-compressed value record: the classification plus the
    stored (raw) payload. The wire order matches `tvdb__write_mask_values`:
    code byte, the inactive values (full width), the selection mask, then the
    value chunk. -/
structure ValueRecord (L : Nat) where
  code : MaskCode
  val0 : Bytes
  val1 : Bytes
  selection : NodeMask L
  stored : Bytes
  deriving Repr

/-- Chunks after the code byte. -/
def ValueRecord.tailChunks {L : Nat} (r : ValueRecord L) : List Bytes :=
  match r.code with
  | .noMaskOrInactiveVals => Chunk.rawChunks r.stored
  | .noMaskAndMinusBg => Chunk.rawChunks r.stored
  | .noMaskAndOneInactiveVal => r.val0 :: Chunk.rawChunks r.stored
  | .maskAndNoInactiveVals => @NodeMask.serialize L r.selection :: Chunk.rawChunks r.stored
  | .maskAndOneInactiveVal =>
    r.val0 :: @NodeMask.serialize L r.selection :: Chunk.rawChunks r.stored
  | .maskAndTwoInactiveVals =>
    r.val0 :: r.val1 :: @NodeMask.serialize L r.selection :: Chunk.rawChunks r.stored
  | .noMaskAndAllVals => Chunk.rawChunks r.stored

def ValueRecord.chunks {L : Nat} (r : ValueRecord L) : List Bytes :=
  putU8 r.code.flag ByteArray.empty :: r.tailChunks

def ValueRecord.WellFormed {L : Nat} (vsize expected : Nat) (r : ValueRecord L) : Prop :=
  (match r.code with
   | .noMaskOrInactiveVals =>
     r.val0 = ByteArray.empty ∧ r.val1 = ByteArray.empty ∧ r.selection = 0
   | .noMaskAndMinusBg =>
     r.val0 = ByteArray.empty ∧ r.val1 = ByteArray.empty ∧ r.selection = 0
   | .noMaskAndOneInactiveVal =>
     r.val0.size = vsize ∧ r.val1 = ByteArray.empty ∧ r.selection = 0
   | .maskAndNoInactiveVals =>
     r.val0 = ByteArray.empty ∧ r.val1 = ByteArray.empty ∧ r.selection < nodeSlots L
   | .maskAndOneInactiveVal =>
     r.val0.size = vsize ∧ r.val1 = ByteArray.empty ∧ r.selection < nodeSlots L
   | .maskAndTwoInactiveVals =>
     r.val0.size = vsize ∧ r.val1.size = vsize ∧ r.selection < nodeSlots L
   | .noMaskAndAllVals =>
     r.val0 = ByteArray.empty ∧ r.val1 = ByteArray.empty ∧ r.selection = 0)
  ∧ r.stored.size = expected ∧ expected < 2 ^ 63

def ValueRecord.parseFrom {L : Nat} (vsize expected : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) :
    Option (ValueRecord L × Nat) :=
  match getU8? b off with
  | none => none
  | some fl =>
    match MaskCode.ofNat? fl.toNat with
    | none => none
    | some code =>
      match code with
      | .noMaskOrInactiveVals =>
        (Chunk.parse decompress b (off + 1) expected).map fun p =>
          (⟨.noMaskOrInactiveVals, ByteArray.empty, ByteArray.empty, 0, p.1⟩, p.2)
      | .noMaskAndMinusBg =>
        (Chunk.parse decompress b (off + 1) expected).map fun p =>
          (⟨.noMaskAndMinusBg, ByteArray.empty, ByteArray.empty, 0, p.1⟩, p.2)
      | .noMaskAndAllVals =>
        (Chunk.parse decompress b (off + 1) expected).map fun p =>
          (⟨.noMaskAndAllVals, ByteArray.empty, ByteArray.empty, 0, p.1⟩, p.2)
      | .noMaskAndOneInactiveVal =>
        match getBytes? b (off + 1) vsize with
        | none => none
        | some v0 =>
          (Chunk.parse decompress b (off + 1 + vsize) expected).map fun p =>
            (⟨.noMaskAndOneInactiveVal, v0, ByteArray.empty, 0, p.1⟩, p.2)
      | .maskAndNoInactiveVals =>
        let sel : NodeMask L := parseNat b (off + 1) (nodeMaskBytes L)
        (Chunk.parse decompress b (off + 1 + nodeMaskBytes L) expected).map fun p =>
          (⟨.maskAndNoInactiveVals, ByteArray.empty, ByteArray.empty, sel, p.1⟩, p.2)
      | .maskAndOneInactiveVal =>
        match getBytes? b (off + 1) vsize with
        | none => none
        | some v0 =>
          let sel : NodeMask L := parseNat b (off + 1 + vsize) (nodeMaskBytes L)
          (Chunk.parse decompress b (off + 1 + vsize + nodeMaskBytes L) expected).map fun p =>
            (⟨.maskAndOneInactiveVal, v0, ByteArray.empty, sel, p.1⟩, p.2)
      | .maskAndTwoInactiveVals =>
        match getBytes? b (off + 1) vsize with
        | none => none
        | some v0 =>
          match getBytes? b (off + 1 + vsize) vsize with
          | none => none
          | some v1 =>
            let sel : NodeMask L := parseNat b (off + 1 + vsize + vsize) (nodeMaskBytes L)
            (Chunk.parse decompress b (off + 1 + vsize + vsize + nodeMaskBytes L) expected).map fun p =>
              (⟨.maskAndTwoInactiveVals, v0, v1, sel, p.1⟩, p.2)

end Vdb
namespace Vdb


theorem getBytes?_chunk_size (pre : List Bytes) (c : Bytes) (post : List Bytes) {n : Nat}
    (h : c.size = n) :
    getBytes? (concatChunks (pre ++ c :: post)) (concatChunks pre).size n = some c := by
  rw [← h]
  exact getBytes?_chunk pre c post

theorem peel_cons (pre : List Bytes) (c d : Bytes) (rest post : List Bytes) :
    concatChunks (pre ++ c :: ((d :: rest) ++ post)) =
      concatChunks ((pre ++ [c]) ++ (d :: (rest ++ post))) := by simp

theorem peel_last (pre : List Bytes) (c : Bytes) (rest post : List Bytes) :
    concatChunks (pre ++ c :: (rest ++ post)) =
      concatChunks ((pre ++ [c]) ++ (rest ++ post)) := by simp

theorem parse_chunk_after (decompress : Bytes → Nat → Option Bytes)
    (l : List Bytes) (stored : Bytes) (post : List Bytes) (hsz : stored.size < 2 ^ 63) :
    Chunk.parse decompress (concatChunks (l ++ (Chunk.rawChunks stored ++ post)))
      (concatChunks l).size stored.size =
    some (stored, (concatChunks (l ++ Chunk.rawChunks stored)).size) := by
  rw [show l ++ (Chunk.rawChunks stored ++ post) = (l ++ Chunk.rawChunks stored) ++ post from by simp]
  exact Chunk.parse_rawChunks decompress l post stored hsz

theorem ValueRecord.parseFrom_emitFrom {L : Nat} (r : ValueRecord L) (vsize expected : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (hwf : r.WellFormed vsize expected)
    (pre post : List Bytes) :
    ValueRecord.parseFrom vsize expected decompress
        (concatChunks (pre ++ r.chunks ++ post)) (concatChunks pre).size =
      some (r, (concatChunks (pre ++ r.chunks)).size) := by
  obtain ⟨hcls, hsize, hbound⟩ := hwf
  rcases r with ⟨code, v0, v1, sel, stored⟩
  cases code
  · -- noMaskOrInactiveVals
    simp only [ValueRecord.WellFormed] at hcls
    obtain ⟨hv0, hv1, hsel⟩ := hcls
    subst hv0 hv1 hsel
    unfold ValueRecord.parseFrom ValueRecord.chunks ValueRecord.tailChunks
    rw [show concatChunks (pre ++ (putU8 (MaskCode.flag .noMaskOrInactiveVals) ByteArray.empty :: Chunk.rawChunks stored) ++ post) =
        concatChunks (pre ++ (putU8 (MaskCode.flag .noMaskOrInactiveVals) ByteArray.empty :: (Chunk.rawChunks stored ++ post))) from by simp]
    rw [getU8?_chunk]
    dsimp only
    rw [MaskCode.ofNat?_flag]
    dsimp only
    rw [show (concatChunks pre).size + 1 =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .noMaskOrInactiveVals) ByteArray.empty])).size from by
      rw [show (1 : Nat) = (putU8 (MaskCode.flag .noMaskOrInactiveVals) ByteArray.empty).size from by simp [putU8_size]]
      conv_rhs => rw [concatChunks_snoc_size]]
    rw [peel_last pre (putU8 (MaskCode.flag .noMaskOrInactiveVals) ByteArray.empty) (Chunk.rawChunks stored) post]
    rw [show expected = stored.size from hsize.symm]
    rw [parse_chunk_after decompress (pre ++ [putU8 (MaskCode.flag .noMaskOrInactiveVals) ByteArray.empty]) stored post (by simpa [hsize] using hbound)]
    simp [ValueRecord.chunks, ValueRecord.tailChunks]
  · -- noMaskAndMinusBg
    simp only [ValueRecord.WellFormed] at hcls
    obtain ⟨hv0, hv1, hsel⟩ := hcls
    subst hv0 hv1 hsel
    unfold ValueRecord.parseFrom ValueRecord.chunks ValueRecord.tailChunks
    rw [show concatChunks (pre ++ (putU8 (MaskCode.flag .noMaskAndMinusBg) ByteArray.empty :: Chunk.rawChunks stored) ++ post) =
        concatChunks (pre ++ (putU8 (MaskCode.flag .noMaskAndMinusBg) ByteArray.empty :: (Chunk.rawChunks stored ++ post))) from by simp]
    rw [getU8?_chunk]
    dsimp only
    rw [MaskCode.ofNat?_flag]
    dsimp only
    rw [show (concatChunks pre).size + 1 =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .noMaskAndMinusBg) ByteArray.empty])).size from by
      rw [show (1 : Nat) = (putU8 (MaskCode.flag .noMaskAndMinusBg) ByteArray.empty).size from by simp [putU8_size]]
      conv_rhs => rw [concatChunks_snoc_size]]
    rw [peel_last pre (putU8 (MaskCode.flag .noMaskAndMinusBg) ByteArray.empty) (Chunk.rawChunks stored) post]
    rw [show expected = stored.size from hsize.symm]
    rw [parse_chunk_after decompress (pre ++ [putU8 (MaskCode.flag .noMaskAndMinusBg) ByteArray.empty]) stored post (by simpa [hsize] using hbound)]
    simp [ValueRecord.chunks, ValueRecord.tailChunks]
  · -- noMaskAndOneInactiveVal
    simp only [ValueRecord.WellFormed] at hcls
    obtain ⟨hv0, hv1, hsel⟩ := hcls
    subst hv1 hsel
    unfold ValueRecord.parseFrom ValueRecord.chunks ValueRecord.tailChunks
    rw [show concatChunks (pre ++ (putU8 (MaskCode.flag .noMaskAndOneInactiveVal) ByteArray.empty :: (v0 :: Chunk.rawChunks stored)) ++ post) =
        concatChunks (pre ++ (putU8 (MaskCode.flag .noMaskAndOneInactiveVal) ByteArray.empty :: ((v0 :: Chunk.rawChunks stored) ++ post))) from by simp]
    rw [getU8?_chunk]
    dsimp only
    rw [MaskCode.ofNat?_flag]
    dsimp only
    rw [show (concatChunks pre).size + 1 =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .noMaskAndOneInactiveVal) ByteArray.empty])).size from by
      rw [show (1 : Nat) = (putU8 (MaskCode.flag .noMaskAndOneInactiveVal) ByteArray.empty).size from by simp [putU8_size]]
      conv_rhs => rw [concatChunks_snoc_size]]
    rw [peel_cons pre (putU8 (MaskCode.flag .noMaskAndOneInactiveVal) ByteArray.empty) (v0) (Chunk.rawChunks stored) post]
    rw [getBytes?_chunk_size (pre ++ [putU8 (MaskCode.flag .noMaskAndOneInactiveVal) ByteArray.empty]) (v0) (Chunk.rawChunks stored ++ post) (h := hv0)]
    dsimp only
    rw [show (concatChunks (pre ++ [putU8 (MaskCode.flag .noMaskAndOneInactiveVal) ByteArray.empty])).size + vsize =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .noMaskAndOneInactiveVal) ByteArray.empty] ++ [v0])).size from by
      conv_rhs => rw [concatChunks_snoc_size]
      rw [hv0]]
    rw [peel_last (pre ++ [putU8 (MaskCode.flag .noMaskAndOneInactiveVal) ByteArray.empty]) (v0) (Chunk.rawChunks stored) post]
    rw [show expected = stored.size from hsize.symm]
    rw [parse_chunk_after decompress (pre ++ [putU8 (MaskCode.flag .noMaskAndOneInactiveVal) ByteArray.empty] ++ [v0]) stored post (by simpa [hsize] using hbound)]
    simp [ValueRecord.chunks, ValueRecord.tailChunks]
  · -- maskAndNoInactiveVals
    simp only [ValueRecord.WellFormed] at hcls
    obtain ⟨hv0, hv1, hsel⟩ := hcls
    subst hv0 hv1
    unfold ValueRecord.parseFrom ValueRecord.chunks ValueRecord.tailChunks
    rw [show concatChunks (pre ++ (putU8 (MaskCode.flag .maskAndNoInactiveVals) ByteArray.empty :: (@NodeMask.serialize L sel :: Chunk.rawChunks stored)) ++ post) =
        concatChunks (pre ++ (putU8 (MaskCode.flag .maskAndNoInactiveVals) ByteArray.empty :: ((@NodeMask.serialize L sel :: Chunk.rawChunks stored) ++ post))) from by simp]
    rw [getU8?_chunk]
    dsimp only
    rw [MaskCode.ofNat?_flag]
    dsimp only
    rw [show (concatChunks pre).size + 1 =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndNoInactiveVals) ByteArray.empty])).size from by
      rw [show (1 : Nat) = (putU8 (MaskCode.flag .maskAndNoInactiveVals) ByteArray.empty).size from by simp [putU8_size]]
      conv_rhs => rw [concatChunks_snoc_size]]
    rw [peel_cons pre (putU8 (MaskCode.flag .maskAndNoInactiveVals) ByteArray.empty) (@NodeMask.serialize L sel) (Chunk.rawChunks stored) post]
    rw [parseNat_chunk_serialize sel hsel (pre ++ [putU8 (MaskCode.flag .maskAndNoInactiveVals) ByteArray.empty]) (Chunk.rawChunks stored ++ post)]
    rw [show (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndNoInactiveVals) ByteArray.empty])).size + nodeMaskBytes L =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndNoInactiveVals) ByteArray.empty] ++ [@NodeMask.serialize L sel])).size from by
      conv_rhs => rw [concatChunks_snoc_size]
      rw [@NodeMask.serialize_size L sel hsel]]
    rw [peel_last (pre ++ [putU8 (MaskCode.flag .maskAndNoInactiveVals) ByteArray.empty]) (@NodeMask.serialize L sel) (Chunk.rawChunks stored) post]
    rw [show expected = stored.size from hsize.symm]
    rw [parse_chunk_after decompress (pre ++ [putU8 (MaskCode.flag .maskAndNoInactiveVals) ByteArray.empty] ++ [@NodeMask.serialize L sel]) stored post (by simpa [hsize] using hbound)]
    simp [ValueRecord.chunks, ValueRecord.tailChunks]
  · -- maskAndOneInactiveVal
    simp only [ValueRecord.WellFormed] at hcls
    obtain ⟨hv0, hv1, hsel⟩ := hcls
    subst hv1
    unfold ValueRecord.parseFrom ValueRecord.chunks ValueRecord.tailChunks
    rw [show concatChunks (pre ++ (putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty :: (v0 :: (@NodeMask.serialize L sel :: Chunk.rawChunks stored))) ++ post) =
        concatChunks (pre ++ (putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty :: ((v0 :: (@NodeMask.serialize L sel :: Chunk.rawChunks stored)) ++ post))) from by simp]
    rw [getU8?_chunk]
    dsimp only
    rw [MaskCode.ofNat?_flag]
    dsimp only
    rw [show (concatChunks pre).size + 1 =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty])).size from by
      rw [show (1 : Nat) = (putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty).size from by simp [putU8_size]]
      conv_rhs => rw [concatChunks_snoc_size]]
    rw [peel_cons pre (putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty) (v0) ((@NodeMask.serialize L sel :: Chunk.rawChunks stored)) post]
    rw [getBytes?_chunk_size (pre ++ [putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty]) (v0) ((@NodeMask.serialize L sel :: Chunk.rawChunks stored) ++ post) (h := hv0)]
    dsimp only
    rw [show (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty])).size + vsize =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty] ++ [v0])).size from by
      conv_rhs => rw [concatChunks_snoc_size]
      rw [hv0]]
    rw [peel_cons (pre ++ [putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty]) (v0) (@NodeMask.serialize L sel) (Chunk.rawChunks stored) post]
    rw [parseNat_chunk_serialize sel hsel (pre ++ [putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty] ++ [v0]) (Chunk.rawChunks stored ++ post)]
    rw [show (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty] ++ [v0])).size + nodeMaskBytes L =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty] ++ [v0] ++ [@NodeMask.serialize L sel])).size from by
      conv_rhs => rw [concatChunks_snoc_size]
      rw [@NodeMask.serialize_size L sel hsel]]
    rw [peel_last (pre ++ [putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty] ++ [v0]) (@NodeMask.serialize L sel) (Chunk.rawChunks stored) post]
    rw [show expected = stored.size from hsize.symm]
    rw [parse_chunk_after decompress (pre ++ [putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty] ++ [v0] ++ [@NodeMask.serialize L sel]) stored post (by simpa [hsize] using hbound)]
    simp [ValueRecord.chunks, ValueRecord.tailChunks]
  · -- maskAndTwoInactiveVals
    simp only [ValueRecord.WellFormed] at hcls
    obtain ⟨hv0, hv1, hsel⟩ := hcls
    unfold ValueRecord.parseFrom ValueRecord.chunks ValueRecord.tailChunks
    rw [show concatChunks (pre ++ (putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty :: (v0 :: (v1 :: (@NodeMask.serialize L sel :: Chunk.rawChunks stored)))) ++ post) =
        concatChunks (pre ++ (putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty :: ((v0 :: (v1 :: (@NodeMask.serialize L sel :: Chunk.rawChunks stored))) ++ post))) from by simp]
    rw [getU8?_chunk]
    dsimp only
    rw [MaskCode.ofNat?_flag]
    dsimp only
    rw [show (concatChunks pre).size + 1 =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty])).size from by
      rw [show (1 : Nat) = (putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty).size from by simp [putU8_size]]
      conv_rhs => rw [concatChunks_snoc_size]]
    rw [peel_cons pre (putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty) (v0) ((v1 :: (@NodeMask.serialize L sel :: Chunk.rawChunks stored))) post]
    rw [getBytes?_chunk_size (pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty]) (v0) ((v1 :: (@NodeMask.serialize L sel :: Chunk.rawChunks stored)) ++ post) (h := hv0)]
    dsimp only
    rw [show (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty])).size + vsize =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty] ++ [v0])).size from by
      conv_rhs => rw [concatChunks_snoc_size]
      rw [hv0]]
    rw [peel_cons (pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty]) (v0) (v1) ((@NodeMask.serialize L sel :: Chunk.rawChunks stored)) post]
    rw [getBytes?_chunk_size (pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty] ++ [v0]) (v1) ((@NodeMask.serialize L sel :: Chunk.rawChunks stored) ++ post) (h := hv1)]
    dsimp only
    rw [show (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty] ++ [v0])).size + vsize =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty] ++ [v0] ++ [v1])).size from by
      conv_rhs => rw [concatChunks_snoc_size]
      rw [hv1]]
    rw [peel_cons (pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty] ++ [v0]) (v1) (@NodeMask.serialize L sel) (Chunk.rawChunks stored) post]
    rw [parseNat_chunk_serialize sel hsel (pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty] ++ [v0] ++ [v1]) (Chunk.rawChunks stored ++ post)]
    rw [show (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty] ++ [v0] ++ [v1])).size + nodeMaskBytes L =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty] ++ [v0] ++ [v1] ++ [@NodeMask.serialize L sel])).size from by
      conv_rhs => rw [concatChunks_snoc_size]
      rw [@NodeMask.serialize_size L sel hsel]]
    rw [peel_last (pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty] ++ [v0] ++ [v1]) (@NodeMask.serialize L sel) (Chunk.rawChunks stored) post]
    rw [show expected = stored.size from hsize.symm]
    rw [parse_chunk_after decompress (pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty] ++ [v0] ++ [v1] ++ [@NodeMask.serialize L sel]) stored post (by simpa [hsize] using hbound)]
    simp [ValueRecord.chunks, ValueRecord.tailChunks]
  · -- noMaskAndAllVals
    simp only [ValueRecord.WellFormed] at hcls
    obtain ⟨hv0, hv1, hsel⟩ := hcls
    subst hv0 hv1 hsel
    unfold ValueRecord.parseFrom ValueRecord.chunks ValueRecord.tailChunks
    rw [show concatChunks (pre ++ (putU8 (MaskCode.flag .noMaskAndAllVals) ByteArray.empty :: Chunk.rawChunks stored) ++ post) =
        concatChunks (pre ++ (putU8 (MaskCode.flag .noMaskAndAllVals) ByteArray.empty :: (Chunk.rawChunks stored ++ post))) from by simp]
    rw [getU8?_chunk]
    dsimp only
    rw [MaskCode.ofNat?_flag]
    dsimp only
    rw [show (concatChunks pre).size + 1 =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .noMaskAndAllVals) ByteArray.empty])).size from by
      rw [show (1 : Nat) = (putU8 (MaskCode.flag .noMaskAndAllVals) ByteArray.empty).size from by simp [putU8_size]]
      conv_rhs => rw [concatChunks_snoc_size]]
    rw [peel_last pre (putU8 (MaskCode.flag .noMaskAndAllVals) ByteArray.empty) (Chunk.rawChunks stored) post]
    rw [show expected = stored.size from hsize.symm]
    rw [parse_chunk_after decompress (pre ++ [putU8 (MaskCode.flag .noMaskAndAllVals) ByteArray.empty]) stored post (by simpa [hsize] using hbound)]
    simp [ValueRecord.chunks, ValueRecord.tailChunks]



theorem bytes_eq_empty_of_size_zero (b : Bytes) (h : b.size = 0) : b = ByteArray.empty := by
  apply ByteArray.ext
  have h' : b.data.size = 0 := h
  rw [Array.eq_empty_of_size_eq_zero h']
  rfl


/-- Peel a scalars chunk off the front of a cons chain (chunk list spelled
    cons-wise). -/
theorem peel_cons' (pre : List Bytes) (c d : Bytes) (rest : List Bytes) :
    concatChunks (pre ++ c :: (d :: rest)) =
      concatChunks ((pre ++ [c]) ++ (d :: rest)) := by simp

/-- Peel the last scalars chunk off the front of a cons chain. -/
theorem peel_last' (pre : List Bytes) (c : Bytes) (post : List Bytes) :
    concatChunks (pre ++ c :: post) = concatChunks ((pre ++ [c]) ++ post) := by simp

/-- The chunks after the code byte, without the value chunk. -/
def ValueRecord.extras {L : Nat} (r : ValueRecord L) : List Bytes :=
  match r.code with
  | .noMaskOrInactiveVals => []
  | .noMaskAndMinusBg => []
  | .noMaskAndOneInactiveVal => [r.val0]
  | .maskAndNoInactiveVals => [@NodeMask.serialize L r.selection]
  | .maskAndOneInactiveVal => [r.val0, @NodeMask.serialize L r.selection]
  | .maskAndTwoInactiveVals => [r.val0, r.val1, @NodeMask.serialize L r.selection]
  | .noMaskAndAllVals => []

/-- The code byte plus the inactive values and selection mask, with no value
    chunk. Half grids write exactly this when the stored count is zero
    (`HalfWriter`: `if (count < 1) return`). -/
def ValueRecord.chunksNoChunk {L : Nat} (r : ValueRecord L) : List Bytes :=
  putU8 r.code.flag ByteArray.empty :: r.extras

/-- The record parser for the zero-count half case: the same dispatch as
    `parseFrom`, but it stops after the inactive values and selection mask. -/
def ValueRecord.parseNoChunk {L : Nat} (vsize : Nat) (b : Bytes) (off : Nat) :
    Option (ValueRecord L × Nat) :=
  match getU8? b off with
  | none => none
  | some fl =>
    match MaskCode.ofNat? fl.toNat with
    | none => none
    | some code =>
      match code with
      | .noMaskOrInactiveVals =>
        some (⟨.noMaskOrInactiveVals, ByteArray.empty, ByteArray.empty, 0,
          ByteArray.empty⟩, off + 1)
      | .noMaskAndMinusBg =>
        some (⟨.noMaskAndMinusBg, ByteArray.empty, ByteArray.empty, 0,
          ByteArray.empty⟩, off + 1)
      | .noMaskAndAllVals =>
        some (⟨.noMaskAndAllVals, ByteArray.empty, ByteArray.empty, 0,
          ByteArray.empty⟩, off + 1)
      | .noMaskAndOneInactiveVal =>
        match getBytes? b (off + 1) vsize with
        | none => none
        | some v0 =>
          some (⟨.noMaskAndOneInactiveVal, v0, ByteArray.empty, 0, ByteArray.empty⟩,
            off + 1 + vsize)
      | .maskAndNoInactiveVals =>
        let sel : NodeMask L := parseNat b (off + 1) (nodeMaskBytes L)
        some (⟨.maskAndNoInactiveVals, ByteArray.empty, ByteArray.empty, sel,
          ByteArray.empty⟩, off + 1 + nodeMaskBytes L)
      | .maskAndOneInactiveVal =>
        match getBytes? b (off + 1) vsize with
        | none => none
        | some v0 =>
          let sel : NodeMask L := parseNat b (off + 1 + vsize) (nodeMaskBytes L)
          some (⟨.maskAndOneInactiveVal, v0, ByteArray.empty, sel, ByteArray.empty⟩,
            off + 1 + vsize + nodeMaskBytes L)
      | .maskAndTwoInactiveVals =>
        match getBytes? b (off + 1) vsize with
        | none => none
        | some v0 =>
          match getBytes? b (off + 1 + vsize) vsize with
          | none => none
          | some v1 =>
            let sel : NodeMask L := parseNat b (off + 1 + vsize + vsize) (nodeMaskBytes L)
            some (⟨.maskAndTwoInactiveVals, v0, v1, sel, ByteArray.empty⟩,
              off + 1 + vsize + vsize + nodeMaskBytes L)

/-- Emit a record, omitting the value chunk in half mode when the stored
    payload is empty (`expected = 0`). -/
def ValueRecord.chunksM {L : Nat} (half : Bool) (r : ValueRecord L) : List Bytes :=
  if half && r.stored.size = 0 then r.chunksNoChunk else r.chunks

/-- Parse a record in either mode. Half grids with an empty payload carry no
    chunk header, so they use `parseNoChunk`. -/
def ValueRecord.parseM {L : Nat} (vsize expected : Nat)
    (decompress : Bytes → Nat → Option Bytes) (half : Bool) (b : Bytes) (off : Nat) :
    Option (ValueRecord L × Nat) :=
  if half && expected = 0 then ValueRecord.parseNoChunk vsize b off
  else ValueRecord.parseFrom vsize expected decompress b off


theorem ValueRecord.parseNoChunk_emit {L : Nat} (r : ValueRecord L) (vsize : Nat)
    (hwf : r.WellFormed vsize 0) (hst : r.stored = ByteArray.empty)
    (pre post : List Bytes) :
    ValueRecord.parseNoChunk vsize
        (concatChunks (pre ++ r.chunksNoChunk ++ post)) (concatChunks pre).size =
      some (r, (concatChunks (pre ++ r.chunksNoChunk)).size) := by
  obtain ⟨hcls, hsize, hbound⟩ := hwf
  rcases r with ⟨code, v0, v1, sel, stored⟩
  cases code
  · -- noMaskOrInactiveVals
    simp only [ValueRecord.WellFormed] at hcls
    obtain ⟨hv0, hv1, hsel⟩ := hcls
    subst hv0 hv1 hsel
    subst hst
    unfold ValueRecord.parseNoChunk ValueRecord.chunksNoChunk ValueRecord.extras
    rw [show pre ++ (putU8 (MaskCode.flag .noMaskOrInactiveVals) ByteArray.empty :: []) ++ post =
        pre ++ (putU8 (MaskCode.flag .noMaskOrInactiveVals) ByteArray.empty :: ([] ++ post)) from by simp]
    simp only [List.cons_append, List.singleton_append, List.nil_append]
    rw [getU8?_chunk]
    dsimp only
    rw [MaskCode.ofNat?_flag]
    dsimp only
    rw [show (concatChunks pre).size + 1 =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .noMaskOrInactiveVals) ByteArray.empty])).size from by
      rw [show (1 : Nat) = (putU8 (MaskCode.flag .noMaskOrInactiveVals) ByteArray.empty).size from by simp [putU8_size]]
      conv_rhs => rw [concatChunks_snoc_size]]
  · -- noMaskAndMinusBg
    simp only [ValueRecord.WellFormed] at hcls
    obtain ⟨hv0, hv1, hsel⟩ := hcls
    subst hv0 hv1 hsel
    subst hst
    unfold ValueRecord.parseNoChunk ValueRecord.chunksNoChunk ValueRecord.extras
    rw [show pre ++ (putU8 (MaskCode.flag .noMaskAndMinusBg) ByteArray.empty :: []) ++ post =
        pre ++ (putU8 (MaskCode.flag .noMaskAndMinusBg) ByteArray.empty :: ([] ++ post)) from by simp]
    simp only [List.cons_append, List.singleton_append, List.nil_append]
    rw [getU8?_chunk]
    dsimp only
    rw [MaskCode.ofNat?_flag]
    dsimp only
    rw [show (concatChunks pre).size + 1 =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .noMaskAndMinusBg) ByteArray.empty])).size from by
      rw [show (1 : Nat) = (putU8 (MaskCode.flag .noMaskAndMinusBg) ByteArray.empty).size from by simp [putU8_size]]
      conv_rhs => rw [concatChunks_snoc_size]]
  · -- noMaskAndOneInactiveVal
    simp only [ValueRecord.WellFormed] at hcls
    obtain ⟨hv0, hv1, hsel⟩ := hcls
    subst hv1 hsel
    subst hst
    unfold ValueRecord.parseNoChunk ValueRecord.chunksNoChunk ValueRecord.extras
    rw [show pre ++ (putU8 (MaskCode.flag .noMaskAndOneInactiveVal) ByteArray.empty :: (v0 :: [])) ++ post =
        pre ++ (putU8 (MaskCode.flag .noMaskAndOneInactiveVal) ByteArray.empty :: ((v0 :: []) ++ post)) from by simp]
    simp only [List.cons_append, List.singleton_append, List.nil_append]
    rw [getU8?_chunk]
    dsimp only
    rw [MaskCode.ofNat?_flag]
    dsimp only
    rw [show (concatChunks pre).size + 1 =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .noMaskAndOneInactiveVal) ByteArray.empty])).size from by
      rw [show (1 : Nat) = (putU8 (MaskCode.flag .noMaskAndOneInactiveVal) ByteArray.empty).size from by simp [putU8_size]]
      conv_rhs => rw [concatChunks_snoc_size]]
    rw [peel_last' pre (putU8 (MaskCode.flag .noMaskAndOneInactiveVal) ByteArray.empty) ((v0 :: post))]
    rw [getBytes?_chunk_size (pre ++ [putU8 (MaskCode.flag .noMaskAndOneInactiveVal) ByteArray.empty]) (v0) (post) (h := hv0)]
    dsimp only
    rw [show (concatChunks (pre ++ [putU8 (MaskCode.flag .noMaskAndOneInactiveVal) ByteArray.empty])).size + vsize =
        (concatChunks ((pre ++ [putU8 (MaskCode.flag .noMaskAndOneInactiveVal) ByteArray.empty]) ++ [v0])).size from by
      conv_rhs => rw [concatChunks_snoc_size]
      rw [hv0]]
    simp [List.append_assoc]
  · -- maskAndNoInactiveVals
    simp only [ValueRecord.WellFormed] at hcls
    obtain ⟨hv0, hv1, hsel⟩ := hcls
    subst hv0 hv1
    subst hst
    unfold ValueRecord.parseNoChunk ValueRecord.chunksNoChunk ValueRecord.extras
    rw [show pre ++ (putU8 (MaskCode.flag .maskAndNoInactiveVals) ByteArray.empty :: (@NodeMask.serialize L sel :: [])) ++ post =
        pre ++ (putU8 (MaskCode.flag .maskAndNoInactiveVals) ByteArray.empty :: ((@NodeMask.serialize L sel :: []) ++ post)) from by simp]
    simp only [List.cons_append, List.singleton_append, List.nil_append]
    rw [getU8?_chunk]
    dsimp only
    rw [MaskCode.ofNat?_flag]
    dsimp only
    rw [show (concatChunks pre).size + 1 =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndNoInactiveVals) ByteArray.empty])).size from by
      rw [show (1 : Nat) = (putU8 (MaskCode.flag .maskAndNoInactiveVals) ByteArray.empty).size from by simp [putU8_size]]
      conv_rhs => rw [concatChunks_snoc_size]]
    rw [peel_last' pre (putU8 (MaskCode.flag .maskAndNoInactiveVals) ByteArray.empty) ((@NodeMask.serialize L sel :: post))]
    rw [parseNat_chunk_serialize sel hsel (pre ++ [putU8 (MaskCode.flag .maskAndNoInactiveVals) ByteArray.empty]) (post)]
    rw [show (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndNoInactiveVals) ByteArray.empty])).size + nodeMaskBytes L =
        (concatChunks ((pre ++ [putU8 (MaskCode.flag .maskAndNoInactiveVals) ByteArray.empty]) ++ [@NodeMask.serialize L sel])).size from by
      conv_rhs => rw [concatChunks_snoc_size]
      rw [@NodeMask.serialize_size L sel hsel]]
    simp [List.append_assoc]
  · -- maskAndOneInactiveVal
    simp only [ValueRecord.WellFormed] at hcls
    obtain ⟨hv0, hv1, hsel⟩ := hcls
    subst hv1
    subst hst
    unfold ValueRecord.parseNoChunk ValueRecord.chunksNoChunk ValueRecord.extras
    rw [show pre ++ (putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty :: (v0 :: (@NodeMask.serialize L sel :: []))) ++ post =
        pre ++ (putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty :: ((v0 :: (@NodeMask.serialize L sel :: [])) ++ post)) from by simp]
    simp only [List.cons_append, List.singleton_append, List.nil_append]
    rw [getU8?_chunk]
    dsimp only
    rw [MaskCode.ofNat?_flag]
    dsimp only
    rw [show (concatChunks pre).size + 1 =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty])).size from by
      rw [show (1 : Nat) = (putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty).size from by simp [putU8_size]]
      conv_rhs => rw [concatChunks_snoc_size]]
    rw [peel_last' pre (putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty) ((v0 :: (@NodeMask.serialize L sel :: post)))]
    rw [getBytes?_chunk_size (pre ++ [putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty]) (v0) ((@NodeMask.serialize L sel :: post)) (h := hv0)]
    dsimp only
    rw [show (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty])).size + vsize =
        (concatChunks ((pre ++ [putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty]) ++ [v0])).size from by
      conv_rhs => rw [concatChunks_snoc_size]
      rw [hv0]]
    rw [peel_cons' (pre ++ [putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty]) (v0) (@NodeMask.serialize L sel) (post)]
    rw [parseNat_chunk_serialize sel hsel ((pre ++ [putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty]) ++ [v0]) (post)]
    rw [show (concatChunks ((pre ++ [putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty]) ++ [v0])).size + nodeMaskBytes L =
        (concatChunks (((pre ++ [putU8 (MaskCode.flag .maskAndOneInactiveVal) ByteArray.empty]) ++ [v0]) ++ [@NodeMask.serialize L sel])).size from by
      conv_rhs => rw [concatChunks_snoc_size]
      rw [@NodeMask.serialize_size L sel hsel]]
    simp [List.append_assoc]
  · -- maskAndTwoInactiveVals
    simp only [ValueRecord.WellFormed] at hcls
    obtain ⟨hv0, hv1, hsel⟩ := hcls
    subst hst
    unfold ValueRecord.parseNoChunk ValueRecord.chunksNoChunk ValueRecord.extras
    rw [show pre ++ (putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty :: (v0 :: (v1 :: (@NodeMask.serialize L sel :: [])))) ++ post =
        pre ++ (putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty :: ((v0 :: (v1 :: (@NodeMask.serialize L sel :: []))) ++ post)) from by simp]
    simp only [List.cons_append, List.singleton_append, List.nil_append]
    rw [getU8?_chunk]
    dsimp only
    rw [MaskCode.ofNat?_flag]
    dsimp only
    rw [show (concatChunks pre).size + 1 =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty])).size from by
      rw [show (1 : Nat) = (putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty).size from by simp [putU8_size]]
      conv_rhs => rw [concatChunks_snoc_size]]
    rw [peel_last' pre (putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty) ((v0 :: (v1 :: (@NodeMask.serialize L sel :: post))))]
    rw [getBytes?_chunk_size (pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty]) (v0) ((v1 :: (@NodeMask.serialize L sel :: post))) (h := hv0)]
    dsimp only
    rw [show (concatChunks (pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty])).size + vsize =
        (concatChunks ((pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty]) ++ [v0])).size from by
      conv_rhs => rw [concatChunks_snoc_size]
      rw [hv0]]
    rw [peel_cons' (pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty]) (v0) (v1) ((@NodeMask.serialize L sel :: post))]
    rw [getBytes?_chunk_size ((pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty]) ++ [v0]) (v1) ((@NodeMask.serialize L sel :: post)) (h := hv1)]
    dsimp only
    rw [show (concatChunks ((pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty]) ++ [v0])).size + vsize =
        (concatChunks (((pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty]) ++ [v0]) ++ [v1])).size from by
      conv_rhs => rw [concatChunks_snoc_size]
      rw [hv1]]
    rw [peel_cons' ((pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty]) ++ [v0]) (v1) (@NodeMask.serialize L sel) (post)]
    rw [parseNat_chunk_serialize sel hsel (((pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty]) ++ [v0]) ++ [v1]) (post)]
    rw [show (concatChunks (((pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty]) ++ [v0]) ++ [v1])).size + nodeMaskBytes L =
        (concatChunks ((((pre ++ [putU8 (MaskCode.flag .maskAndTwoInactiveVals) ByteArray.empty]) ++ [v0]) ++ [v1]) ++ [@NodeMask.serialize L sel])).size from by
      conv_rhs => rw [concatChunks_snoc_size]
      rw [@NodeMask.serialize_size L sel hsel]]
    simp [List.append_assoc]
  · -- noMaskAndAllVals
    simp only [ValueRecord.WellFormed] at hcls
    obtain ⟨hv0, hv1, hsel⟩ := hcls
    subst hv0 hv1 hsel
    subst hst
    unfold ValueRecord.parseNoChunk ValueRecord.chunksNoChunk ValueRecord.extras
    rw [show pre ++ (putU8 (MaskCode.flag .noMaskAndAllVals) ByteArray.empty :: []) ++ post =
        pre ++ (putU8 (MaskCode.flag .noMaskAndAllVals) ByteArray.empty :: ([] ++ post)) from by simp]
    simp only [List.cons_append, List.singleton_append, List.nil_append]
    rw [getU8?_chunk]
    dsimp only
    rw [MaskCode.ofNat?_flag]
    dsimp only
    rw [show (concatChunks pre).size + 1 =
        (concatChunks (pre ++ [putU8 (MaskCode.flag .noMaskAndAllVals) ByteArray.empty])).size from by
      rw [show (1 : Nat) = (putU8 (MaskCode.flag .noMaskAndAllVals) ByteArray.empty).size from by simp [putU8_size]]
      conv_rhs => rw [concatChunks_snoc_size]]


theorem ValueRecord.parseM_emitFrom {L : Nat} (r : ValueRecord L) (vsize expected : Nat)
    (decompress : Bytes → Nat → Option Bytes) (half : Bool)
    (hwf : r.WellFormed vsize expected) (pre post : List Bytes) :
    ValueRecord.parseM vsize expected decompress half
        (concatChunks (pre ++ r.chunksM half ++ post)) (concatChunks pre).size =
      some (r, (concatChunks (pre ++ r.chunksM half)).size) := by
  obtain ⟨hcls, hsize, hbound⟩ := hwf
  by_cases hz : half && r.stored.size = 0
  · have hsize0 : r.stored.size = 0 := by
      have := (Bool.and_eq_true _ _).mp hz
      simpa using this.2
    have hexp : expected = 0 := by rw [← hsize]; exact hsize0
    have hst : r.stored = ByteArray.empty := bytes_eq_empty_of_size_zero _ hsize0
    have hz' : half && expected = 0 := by rw [← hsize]; exact hz
    have h0 : r.WellFormed vsize 0 := ⟨hcls, by simpa [hexp], by simp [hexp]⟩
    simp only [ValueRecord.chunksM, hz, ValueRecord.parseM, hz']
    exact ValueRecord.parseNoChunk_emit r vsize h0 hst pre post
  · have hz' : ¬ (half && expected = 0) := by
      intro h'
      apply hz
      rw [hsize]
      exact h'
    simp only [ValueRecord.chunksM, hz, ValueRecord.parseM, hz']
    exact ValueRecord.parseFrom_emitFrom r vsize expected decompress ⟨hcls, hsize, hbound⟩ pre post


/-! ### Raw (uncompressed) record framing (F14) -/

/-- Raw-framed record chunks (no BLOSC/ZIP): the payload follows the extras
    directly, with no size word. -/
def ValueRecord.chunksRaw {L : Nat} (r : ValueRecord L) : List Bytes :=
  r.chunksNoChunk ++ [r.stored]

/-- The raw-framed record parser: extras, then exactly `expected` payload
    bytes. -/
def ValueRecord.parseRaw {L : Nat} (vsize expected : Nat) (b : Bytes) (off : Nat) :
    Option (ValueRecord L × Nat) :=
  match ValueRecord.parseNoChunk vsize b off with
  | none => none
  | some (r, o1) =>
    (getBytes? b o1 expected).map fun d =>
      (⟨r.code, r.val0, r.val1, r.selection, d⟩, o1 + expected)

theorem ValueRecord.parseRaw_emit {L : Nat} (r : ValueRecord L) (vsize expected : Nat)
    (h : r.WellFormed vsize expected) (pre post : List Bytes) :
    ValueRecord.parseRaw vsize expected
        (concatChunks (pre ++ r.chunksRaw ++ post)) (concatChunks pre).size =
      some (r, (concatChunks (pre ++ r.chunksRaw)).size) := by
  obtain ⟨hcls, hsize, hbound⟩ := h
  let r0 : ValueRecord L := ⟨r.code, r.val0, r.val1, r.selection, ByteArray.empty⟩
  have h0 : r0.WellFormed vsize 0 := ⟨hcls, rfl, by norm_num⟩
  have hch : r.chunksRaw = r0.chunksNoChunk ++ [r.stored] := rfl
  unfold ValueRecord.parseRaw
  rw [show concatChunks (pre ++ r.chunksRaw ++ post) =
      concatChunks (pre ++ r0.chunksNoChunk ++ (r.stored :: post)) from by
    rw [hch]; simp]
  rw [ValueRecord.parseNoChunk_emit r0 vsize h0 rfl pre (r.stored :: post)]
  dsimp only
  rw [show expected = r.stored.size from hsize.symm]
  rw [getBytes?_chunk_size (pre ++ r0.chunksNoChunk) r.stored post (h := rfl)]
  rw [show (concatChunks (pre ++ r.chunksRaw)).size =
      (concatChunks (pre ++ r0.chunksNoChunk)).size + r.stored.size from by
    rw [show pre ++ r.chunksRaw = (pre ++ r0.chunksNoChunk) ++ [r.stored] from by
      rw [hch]; simp]
    rw [concatChunks_snoc_size]]
  rfl

end Vdb
