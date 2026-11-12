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

end Vdb
