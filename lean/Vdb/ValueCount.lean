/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  The per-node stored-value count. `tvdb__read_mask_values` computes the
  number of values the chunk holds from the grid's active-mask compression
  flag, the file version and (for mask compression) the node's value mask:

  * every slot, for the "all values" code, non-mask-compressed grids and
    pre-222 files (whose values are not compacted at internal level);
  * the active count of the value mask otherwise.

  `storedCount` models that rule, and `ValueRecord.parseFromCount` derives the
  value-chunk size from it, so a record can be parsed without an externally
  supplied `expected`.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.NodeRecord

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Vdb

/-- Number of values stored in a node's compressed record, i.e. the C
    reader's `read_count`: every slot for the "all values" code (or when the
    grid does not use active-mask compression, or for pre-222 files), and the
    active count of the value mask otherwise. -/
def storedCount {L : Nat} (maskCompressed : Bool) (ver : Nat)
    (m : NodeMask L) (code : MaskCode) : Nat :=
  if maskCompressed && 222 ≤ ver && code ≠ .noMaskAndAllVals then
    (setBits m (nodeSlots L)).length
  else nodeSlots L

theorem setBits_length_le (m : Nat) (n : Nat) : (setBits m n).length ≤ n := by
  unfold setBits
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.filter_append]
    simp only [List.length_append]
    have h : (List.filter (fun i => m.testBit i) [k]).length ≤ 1 := by
      by_cases hk : m.testBit k <;> simp [hk]
    omega

theorem storedCount_le {L : Nat} (maskCompressed : Bool) (ver : Nat)
    (m : NodeMask L) (code : MaskCode) : storedCount maskCompressed ver m code ≤ nodeSlots L := by
  unfold storedCount
  split
  · exact setBits_length_le m (nodeSlots L)
  · exact le_rfl

/-- The record parser when the stored-value count is derived from the code
    (the C reader's `read_count` rule) instead of being supplied. -/
def ValueRecord.parseFromCount {L : Nat} (vsize elemSize : Nat) (countOf : MaskCode → Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) :
    Option (ValueRecord L × Nat) :=
  match getU8? b off with
  | none => none
  | some fl =>
    match MaskCode.ofNat? fl.toNat with
    | none => none
    | some code => ValueRecord.parseFrom vsize (countOf code * elemSize) decompress b off

theorem ValueRecord.parseFromCount_emit {L : Nat} (r : ValueRecord L)
    (vsize elemSize : Nat) (countOf : MaskCode → Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : r.WellFormed vsize (countOf r.code * elemSize))
    (pre post : List Bytes) :
    ValueRecord.parseFromCount vsize elemSize countOf decompress
        (concatChunks (pre ++ r.chunks ++ post)) (concatChunks pre).size =
      some (r, (concatChunks (pre ++ r.chunks)).size) := by
  unfold ValueRecord.parseFromCount ValueRecord.chunks
  rw [show pre ++ (putU8 r.code.flag ByteArray.empty :: r.tailChunks) ++ post =
      pre ++ (putU8 r.code.flag ByteArray.empty :: (r.tailChunks ++ post)) from by simp]
  rw [getU8?_chunk]
  dsimp only
  rw [MaskCode.ofNat?_flag]
  dsimp only
  rw [show concatChunks (pre ++ putU8 r.code.flag ByteArray.empty :: (r.tailChunks ++ post)) =
      concatChunks (pre ++ r.chunks ++ post) from by simp [ValueRecord.chunks]]
  exact ValueRecord.parseFrom_emitFrom r vsize (countOf r.code * elemSize) decompress h pre post



/-- The half/full-aware count-derived record parser. `half` selects the
    half-grid chunk omission (F6). -/
def ValueRecord.parseFromCountM {L : Nat} (vsize elemSize : Nat)
    (countOf : MaskCode → Nat) (decompress : Bytes → Nat → Option Bytes)
    (b : Bytes) (off : Nat) (half : Bool := false) : Option (ValueRecord L × Nat) :=
  match getU8? b off with
  | none => none
  | some fl =>
    match MaskCode.ofNat? fl.toNat with
    | none => none
    | some code =>
      ValueRecord.parseM vsize (countOf code * elemSize) decompress half b off

/-- Both branches of `chunksM` start with the code byte. -/
theorem ValueRecord.getU8?_chunksM {L : Nat} (r : ValueRecord L) (half : Bool)
    (pre post : List Bytes) :
    getU8? (concatChunks (pre ++ r.chunksM half ++ post)) (concatChunks pre).size =
      some r.code.flag := by
  unfold ValueRecord.chunksM
  split
  · unfold ValueRecord.chunksNoChunk
    rw [show pre ++ (putU8 r.code.flag ByteArray.empty :: r.extras) ++ post =
        pre ++ (putU8 r.code.flag ByteArray.empty :: (r.extras ++ post)) from by simp]
    exact getU8?_chunk pre _ (r.extras ++ post)
  · unfold ValueRecord.chunks
    rw [show pre ++ (putU8 r.code.flag ByteArray.empty :: r.tailChunks) ++ post =
        pre ++ (putU8 r.code.flag ByteArray.empty :: (r.tailChunks ++ post)) from by simp]
    exact getU8?_chunk pre _ (r.tailChunks ++ post)

theorem ValueRecord.parseFromCountM_emit {L : Nat} (r : ValueRecord L)
    (vsize elemSize : Nat) (countOf : MaskCode → Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : r.WellFormed vsize (countOf r.code * elemSize))
    (pre post : List Bytes) (half : Bool := false) :
    ValueRecord.parseFromCountM vsize elemSize countOf decompress
        (concatChunks (pre ++ r.chunksM half ++ post)) (concatChunks pre).size (half := half) =
      some (r, (concatChunks (pre ++ r.chunksM half)).size) := by
  unfold ValueRecord.parseFromCountM
  rw [ValueRecord.getU8?_chunksM]
  dsimp only
  rw [MaskCode.ofNat?_flag]
  dsimp only
  exact ValueRecord.parseM_emitFrom r vsize (countOf r.code * elemSize) decompress half h pre post


/-! ### Framing dispatch (BLOSC/ZIP vs raw) -/

/-- Mode-aware record emit: BLOSC/ZIP framing (with the half/zero chunk rule)
    or raw framing (payload directly, no size word). -/
def ValueRecord.chunksF {L : Nat} (framed : Bool) (half : Bool) (r : ValueRecord L) : List Bytes :=
  if framed then r.chunksM half else r.chunksRaw

def ValueRecord.parseF {L : Nat} (framed : Bool) (vsize expected : Nat)
    (decompress : Bytes → Nat → Option Bytes) (half : Bool) (b : Bytes) (off : Nat) :
    Option (ValueRecord L × Nat) :=
  if framed then ValueRecord.parseM vsize expected decompress half b off
  else ValueRecord.parseRaw vsize expected b off

theorem ValueRecord.getU8?_chunksF {L : Nat} (r : ValueRecord L) (framed half : Bool)
    (pre post : List Bytes) :
    getU8? (concatChunks (pre ++ r.chunksF framed half ++ post)) (concatChunks pre).size =
      some r.code.flag := by
  unfold ValueRecord.chunksF
  split
  · exact ValueRecord.getU8?_chunksM r half pre post
  · unfold ValueRecord.chunksRaw
    rw [show pre ++ (r.chunksNoChunk ++ [r.stored]) ++ post =
        pre ++ r.chunksNoChunk ++ (r.stored :: post) from by simp]
    unfold ValueRecord.chunksNoChunk
    rw [show pre ++ (putU8 r.code.flag ByteArray.empty :: r.extras) ++ (r.stored :: post) =
        pre ++ (putU8 r.code.flag ByteArray.empty :: (r.extras ++ (r.stored :: post))) from by simp]
    exact getU8?_chunk pre _ _

def ValueRecord.parseFromCountF {L : Nat} (framed : Bool := true)
    (vsize elemSize : Nat) (countOf : MaskCode → Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) (half : Bool := false) :
    Option (ValueRecord L × Nat) :=
  match getU8? b off with
  | none => none
  | some fl =>
    match MaskCode.ofNat? fl.toNat with
    | none => none
    | some code =>
      ValueRecord.parseF framed vsize (countOf code * elemSize) decompress half b off

theorem ValueRecord.parseFromCountF_emit {L : Nat} (r : ValueRecord L)
    (vsize elemSize : Nat) (countOf : MaskCode → Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : r.WellFormed vsize (countOf r.code * elemSize))
    (pre post : List Bytes) (framed : Bool := true) (half : Bool := false) :
    ValueRecord.parseFromCountF framed vsize elemSize countOf decompress
        (concatChunks (pre ++ r.chunksF framed half ++ post)) (concatChunks pre).size
        (half := half) =
      some (r, (concatChunks (pre ++ r.chunksF framed half)).size) := by
  unfold ValueRecord.parseFromCountF
  rw [ValueRecord.getU8?_chunksF]
  dsimp only
  rw [MaskCode.ofNat?_flag]
  dsimp only
  by_cases hf : framed = true
  · simp only [ValueRecord.parseF, ValueRecord.chunksF, hf, ite_true]
    exact ValueRecord.parseM_emitFrom r vsize (countOf r.code * elemSize) decompress half h pre post
  · have hf' : framed = false := by
      cases framed <;> simp_all
    simp only [ValueRecord.parseF, ValueRecord.chunksF, hf', ite_false]
    exact ValueRecord.parseRaw_emit r vsize (countOf r.code * elemSize) h pre post

end Vdb
