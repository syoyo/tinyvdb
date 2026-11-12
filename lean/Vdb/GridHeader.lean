/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Grid body prefix (`tvdb__read_grid_inner` before the tree): the per-grid
  compression flags (file version 222 and later), the grid metadata list and
  the grid transform. The tree base and buffers follow; they are not modelled
  here.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Meta
import Vdb.Transform

set_option linter.unusedSimpArgs false

namespace Vdb

/-- The per-grid prefix before the tree: compression flags (file version 222
    and later), the grid metadata list, and the grid transform. -/
structure GridHeader where
  compressionFlags : UInt32
  metadata : MetaList
  transform : Transform
  deriving Repr

def GridHeader.Canonical (h : GridHeader) : Prop :=
  h.metadata.entries.length ≤ 4096 ∧
  (∀ e ∈ h.metadata.entries, e.WellFormed) ∧ h.transform.WellFormed

def GridHeader.chunks (h : GridHeader) : List Bytes :=
  [putU32LE h.compressionFlags ByteArray.empty] ++ h.metadata.chunks ++ h.transform.chunks

def GridHeader.emitFrom (h : GridHeader) (acc : Bytes) : Bytes :=
  acc ++ concatChunks h.chunks

def GridHeader.emit (h : GridHeader) : Bytes := h.emitFrom ByteArray.empty

def GridHeader.parseFrom (b : Bytes) (off : Nat) : Option (GridHeader × Nat) :=
  match getU32LE b off with
  | none => none
  | some fl =>
    match MetaList.parseFrom b (off + 4) with
    | none => none
    | some (md, o1) =>
      match Transform.parseFrom b o1 with
      | none => none
      | some (tr, o2) => some (⟨fl, md, tr⟩, o2)

theorem GridHeader.parseFrom_emitFrom (h : GridHeader) (hc : h.Canonical)
    (acc : Bytes) :
    ∃ out, GridHeader.parseFrom (h.emitFrom acc) acc.size = some (h, out) := by
  obtain ⟨hcnt, hwf, htr⟩ := hc
  rcases h with ⟨fl, md, tr⟩
  unfold GridHeader.parseFrom GridHeader.emitFrom GridHeader.chunks
  dsimp only
  rw [acc_append_concatChunks]
  rw [show concatChunks (acc :: ([putU32LE fl ByteArray.empty] ++ md.chunks ++ tr.chunks)) =
      concatChunks ([acc] ++ putU32LE fl ByteArray.empty :: (md.chunks ++ tr.chunks)) from by simp]
  rw [show acc.size = (concatChunks [acc]).size from by simp [concatChunks]]
  rw [getU32LE_chunk]
  dsimp only
  rw [show (concatChunks [acc]).size + 4 =
      (concatChunks [acc, putU32LE fl ByteArray.empty]).size from by
    conv_rhs => rw [concatChunks_size]
    simp [concatChunks_size, putU32LE_size]]
  rw [show concatChunks ([acc] ++ putU32LE fl ByteArray.empty :: (md.chunks ++ tr.chunks)) =
      concatChunks ([acc, putU32LE fl ByteArray.empty] ++ md.chunks ++ tr.chunks) from by simp]
  rw [MetaList.parseFromChunks md hcnt hwf [acc, putU32LE fl ByteArray.empty] tr.chunks]
  dsimp only
  rw [show concatChunks (([acc, putU32LE fl ByteArray.empty] ++ md.chunks) ++ tr.chunks) =
      concatChunks ([acc, putU32LE fl ByteArray.empty] ++ md.chunks) ++
        concatChunks tr.chunks from by
    rw [concatChunks_append]]
  obtain ⟨tout, htout⟩ := Transform.parseFrom_emitFrom tr htr
    (concatChunks ([acc, putU32LE fl ByteArray.empty] ++ md.chunks))
  rw [show concatChunks ([acc, putU32LE fl ByteArray.empty] ++ md.chunks) ++
      concatChunks tr.chunks =
      tr.emitFrom (concatChunks ([acc, putU32LE fl ByteArray.empty] ++ md.chunks)) from rfl]
  rw [htout]
  exact ⟨tout, rfl⟩


theorem GridHeader.parseFromChunks (h : GridHeader) (hc : h.Canonical)
    (pre rest : List Bytes) :
    ∃ out, GridHeader.parseFrom (concatChunks (pre ++ h.chunks ++ rest))
      (concatChunks pre).size = some (h, out) := by
  obtain ⟨hcnt, hwf, htr⟩ := hc
  rcases h with ⟨fl, md, tr⟩
  unfold GridHeader.parseFrom GridHeader.chunks
  dsimp only
  rw [show concatChunks (pre ++ ([putU32LE fl ByteArray.empty] ++ md.chunks ++ tr.chunks) ++ rest) =
      concatChunks (pre ++ putU32LE fl ByteArray.empty ::
        (md.chunks ++ (tr.chunks ++ rest))) from by simp]
  rw [getU32LE_chunk]
  dsimp only
  rw [show (concatChunks pre).size + 4 =
      (concatChunks (pre ++ [putU32LE fl ByteArray.empty])).size from by
    conv_lhs => rw [concatChunks_size]
    conv_rhs => rw [concatChunks_size]
    simp [putU32LE_size]]
  rw [show concatChunks (pre ++ putU32LE fl ByteArray.empty ::
      (md.chunks ++ (tr.chunks ++ rest))) =
      concatChunks (((pre ++ [putU32LE fl ByteArray.empty]) ++ md.chunks) ++
        (tr.chunks ++ rest)) from by simp]
  rw [MetaList.parseFromChunks md hcnt hwf (pre ++ [putU32LE fl ByteArray.empty])
    (tr.chunks ++ rest)]
  dsimp only
  rw [show concatChunks (((pre ++ [putU32LE fl ByteArray.empty]) ++ md.chunks) ++
      (tr.chunks ++ rest)) =
      tr.emitFrom (concatChunks ((pre ++ [putU32LE fl ByteArray.empty]) ++ md.chunks))
        ++ concatChunks rest from by
    simp only [Transform.emitFrom]
    rw [show concatChunks (pre ++ [putU32LE fl ByteArray.empty] ++ md.chunks ++
        (tr.chunks ++ rest)) =
        concatChunks (pre ++ [putU32LE fl ByteArray.empty] ++ md.chunks) ++
          concatChunks (tr.chunks ++ rest) from concatChunks_append _ _]
    rw [show concatChunks (tr.chunks ++ rest) =
        concatChunks tr.chunks ++ concatChunks rest from concatChunks_append _ _]
    conv_rhs => rw [ByteArray.append_assoc]]
  obtain ⟨tout, htout⟩ := Transform.parseFrom_emitFrom_rest tr htr
    (concatChunks ((pre ++ [putU32LE fl ByteArray.empty]) ++ md.chunks)) rest
  rw [htout]
  exact ⟨tout, rfl⟩

end Vdb
