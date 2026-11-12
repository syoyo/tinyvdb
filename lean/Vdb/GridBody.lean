/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  A grid body in the file: the grid header (flags, metadata, transform), the
  tree-base buffer count (`i32`) and the tree data. The tree data (node
  topology and buffers) is carried as opaque bytes delimited by the
  descriptor's end offset; its internal structure is a later layer.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.GridHeader

set_option linter.unusedSimpArgs false

namespace Vdb

structure GridBody where
  header : GridHeader
  bufferCount : Int32
  tree : Bytes
  deriving Repr

def GridBody.Canonical (g : GridBody) : Prop :=
  g.header.Canonical

def GridBody.chunks (g : GridBody) : List Bytes :=
  g.header.chunks ++ [putI32LE g.bufferCount ByteArray.empty, g.tree]

def GridBody.emitFrom (g : GridBody) (acc : Bytes) : Bytes :=
  acc ++ concatChunks g.chunks

def GridBody.emit (g : GridBody) : Bytes := g.emitFrom ByteArray.empty

/-- Parse a grid body in `[off, endOff)`: header, tree-base count, then the
    tree bytes up to `endOff`. -/
def GridBody.parseFrom (b : Bytes) (off endOff : Nat) : Option (GridBody × Nat) :=
  match GridHeader.parseFrom b off with
  | none => none
  | some (h, o1) =>
    match getI32LE b o1 with
    | none => none
    | some bc =>
      match getBytes? b (o1 + 4) (endOff - (o1 + 4)) with
      | none => none
      | some t => some (⟨h, bc, t⟩, o1 + 4 + (endOff - (o1 + 4)))

theorem GridBody.parseFrom_emitFrom (g : GridBody) (hg : g.Canonical) (acc : Bytes) :
    GridBody.parseFrom (g.emitFrom acc) acc.size (concatChunks (acc :: g.chunks)).size =
      some (g, (concatChunks (acc :: g.chunks)).size) := by
  rcases g with ⟨h, bc, tree⟩
  simp only [GridBody.Canonical] at hg
  unfold GridBody.parseFrom GridBody.emitFrom GridBody.chunks
  dsimp only
  rw [acc_append_concatChunks]
  rw [show concatChunks (acc :: (h.chunks ++ [putI32LE bc ByteArray.empty, tree])) =
      concatChunks ([acc] ++ h.chunks ++ (putI32LE bc ByteArray.empty :: (tree :: []))) from by simp]
  rw [show acc.size = (concatChunks [acc]).size from by simp [concatChunks]]
  rw [GridHeader.parseFromChunks_exact h hg [acc]
    (putI32LE bc ByteArray.empty :: (tree :: []))]
  dsimp only
  rw [show concatChunks ([acc] ++ h.chunks ++ (putI32LE bc ByteArray.empty :: (tree :: []))) =
      concatChunks (([acc] ++ h.chunks) ++ (putI32LE bc ByteArray.empty :: (tree :: []))) from by simp]
  rw [getI32LE_chunk]
  dsimp only
  rw [show (concatChunks ([acc] ++ h.chunks)).size + 4 =
      (concatChunks (([acc] ++ h.chunks) ++ [putI32LE bc ByteArray.empty])).size from by
    conv_lhs => rw [concatChunks_size]
    conv_rhs => rw [concatChunks_size]
    simp [putI32LE_size]
    omega]
  rw [show concatChunks (([acc] ++ h.chunks) ++ (putI32LE bc ByteArray.empty :: (tree :: []))) =
      concatChunks ((([acc] ++ h.chunks) ++ [putI32LE bc ByteArray.empty]) ++ (tree :: [])) from by simp]
  rw [show (concatChunks ([acc] ++ h.chunks ++ [putI32LE bc ByteArray.empty] ++ [tree])).size -
      (concatChunks ([acc] ++ h.chunks ++ [putI32LE bc ByteArray.empty])).size = tree.size from by
    rw [show [acc] ++ h.chunks ++ [putI32LE bc ByteArray.empty] ++ [tree] =
        ([acc] ++ h.chunks ++ [putI32LE bc ByteArray.empty]) ++ [tree] from by simp]
    rw [concatChunks_snoc_size]
    simp]
  rw [getBytes?_chunk]
  dsimp only
  rw [show (concatChunks ([acc] ++ h.chunks ++ [putI32LE bc ByteArray.empty])).size + tree.size =
      (concatChunks ([acc] ++ h.chunks ++ [putI32LE bc ByteArray.empty] ++ [tree])).size from by
    have ha : (concatChunks ([acc] ++ h.chunks ++ [putI32LE bc ByteArray.empty] ++ [tree])).size =
        (concatChunks ([acc] ++ h.chunks ++ [putI32LE bc ByteArray.empty])).size + tree.size := by
      rw [show [acc] ++ h.chunks ++ [putI32LE bc ByteArray.empty] ++ [tree] =
          ([acc] ++ h.chunks ++ [putI32LE bc ByteArray.empty]) ++ [tree] from by simp]
      rw [concatChunks_snoc_size]
    rw [ha]]


theorem GridBody.parseFromChunks (g : GridBody) (hg : g.Canonical)
    (pre next : List Bytes) :
    GridBody.parseFrom (concatChunks (pre ++ g.chunks ++ next)) (concatChunks pre).size
      (concatChunks (pre ++ g.chunks)).size =
        some (g, (concatChunks (pre ++ g.chunks)).size) := by
  rcases g with ⟨h, bc, tree⟩
  simp only [GridBody.Canonical] at hg
  unfold GridBody.parseFrom GridBody.chunks
  dsimp only
  rw [show concatChunks (pre ++ (h.chunks ++ [putI32LE bc ByteArray.empty, tree]) ++ next) =
      concatChunks (pre ++ h.chunks ++
        (putI32LE bc ByteArray.empty :: (tree :: next))) from by simp]
  rw [GridHeader.parseFromChunks_exact h hg pre
    (putI32LE bc ByteArray.empty :: (tree :: next))]
  dsimp only
  rw [getI32LE_chunk]
  dsimp only
  rw [show (concatChunks (pre ++ h.chunks)).size + 4 =
      (concatChunks ((pre ++ h.chunks) ++ [putI32LE bc ByteArray.empty])).size from by
    conv_rhs => rw [concatChunks_snoc_size]
    simp [putI32LE_size]]
  rw [show concatChunks (pre ++ h.chunks ++
      (putI32LE bc ByteArray.empty :: (tree :: next))) =
      concatChunks (((pre ++ h.chunks) ++ [putI32LE bc ByteArray.empty]) ++ (tree :: next)) from by simp]
  rw [show (concatChunks (pre ++ (h.chunks ++ [putI32LE bc ByteArray.empty, tree]))).size -
      (concatChunks ((pre ++ h.chunks) ++ [putI32LE bc ByteArray.empty])).size = tree.size from by
    rw [show pre ++ (h.chunks ++ [putI32LE bc ByteArray.empty, tree]) =
        ((pre ++ h.chunks) ++ [putI32LE bc ByteArray.empty]) ++ [tree] from by simp]
    rw [concatChunks_snoc_size]
    simp]
  rw [getBytes?_chunk]
  dsimp only
  rw [show (concatChunks ((pre ++ h.chunks) ++ [putI32LE bc ByteArray.empty])).size + tree.size =
      (concatChunks (pre ++ (h.chunks ++ [putI32LE bc ByteArray.empty, tree]))).size from by
    conv_lhs => rw [concatChunks_size]
    conv_rhs => rw [concatChunks_size]
    simp [List.map_append, List.sum_append, putI32LE_size]
    omega]

end Vdb
