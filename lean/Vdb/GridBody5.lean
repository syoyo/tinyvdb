/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  A grid body whose tree is fully structured: the grid header (compression
  flags, metadata, transform) followed by the tree topology (`TreeData5`)
  and its buffer pass (`Vdb/TreeBuffer.lean`). This replaces the opaque
  `GridBody.tree : Bytes` model for the standard `Tree_float_5_4_3` layout.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.GridHeader
import Vdb.TreeBuffer

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Vdb

/-- A grid body with its tree fully modelled: the grid header (flags,
    metadata, transform), the tree data (topology) and the buffer pass. -/
structure GridBody5 where
  header : GridHeader
  tree : TreeData5
  buffers : List (List LeafBuffer)

def GridBody5.Canonical (vsize expected : Nat) (g : GridBody5) : Prop :=
  g.header.Canonical ∧ g.tree.WellFormed vsize expected ∧
  BufMatch g.tree.root.children g.buffers ∧
  (∀ bs ∈ g.buffers, ∀ b ∈ bs, b.WellFormed vsize expected)

def GridBody5.chunks (g : GridBody5) : List Bytes :=
  g.header.chunks ++ g.tree.fullChunks g.buffers

def GridBody5.parseFrom (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (b : Bytes) (off : Nat) : Option (GridBody5 × Nat) :=
  match GridHeader.parseFrom b off with
  | none => none
  | some (h, o1) =>
    match TreeData5.parseFull vsize expected decompress b o1 with
    | none => none
    | some (t, bss, o2) => some (⟨h, t, bss⟩, o2)

theorem GridBody5.parseFrom_emit (g : GridBody5) (vsize expected : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (hc : g.Canonical vsize expected) (pre post : List Bytes) :
    GridBody5.parseFrom vsize expected decompress
        (concatChunks (pre ++ g.chunks ++ post)) (concatChunks pre).size =
      some (g, (concatChunks (pre ++ g.chunks)).size) := by
  obtain ⟨hh, ht, hm, hwf⟩ := hc
  rcases g with ⟨h, t, bss⟩
  unfold GridBody5.parseFrom GridBody5.chunks
  rw [show pre ++ (h.chunks ++ t.fullChunks bss) ++ post =
      pre ++ h.chunks ++ (t.fullChunks bss ++ post) from by simp]
  rw [GridHeader.parseFromChunks_exact h hh pre (t.fullChunks bss ++ post)]
  dsimp only
  rw [show concatChunks (pre ++ h.chunks ++ (t.fullChunks bss ++ post)) =
      concatChunks ((pre ++ h.chunks) ++ t.fullChunks bss ++ post) from by simp]
  rw [TreeData5.parseFull_emit t bss vsize expected decompress ht hm hwf (pre ++ h.chunks) post]
  simp [GridBody5.chunks, List.append_assoc]

end Vdb
