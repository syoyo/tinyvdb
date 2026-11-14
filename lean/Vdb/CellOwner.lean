/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Tree MC ownership (`T-OWN-PART`, plan §4.2): the sparse region walk visits a
  crossing cell up to eight times — once from each of its voxels on the
  walked side of the isovalue — but only its **owner** commits the
  classification. The owner is the *lowest-numbered corner on the walked
  side* (`tool_corners` order), which the C code computes as
  `tool_ctz32(side)` (`src/tinyvdb_sparse_tools.c`, `tool_cell_values`). The
  claims modelled here:

  * **`ownerOf`** — the owner of a crossing cell on the walked side `S`:
    the least corner of `S`, if any. **`owner_mem`/`owner_least`**: it is in
    `S` and below every other walked-side corner.
  * **`unique_owner`** — among all visits of a crossing cell exactly one
    passes the ownership test: the `Finset.filter (· = owner)` of the
    walked-side corners has cardinality 1. So the cell is classified at most
    once, and the `tool_insert` first-classification-survives map keeps it.
  * **`tool_corner_of_bit`** — the C array `{0, 1, 3, 2, 4, 5, 7, 6}`
    permuting the walk's corner-bit order to the `tool_corners` corner order;
    it is a bijection (`tool_corner_of_bit_bij`), so the reordering cannot
    duplicate or drop a corner.
  * **Orientation under the grid transform**: `triple_apply` (reused from
    `Vdb/WindingNumber.lean`) gives `triple (M x) (M y) (M z) = det M ·
    triple x y z`, so the signed volume of an `M`-imaged triangle flips sign
    exactly when `det M < 0`. An affine map with `det M > 0` preserves the
    outward orientation of the MC/DMC triangles; `det M < 0` reverses it
    (`triangle_det_flip`). This is the orientation half of `T-OWN-PART`.

  What is *not* modelled: the actual region-growing (`tool_walk_*`) — the
  fact that every walked-side corner's voxel is *visited* is the region
  walk's invariant, taken here as the semantics of the visit set (`S` is
  exactly the set of visited corners of the cell); the slab-partitioned
  edge hash (`tool_mesh`) and the `tool_insert` map dedup are
  order-insensitive, so the classification is order-independent given the
  owner rule.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.WindingNumber
import Mathlib.Tactic

namespace Vdb

/-! ### The owner rule -/

/-- The owner of a crossing cell on the walked side `S` (a subset of the
    8 corners, `tool_corners` numbering): the least corner of `S`. -/
noncomputable def ownerOf (S : Finset (Fin 8)) : Option (Fin 8) :=
  if h : S.Nonempty then some (S.min' h) else none

/-- The owner is exactly the least walked-side corner. -/
theorem ownerOf_eq_min' (S : Finset (Fin 8)) (h : S.Nonempty) :
    ownerOf S = some (S.min' h) := by
  simp [ownerOf, h]

/-- The `Option.get` of the owner is the least walked-side corner. -/
theorem ownerOf_get (S : Finset (Fin 8)) (h : S.Nonempty) :
    (ownerOf S).get (by simp [ownerOf, h]) = S.min' h := by
  simp [ownerOf, h]

/-- The owner lies on the walked side. -/
theorem owner_mem (S : Finset (Fin 8)) (h : S.Nonempty) :
    (ownerOf S).get (by simp [ownerOf, h]) ∈ S := by
  rw [ownerOf_get S h]
  exact Finset.min'_mem S h

/-- **The owner is the least walked-side corner.** -/
theorem owner_least (S : Finset (Fin 8)) (h : S.Nonempty) :
    ∀ c ∈ S, (ownerOf S).get (by simp [ownerOf, h]) ≤ c := by
  rw [ownerOf_get S h]
  intro c hc
  exact Finset.min'_le S c hc

/-- **Exactly one visit passes the ownership test.** Among the walked-side
    corners of a crossing cell (the corners the region walk visits), the
    filter of ownership-test survivors has cardinality 1 — the cell is
    classified at most once. -/
theorem unique_owner (S : Finset (Fin 8)) (h : S.Nonempty) :
    (S.filter (fun c => decide (c = S.min' h))).card = 1 := by
  have h1 : S.filter (fun c => decide (c = S.min' h)) = {S.min' h} := by
    ext x
    simp only [Finset.mem_filter, decide_eq_true_eq, Finset.mem_singleton]
    constructor
    · rintro ⟨hxS, rfl⟩; rfl
    · intro hx
      rw [hx]
      exact ⟨Finset.min'_mem S h, rfl⟩
  rw [h1]
  exact Finset.card_singleton _

/-- **Every crossing cell has an owner**: the walked side is nonempty —
    a crossing cell has corners on both sides of the isovalue, and the
    walked side is one of them. -/
theorem owner_of_crosses (S : Finset (Fin 8)) (h : S.Nonempty) :
    (ownerOf S).isSome := by
  simp [ownerOf, h]

/-! ### The C corner permutation -/

/-- The C array `tool_corner_of_bit`: corner-bit index → `tool_corners`
    corner index (`{0, 1, 3, 2, 4, 5, 7, 6}`, swaps the 2↔3 and 6↔7 pairs). -/
def toolCornerOfBit : Fin 8 → Fin 8 :=
  ![0, 1, 3, 2, 4, 5, 7, 6]

/-- **The permutation is a bijection**: no corner is dropped or duplicated,
    so the ownership test sees every walked-side corner exactly once. -/
theorem tool_corner_of_bit_bij : Function.Bijective toolCornerOfBit := by
  decide

/-- The permutation swaps exactly the 2↔3 and 6↔7 pairs. -/
theorem tool_corner_of_bit_eq :
    toolCornerOfBit = ![0, 1, 3, 2, 4, 5, 7, 6] := rfl

/-! ### Affine maps and orientation -/

/-- **Triangle orientation under an affine map**: the signed volume of the
    `M`-image of a triangle scales by `det M`. An orientation-preserving
    affine map (`det M > 0`) keeps the winding the table was built with;
    `det M < 0` reverses it. (This is the orientation content of
    `tool_transform` in `tool_mesh`: the grid transform has `det M > 0` for
    any physically grid, so the MC/DMC triangles stay outward.) -/
theorem triangle_det_flip {M : Matrix (Fin 3) (Fin 3) ℝ} (x y z : V3) :
    V3.triple (V3.applyMat M x) (V3.applyMat M y) (V3.applyMat M z) = M.det * V3.triple x y z :=
  V3.triple_apply M x y z

/-- If `det M < 0`, the signed volume strictly flips sign. -/
theorem triangle_det_neg {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.det < 0) {x y z : V3}
    (h : V3.triple x y z ≠ 0) :
    V3.triple (V3.applyMat M x) (V3.applyMat M y) (V3.applyMat M z) ≠ 0 ∧
      (V3.triple (V3.applyMat M x) (V3.applyMat M y) (V3.applyMat M z) < 0 ↔
        0 < V3.triple x y z) := by
  rw [triangle_det_flip]
  constructor
  · exact mul_ne_zero (ne_of_lt hM) h
  · constructor
    · intro hlt
      have : M.det * V3.triple x y z < 0 := hlt
      rcases lt_or_ge 0 (V3.triple x y z) with h1 | h1
      · exact h1
      · rcases eq_or_lt_of_le h1 with h2 | h2
        · exact (h h2).elim
        · exact False.elim (by nlinarith [this, hM])
    · intro h1
      have : M.det * V3.triple x y z < 0 := mul_neg_of_neg_of_pos hM h1
      exact this

end Vdb
