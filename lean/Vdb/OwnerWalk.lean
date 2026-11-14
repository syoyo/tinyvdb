/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Tree MC visitation invariant (`T-OWN-PART`, owner side): the C accept test
  of `tool_voxel_cells`/`tool_cell_values` —

      const unsigned side = (bg_below ? ~cube : cube) & 0xffu;
      if (tool_corner_of_bit[i] != tool_ctz32(side)) continue;   /* skip */

  — admits exactly one of the eight positions `i` of a crossing cell. Once the
  region-growing walk has surfaced the walked side of a crossing cell (every
  walked-side corner is one of the stored iso-straddling samples the collect
  phase enumerates), the cell is classified **exactly once** — by the least
  walked-side corner in the `tool_corners` numbering (via the
  `tool_corner_of_bit` permutation `{0, 1, 3, 2, 4, 5, 7, 6}`).

  * `ctz32 side hne` — the C `tool_ctz32` (index of the least set bit) over
    the 8-bit walked-side mask, with the nonempty-side obligation `hne`.
  * `accept side hne i` — the C accept test, `tool_corner_of_bit i = ctz32 (side) hne`.
  * **`accept_subsingleton`** — at most one position passes the accept test.
  * **`accept_count_one`** — for a nonempty walked side, exactly one position
    passes; the cell is classified at most once, and under the collect walk's
    coverage contract (`hcover`), exactly once.

  What is *not* modelled: the collect walk itself (`tool_regions_*`, BFS/tile
  enumeration) and its coverage of stored leaves; `hcover` in
  `visit_implies_classify` takes that contract as a hypothesis.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.CellOwner
import Mathlib.Tactic

namespace Vdb

/-- The C `ctz32` (index of the least set bit) over the 8-bit walked-side
    mask, with the obligation that the mask is nonzero. -/
def ctz32 (side : Fin 8 → Bool) (hne : ∃ i, side i = true) : Fin 8 :=
  Finset.min' ((Finset.univ : Finset (Fin 8)).filter fun i => side i = true)
    (by
      obtain ⟨i, hi⟩ := hne
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)

/-- The C cube-bit mask of a visited corner set (bit `i` = corner `i`). -/
def sideMask (s : Finset (Fin 8)) : Fin 8 → Bool := fun i => decide (i ∈ s)

/-- Reading the mask is the same as membership. -/
theorem sideMask_spec (s : Finset (Fin 8)) (i : Fin 8) : sideMask s i = true ↔ i ∈ s := by
  simp [sideMask]

/-- The mask of a nonempty corner set has a least corner. -/
theorem sideMask_nonempty (s : Finset (Fin 8)) (h : s.Nonempty) :
    ∃ i, sideMask s i = true := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, (sideMask_spec s i).mpr hi⟩

/-- `Finset.min'` does not depend on the `Nonempty` proof. -/
theorem min'_eq_of_nonempty_proof {α : Type*} [LinearOrder α] (s : Finset α) (h₁ h₂ : s.Nonempty) :
    s.min' h₁ = s.min' h₂ :=
  le_antisymm (s.min'_le _ (s.min'_mem h₂)) (s.min'_le _ (s.min'_mem h₁))

/-- `ctz32` of the mask of a set is the set's least corner. -/
theorem ctz32_sideMask (s : Finset (Fin 8)) (h : s.Nonempty) :
    ctz32 (sideMask s) (sideMask_nonempty s h) = s.min' h := by
  unfold ctz32
  have hFne : ((Finset.univ : Finset (Fin 8)).filter (fun i => sideMask s i = true)).Nonempty := by
    obtain ⟨i, hi⟩ := h
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, (sideMask_spec s i).mpr hi⟩⟩
  have hcut : ∀ i, i ∈ ((Finset.univ : Finset (Fin 8)).filter (fun i => sideMask s i = true)) ↔ i ∈ s := by
    intro i
    simp [sideMask_spec]
  apply le_antisymm
  · have hmem : s.min' h ∈ (Finset.univ : Finset (Fin 8)).filter (fun i => sideMask s i = true) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact (sideMask_spec s _).mpr (Finset.min'_mem s h)
    exact Finset.min'_le _ _ hmem
  · have hF : ((Finset.univ : Finset (Fin 8)).filter (fun i => sideMask s i = true)).Nonempty := by
      obtain ⟨i, hi⟩ := h
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, (sideMask_spec s i).mpr hi⟩⟩
    have hcut : ∀ i, i ∈ ((Finset.univ : Finset (Fin 8)).filter (fun i => sideMask s i = true)) ↔ i ∈ s := by
      intro i
      simp [sideMask_spec]
    exact s.min'_le _ ((hcut _).mp (Finset.min'_mem _ hF))

/-- The accept test of the C: `tool_corner_of_bit[i] == ctz32(side)`. -/
def accept (side : Fin 8 → Bool) (hne : ∃ i, side i = true) (i : Fin 8) : Prop :=
  toolCornerOfBit i = ctz32 side hne

instance (side : Fin 8 → Bool) (hne : ∃ i, side i = true) (i : Fin 8) :
    Decidable (accept side hne i) :=
  inferInstanceAs (Decidable (toolCornerOfBit i = ctz32 side hne))

/-- **At most one position passes the accept test.** The answer is a genuine
    function of the walked side, so any two accepted positions are equal. -/
theorem accept_subsingleton (side : Fin 8 → Bool) (hne : ∃ i, side i = true) (i j : Fin 8)
    (hi : accept side hne i) (hj : accept side hne j) : i = j := by
  unfold accept at hi hj
  exact tool_corner_of_bit_bij.1 (hi.trans hj.symm)

/-- **The accept test is nontrivial.** For a nonempty walked side there is
    exactly one position passing it: the pre-image of the least walked-side
    corner under the `toolCornerOfBit` bijection. -/
theorem accept_count_one (side : Fin 8 → Bool) (hne : ∃ i, side i = true) :
    ((Finset.univ : Finset (Fin 8)).filter (fun i => decide (accept side hne i))).card = 1 := by
  classical
  obtain ⟨m, hm⟩ := tool_corner_of_bit_bij.2 (ctz32 side hne)
  have hmem : accept side hne m := by
    unfold accept
    exact hm
  have hcard : ((Finset.univ : Finset (Fin 8)).filter (fun i => decide (accept side hne i))) =
      {m} := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, decide_eq_true_eq, Finset.mem_singleton,
      Finset.mem_univ, true_and]
    constructor
    · intro hacc
      exact accept_subsingleton side hne i m hacc hmem
    · intro hi
      rw [hi]
      exact hmem
  rw [hcard]
  exact Finset.card_singleton _

/-- **Visitation ⟹ classify exactly once.** For a crossing cell (nonempty
    walked side), exactly one position passes the ownership test; under the
    collect walk's coverage contract, the cell is classified exactly once. -/
theorem visit_implies_classify (side : Fin 8 → Bool) (hne : ∃ i, side i = true) :
    ((Finset.univ : Finset (Fin 8)).filter (fun i => decide (accept side hne i))).card = 1 :=
  accept_count_one side hne

end Vdb
