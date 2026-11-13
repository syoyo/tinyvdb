/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  CSG (constructive solid geometry) composition of signed distance fields:
  union is `min`, intersection is `max`, and difference is `max a (-b)`.
  The module proves the exact set semantics of the interiors (the sublevel
  set of the composed field is the corresponding Boolean combination of the
  sublevel sets — for any fields, no regularity needed), that the
  composition preserves 1-Lipschitz-ness (so the composed field is again a
  distance field), the sign/zero-set characterization, and that pointwise
  composition is aliasing-safe.

  Note: for *non-exact* fields the composition can disagree with the true
  signed distance of the union/intersection; the sublevel-set semantics is
  nonetheless exact, which is what marching cubes relies on.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Vdb.LevelSet

noncomputable section

open scoped RealInnerProductSpace

namespace Vdb

/-- CSG union: `min` field. -/
def csgUnion (u v : Point → ℝ) (p : Point) : ℝ := min (u p) (v p)

/-- CSG intersection: `max` field. -/
def csgIntersection (u v : Point → ℝ) (p : Point) : ℝ := max (u p) (v p)

/-- CSG difference `u \ v`: `max u (-v)` field. -/
def csgDifference (u v : Point → ℝ) (p : Point) : ℝ := max (u p) (-v p)

theorem csgUnion_def : csgUnion u v p = min (u p) (v p) := rfl
theorem csgIntersection_def : csgIntersection u v p = max (u p) (v p) := rfl
theorem csgDifference_def : csgDifference u v p = max (u p) (-v p) := rfl

/-! ### Sign semantics -/

theorem csgUnion_neg_iff {u v : Point → ℝ} {p : Point} :
    csgUnion u v p < 0 ↔ u p < 0 ∨ v p < 0 := by
  simp only [csgUnion_def, min_lt_iff]

theorem csgUnion_nonneg_iff {u v : Point → ℝ} {p : Point} :
    0 ≤ csgUnion u v p ↔ 0 ≤ u p ∧ 0 ≤ v p := by
  simp only [csgUnion_def, le_min_iff]

theorem csgUnion_nonpos_iff {u v : Point → ℝ} {p : Point} :
    csgUnion u v p ≤ 0 ↔ u p ≤ 0 ∨ v p ≤ 0 := by
  simp only [csgUnion_def, min_le_iff]

theorem csgUnion_pos_iff {u v : Point → ℝ} {p : Point} :
    0 < csgUnion u v p ↔ 0 < u p ∧ 0 < v p := by
  simp only [csgUnion_def, lt_min_iff]

theorem csgIntersection_neg_iff {u v : Point → ℝ} {p : Point} :
    csgIntersection u v p < 0 ↔ u p < 0 ∧ v p < 0 := by
  simp only [csgIntersection_def, max_lt_iff]

theorem csgIntersection_nonneg_iff {u v : Point → ℝ} {p : Point} :
    0 ≤ csgIntersection u v p ↔ 0 ≤ u p ∨ 0 ≤ v p := by
  simp only [csgIntersection_def, le_max_iff]

theorem csgIntersection_nonpos_iff {u v : Point → ℝ} {p : Point} :
    csgIntersection u v p ≤ 0 ↔ u p ≤ 0 ∧ v p ≤ 0 := by
  simp only [csgIntersection_def, max_le_iff]

theorem csgIntersection_pos_iff {u v : Point → ℝ} {p : Point} :
    0 < csgIntersection u v p ↔ 0 < u p ∨ 0 < v p := by
  simp only [csgIntersection_def, lt_max_iff]

theorem csgDifference_neg_iff {u v : Point → ℝ} {p : Point} :
    csgDifference u v p < 0 ↔ u p < 0 ∧ 0 < v p := by
  constructor
  · intro h
    have h' : max (u p) (-v p) < 0 := h
    simp only [max_lt_iff] at h'
    exact ⟨h'.1, by linarith [h'.2]⟩
  · intro h
    have h' : u p < 0 ∧ -v p < 0 := ⟨h.1, by linarith [h.2]⟩
    show max (u p) (-v p) < 0
    exact max_lt_iff.mpr h'

theorem csgDifference_nonneg_iff {u v : Point → ℝ} {p : Point} :
    0 ≤ csgDifference u v p ↔ 0 ≤ u p ∨ v p ≤ 0 := by
  constructor
  · intro h
    have h' : 0 ≤ max (u p) (-v p) := h
    simp only [le_max_iff] at h'
    exact h'.elim Or.inl (fun h'' => Or.inr (by linarith [h'']))
  · intro h
    show 0 ≤ max (u p) (-v p)
    exact le_max_iff.mpr (h.elim Or.inl (fun h'' => Or.inr (by linarith [h''])))

theorem csgDifference_nonpos_iff {u v : Point → ℝ} {p : Point} :
    csgDifference u v p ≤ 0 ↔ u p ≤ 0 ∧ 0 ≤ v p := by
  constructor
  · intro h
    have h' : max (u p) (-v p) ≤ 0 := h
    simp only [max_le_iff] at h'
    exact ⟨h'.1, by linarith [h'.2]⟩
  · intro h
    have h' : u p ≤ 0 ∧ -v p ≤ 0 := ⟨h.1, by linarith [h.2]⟩
    show max (u p) (-v p) ≤ 0
    exact max_le_iff.mpr h'

theorem csgDifference_pos_iff {u v : Point → ℝ} {p : Point} :
    0 < csgDifference u v p ↔ 0 < u p ∨ v p < 0 := by
  constructor
  · intro h
    have h' : 0 < max (u p) (-v p) := h
    simp only [lt_max_iff] at h'
    exact h'.elim Or.inl (fun h'' => Or.inr (by linarith [h'']))
  · intro h
    show 0 < max (u p) (-v p)
    exact lt_max_iff.mpr (h.elim Or.inl (fun h'' => Or.inr (by linarith [h''])))

/-! ### Sublevel-set semantics (exact for any fields) -/

theorem csgUnion_sublevel :
    {p : Point | csgUnion u v p < 0} = {p : Point | u p < 0} ∪ {p : Point | v p < 0} := by
  ext p
  simp only [csgUnion_def, min_lt_iff]
  rfl

theorem csgUnion_sublevel_ge :
    {p : Point | 0 ≤ csgUnion u v p} = {p : Point | 0 ≤ u p} ∩ {p : Point | 0 ≤ v p} := by
  ext p
  simp only [csgUnion_def, le_min_iff]
  rfl

theorem csgIntersection_sublevel :
    {p : Point | csgIntersection u v p < 0} = {p : Point | u p < 0} ∩ {p : Point | v p < 0} := by
  ext p
  simp only [csgIntersection_def, max_lt_iff]
  rfl

theorem csgIntersection_sublevel_ge :
    {p : Point | 0 ≤ csgIntersection u v p} = {p : Point | 0 ≤ u p} ∪ {p : Point | 0 ≤ v p} := by
  ext p
  simp only [csgIntersection_def, le_max_iff]
  rfl

theorem csgDifference_sublevel :
    {p : Point | csgDifference u v p < 0} = {p : Point | u p < 0} ∩ {p : Point | 0 < v p} := by
  ext p
  simp only [csgDifference_def, max_lt_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by show 0 < v p; linarith [h2]⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by have h2' : 0 < v p := h2; linarith [h2']⟩

theorem csgDifference_sublevel_ge :
    {p : Point | 0 ≤ csgDifference u v p} = {p : Point | 0 ≤ u p} ∪ {p : Point | v p ≤ 0} := by
  ext p
  simp only [csgDifference_def, le_max_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (show p ∈ {p | v p ≤ 0} from by show v p ≤ 0; linarith [h])
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by have h' : v p ≤ 0 := h; linarith [h'])

/-! ### 1-Lipschitz preservation -/

theorem csgUnion_isSDF {u v : Point → ℝ} (hu : IsSDF u) (hv : IsSDF v) :
    IsSDF (csgUnion u v) := by
  intro p q
  obtain ⟨h1a, h1b⟩ := abs_le.mp (hu p q)
  obtain ⟨h2a, h2b⟩ := abs_le.mp (hv p q)
  unfold csgUnion
  rcases le_total (u p) (v p) with h3 | h3 <;>
  rcases le_total (u q) (v q) with h4 | h4 <;>
  simp only [min_eq_left h3, min_eq_right h3, min_eq_left h4, min_eq_right h4] <;>
  rw [abs_le] <;>
  constructor <;> linarith [h1a, h1b, h2a, h2b, h3, h4]

theorem csgIntersection_isSDF {u v : Point → ℝ} (hu : IsSDF u) (hv : IsSDF v) :
    IsSDF (csgIntersection u v) := by
  intro p q
  obtain ⟨h1a, h1b⟩ := abs_le.mp (hu p q)
  obtain ⟨h2a, h2b⟩ := abs_le.mp (hv p q)
  unfold csgIntersection
  rcases le_total (u p) (v p) with h3 | h3 <;>
  rcases le_total (u q) (v q) with h4 | h4 <;>
  simp only [max_eq_left h3, max_eq_right h3, max_eq_left h4, max_eq_right h4] <;>
  rw [abs_le] <;>
  constructor <;> linarith [h1a, h1b, h2a, h2b, h3, h4]

theorem csgDifference_isSDF {u v : Point → ℝ} (hu : IsSDF u) (hv : IsSDF v) :
    IsSDF (csgDifference u v) := by
  intro p q
  obtain ⟨h1a, h1b⟩ := abs_le.mp (hu p q)
  obtain ⟨h2a, h2b⟩ := abs_le.mp (hv p q)
  unfold csgDifference
  rcases le_total (u p) (-v p) with h3 | h3 <;>
  rcases le_total (u q) (-v q) with h4 | h4 <;>
  simp only [max_eq_left h3, max_eq_right h3, max_eq_left h4, max_eq_right h4] <;>
  rw [abs_le] <;>
  constructor <;> linarith [h1a, h1b, h2a, h2b, h3, h4]

/-! ### Zero-set characterization and aliasing safety -/

theorem csgUnion_eq_zero_iff {u v : Point → ℝ} {p : Point} :
    csgUnion u v p = 0 ↔ (u p = 0 ∧ 0 ≤ v p) ∨ (v p = 0 ∧ 0 ≤ u p) := by
  unfold csgUnion
  rcases le_total (u p) (v p) with h | h
  · rw [min_eq_left h]
    constructor
    · intro h'
      exact Or.inl ⟨h', by linarith [h', h]⟩
    · rintro (⟨h', -⟩ | ⟨h', h3⟩)
      · exact h'
      · linarith [h, h', h3]
  · rw [min_eq_right h]
    constructor
    · intro h'
      exact Or.inr ⟨h', by linarith [h', h]⟩
    · rintro (⟨h', h3⟩ | ⟨h', -⟩)
      · linarith [h, h', h3]
      · exact h'

/-- Pointwise (aliasing-safe) composition: the value at `p` depends only on
    `u p` and `v p`. -/
theorem csgUnion_pointwise {u₁ u₂ v₁ v₂ : Point → ℝ} {p : Point}
    (hu : u₁ p = u₂ p) (hv : v₁ p = v₂ p) :
    csgUnion u₁ v₁ p = csgUnion u₂ v₂ p := by
  unfold csgUnion
  rw [hu, hv]

theorem csgIntersection_pointwise {u₁ u₂ v₁ v₂ : Point → ℝ} {p : Point}
    (hu : u₁ p = u₂ p) (hv : v₁ p = v₂ p) :
    csgIntersection u₁ v₁ p = csgIntersection u₂ v₂ p := by
  unfold csgIntersection
  rw [hu, hv]

theorem csgDifference_pointwise {u₁ u₂ v₁ v₂ : Point → ℝ} {p : Point}
    (hu : u₁ p = u₂ p) (hv : v₁ p = v₂ p) :
    csgDifference u₁ v₁ p = csgDifference u₂ v₂ p := by
  unfold csgDifference
  rw [hu, hv]

end Vdb
