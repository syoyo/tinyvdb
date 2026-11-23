/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  PH-3: convex parts for physics collision. A convex part is an axis-aligned
  world box; boxes are convex, contain every point used to build them, and two
  boxes are separated along an axis exactly when their coordinate intervals are
  disjoint (the box special case of the separating-axis theorem). This keeps
  the C implementation deterministic and its Lean twin exact over rationals.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Basic
import Vdb.LevelSet

noncomputable section

open scoped RealInnerProductSpace

namespace Vdb

/-- An axis-aligned box by its lower and upper corners. -/
abbrev Box3 := Point × Point

/-- Point membership in a box, coordinatewise. -/
def memBox (b : Box3) (p : Point) : Prop :=
  ∀ i : Fin 3, b.1 i ≤ p i ∧ p i ≤ b.2 i

theorem memBox_iff (b : Box3) (p : Point) :
    memBox b p ↔ ∀ i : Fin 3, b.1 i ≤ p i ∧ p i ≤ b.2 i := Iff.rfl

/-- An axis-aligned box is a convex set. -/
theorem convex_box (b : Box3) : Convex ℝ {p : Point | memBox b p} := by
  intro x hx y hy a t ha ht hab i
  constructor
  · have hxi := (hx i).1
    have hyi := (hy i).1
    have h1 : a * (b.1 i) ≤ a * x i := mul_le_mul_of_nonneg_left hxi ha
    have h2 : t * (b.1 i) ≤ t * y i := mul_le_mul_of_nonneg_left hyi ht
    have h3 : a * (b.1 i) + t * (b.1 i) = b.1 i := by
      rw [← add_mul, hab, one_mul]
    simp only [PiLp.add_apply, PiLp.smul_apply]
    rw [smul_eq_mul, smul_eq_mul]
    nlinarith
  · have hxi := (hx i).2
    have hyi := (hy i).2
    have h1 : a * x i ≤ a * (b.2 i) := mul_le_mul_of_nonneg_left hxi ha
    have h2 : t * y i ≤ t * (b.2 i) := mul_le_mul_of_nonneg_left hyi ht
    have h3 : a * (b.2 i) + t * (b.2 i) = b.2 i := by
      rw [← add_mul, hab, one_mul]
    simp only [PiLp.add_apply, PiLp.smul_apply]
    rw [smul_eq_mul, smul_eq_mul]
    nlinarith

/-- Boxes are separated along an axis when one's upper bound is below the
    other's lower bound; such boxes are disjoint. -/
theorem boxes_disjoint_of_separated {b c : Box3} (i : Fin 3)
    (h : b.2 i < c.1 i) : Disjoint {p | memBox b p} {p | memBox c p} := by
  rw [Set.disjoint_left]
  intro p hb hc
  exact not_lt_of_ge (hb i).2 (lt_of_lt_of_le h (hc i).1)

end Vdb
