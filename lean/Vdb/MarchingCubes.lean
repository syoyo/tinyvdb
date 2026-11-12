/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  The marching-cubes sign rule. Cubes are classified by the signs of their
  eight corner values; edges of opposite sign are crossed by the surface, and
  ambiguous (checkerboard) faces are resolved by a *consistent* rule: connect
  the negative diagonal exactly when the face's mean value is negative.

  The mean depends only on the unordered four corner values, so both cubes
  sharing a face decide the same way (the rule is invariant under the dihedral
  symmetries of the face, including the reversal the neighbouring cube walks).
  This is the "consistent face rule" chosen over the asymptotic decider in
  `plan-lean.md` (F10).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

set_option linter.unusedSimpArgs false

namespace Vdb

/-- A corner value is inside when it is negative (the level-set sign
    convention used by the volume operators). -/
def isInside (q : ℚ) : Bool := decide (q < 0)

@[simp] theorem isInside_iff {q : ℚ} : isInside q = true ↔ q < 0 := by
  simp [isInside]

@[simp] theorem isInside_false_iff {q : ℚ} : isInside q = false ↔ ¬ q < 0 := by
  simp [isInside]

/-- A cube face's four corner values in cyclic order. The diagonals are
    `(a, c)` and `(b, d)`. -/
structure Face where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ

/-- The consistent face rule: connect the negative diagonal exactly when the
    face's mean value is negative. The mean depends only on the unordered set
    of the four values, so both cubes sharing a face decide the same way. -/
def Face.negConnected (f : Face) : Bool :=
  decide (f.a + f.b + f.c + f.d < 0)

/-- An ambiguous (checkerboard) face: opposite corners agree and the two
    diagonals carry opposite signs. -/
def Face.Ambiguous (f : Face) : Prop :=
  isInside f.a = isInside f.c ∧ isInside f.b = isInside f.d ∧
    isInside f.a ≠ isInside f.b

/-- The decision only depends on the four values (it is a function). -/
theorem Face.negConnected_eq_sum (f : Face) :
    f.negConnected = decide (f.a + f.b + f.c + f.d < 0) := rfl

/-- Cyclic rotation of the face's corner order. -/
def Face.rot (f : Face) : Face := ⟨f.b, f.c, f.d, f.a⟩

/-- Reversal of the corner order (the order the neighbouring cube sees when
    traversing the shared face the other way). -/
def Face.rev (f : Face) : Face := ⟨f.d, f.c, f.b, f.a⟩

/-- Reflection fixing the `(a, c)` diagonal. -/
def Face.refl (f : Face) : Face := ⟨f.a, f.d, f.c, f.b⟩

/-- The rule is invariant under a cyclic rotation of the face. -/
theorem Face.negConnected_rot (f : Face) :
    f.rot.negConnected = f.negConnected := by
  unfold Face.negConnected Face.rot
  have h : f.b + f.c + f.d + f.a = f.a + f.b + f.c + f.d := by ring
  rw [h]

/-- The rule is invariant under reversal (the neighbour's orientation). -/
theorem Face.negConnected_rev (f : Face) :
    f.rev.negConnected = f.negConnected := by
  unfold Face.negConnected Face.rev
  have h : f.d + f.c + f.b + f.a = f.a + f.b + f.c + f.d := by ring
  rw [h]

/-- The rule is invariant under the diagonal reflection. -/
theorem Face.negConnected_refl (f : Face) :
    f.refl.negConnected = f.negConnected := by
  unfold Face.negConnected Face.refl
  have h : f.a + f.d + f.c + f.b = f.a + f.b + f.c + f.d := by ring
  rw [h]

/-- **Consistency**: any two cubes sharing a face agree on which diagonal is
    connected, whatever corner order each of them walks the face in. -/
theorem Face.negConnected_all_symmetries (f : Face) :
    f.negConnected = f.rot.negConnected ∧
      f.negConnected = f.rev.negConnected ∧
      f.negConnected = f.refl.negConnected ∧
      f.negConnected = f.rot.rev.negConnected ∧
      f.negConnected = f.rot.refl.negConnected ∧
      f.negConnected = f.rev.refl.negConnected := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Face.negConnected_rot]
  · rw [Face.negConnected_rev]
  · rw [Face.negConnected_refl]
  · rw [Face.negConnected_rev, Face.negConnected_rot]
  · rw [Face.negConnected_refl, Face.negConnected_rot]
  · rw [Face.negConnected_refl, Face.negConnected_rev]

/-- Flipping the field (inside/outside swap) flips the rule, provided the
    face mean is not zero. -/
def Face.neg (f : Face) : Face := ⟨-f.a, -f.b, -f.c, -f.d⟩

theorem Face.negConnected_neg (f : Face)
    (hs : f.a + f.b + f.c + f.d ≠ 0) :
    f.neg.negConnected = !f.negConnected := by
  unfold Face.negConnected Face.neg
  have hs' : -f.a + -f.b + -f.c + -f.d = -(f.a + f.b + f.c + f.d) := by ring
  rw [hs']
  by_cases h : f.a + f.b + f.c + f.d < 0
  · have h2 : ¬ -(f.a + f.b + f.c + f.d) < 0 := by
      rw [neg_lt_zero]
      exact not_lt.mpr (le_of_lt h)
    rw [decide_eq_true_eq.mpr h, decide_eq_false_iff_not.mpr h2]
    rfl
  · have h2 : -(f.a + f.b + f.c + f.d) < 0 := by
      rw [neg_lt_zero]
      exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm hs)
    rw [decide_eq_false_iff_not.mpr h, decide_eq_true_eq.mpr h2]
    rfl

/-- An all-inside face is not ambiguous. -/
theorem Face.not_ambiguous_all_neg (f : Face)
    (ha : f.a < 0) (hb : f.b < 0) (_hc : f.c < 0) (_hd : f.d < 0) :
    ¬ f.Ambiguous := by
  rintro ⟨hac, hbd, hab⟩
  have h1 : isInside f.a = true := isInside_iff.mpr ha
  have h2 : isInside f.b = true := isInside_iff.mpr hb
  exact hab (by rw [h1, h2])

/-- An all-outside face is not ambiguous. -/
theorem Face.not_ambiguous_all_pos (f : Face)
    (ha : 0 < f.a) (hb : 0 < f.b) (_hc : 0 < f.c) (_hd : 0 < f.d) :
    ¬ f.Ambiguous := by
  rintro ⟨hac, hbd, hab⟩
  have h1 : isInside f.a = false := isInside_false_iff.mpr (not_lt.mpr (le_of_lt ha))
  have h2 : isInside f.b = false := isInside_false_iff.mpr (not_lt.mpr (le_of_lt hb))
  exact hab (by rw [h1, h2])

/-- Whether the surface crosses an edge (the two endpoint signs differ). -/
def edgeCrosses (u v : ℚ) : Bool := isInside u != isInside v

/-- The edge test is symmetric, so neighbouring cubes agree when they walk a
    shared edge in opposite directions. -/
theorem edgeCrosses_comm (u v : ℚ) : edgeCrosses u v = edgeCrosses v u := by
  unfold edgeCrosses
  cases isInside u <;> cases isInside v <;> rfl

theorem Face.ambiguous_diagonals (f : Face) (h : f.Ambiguous)
    (ha : f.a ≠ 0) (hb : f.b ≠ 0) (hc : f.c ≠ 0) (hd : f.d ≠ 0) :
    (f.a < 0 ∧ f.c < 0 ∧ 0 < f.b ∧ 0 < f.d) ∨
      (0 < f.a ∧ 0 < f.c ∧ f.b < 0 ∧ f.d < 0) := by
  obtain ⟨hac, hbd, hab⟩ := h
  cases hin : isInside f.a
  · have ha' : 0 < f.a := by
      have : ¬ f.a < 0 := isInside_false_iff.mp hin
      exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm ha)
    have hc' : 0 < f.c := by
      have hc0 : isInside f.c = false := by rw [← hac]; exact hin
      have : ¬ f.c < 0 := isInside_false_iff.mp hc0
      exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hc)
    have hb' : f.b < 0 := by
      have hb1 : isInside f.b = true := by
        cases h2 : isInside f.b
        · exact absurd (by rw [hin, h2]) hab
        · rfl
      exact isInside_iff.mp hb1
    have hd' : f.d < 0 := by
      have hd1 : isInside f.d = true := by rw [← hbd]; exact isInside_iff.mpr hb'
      exact isInside_iff.mp hd1
    exact Or.inr ⟨ha', hc', hb', hd'⟩
  · have ha' : f.a < 0 := isInside_iff.mp hin
    have hc' : f.c < 0 := by
      have hc1 : isInside f.c = true := by rw [← hac]; exact hin
      exact isInside_iff.mp hc1
    have hb' : 0 < f.b := by
      have hb0 : isInside f.b = false := by
        cases h2 : isInside f.b
        · rfl
        · exact absurd (by rw [hin, h2]) hab
      have : ¬ f.b < 0 := isInside_false_iff.mp hb0
      exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hb)
    have hd' : 0 < f.d := by
      have hd0 : isInside f.d = false := by rw [← hbd]; exact isInside_false_iff.mpr (not_lt.mpr (le_of_lt hb'))
      have : ¬ f.d < 0 := isInside_false_iff.mp hd0
      exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hd)
    exact Or.inl ⟨ha', hc', hb', hd'⟩

end Vdb
