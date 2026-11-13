/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  A 3D inside predicate for a closed (convex, axis-aligned) surface and its
  signed distance field.

  * The half-space test `boxInside` (the intersection of six open half-spaces)
    is the inside predicate of the box surface; the signed Chebyshev field
    `sdfBox` is negative exactly inside, zero exactly on the boundary, and
    positive outside, so it is a signed distance field with a verified zero set
    and sign.
  * The ray-crossing test `boxRayParity` casts the `+x` ray and counts the
    boundary crossings (parity); for a point off the boundary it is true
    exactly inside the box. This is the 3D analogue of the planar parity test.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.LevelSet

set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace

namespace Vdb

/-! ### Half-space inside test and the signed box field -/

/-- Strict inside of the axis-aligned box (the intersection of six open
    half-spaces): the 3D inside predicate of the box surface. -/
def boxInside (h p : Point) : Prop := ∀ i : Fin 3, |p i| < h i

/-- The box surface: inside-or-on with at least one coordinate on a face. -/
def boxBoundary (h p : Point) : Prop :=
  (∀ i : Fin 3, |p i| ≤ h i) ∧ (∃ i : Fin 3, |p i| = h i)

/-- The signed Chebyshev field vanishes exactly on the box boundary. -/
theorem signedBoxField_eq_zero_iff (h p : Point) :
    sdfBox h p = 0 ↔ boxBoundary h p := by
  rw [sdfBox_eq_zero_iff]
  rfl

/-- Inside the box exactly where the signed field is negative. -/
theorem signedBoxField_neg_iff (h p : Point) :
    sdfBox h p < 0 ↔ boxInside h p := by
  unfold boxInside sdfBox
  rw [max_lt_iff, max_lt_iff]
  constructor
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
  · intro hall
    exact ⟨by simpa using hall 0, by simpa using hall 1, by simpa using hall 2⟩

/-- Outside the box (away from the boundary) exactly where the signed field
    is positive. -/
theorem signedBoxField_pos_iff (h p : Point) :
    0 < sdfBox h p ↔ ¬ (∀ i : Fin 3, |p i| ≤ h i) := by
  constructor
  · intro hp hle
    have h0 := (sdfBox_le_zero_iff h p).mpr ⟨hle 0, hle 1, hle 2⟩
    linarith
  · intro hout
    by_contra hnot
    apply hout
    obtain ⟨h0, h1, h2⟩ := (sdfBox_le_zero_iff h p).mp (not_lt.mp hnot)
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

/-- The three regions of the signed box field: inside, boundary, outside. -/
theorem signedBoxField_trichotomy (h p : Point) :
    (sdfBox h p < 0 ∧ boxInside h p) ∨
      (sdfBox h p = 0 ∧ boxBoundary h p) ∨
      (0 < sdfBox h p ∧ ¬ (∀ i : Fin 3, |p i| ≤ h i)) := by
  rcases lt_trichotomy (sdfBox h p) 0 with hlt | heq | hgt
  · exact Or.inl ⟨hlt, (signedBoxField_neg_iff h p).mp hlt⟩
  · exact Or.inr (Or.inl ⟨heq, (signedBoxField_eq_zero_iff h p).mp heq⟩)
  · exact Or.inr (Or.inr ⟨hgt, (signedBoxField_pos_iff h p).mp hgt⟩)

/-! ### Ray-crossing parity in 3D -/

/-- Rational 3D points (the ray test is exact over `ℚ`). -/
abbrev RQ3 : Type := Fin 3 → ℚ

/-- Strict inside of the rational box. -/
def boxInsideQ (h p : RQ3) : Prop := ∀ i : Fin 3, |p i| < h i

/-- **Ray-crossing parity** of the `+x` ray from `p` against the box boundary.
    The ray meets the boundary at `x = -h 0` and `x = h 0`; it crosses only
    when the other two coordinates are within the box. -/
def boxRayParity (h p : RQ3) : Bool :=
  (decide (|p 1| ≤ h 1) && decide (|p 2| ≤ h 2)) &&
    ((0 < -h 0 - p 0) != (0 < h 0 - p 0))

/-- The `x`-slab part of the parity: the two crossings are the `x` faces, and
    their parity is exactly "inside the slab". -/
theorem xParity_iff (h0 p0 : ℚ) (hpos : 0 < h0) (hne : |p0| ≠ h0) :
    ¬ (p0 < -h0 ↔ p0 < h0) ↔ |p0| < h0 := by
  by_cases hL : p0 < -h0 <;> by_cases hR : p0 < h0
  · have hnot : ¬ |p0| < h0 := by
      have habs : |p0| = -p0 := abs_of_neg (by linarith)
      rw [habs]; linarith
    simp [hL, hR, hnot]
  · exfalso; linarith
  · have hne' : -h0 ≠ p0 := by
      intro he; apply hne; rw [← he, abs_neg, abs_of_pos hpos]
    have hlt : -h0 < p0 := lt_of_le_of_ne (not_lt.mp hL) hne'
    have hmem : |p0| < h0 := by
      rw [abs_lt]; constructor <;> linarith
    simp [hL, hR, hmem]
  · have hnot : ¬ |p0| < h0 := by
      have habs : |p0| = p0 := abs_of_nonneg (by linarith)
      rw [habs]; linarith
    simp [hL, hR, hnot]

/-- **The 3D inside test by ray crossing**: for a point off the boundary, the
    parity of the boundary crossings of the `+x` ray is true exactly inside
    the box. -/
theorem boxRayParity_iff (h p : RQ3) (hpos : ∀ i, 0 < h i)
    (hbd : ∀ i, |p i| ≠ h i) :
    boxRayParity h p = true ↔ boxInsideQ h p := by
  unfold boxRayParity boxInsideQ
  by_cases hy : |p 1| ≤ h 1
  · by_cases hz : |p 2| ≤ h 2
    · have hx := xParity_iff (h 0) (p 0) (hpos 0) (hbd 0)
      simp [hy, hz]
      constructor
      · intro hpar i
        fin_cases i
        · simpa using hx.mp hpar
        · exact lt_of_le_of_ne hy (hbd 1)
        · exact lt_of_le_of_ne hz (hbd 2)
      · intro hall
        exact hx.mpr (by simpa using hall 0)
    · have hz' : h 2 < |p 2| := lt_of_not_ge hz
      simp [hy, hz]
      exact ⟨2, le_of_lt hz'⟩
  · have hy' : h 1 < |p 1| := lt_of_not_ge hy
    simp [hy]
    exact ⟨1, le_of_lt hy'⟩

end Vdb
