/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  Vertex figures of angle-weighted pseudo-normals: the three-face
  (trihedral) case of the geometric seam (S).

  The general angle-weighted sign theorem lands modulo the per-face
  positivity seam (S) in `Vdb/AnglePseudoNormal.lean`:

      ∀ j, 0 < Σ i, θ i * ⟪n i, n j⟫.                            (S)

  This module discharges (S) for a trihedral vertex whose three outward
  unit normals have pairwise dots `c₁₂ = c₁₃ = p`, `c₂₃ = q` (the
  *isosceles* vertex figure).  That family contains the F16 apex
  (`p = -2/3`, `q = 1/9`) but is not restricted to it: the dihedral angles
  may be acute or obtuse, and the corner angles are the genuine geometric
  ones (angles between the cone's edge rays, computed from cross products).

  Reduction.  Write `a = θ₁` (corner angle of the apex face) and
  `b = θ₂ = θ₃` (the two equal corner angles).  The spherical vertex
  figure is an isosceles spherical triangle with sides `a, b, b`, so the
  law of cosines gives

      cos B = (1 - cos a) / sin a * cos b / sin b = tan(a/2) * cot b,
      cos A = (cos a - cos²b) / sin²b,

  where `A, B` are the interior angles at the apex and base edges; the
  outward-normal dots are `p = -cos B`, `q = -cos A`.  Hence

      S₁ = a - 2 b cos B,     S₂ = (1 + q) b + p a = b (1 - cos A) - a cos B.

  With `t = a/2`, `S₁ > 0` is equivalent to `t cot t > b cot b`, which
  follows from the strict decrease of `sin x / x` on `(0, π)` and
  `a < 2b`.  `S₂ > 0` reduces to `sin a / a > sin(2b) / (2b)`, again the
  same monotonicity and `a < 2b`.  The only algebraic input is the Gram
  determinant identity `det = (1 - q)(1 + q - 2p²) = triple² > 0`, which
  gives `1 + q - 2p² > 0` — exactly the strict triangle inequality `a < 2b`.

  Everything is machine-checked; no spherical Stokes/surface measure is
  used.  The three-face (trihedral) case is now unconditional, including the
  non-isosceles vertex figure and the three hyperplane slices; the general
  n-face seam stays open.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.AnglePseudoNormal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace Vdb
namespace V3

open scoped Real
open scoped Topology
open Real

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! ### Cross-product algebra -/

/-- Lagrange identity with a repeated first argument:
    `⟪a×b, a×c⟫ = ⟪b,c⟫⟪a,a⟫ - ⟪a,b⟫⟪a,c⟫` (all dots are `V3.dot`). -/
theorem dot_cross_cross (a b c : V3) :
    dot (cross a b) (cross a c) = dot b c * dot a a - dot a b * dot a c := by
  unfold dot cross
  ring

/-- The scalar triple product is `⟪a, b×c⟫`. -/
theorem dot_cross_eq_triple (a b c : V3) : dot a (cross b c) = triple a b c := by
  unfold triple
  rw [Matrix.det_fin_three]
  simp only [cols_00, cols_01, cols_02, cols_10, cols_11, cols_12,
    cols_20, cols_21, cols_22]
  unfold dot cross
  simp
  ring

/-- `|a×b|² = 1 - p²` for unit `a, b` with `⟪a,b⟫ = p`. -/
theorem cross_sq_of_unit (a b : V3) {p : ℝ}
    (ha : dot a a = 1) (hb : dot b b = 1) (hab : dot a b = p) :
    dot (cross a b) (cross a b) = 1 - p ^ 2 := by
  have h := lagrange a b
  rw [ha, hb, hab] at h
  nlinarith

/-- Squared triple product equals the Gram determinant
    `det [[1,p,p],[p,1,q],[p,q,1]] = (1-q)(1+q-2p²)` for an isosceles
    triple of unit vectors. -/
theorem triple_sq_isosceles (n₁ n₂ n₃ : V3) {p q : ℝ}
    (h1 : dot n₁ n₁ = 1) (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1)
    (h12 : dot n₁ n₂ = p) (h13 : dot n₁ n₃ = p) (h23 : dot n₂ n₃ = q) :
    (triple n₁ n₂ n₃) ^ 2 = (1 - q) * (1 + q - 2 * p ^ 2) := by
  have hpoly : (triple n₁ n₂ n₃) ^ 2 =
      dot n₁ n₁ * dot n₂ n₂ * dot n₃ n₃
        + 2 * dot n₁ n₂ * dot n₁ n₃ * dot n₂ n₃
        - dot n₁ n₁ * (dot n₂ n₃) ^ 2
        - dot n₂ n₂ * (dot n₁ n₃) ^ 2
        - dot n₃ n₃ * (dot n₁ n₂) ^ 2 := by
    rw [← dot_cross_eq_triple]
    unfold dot cross
    ring
  rw [hpoly, h1, h2, h3, h12, h13, h23]
  ring

/-! ### Strict decrease of `sin x / x` on `(0, π)` -/

/-- For `0 < x < y < π`, `sin y / y < sin x / x`.  This is the strict
    concavity of `sin` on `[0, π]` applied to the two points `0` and `y`
    with weight `x / y`. -/
theorem sin_div_strictAnti {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < Real.pi) :
    Real.sin y / y < Real.sin x / x := by
  have hy0 : 0 < y := lt_trans hx hxy
  have hxmem : (0 : ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_rfl, Real.pi_pos.le⟩
  have hymem : y ∈ Set.Icc 0 Real.pi := ⟨le_of_lt hy0, le_of_lt hy⟩
  have hne : (0 : ℝ) ≠ y := ne_of_lt hy0
  have htpos : 0 < x / y := div_pos hx hy0
  have htlt : x / y < 1 := (div_lt_one hy0).2 hxy
  have hc : 0 < 1 - x / y := by linarith
  have hconc := strictConcaveOn_sin_Icc.2 hxmem hymem hne hc htpos
    (by ring : (1 - x / y) + x / y = 1)
  have hconc' : (1 - x / y) * Real.sin 0 + (x / y) * Real.sin y <
      Real.sin ((1 - x / y) * 0 + (x / y) * y) := by
    simpa [smul_eq_mul] using hconc
  have hsin : (x / y) * Real.sin y < Real.sin x := by
    simpa [Real.sin_zero, div_mul_cancel₀ x (ne_of_gt hy0)] using hconc'
  have hcross : x * Real.sin y < y * Real.sin x := by
    calc
      x * Real.sin y = ((x / y) * Real.sin y) * y := by
        field_simp [ne_of_gt hy0]
      _ < Real.sin x * y := mul_lt_mul_of_pos_right hsin hy0
      _ = y * Real.sin x := by ring
  rw [div_lt_div_iff₀ hy0 hx]
  nlinarith


/-! ### The two scalar inequalities of the isosceles vertex figure

Write `a` for the corner angle of the apex face and `b` for the (equal)
corner angles of the other two faces.  The spherical vertex figure is an
isosceles spherical triangle with sides `a, b, b`; its base interior angle
`B` and apex interior angle `A` satisfy

    cos B = ((1 - cos a) / sin a) * (cos b / sin b),
    cos A = (cos a - cos²b) / sin²b,

and the outward-normal dots are `p = -cos B`, `q = -cos A`.  The two
needed face-positivity inequalities are proved from `0 < a < 2b` and
`a, b ∈ (0, π)` alone. -/

/-- The elementary trigonometric core:
    `(a/2)·cos(a/2)·sin b > b·cos b·sin(a/2)` for `0 < a < 2b`, `b < π`. -/
theorem half_key (a b : ℝ) (ha : 0 < a) (hbpi : b < Real.pi)
    (hab : a < 2 * b) :
    (a / 2) * Real.cos (a / 2) * Real.sin b >
      b * Real.cos b * Real.sin (a / 2) := by
  let t : ℝ := a / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have htb : t < b := by dsimp [t]; linarith
  have hbt0 : 0 < b - t := by linarith
  have hbtpi : b - t < Real.pi := by linarith
  have hbtpos : 0 < Real.sin (b - t) := Real.sin_pos_of_pos_of_lt_pi hbt0 hbtpi
  have hsumpos : 0 < b + t := by linarith [htb]
  have hterm2 : 0 < (b + t) * Real.sin (b - t) := mul_pos hsumpos hbtpos
  have hid : (t - b) * Real.sin (b + t) + (t + b) * Real.sin (b - t) =
      2 * (t * Real.cos t * Real.sin b - b * Real.cos b * Real.sin t) := by
    rw [Real.sin_add, Real.sin_sub]
    ring
  have hsum : 0 < (t - b) * Real.sin (b + t) + (t + b) * Real.sin (b - t) := by
    by_cases hle : b + t < Real.pi
    · have hs := sin_div_strictAnti hbt0 (by linarith : b - t < b + t) hle
      rw [div_lt_div_iff₀ hsumpos hbt0] at hs
      have : (b - t) * Real.sin (b + t) < (b + t) * Real.sin (b - t) := by
        nlinarith
      nlinarith
    · have hge : Real.pi ≤ b + t := le_of_not_gt hle
      have hu0 : 0 ≤ b + t - Real.pi := by linarith
      have hupt : b + t - Real.pi < Real.pi := by
        have ht2 : t < Real.pi := by linarith [ht, htb]
        linarith
      have husin : 0 ≤ Real.sin (b + t - Real.pi) :=
        Real.sin_nonneg_of_mem_Icc ⟨hu0, le_of_lt hupt⟩
      have hsinnonpos : Real.sin (b + t) ≤ 0 := by
        rw [show b + t = (b + t - Real.pi) + Real.pi by ring, Real.sin_add_pi]
        linarith
      have hterm1 : 0 ≤ (t - b) * Real.sin (b + t) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) hsinnonpos
      nlinarith
  rw [hid] at hsum
  dsimp [t] at hsum ⊢
  nlinarith

/-- First face positivity: `a - 2 b cos B > 0`, where
    `cos B = ((1 - cos a) / sin a) * (cos b / sin b)`. -/
theorem iso_face1_pos (a b : ℝ) (ha : 0 < a) (hapi : a < Real.pi)
    (hb : 0 < b) (hbpi : b < Real.pi) (hab : a < 2 * b) :
    0 < a - 2 * b * (((1 - Real.cos a) / Real.sin a) *
      (Real.cos b / Real.sin b)) := by
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha hapi
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb hbpi
  have hst : 0 < Real.sin (a / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hkey := half_key a b ha hbpi hab
  have hcosa : Real.cos a = 2 * Real.cos (a / 2) ^ 2 - 1 := by
    conv_lhs => rw [show a = 2 * (a / 2) by ring, Real.cos_two_mul]
  have hsina : Real.sin a = 2 * Real.sin (a / 2) * Real.cos (a / 2) := by
    conv_lhs => rw [show a = 2 * (a / 2) by ring, Real.sin_two_mul]
  have hprod : 0 < 4 * Real.sin (a / 2) *
      ((a / 2) * Real.cos (a / 2) * Real.sin b - b * Real.cos b * Real.sin (a / 2)) := by
    positivity
  have hnum : 0 < a * Real.sin a * Real.sin b - 2 * b * (1 - Real.cos a) * Real.cos b := by
    rw [hcosa, hsina]
    have hsincos := Real.sin_sq_add_cos_sq (a / 2)
    have hone : 1 - (2 * Real.cos (a / 2) ^ 2 - 1) = 2 * Real.sin (a / 2) ^ 2 := by
      nlinarith
    rw [hone]
    have hnum_eq : a * (2 * Real.sin (a / 2) * Real.cos (a / 2)) * Real.sin b -
        2 * b * (2 * Real.sin (a / 2) ^ 2) * Real.cos b =
      4 * Real.sin (a / 2) *
        ((a / 2) * Real.cos (a / 2) * Real.sin b - b * Real.cos b * Real.sin (a / 2)) := by
      ring
    rw [hnum_eq]
    exact hprod
  have hden : 0 < Real.sin a * Real.sin b := mul_pos hsa hsb
  have hfrac : (a * Real.sin a * Real.sin b - 2 * b * (1 - Real.cos a) * Real.cos b) /
        (Real.sin a * Real.sin b) =
      a - 2 * b * (((1 - Real.cos a) / Real.sin a) * (Real.cos b / Real.sin b)) := by
    field_simp [ne_of_gt hsa, ne_of_gt hsb]
  rw [← hfrac]
  exact div_pos hnum hden

/-- Second face positivity: `b(1 - cos A) - a cos B > 0`, where
    `cos A = (cos a - cos²b) / sin²b` and
    `cos B = ((1 - cos a) / sin a) * (cos b / sin b)`. -/
theorem iso_face2_pos (a b : ℝ) (ha : 0 < a) (hapi : a < Real.pi)
    (hb : 0 < b) (hbpi : b < Real.pi) (hab : a < 2 * b) :
    0 < b * (1 - (Real.cos a - Real.cos b ^ 2) / Real.sin b ^ 2) -
      a * (((1 - Real.cos a) / Real.sin a) * (Real.cos b / Real.sin b)) := by
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha hapi
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb hbpi
  have hsin2b : Real.sin (2 * b) = 2 * Real.sin b * Real.cos b := by
    rw [Real.sin_two_mul]
  have hcore : a * Real.cos b * Real.sin b < b * Real.sin a := by
    by_cases hle : 2 * b < Real.pi
    · have hs := sin_div_strictAnti ha hab hle
      rw [div_lt_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 2) hb) ha] at hs
      rw [hsin2b] at hs
      nlinarith
    · have hge : Real.pi ≤ 2 * b := le_of_not_gt hle
      have hu0 : 0 ≤ 2 * b - Real.pi := by linarith
      have hupt : 2 * b - Real.pi < Real.pi := by linarith
      have husin : 0 ≤ Real.sin (2 * b - Real.pi) :=
        Real.sin_nonneg_of_mem_Icc ⟨hu0, le_of_lt hupt⟩
      have hsin2nonpos : Real.sin (2 * b) ≤ 0 := by
        rw [show 2 * b = (2 * b - Real.pi) + Real.pi by ring, Real.sin_add_pi]
        linarith
      rw [hsin2b] at hsin2nonpos
      have hcb : Real.cos b * Real.sin b ≤ 0 := by nlinarith
      have : a * (Real.cos b * Real.sin b) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) hcb
      nlinarith [mul_pos hb hsa]
  have hdiff : 0 < b * Real.sin a - a * Real.cos b * Real.sin b := by linarith
  have hca_ne : Real.cos a ≠ 1 := by
    intro h
    have hzero : a = 0 := (Real.cos_eq_one_iff_of_lt_of_lt
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).1 h
    linarith
  have hca : Real.cos a < 1 := lt_of_le_of_ne (Real.cos_le_one a) hca_ne
  have hfactor : 0 < (1 - Real.cos a) / (Real.sin a * Real.sin b ^ 2) := by positivity
  have honeA : 1 - (Real.cos a - Real.cos b ^ 2) / Real.sin b ^ 2 =
      (1 - Real.cos a) / Real.sin b ^ 2 := by
    have hsc := Real.sin_sq_add_cos_sq b
    field_simp [ne_of_gt hsb]
    nlinarith
  have hident : b * (1 - (Real.cos a - Real.cos b ^ 2) / Real.sin b ^ 2) -
        a * (((1 - Real.cos a) / Real.sin a) * (Real.cos b / Real.sin b)) =
      ((1 - Real.cos a) / (Real.sin a * Real.sin b ^ 2)) *
        (b * Real.sin a - a * Real.cos b * Real.sin b) := by
    rw [honeA]
    field_simp [ne_of_gt hsa, ne_of_gt hsb]
  rw [hident]
  exact mul_pos hfactor hdiff


/-! ### Corner angles from the cone's edge rays -/

/-- Unnormalised edge ray in the intersection of faces `i, j`. -/
def isoEdge12 (n₁ n₂ : V3) : V3 := cross n₁ n₂
def isoEdge13 (n₁ n₃ : V3) : V3 := pnSmul (-1) (cross n₁ n₃)
def isoEdge23 (n₂ n₃ : V3) : V3 := cross n₂ n₃

theorem unit_norm_one (a : V3) (h : dot a a = 1) : norm a = 1 := by
  rw [norm, h, Real.sqrt_one]

theorem dot_commV (a b : V3) : dot a b = dot b a := by
  unfold dot
  ring

theorem norm_pnSmul_neg (v : V3) : norm (pnSmul (-1) v) = norm v := by
  unfold norm
  congr 1
  unfold pnSmul dot
  ring

theorem dot_pnSmul_neg (a v : V3) : dot a (pnSmul (-1) v) = - dot a v := by
  unfold pnSmul dot
  ring

theorem dot_pnSmul_neg_left (v a : V3) : dot (pnSmul (-1) v) a = - dot v a := by
  unfold pnSmul dot
  ring

theorem norm_cross_unit (a b : V3) (p : ℝ)
    (ha : dot a a = 1) (hb : dot b b = 1) (hab : dot a b = p) :
    norm (cross a b) = Real.sqrt (1 - p ^ 2) := by
  unfold norm
  rw [cross_sq_of_unit a b ha hb hab]

/-- The apex-face corner angle is `arccos ((p²-q)/(1-p²))`. -/
theorem iso_corner1_eq (n₁ n₂ n₃ : V3) {p q : ℝ}
    (h1 : dot n₁ n₁ = 1) (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1)
    (h12 : dot n₁ n₂ = p) (h13 : dot n₁ n₃ = p) (h23 : dot n₂ n₃ = q)
    (hqhi : q < 1) (hdet : 0 < 1 + q - 2 * p ^ 2) :
    cornerAngle (isoEdge12 n₁ n₂) (isoEdge13 n₁ n₃) =
      Real.arccos ((p ^ 2 - q) / (1 - p ^ 2)) := by
  have hp2 : p ^ 2 < 1 := by nlinarith [hdet, hqhi]
  have h1p2 : 0 < 1 - p ^ 2 := by linarith
  have hw := dot_cross_cross n₁ n₂ n₃
  rw [h12, h13, h1, h23] at hw
  unfold cornerAngle isoEdge12 isoEdge13
  rw [norm_pnSmul_neg, norm_cross_unit n₁ n₂ p h1 h2 h12,
    norm_cross_unit n₁ n₃ p h1 h3 h13]
  rw [dot_pnSmul_neg, hw]
  have hs : Real.sqrt (1 - p ^ 2) * Real.sqrt (1 - p ^ 2) = 1 - p ^ 2 := by
    rw [← pow_two, Real.sq_sqrt (le_of_lt h1p2)]
  rw [hs]
  congr 1
  field_simp [ne_of_gt h1p2]
  ring

/-- The two other corner angles are `arccos (p(q-1)/√((1-p²)(1-q²)))`. -/
theorem iso_corner2_eq (n₁ n₂ n₃ : V3) {p q : ℝ}
    (h1 : dot n₁ n₁ = 1) (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1)
    (h12 : dot n₁ n₂ = p) (h13 : dot n₁ n₃ = p) (h23 : dot n₂ n₃ = q)
    (hqhi : q < 1) (hdet : 0 < 1 + q - 2 * p ^ 2) :
    cornerAngle (isoEdge12 n₁ n₂) (isoEdge23 n₂ n₃) =
      Real.arccos (p * (q - 1) / Real.sqrt ((1 - p ^ 2) * (1 - q ^ 2))) ∧
    cornerAngle (isoEdge13 n₁ n₃) (isoEdge23 n₂ n₃) =
      Real.arccos (p * (q - 1) / Real.sqrt ((1 - p ^ 2) * (1 - q ^ 2))) := by
  have hqlo : -1 < q := by nlinarith [hdet, sq_nonneg p]
  have hp2 : p ^ 2 < 1 := by nlinarith [hdet, hqhi]
  have h1p2 : 0 < 1 - p ^ 2 := by linarith
  have h1q2 : 0 < 1 - q ^ 2 := by nlinarith
  have hRpos : 0 < (1 - p ^ 2) * (1 - q ^ 2) := mul_pos h1p2 h1q2
  have hmul : Real.sqrt (1 - p ^ 2) * Real.sqrt (1 - q ^ 2) =
      Real.sqrt ((1 - p ^ 2) * (1 - q ^ 2)) := by
    rw [Real.sqrt_mul (le_of_lt h1p2)]
  have hw12 := dot_cross_cross n₂ n₁ n₃
  rw [h13, h2, show dot n₂ n₁ = p by rw [dot_commV, h12], h23] at hw12
  have hw13 := dot_cross_cross n₃ n₁ n₂
  rw [h12, h3, show dot n₃ n₁ = p by rw [dot_commV, h13],
    show dot n₃ n₂ = q by rw [dot_commV, h23]] at hw13
  constructor
  · unfold cornerAngle isoEdge12 isoEdge23
    rw [norm_cross_unit n₁ n₂ p h1 h2 h12,
      norm_cross_unit n₂ n₃ q h2 h3 h23, hmul]
    rw [show dot (cross n₁ n₂) (cross n₂ n₃) = - dot (cross n₂ n₁) (cross n₂ n₃) by
      unfold dot cross; ring, hw12]
    congr 1
    ring
  · unfold cornerAngle isoEdge13 isoEdge23
    rw [norm_pnSmul_neg, norm_cross_unit n₁ n₃ p h1 h3 h13,
      norm_cross_unit n₂ n₃ q h2 h3 h23, hmul]
    rw [dot_pnSmul_neg_left]
    rw [show dot (cross n₁ n₃) (cross n₂ n₃) = dot (cross n₃ n₁) (cross n₃ n₂) by
      unfold dot cross; ring, hw13]
    congr 1
    ring

/-! ### The spherical law of cosines for the isosceles vertex figure -/

/-- For an isosceles spherical triangle with sides `a, b, b`, the base
    interior angle `B` and apex interior angle `A` satisfy
    `cos B = ((1-cos a)/sin a)(cos b/sin b)` and
    `cos A = (cos a - cos²b)/sin²b`. -/
theorem iso_cos_formulas (p q : ℝ) (hqhi : q < 1) (hdet : 0 < 1 + q - 2 * p ^ 2) :
    let a := Real.arccos ((p ^ 2 - q) / (1 - p ^ 2))
    let b := Real.arccos (p * (q - 1) / Real.sqrt ((1 - p ^ 2) * (1 - q ^ 2)))
    ((1 - Real.cos a) / Real.sin a) * (Real.cos b / Real.sin b) = -p ∧
    (Real.cos a - Real.cos b ^ 2) / Real.sin b ^ 2 = -q := by
  have hqlo : -1 < q := by nlinarith [hdet, sq_nonneg p]
  have hp2 : p ^ 2 < 1 := by nlinarith [hdet, hqhi]
  have h1p2 : 0 < 1 - p ^ 2 := by linarith
  have h1q2 : 0 < 1 - q ^ 2 := by nlinarith
  let R : ℝ := (1 - p ^ 2) * (1 - q ^ 2)
  have hRpos : 0 < R := by dsimp [R]; positivity
  let D : ℝ := (1 - q) * (1 + q - 2 * p ^ 2)
  have hDpos : 0 < D := by dsimp [D]; positivity
  let ca : ℝ := (p ^ 2 - q) / (1 - p ^ 2)
  let cb : ℝ := p * (q - 1) / Real.sqrt R
  have hcarange_lo : -1 < ca := by
    dsimp [ca]
    rw [lt_div_iff₀ h1p2]
    nlinarith
  have hcarange_hi : ca < 1 := by
    dsimp [ca]
    rw [div_lt_iff₀ h1p2]
    nlinarith
  have hcbrange_lo : -1 < cb := by
    dsimp [cb]
    have hs : 0 < Real.sqrt R := Real.sqrt_pos.2 hRpos
    rw [lt_div_iff₀ hs]
    have hsq : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt (le_of_lt hRpos)
    nlinarith
  have hcbrange_hi : cb < 1 := by
    dsimp [cb]
    have hs : 0 < Real.sqrt R := Real.sqrt_pos.2 hRpos
    rw [div_lt_iff₀ hs]
    have hsq : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt (le_of_lt hRpos)
    dsimp [R] at hsq
    nlinarith
  have hca_sq : 1 - ca ^ 2 = D / (1 - p ^ 2) ^ 2 := by
    dsimp [ca, D]
    field_simp [ne_of_gt h1p2]
    ring
  have hcb_sq : 1 - cb ^ 2 = D / R := by
    have hsR : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt (le_of_lt hRpos)
    dsimp [cb]
    rw [div_pow, hsR]
    dsimp [D, R]
    field_simp [ne_of_gt h1p2, ne_of_gt h1q2]
    ring
  have hsa_eq : Real.sqrt (1 - ca ^ 2) = Real.sqrt D / (1 - p ^ 2) := by
    rw [hca_sq, Real.sqrt_div (le_of_lt hDpos), Real.sqrt_sq (le_of_lt h1p2)]
  have hsb_eq : Real.sqrt (1 - cb ^ 2) = Real.sqrt D / Real.sqrt R := by
    rw [hcb_sq, Real.sqrt_div (le_of_lt hDpos)]
  have hcosB : ((1 - ca) / (Real.sqrt (1 - ca ^ 2))) *
        (cb / (Real.sqrt (1 - cb ^ 2))) = -p := by
    rw [hsa_eq, hsb_eq]
    dsimp [ca, cb]
    field_simp [ne_of_gt hDpos, ne_of_gt hRpos, ne_of_gt (Real.sqrt_pos.2 hDpos),
      ne_of_gt (Real.sqrt_pos.2 hRpos), ne_of_gt h1p2]
    have hsD : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt (le_of_lt hDpos)
    rw [hsD]
    dsimp [D]
    ring_nf
  have hcosA : (ca - cb ^ 2) / (1 - cb ^ 2) = -q := by
    have hcb2 : cb ^ 2 = 1 - D / R := by linarith [hcb_sq]
    have hnum : ca - cb ^ 2 = -q * (1 - cb ^ 2) := by
      rw [hcb2]
      dsimp [ca, D, R]
      field_simp [ne_of_gt h1p2, ne_of_gt h1q2]
      ring
    have hdenne : 1 - cb ^ 2 ≠ 0 := by
      rw [hcb_sq]
      exact ne_of_gt (div_pos hDpos hRpos)
    rw [hnum]
    field_simp [hdenne]
  dsimp
  rw [Real.cos_arccos hcarange_lo.le hcarange_hi.le,
    Real.cos_arccos hcbrange_lo.le hcbrange_hi.le,
    Real.sin_arccos, Real.sin_arccos]
  have hsinb_sq : Real.sqrt (1 - cb ^ 2) ^ 2 = 1 - cb ^ 2 :=
    Real.sq_sqrt (by rw [hcb_sq]; exact le_of_lt (div_pos hDpos hRpos))
  rw [hsinb_sq]
  exact ⟨hcosB, hcosA⟩

/-! ### Bounds on the two corner angles -/

/-- For `a = arccos((p²-q)/(1-p²))`, `b = arccos(p(q-1)/√((1-p²)(1-q²)))`
    one has `0 < a < π`, `0 < b < π` and `a < 2b`. -/
theorem iso_angle_bounds (p q : ℝ) (hqhi : q < 1) (hdet : 0 < 1 + q - 2 * p ^ 2) :
    let a := Real.arccos ((p ^ 2 - q) / (1 - p ^ 2))
    let b := Real.arccos (p * (q - 1) / Real.sqrt ((1 - p ^ 2) * (1 - q ^ 2)))
    0 < a ∧ a < Real.pi ∧ 0 < b ∧ b < Real.pi ∧ a < 2 * b := by
  have hqlo : -1 < q := by nlinarith [hdet, sq_nonneg p]
  have hp2 : p ^ 2 < 1 := by nlinarith [hdet, hqhi]
  have h1p2 : 0 < 1 - p ^ 2 := by linarith
  have h1q2 : 0 < 1 - q ^ 2 := by nlinarith
  have hRpos : 0 < (1 - p ^ 2) * (1 - q ^ 2) := mul_pos h1p2 h1q2
  have hspos : 0 < Real.sqrt ((1 - p ^ 2) * (1 - q ^ 2)) := Real.sqrt_pos.2 hRpos
  let a := Real.arccos ((p ^ 2 - q) / (1 - p ^ 2))
  let b := Real.arccos (p * (q - 1) / Real.sqrt ((1 - p ^ 2) * (1 - q ^ 2)))
  have ha0 : 0 < a := by
    dsimp [a]
    exact Real.arccos_pos.mpr (by
      rw [div_lt_one h1p2]
      nlinarith)
  have hap : a < Real.pi := by
    dsimp [a]
    exact Real.arccos_lt_pi.mpr (by
      rw [lt_div_iff₀ h1p2]
      nlinarith)
  have hb0 : 0 < b := by
    dsimp [b]
    exact Real.arccos_pos.mpr (by
      rw [div_lt_one hspos]
      have hs : (Real.sqrt ((1 - p ^ 2) * (1 - q ^ 2))) ^ 2 =
          (1 - p ^ 2) * (1 - q ^ 2) := Real.sq_sqrt (le_of_lt hRpos)
      nlinarith)
  have hbp : b < Real.pi := by
    dsimp [b]
    exact Real.arccos_lt_pi.mpr (by
      rw [lt_div_iff₀ hspos]
      have hs : (Real.sqrt ((1 - p ^ 2) * (1 - q ^ 2))) ^ 2 =
          (1 - p ^ 2) * (1 - q ^ 2) := Real.sq_sqrt (le_of_lt hRpos)
      nlinarith)
  have hca : Real.cos a = (p ^ 2 - q) / (1 - p ^ 2) := by
    dsimp [a]
    exact Real.cos_arccos (by rw [le_div_iff₀ h1p2]; nlinarith)
      (by rw [div_le_iff₀ h1p2]; nlinarith)
  have hcb : Real.cos b = p * (q - 1) / Real.sqrt ((1 - p ^ 2) * (1 - q ^ 2)) := by
    dsimp [b]
    exact Real.cos_arccos (by
      rw [le_div_iff₀ hspos]
      have hs : (Real.sqrt ((1 - p ^ 2) * (1 - q ^ 2))) ^ 2 =
          (1 - p ^ 2) * (1 - q ^ 2) := Real.sq_sqrt (le_of_lt hRpos)
      nlinarith) (by
      rw [div_le_iff₀ hspos]
      have hs : (Real.sqrt ((1 - p ^ 2) * (1 - q ^ 2))) ^ 2 =
          (1 - p ^ 2) * (1 - q ^ 2) := Real.sq_sqrt (le_of_lt hRpos)
      nlinarith)
  have hcosgap : Real.cos (2 * b) < Real.cos a := by
    rw [Real.cos_two_mul, hcb, hca]
    have hs : (Real.sqrt ((1 - p ^ 2) * (1 - q ^ 2))) ^ 2 =
        (1 - p ^ 2) * (1 - q ^ 2) := Real.sq_sqrt (le_of_lt hRpos)
    have hcb_sq' : (p * (q - 1) / Real.sqrt ((1 - p ^ 2) * (1 - q ^ 2))) ^ 2 =
        p ^ 2 * (q - 1) ^ 2 / ((1 - p ^ 2) * (1 - q ^ 2)) := by
      rw [div_pow, hs]
      ring
    rw [hcb_sq']
    field_simp [ne_of_gt h1p2, ne_of_gt h1q2]
    have hprod : 0 < (1 - q) ^ 2 * (1 + q - 2 * p ^ 2) :=
      mul_pos (sq_pos_of_ne_zero (by linarith : 1 - q ≠ 0)) hdet
    nlinarith
  have hab : a < 2 * b := by
    by_contra hnot
    have hle : 2 * b ≤ a := le_of_not_gt hnot
    have hcosle : Real.cos a ≤ Real.cos (2 * b) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hb0]) (le_of_lt hap) hle
    linarith
  dsimp [a, b]
  exact ⟨ha0, hap, hb0, hbp, hab⟩

/-! ### The three-face (isosceles) theorem -/

/-- **Geometric seam (S) for an isosceles trihedral vertex**: for three
    unit outward normals with `⟪n₁,n₂⟫ = ⟪n₁,n₃⟫ = p`, `⟪n₂,n₃⟫ = q` and
    a nondegenerate cone (`triple ≠ 0`), the angle-weighted sum pairs
    strictly positively with every face normal. -/
theorem iso_three_face_face_pos (n₁ n₂ n₃ : V3) {p q : ℝ}
    (h1 : dot n₁ n₁ = 1) (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1)
    (h12 : dot n₁ n₂ = p) (h13 : dot n₁ n₃ = p) (h23 : dot n₂ n₃ = q)
    (htriple : triple n₁ n₂ n₃ ≠ 0) :
    let θ₁ := cornerAngle (isoEdge12 n₁ n₂) (isoEdge13 n₁ n₃)
    let θ₂ := cornerAngle (isoEdge12 n₁ n₂) (isoEdge23 n₂ n₃)
    let θ₃ := cornerAngle (isoEdge13 n₁ n₃) (isoEdge23 n₂ n₃)
    0 < θ₁ * dot n₁ n₁ + θ₂ * dot n₂ n₁ + θ₃ * dot n₃ n₁ ∧
    0 < θ₁ * dot n₁ n₂ + θ₂ * dot n₂ n₂ + θ₃ * dot n₃ n₂ ∧
    0 < θ₁ * dot n₁ n₃ + θ₂ * dot n₂ n₃ + θ₃ * dot n₃ n₃ := by
  have hsq := triple_sq_isosceles n₁ n₂ n₃ h1 h2 h3 h12 h13 h23
  have hqle : q ≤ 1 := by
    have hcs := V3.dot_abs_le n₂ n₃
    rw [h23, unit_norm_one n₂ h2, unit_norm_one n₃ h3] at hcs
    have hcs' : |q| ≤ 1 := by simpa using hcs
    exact le_trans (le_abs_self q) hcs'
  have hqhi : q < 1 := by
    exact lt_of_le_of_ne hqle (by intro h; rw [h] at hsq; nlinarith [sq_pos_of_ne_zero htriple])
  have hdetpos : 0 < 1 + q - 2 * p ^ 2 := by
    have hsqpos : 0 < (triple n₁ n₂ n₃) ^ 2 := sq_pos_of_ne_zero htriple
    rw [hsq] at hsqpos
    nlinarith [mul_pos (by linarith : 0 < 1 - q) hsqpos]
  let a := Real.arccos ((p ^ 2 - q) / (1 - p ^ 2))
  let b := Real.arccos (p * (q - 1) / Real.sqrt ((1 - p ^ 2) * (1 - q ^ 2)))
  have hca := iso_corner1_eq n₁ n₂ n₃ h1 h2 h3 h12 h13 h23 hqhi hdetpos
  have hcb := iso_corner2_eq n₁ n₂ n₃ h1 h2 h3 h12 h13 h23 hqhi hdetpos
  have hform := iso_cos_formulas p q hqhi hdetpos
  dsimp [a, b] at hform
  have hbnds := iso_angle_bounds p q hqhi hdetpos
  dsimp [a, b] at hbnds
  have hf1 := iso_face1_pos a b hbnds.1 hbnds.2.1 hbnds.2.2.1 hbnds.2.2.2.1 hbnds.2.2.2.2
  have hf2 := iso_face2_pos a b hbnds.1 hbnds.2.1 hbnds.2.2.1 hbnds.2.2.2.1 hbnds.2.2.2.2
  have hcosB : ((1 - Real.cos a) / Real.sin a) * (Real.cos b / Real.sin b) = -p := hform.1
  have hcosA : (Real.cos a - Real.cos b ^ 2) / Real.sin b ^ 2 = -q := hform.2
  have h21 : dot n₂ n₁ = p := by rw [dot_commV, h12]
  have h31 : dot n₃ n₁ = p := by rw [dot_commV, h13]
  have h32 : dot n₃ n₂ = q := by rw [dot_commV, h23]
  dsimp
  rw [hca, hcb.1, hcb.2, h12, h21, h13, h31, h23, h32, h1, h2, h3]
  constructor
  · nlinarith [hf1, hcosB]
  constructor
  · nlinarith [hf2, hcosA, hcosB]
  · nlinarith [hf2, hcosA, hcosB]


/-- The exact `(S)` shape for an isosceles trihedral vertex: with the three
    geometric corner angles indexed by `Fin 3`, the weighted sum is positive
    against every face normal. -/
theorem iso_three_face_S (n₁ n₂ n₃ : V3) {p q : ℝ}
    (h1 : dot n₁ n₁ = 1) (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1)
    (h12 : dot n₁ n₂ = p) (h13 : dot n₁ n₃ = p) (h23 : dot n₂ n₃ = q)
    (htriple : triple n₁ n₂ n₃ ≠ 0) :
    let v : Fin 3 → V3 := fun i => if i = 0 then n₁ else if i = 1 then n₂ else n₃
    let θ : Fin 3 → ℝ := fun i =>
      if i = 0 then cornerAngle (isoEdge12 n₁ n₂) (isoEdge13 n₁ n₃)
      else if i = 1 then cornerAngle (isoEdge12 n₁ n₂) (isoEdge23 n₂ n₃)
      else cornerAngle (isoEdge13 n₁ n₃) (isoEdge23 n₂ n₃)
    ∀ j : Fin 3, 0 < ∑ i : Fin 3, θ i * dot (v i) (v j) := by
  have h := iso_three_face_face_pos n₁ n₂ n₃ h1 h2 h3 h12 h13 h23 htriple
  dsimp at h
  rcases h with ⟨hA, hB, hC⟩
  dsimp
  intro j
  fin_cases j
  · simpa [Fin.sum_univ_three] using hA
  · simpa [Fin.sum_univ_three] using hB
  · simpa [Fin.sum_univ_three] using hC

/-- F16 apex, instantiated: `p = -2/3`, `q = 1/9`.  The general isosceles
    theorem above covers this obtuse vertex (two acute dihedrals, one
    obtuse), independently of the hand-proved `arccos` comparison in
    `Vdb/AnglePseudoNormal.lean`. -/
theorem f16_isosceles_face_pos :
    let θ₁ := cornerAngle (isoEdge12 pnN1 pnN2) (isoEdge13 pnN1 pnN3)
    let θ₂ := cornerAngle (isoEdge12 pnN1 pnN2) (isoEdge23 pnN2 pnN3)
    let θ₃ := cornerAngle (isoEdge13 pnN1 pnN3) (isoEdge23 pnN2 pnN3)
    0 < θ₁ * dot pnN1 pnN1 + θ₂ * dot pnN2 pnN1 + θ₃ * dot pnN3 pnN1 ∧
    0 < θ₁ * dot pnN1 pnN2 + θ₂ * dot pnN2 pnN2 + θ₃ * dot pnN3 pnN2 ∧
    0 < θ₁ * dot pnN1 pnN3 + θ₂ * dot pnN2 pnN3 + θ₃ * dot pnN3 pnN3 := by
  have h12 : dot pnN1 pnN2 = (-2 / 3 : ℝ) := by norm_num [pnN1, pnN2, dot]
  have h13 : dot pnN1 pnN3 = (-2 / 3 : ℝ) := by norm_num [pnN1, pnN3, dot]
  have h23 : dot pnN2 pnN3 = (1 / 9 : ℝ) := by norm_num [pnN2, pnN3, dot]
  have htr : triple pnN1 pnN2 pnN3 ≠ 0 := by
    rw [← dot_cross_eq_triple]
    norm_num [pnN1, pnN2, pnN3, dot, cross]
  exact iso_three_face_face_pos pnN1 pnN2 pnN3 pnN1_unit pnN2_unit pnN3_unit
    h12 h13 h23 htr

/-! ### General (non-isosceles) trihedral vertex

Everything above assumed `⟪n₁,n₂⟫ = ⟪n₁,n₃⟫ = p`.  This section removes that
restriction: the pairwise dots are independent reals `p = ⟪n₁,n₂⟫`,
`r = ⟪n₁,n₃⟫`, `q = ⟪n₂,n₃⟫`.  We prove the algebraic half of the geometric
seam for this general case — the Gram determinant and the three geometric corner
angles as explicit functions of `(p,r,q)` — and reduce (S) to a single named
*spherical projection inequality* about those three angles.  The inequality is
discharged for the isosceles slice `p = r` by the machinery above; proving it
for `p ≠ r` is the remaining gap (recorded in the final comment block). -/

/-- The Gram determinant of three unit vectors with pairwise dots `p, r, q`
    (in the order `⟪n₁,n₂⟫ = p`, `⟪n₁,n₃⟫ = r`, `⟪n₂,n₃⟫ = q`) is
    `1 + 2p·r·q − p² − r² − q²`, and equals the squared triple product. -/
theorem triple_sq_general (n₁ n₂ n₃ : V3) {p r q : ℝ}
    (h1 : dot n₁ n₁ = 1) (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1)
    (h12 : dot n₁ n₂ = p) (h13 : dot n₁ n₃ = r) (h23 : dot n₂ n₃ = q) :
    (triple n₁ n₂ n₃) ^ 2 = 1 + 2 * p * r * q - p ^ 2 - r ^ 2 - q ^ 2 := by
  have hpoly : (triple n₁ n₂ n₃) ^ 2 =
      dot n₁ n₁ * dot n₂ n₂ * dot n₃ n₃
        + 2 * dot n₁ n₂ * dot n₁ n₃ * dot n₂ n₃
        - dot n₁ n₁ * (dot n₂ n₃) ^ 2
        - dot n₂ n₂ * (dot n₁ n₃) ^ 2
        - dot n₃ n₃ * (dot n₁ n₂) ^ 2 := by
    rw [← dot_cross_eq_triple]
    unfold dot cross
    ring
  rw [hpoly, h1, h2, h3, h12, h13, h23]
  ring

/-- The three geometric corner angles of a trihedral vertex with pairwise dots
    `(p, r, q)`, as functions of the dots.  These are exactly the side lengths
    of the spherical vertex figure; `triSideA` is the angle at the face spanned
    by `n₁` (between edges `12` and `13`), etc. -/
noncomputable def triSideA (p r q : ℝ) : ℝ :=
  Real.arccos ((p * r - q) / Real.sqrt ((1 - p ^ 2) * (1 - r ^ 2)))
noncomputable def triSideB (p r q : ℝ) : ℝ :=
  Real.arccos ((p * q - r) / Real.sqrt ((1 - p ^ 2) * (1 - q ^ 2)))
noncomputable def triSideC (p r q : ℝ) : ℝ :=
  Real.arccos ((r * q - p) / Real.sqrt ((1 - r ^ 2) * (1 - q ^ 2)))

/-- The apex corner angle (edges `12`, `13`) is `triSideA p r q`. -/
theorem corner12_13_eq (n₁ n₂ n₃ : V3) {p r q : ℝ}
    (h1 : dot n₁ n₁ = 1) (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1)
    (h12 : dot n₁ n₂ = p) (h13 : dot n₁ n₃ = r) (h23 : dot n₂ n₃ = q)
    (hp2 : p ^ 2 < 1) (hr2 : r ^ 2 < 1) :
    cornerAngle (isoEdge12 n₁ n₂) (isoEdge13 n₁ n₃) = triSideA p r q := by
  have h1p2 : 0 < 1 - p ^ 2 := by linarith
  have h1r2 : 0 < 1 - r ^ 2 := by linarith
  have h12n : 0 < dot (cross n₁ n₂) (cross n₁ n₂) := by
    rw [cross_sq_of_unit n₁ n₂ h1 h2 h12]; linarith
  have h13n : 0 < dot (cross n₁ n₃) (cross n₁ n₃) := by
    rw [cross_sq_of_unit n₁ n₃ h1 h3 h13]; linarith
  have hn12 : norm (cross n₁ n₂) = Real.sqrt (1 - p ^ 2) :=
    norm_cross_unit n₁ n₂ p h1 h2 h12
  have hn13 : norm (cross n₁ n₃) = Real.sqrt (1 - r ^ 2) :=
    norm_cross_unit n₁ n₃ r h1 h3 h13
  have hw := dot_cross_cross n₁ n₂ n₃
  rw [h12, h13, h1, h23] at hw
  unfold cornerAngle isoEdge12 isoEdge13 triSideA
  rw [norm_pnSmul_neg, hn12, hn13, dot_pnSmul_neg, hw]
  rw [Real.sqrt_mul (le_of_lt h1p2)]
  congr 1
  ring

/-- The corner angle at edges `12`, `23` is `triSideB p r q`. -/
theorem corner12_23_eq (n₁ n₂ n₃ : V3) {p r q : ℝ}
    (h1 : dot n₁ n₁ = 1) (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1)
    (h12 : dot n₁ n₂ = p) (h13 : dot n₁ n₃ = r) (h23 : dot n₂ n₃ = q)
    (hp2 : p ^ 2 < 1) (hq2 : q ^ 2 < 1) :
    cornerAngle (isoEdge12 n₁ n₂) (isoEdge23 n₂ n₃) = triSideB p r q := by
  have h1p2 : 0 < 1 - p ^ 2 := by linarith
  have h1q2 : 0 < 1 - q ^ 2 := by linarith
  have hn12 : norm (cross n₁ n₂) = Real.sqrt (1 - p ^ 2) :=
    norm_cross_unit n₁ n₂ p h1 h2 h12
  have hn23 : norm (cross n₂ n₃) = Real.sqrt (1 - q ^ 2) :=
    norm_cross_unit n₂ n₃ q h2 h3 h23
  have hw := dot_cross_cross n₂ n₁ n₃
  rw [h13, h2, show dot n₂ n₁ = p by rw [dot_commV, h12], h23] at hw
  unfold cornerAngle isoEdge12 isoEdge23 triSideB
  rw [hn12, hn23]
  rw [show dot (cross n₁ n₂) (cross n₂ n₃) = - dot (cross n₂ n₁) (cross n₂ n₃) by
    unfold dot cross; ring, hw]
  rw [Real.sqrt_mul (le_of_lt h1p2)]
  congr 1
  ring

/-- The corner angle at edges `13`, `23` is `triSideC p r q`. -/
theorem corner13_23_eq (n₁ n₂ n₃ : V3) {p r q : ℝ}
    (h1 : dot n₁ n₁ = 1) (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1)
    (h12 : dot n₁ n₂ = p) (h13 : dot n₁ n₃ = r) (h23 : dot n₂ n₃ = q)
    (hr2 : r ^ 2 < 1) (hq2 : q ^ 2 < 1) :
    cornerAngle (isoEdge13 n₁ n₃) (isoEdge23 n₂ n₃) = triSideC p r q := by
  have h1r2 : 0 < 1 - r ^ 2 := by linarith
  have h1q2 : 0 < 1 - q ^ 2 := by linarith
  have hn13 : norm (cross n₁ n₃) = Real.sqrt (1 - r ^ 2) :=
    norm_cross_unit n₁ n₃ r h1 h3 h13
  have hn23 : norm (cross n₂ n₃) = Real.sqrt (1 - q ^ 2) :=
    norm_cross_unit n₂ n₃ q h2 h3 h23
  have hw := dot_cross_cross n₃ n₁ n₂
  rw [h12, h3, show dot n₃ n₁ = r by rw [dot_commV, h13],
    show dot n₃ n₂ = q by rw [dot_commV, h23]] at hw
  unfold cornerAngle isoEdge13 isoEdge23 triSideC
  rw [norm_pnSmul_neg, hn13, hn23, dot_pnSmul_neg_left]
  rw [show dot (cross n₁ n₃) (cross n₂ n₃) = dot (cross n₃ n₁) (cross n₃ n₂) by
    unfold dot cross; ring, hw]
  rw [Real.sqrt_mul (le_of_lt h1r2)]
  congr 1
  ring

/-- The spherical projection inequality: each side of the spherical vertex
    figure strictly exceeds the sum of the projections of the other two onto
    it.  This is exactly the remaining hard step of (S) for a non-isosceles
    trihedron; `p = ⟪n₁,n₂⟫`, `r = ⟪n₁,n₃⟫`, `q = ⟪n₂,n₃⟫`. -/
def sphericalProj (p r q : ℝ) : Prop :=
  triSideA p r q > triSideB p r q * (-p) + triSideC p r q * (-r) ∧
  triSideB p r q > triSideA p r q * (-p) + triSideC p r q * (-q) ∧
  triSideC p r q > triSideA p r q * (-r) + triSideB p r q * (-q)

/-- For a nondegenerate trihedral vertex all three pairwise dots have square
    strictly less than one (Cauchy–Schwarz is strict: equality would make two
    faces parallel and collapse the triple product). -/
theorem dots_sq_lt_one (n₁ n₂ n₃ : V3) {p r q : ℝ}
    (h1 : dot n₁ n₁ = 1) (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1)
    (h12 : dot n₁ n₂ = p) (h13 : dot n₁ n₃ = r) (h23 : dot n₂ n₃ = q)
    (htriple : triple n₁ n₂ n₃ ≠ 0) :
    p ^ 2 < 1 ∧ r ^ 2 < 1 ∧ q ^ 2 < 1 := by
  have hsq := triple_sq_general n₁ n₂ n₃ h1 h2 h3 h12 h13 h23
  have hpos : 0 < 1 + 2 * p * r * q - p ^ 2 - r ^ 2 - q ^ 2 := by
    have : 0 < (triple n₁ n₂ n₃) ^ 2 := sq_pos_of_ne_zero htriple
    nlinarith
  have hn1 : norm n₁ = 1 := unit_norm_one n₁ h1
  have hn2 : norm n₂ = 1 := unit_norm_one n₂ h2
  have hn3 : norm n₃ = 1 := unit_norm_one n₃ h3
  have hsolve {a b : V3} (ha : norm a = 1) (hb : norm b = 1)
      {s : ℝ} (hab : dot a b = s) : s ^ 2 ≤ 1 := by
    have hcs := dot_abs_le a b
    rw [hab, ha, hb] at hcs
    norm_num at hcs
    have hcs' : |s| ≤ |(1 : ℝ)| := by simpa using hcs
    nlinarith [sq_le_sq.mpr hcs']
  have hp_le := hsolve hn1 hn2 h12
  have hr_le := hsolve hn1 hn3 h13
  have hq_le := hsolve hn2 hn3 h23
  constructor
  · by_contra hnot
    have hp_eq : p ^ 2 = 1 := by nlinarith
    nlinarith [sq_nonneg (r - p * q)]
  constructor
  · by_contra hnot
    have hr_eq : r ^ 2 = 1 := by nlinarith
    nlinarith [sq_nonneg (p - r * q)]
  · by_contra hnot
    have hq_eq : q ^ 2 = 1 := by nlinarith
    nlinarith [sq_nonneg (p - q * r)]

/-- **Geometric seam (S) for an arbitrary (non-isosceles) trihedral vertex**,
    reduced to the spherical projection inequality.  For three unit outward
    normals with arbitrary pairwise dots and a nonzero triple product, if the
    spherical projection inequality `sphericalProj p r q` holds, then the
    angle-weighted sum pairs strictly positively with every face normal. -/
theorem three_face_face_pos_of_spherical (n₁ n₂ n₃ : V3) {p r q : ℝ}
    (h1 : dot n₁ n₁ = 1) (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1)
    (h12 : dot n₁ n₂ = p) (h13 : dot n₁ n₃ = r) (h23 : dot n₂ n₃ = q)
    (htriple : triple n₁ n₂ n₃ ≠ 0)
    (hsph : sphericalProj p r q) :
    let θ₁ := cornerAngle (isoEdge12 n₁ n₂) (isoEdge13 n₁ n₃)
    let θ₂ := cornerAngle (isoEdge12 n₁ n₂) (isoEdge23 n₂ n₃)
    let θ₃ := cornerAngle (isoEdge13 n₁ n₃) (isoEdge23 n₂ n₃)
    0 < θ₁ * dot n₁ n₁ + θ₂ * dot n₂ n₁ + θ₃ * dot n₃ n₁ ∧
    0 < θ₁ * dot n₁ n₂ + θ₂ * dot n₂ n₂ + θ₃ * dot n₃ n₂ ∧
    0 < θ₁ * dot n₁ n₃ + θ₂ * dot n₂ n₃ + θ₃ * dot n₃ n₃ := by
  have hlt := dots_sq_lt_one n₁ n₂ n₃ h1 h2 h3 h12 h13 h23 htriple
  have hc1 := corner12_13_eq n₁ n₂ n₃ h1 h2 h3 h12 h13 h23 hlt.1 hlt.2.1
  have hc2 := corner12_23_eq n₁ n₂ n₃ h1 h2 h3 h12 h13 h23 hlt.1 hlt.2.2
  have hc3 := corner13_23_eq n₁ n₂ n₃ h1 h2 h3 h12 h13 h23 hlt.2.1 hlt.2.2
  have h21 : dot n₂ n₁ = p := by rw [dot_commV, h12]
  have h31 : dot n₃ n₁ = r := by rw [dot_commV, h13]
  have h32 : dot n₃ n₂ = q := by rw [dot_commV, h23]
  dsimp
  rw [hc1, hc2, hc3, h1, h2, h3, h12, h21, h13, h31, h23, h32]
  dsimp [sphericalProj] at hsph
  constructor
  · nlinarith [hsph.1]
  constructor
  · nlinarith [hsph.2.1]
  · nlinarith [hsph.2.2]

/-- The spherical projection inequality holds on the isosceles slice `p = r`.
    This re-derives the landed isosceles theorem through the general reduction
    above, and shows the new seam is a faithful abstraction. -/
theorem sphericalProj_isosceles (p q : ℝ) (hqhi : q < 1) (hdet : 0 < 1 + q - 2 * p ^ 2) :
    sphericalProj p p q := by
  have hp2 : p ^ 2 < 1 := by nlinarith [hdet, hqhi]
  have h1p2 : 0 < 1 - p ^ 2 := by linarith
  let a : ℝ := Real.arccos ((p ^ 2 - q) / (1 - p ^ 2))
  let b : ℝ := Real.arccos (p * (q - 1) / Real.sqrt ((1 - p ^ 2) * (1 - q ^ 2)))
  have hbnds := iso_angle_bounds p q hqhi hdet
  dsimp [a, b] at hbnds
  have hform := iso_cos_formulas p q hqhi hdet
  dsimp [a, b] at hform
  have hf1 := iso_face1_pos a b hbnds.1 hbnds.2.1 hbnds.2.2.1 hbnds.2.2.2.1 hbnds.2.2.2.2
  have hf2 := iso_face2_pos a b hbnds.1 hbnds.2.1 hbnds.2.2.1 hbnds.2.2.2.1 hbnds.2.2.2.2
  have hs : Real.sqrt ((1 - p ^ 2) * (1 - p ^ 2)) = 1 - p ^ 2 := by
    rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_pos h1p2]
  have hcb : p * q - p = p * (q - 1) := by ring
  have hpp : p * p = p ^ 2 := by ring
  dsimp [sphericalProj, triSideA, triSideB, triSideC]
  rw [hs, hcb, hpp]
  dsimp [a, b] at hf1 hf2 hform
  constructor
  · nlinarith [hf1, hform.1]
  constructor
  · nlinarith [hf2, hform.1, hform.2]
  · nlinarith [hf2, hform.1, hform.2]

/-- The full (S) shape for an arbitrary trihedral vertex, conditional on the
    spherical projection inequality.  This is the general non-isosceles
    statement modulo its single remaining hypothesis. -/
theorem three_face_S_of_spherical (n₁ n₂ n₃ : V3) {p r q : ℝ}
    (h1 : dot n₁ n₁ = 1) (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1)
    (h12 : dot n₁ n₂ = p) (h13 : dot n₁ n₃ = r) (h23 : dot n₂ n₃ = q)
    (htriple : triple n₁ n₂ n₃ ≠ 0)
    (hsph : sphericalProj p r q) :
    let v : Fin 3 → V3 := fun i => if i = 0 then n₁ else if i = 1 then n₂ else n₃
    let θ : Fin 3 → ℝ := fun i =>
      if i = 0 then cornerAngle (isoEdge12 n₁ n₂) (isoEdge13 n₁ n₃)
      else if i = 1 then cornerAngle (isoEdge12 n₁ n₂) (isoEdge23 n₂ n₃)
      else cornerAngle (isoEdge13 n₁ n₃) (isoEdge23 n₂ n₃)
    ∀ j : Fin 3, 0 < ∑ i : Fin 3, θ i * dot (v i) (v j) := by
  have h := three_face_face_pos_of_spherical n₁ n₂ n₃ h1 h2 h3 h12 h13 h23 htriple hsph
  dsimp at h
  rcases h with ⟨hA, hB, hC⟩
  dsimp
  intro j
  fin_cases j
  · simpa [Fin.sum_univ_three] using hA
  · simpa [Fin.sum_univ_three] using hB
  · simpa [Fin.sum_univ_three] using hC


set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

/-! Derivative of the three sides with respect to the third dot. -/

lemma hasDerivAt_triSideA (p r q : ℝ) (hp : p^2 < 1) (hr : r^2 < 1)
    (hΔ : 0 < 1 + 2*p*r*q - p^2 - r^2 - q^2) :
    HasDerivAt (fun x : ℝ => triSideA p r x)
      (1 / sqrt (1 + 2*p*r*q - p^2 - r^2 - q^2)) q := by
  have hA2 : 0 < 1 - p^2 := by linarith
  have hB2 : 0 < 1 - r^2 := by linarith
  have hA : 0 < sqrt (1-p^2) := Real.sqrt_pos.2 hA2
  have hB : 0 < sqrt (1-r^2) := Real.sqrt_pos.2 hB2
  have hABpos : 0 < sqrt (1-p^2) * sqrt (1-r^2) := mul_pos hA hB
  have hsqA : (sqrt (1-p^2))^2 = 1-p^2 := Real.sq_sqrt (le_of_lt hA2)
  have hsqB : (sqrt (1-r^2))^2 = 1-r^2 := Real.sq_sqrt (le_of_lt hB2)
  let AB : ℝ := sqrt (1-p^2) * sqrt (1-r^2)
  have hone : 1 - ((p*r - q)/AB)^2 = (1 + 2*p*r*q - p^2 - r^2 - q^2)/((1-p^2)*(1-r^2)) := by
    dsimp [AB]
    rw [div_pow]
    field_simp [ne_of_gt hA2, ne_of_gt hB2, hsqA, hsqB]
    simp only [hsqA, hsqB]
    ring_nf
  have hu_ne : (p*r - q)/AB ≠ 1 ∧ (p*r - q)/AB ≠ -1 := by
    constructor <;> intro h
    · have hs : ((p*r-q)/AB)^2 = 1 := by rw [h]; norm_num
      have hz : 1 - ((p*r-q)/AB)^2 = 0 := by rw [hs]; norm_num
      rw [hone] at hz
      have hf : 0 < (1+2*p*r*q-p^2-r^2-q^2)/((1-p^2)*(1-r^2)) := by positivity
      nlinarith
    · have hs : ((p*r-q)/AB)^2 = 1 := by rw [h]; norm_num
      have hz : 1 - ((p*r-q)/AB)^2 = 0 := by rw [hs]; norm_num
      rw [hone] at hz
      have hf : 0 < (1+2*p*r*q-p^2-r^2-q^2)/((1-p^2)*(1-r^2)) := by positivity
      nlinarith
  have hder := (Real.hasDerivAt_arccos hu_ne.2 hu_ne.1).comp q
    (((hasDerivAt_const (x := q) (c := p*r)).sub (hasDerivAt_id q)).div_const AB)
  unfold triSideA
  dsimp [AB] at hder ⊢
  convert hder using 1
  · ext x
    rw [Real.sqrt_mul (le_of_lt hA2)]
    rfl
  · rw [hone, Real.sqrt_div (le_of_lt hΔ)]
    rw [Real.sqrt_mul (le_of_lt hA2)]
    field_simp [ne_of_gt hABpos, ne_of_gt (Real.sqrt_pos.2 hΔ)]
    norm_num

lemma hasDerivAt_triSideB (p r q : ℝ) (hp : p^2 < 1) (hq : q^2 < 1)
    (hΔ : 0 < 1 + 2*p*r*q - p^2 - r^2 - q^2) :
    HasDerivAt (fun x : ℝ => triSideB p r x)
      ((r*q - p)/((1-q^2) * sqrt (1 + 2*p*r*q - p^2 - r^2 - q^2))) q := by
  have hA2 : 0 < 1 - p^2 := by linarith
  have hQ2 : 0 < 1 - q^2 := by linarith
  have hA : 0 < sqrt (1-p^2) := Real.sqrt_pos.2 hA2
  have hQ : 0 < sqrt (1-q^2) := Real.sqrt_pos.2 hQ2
  have hD : 0 < sqrt (1 + 2*p*r*q - p^2 - r^2 - q^2) := Real.sqrt_pos.2 hΔ
  have hsqA : (sqrt (1-p^2))^2 = 1-p^2 := Real.sq_sqrt (le_of_lt hA2)
  have hsqQ : (sqrt (1-q^2))^2 = 1-q^2 := Real.sq_sqrt (le_of_lt hQ2)
  let A : ℝ := sqrt (1-p^2)
  let Q : ℝ := sqrt (1-q^2)
  have h1 : HasDerivAt (fun x : ℝ => 1 - x^2) (-2*q) q := by
    have hh := (hasDerivAt_const (x := q) (c := (1:ℝ))).sub ((hasDerivAt_id q).pow 2)
    convert hh using 1
    · ext x <;> simp [id]
    · simp [id]
  have hsqrt : HasDerivAt (fun x : ℝ => sqrt (1-x^2)) (-q/Q) q := by
    have hs := (Real.hasDerivAt_sqrt (show 1-q^2 ≠ 0 by positivity)).comp q h1
    convert hs using 1
    · ext x; rfl
    · field_simp [Q, ne_of_gt hQ] <;> ring
  have hnum : HasDerivAt (fun x : ℝ => p*x - r) p q := by
    have hh := ((hasDerivAt_const (x := q) (c := p)).mul (hasDerivAt_id q)).sub
        (hasDerivAt_const (x := q) (c := r))
    convert hh using 1
    · ext x <;> simp [id]
    · simp [id]
  have hden : HasDerivAt (fun x : ℝ => A * sqrt (1-x^2)) (A * (-q/Q)) q := by
    have hh := (hasDerivAt_const (x := q) (c := A)).mul hsqrt
    convert hh using 1 <;> ring
  have hinner : HasDerivAt (fun x : ℝ => (p*x - r) / (A * sqrt (1-x^2)))
      ((p - r*q)/(A * Q^3)) q := by
    have hv := hnum.div hden (show A * Q ≠ 0 by positivity)
    convert hv using 1
    · dsimp [A, Q] at *
      field_simp [ne_of_gt hA, ne_of_gt hQ]
      rw [hsqQ]
      ring
  have hone : 1 - ((p*q - r)/(A*Q))^2 = (1 + 2*p*r*q - p^2 - r^2 - q^2)/((1-p^2)*(1-q^2)) := by
    dsimp [A, Q]
    rw [div_pow]
    field_simp [ne_of_gt hA2, ne_of_gt hQ2, hsqA, hsqQ]
    simp only [hsqA, hsqQ]
    ring_nf
  have hu_ne : (p*q - r)/(A*Q) ≠ 1 ∧ (p*q - r)/(A*Q) ≠ -1 := by
    constructor <;> intro h
    · have hs : ((p*q-r)/(A*Q))^2 = 1 := by rw [h]; norm_num
      have hz : 1 - ((p*q-r)/(A*Q))^2 = 0 := by rw [hs]; norm_num
      rw [hone] at hz
      have hf : 0 < (1+2*p*r*q-p^2-r^2-q^2)/((1-p^2)*(1-q^2)) := by positivity
      nlinarith
    · have hs : ((p*q-r)/(A*Q))^2 = 1 := by rw [h]; norm_num
      have hz : 1 - ((p*q-r)/(A*Q))^2 = 0 := by rw [hs]; norm_num
      rw [hone] at hz
      have hf : 0 < (1+2*p*r*q-p^2-r^2-q^2)/((1-p^2)*(1-q^2)) := by positivity
      nlinarith
  have hder := (Real.hasDerivAt_arccos hu_ne.2 hu_ne.1).comp q hinner
  unfold triSideB
  convert hder using 1
  · ext x
    rw [Real.sqrt_mul (le_of_lt hA2)]
    rfl
  · rw [hone, Real.sqrt_div (le_of_lt hΔ)]
    rw [Real.sqrt_mul (le_of_lt hA2)]
    dsimp [A, Q] at *
    field_simp [ne_of_gt hA, ne_of_gt hQ, ne_of_gt hD]
    rw [hsqQ]
    ring

lemma hasDerivAt_triSideC (p r q : ℝ) (hr : r^2 < 1) (hq : q^2 < 1)
    (hΔ : 0 < 1 + 2*p*r*q - p^2 - r^2 - q^2) :
    HasDerivAt (fun x : ℝ => triSideC p r x)
      ((p*q - r)/((1-q^2) * sqrt (1 + 2*p*r*q - p^2 - r^2 - q^2))) q := by
  -- symmetry: swap p and r in the triSideB lemma
  have hΔ' : 0 < 1 + 2*r*p*q - r^2 - p^2 - q^2 := by nlinarith
  have h := hasDerivAt_triSideB r p q hr hq hΔ'
  unfold triSideB at h
  unfold triSideC
  convert h using 1
  · ring_nf

lemma hasDerivAt_sphericalSum (p r q : ℝ) (hp : p^2 < 1) (hr : r^2 < 1) (hq : q^2 < 1)
    (hΔ : 0 < 1 + 2*p*r*q - p^2 - r^2 - q^2) :
    HasDerivAt (fun x : ℝ => triSideA p r x + p * triSideB p r x + r * triSideC p r x)
      (sqrt (1 + 2*p*r*q - p^2 - r^2 - q^2) / (1 - q^2)) q := by
  have hA := hasDerivAt_triSideA p r q hp hr hΔ
  have hB := hasDerivAt_triSideB p r q hp hq hΔ
  have hC := hasDerivAt_triSideC p r q hr hq hΔ
  have hs := (hA.add ((hasDerivAt_const (x := q) (c := p)).mul hB)).add
    ((hasDerivAt_const (x := q) (c := r)).mul hC)
  convert hs using 1
  · have hQ2 : 0 < 1 - q^2 := by linarith
    have hD : 0 < sqrt (1 + 2*p*r*q - p^2 - r^2 - q^2) := Real.sqrt_pos.2 hΔ
    field_simp [ne_of_gt hQ2, ne_of_gt hD]
    rw [Real.sq_sqrt (le_of_lt hΔ)]
    ring


lemma sphericalProj_aux1 (p r q : ℝ) (hp : p^2 < 1) (hr : r^2 < 1) (hq : q^2 < 1)
    (hΔ : 0 < 1 + 2*p*r*q - p^2 - r^2 - q^2) (hpr : p + r ≠ 0) :
    0 < triSideA p r q + p * triSideB p r q + r * triSideC p r q := by
  let A : ℝ := sqrt (1 - p^2)
  let B : ℝ := sqrt (1 - r^2)
  let s : ℝ := A * B
  let q0 : ℝ := p*r - s
  have hA2 : 0 < 1 - p^2 := by linarith only [hp]
  have hB2 : 0 < 1 - r^2 := by linarith only [hr]
  have hA : 0 < A := by dsimp [A]; exact Real.sqrt_pos.2 hA2
  have hB : 0 < B := by dsimp [B]; exact Real.sqrt_pos.2 hB2
  have hs : 0 < s := by dsimp [s]; exact mul_pos hA hB
  have hsqA : A^2 = 1-p^2 := by dsimp [A]; rw [Real.sq_sqrt (le_of_lt hA2)]
  have hsqB : B^2 = 1-r^2 := by dsimp [B]; rw [Real.sq_sqrt (le_of_lt hB2)]
  have hsqs : s^2 = (1-p^2)*(1-r^2) := by dsimp [s]; rw [mul_pow, hsqA, hsqB]
  have hDelta_eq (x : ℝ) : 1 + 2*p*r*x - p^2 - r^2 - x^2 = s^2 - (x - p*r)^2 := by
    rw [hsqs]
    ring
  have hposq : 0 < s^2 - (q - p*r)^2 := by rwa [← hDelta_eq q]
  have habs : |q - p*r| < s := by
    have hsq : (q - p*r)^2 < s^2 := by linarith only [hposq]
    have ht := (sq_lt_sq.mp hsq)
    rwa [abs_of_pos hs] at ht
  have hq_lt : q < p*r + s := by linarith only [le_abs_self (q - p*r), habs]
  have hq0_lt : q0 < q := by
    dsimp [q0]
    linarith only [neg_le_abs (q - p*r), habs]
  have hq0_ge : -1 ≤ q0 := by
    have hid : 1 - q0^2 = (r*A + p*B)^2 := by
      dsimp [q0, s]
      ring_nf
      rw [hsqA, hsqB]
      ring
    nlinarith only [hid, sq_nonneg (r*A + p*B)]
  have hq0_ne : q0 ≠ -1 := by
    intro h
    have hpreq : p*r + 1 = s := by dsimp [q0] at h; linarith only [h]
    have hsquare : (p*r + 1)^2 = s^2 := by rw [hpreq]
    rw [hsqs] at hsquare
    have hs0 : (p + r)^2 = 0 := by nlinarith only [hsquare]
    exact hpr (sq_eq_zero_iff.mp hs0)
  have hq0_gt : -1 < q0 := lt_of_le_of_ne hq0_ge (Ne.symm hq0_ne)
  have hq_lt1 : q < 1 := by nlinarith only [hq, sq_nonneg (q - 1)]
  have hq_gtm1 : -1 < q := by nlinarith only [hq, sq_nonneg (q + 1)]
  let F : ℝ → ℝ := fun x => triSideA p r x + p * triSideB p r x + r * triSideC p r x
  have hcont : ContinuousOn F (Set.Icc q0 q) := by
    unfold F triSideA triSideB triSideC
    intro x hx
    have hxge : q0 ≤ x := hx.1
    have hxle : x ≤ q := hx.2
    have hxlt1 : x < 1 := lt_of_le_of_lt hxle hq_lt1
    have hxgtm1 : -1 < x := lt_of_lt_of_le hq0_gt hxge
    have hx2 : 0 < 1 - x^2 := by nlinarith only [hxlt1, hxgtm1, sq_nonneg (x-1), sq_nonneg (x+1)]
    have hden : Real.sqrt ((1-p^2)*(1-x^2)) ≠ 0 := by positivity
    have hden2 : Real.sqrt ((1-r^2)*(1-x^2)) ≠ 0 := by positivity
    have hden3 : Real.sqrt ((1-p^2)*(1-r^2)) ≠ 0 := by positivity
    fun_prop
  have hderiv_pos : ∀ x ∈ Set.Ioo q0 q, 0 < deriv F x := by
    intro x hx
    have hxlt : x < q := hx.2
    have hxgt : q0 < x := hx.1
    have hxlt1 : x < 1 := lt_trans hxlt hq_lt1
    have hxgtm1 : -1 < x := lt_trans hq0_gt hxgt
    have hx2 : 0 < 1 - x^2 := by nlinarith only [hxlt1, hxgtm1, sq_nonneg (x-1), sq_nonneg (x+1)]
    have hxltup : x < p*r + s := lt_trans hxlt hq_lt
    have hposfac : 0 < x - p*r + s := by dsimp [q0] at hxgt; linarith only [hxgt]
    have hnegfac : x - p*r - s < 0 := by linarith only [hxltup]
    have hmul : (x - p*r + s) * (x - p*r - s) < 0 := mul_neg_of_pos_of_neg hposfac hnegfac
    have hDx : 0 < 1 + 2*p*r*x - p^2 - r^2 - x^2 := by
      rw [hDelta_eq x]
      nlinarith only [hmul]
    have hd := hasDerivAt_sphericalSum p r x hp hr
      (by nlinarith only [hxlt1, hxgtm1, sq_nonneg (x-1), sq_nonneg (x+1)]) hDx
    rw [hd.deriv]
    exact div_pos (Real.sqrt_pos.2 hDx) hx2
  have hmono : StrictMonoOn F (Set.Icc q0 q) :=
    strictMonoOn_of_deriv_pos (convex_Icc q0 q) hcont (by
      intro x hx
      rw [interior_Icc] at hx
      exact hderiv_pos x hx)
  have hFq0lt : F q0 < F q := hmono (by exact ⟨le_rfl, le_of_lt hq0_lt⟩)
    (by exact ⟨le_of_lt hq0_lt, le_rfl⟩) hq0_lt
  have hFq0 : 0 ≤ F q0 := by
    have hida : (p*r - q0) / sqrt ((1-p^2)*(1-r^2)) = 1 := by
      dsimp [q0, s]
      rw [Real.sqrt_mul (le_of_lt hA2)]
      field_simp [ne_of_gt hA, ne_of_gt hB]
      dsimp [A, B]
      ring
    have hsq1 : 1 - q0^2 = (r*A + p*B)^2 := by
      dsimp [q0, s]
      ring_nf
      rw [hsqA, hsqB]
      ring
    have hroot : sqrt (1 - q0^2) = |r*A + p*B| := by rw [hsq1, Real.sqrt_sq_eq_abs]
    by_cases hpos : 0 < r*A + p*B
    · have hbarg : (p*q0 - r) / sqrt ((1-p^2)*(1-q0^2)) = -1 := by
        rw [Real.sqrt_mul (le_of_lt hA2), hroot, abs_of_pos hpos]
        field_simp [ne_of_gt hA]
        dsimp [q0, s]
        ring_nf
        simp only [show Real.sqrt (1-p^2) = A by rfl]
        ring_nf
        rw [hsqA]
        ring
      have hcarg : (r*q0 - p) / sqrt ((1-r^2)*(1-q0^2)) = -1 := by
        rw [Real.sqrt_mul (le_of_lt hB2), hroot, abs_of_pos hpos]
        field_simp [ne_of_gt hB]
        dsimp [q0, s]
        ring_nf
        simp only [show Real.sqrt (1-r^2) = B by rfl]
        ring_nf
        rw [hsqB]
        ring
      have hsumpos : 0 < p + r := by
        by_contra hnot
        have hle : p + r ≤ 0 := le_of_not_gt hnot
        by_cases hp0 : 0 < p
        · have hrneg : r < 0 := by linarith only [hle, hp0]
          have hp_le_negr : p ≤ -r := by linarith only [hle]
          have habsle : |p| ≤ |r| := by
            rw [abs_of_pos hp0, abs_of_neg hrneg]
            exact hp_le_negr
          have hp2le : p^2 ≤ r^2 := (sq_le_sq).2 habsle
          have hB2leA2 : B^2 ≤ A^2 := by rw [hsqB, hsqA]; linarith only [hp2le]
          have hBA : B ≤ A := by
            have ht := (sq_le_sq.mp hB2leA2)
            rwa [abs_of_nonneg (le_of_lt hB), abs_of_nonneg (le_of_lt hA)] at ht
          have hmul1 : p*B ≤ (-r)*B := mul_le_mul_of_nonneg_right hp_le_negr (le_of_lt hB)
          have hmul2 : r*(A-B) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hrneg) (sub_nonneg.mpr hBA)
          nlinarith only [hpos, hmul1, hmul2]
        · have hple : p ≤ 0 := le_of_not_gt hp0
          have hrpos : 0 < r := by
            by_contra hnot2
            have hrle : r ≤ 0 := le_of_not_gt hnot2
            nlinarith only [hpos, hA, hB, hple, hrle]
          have hr_le_negp : r ≤ -p := by linarith only [hle]
          have habsle : |r| ≤ |p| := by
            rw [abs_of_pos hrpos, abs_of_nonpos hple]
            exact hr_le_negp
          have hr2le : r^2 ≤ p^2 := (sq_le_sq).2 habsle
          have hA2leB2 : A^2 ≤ B^2 := by rw [hsqA, hsqB]; linarith only [hr2le]
          have hAB : A ≤ B := by
            have ht := (sq_le_sq.mp hA2leB2)
            rwa [abs_of_nonneg (le_of_lt hA), abs_of_nonneg (le_of_lt hB)] at ht
          have hmul1 : r*A ≤ (-p)*A := mul_le_mul_of_nonneg_right hr_le_negp (le_of_lt hA)
          have hmul2 : p*(B-A) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hple (sub_nonneg.mpr hAB)
          nlinarith only [hpos, hmul1, hmul2]
      have ha0 : triSideA p r q0 = 0 := by
        unfold triSideA
        rw [hida, Real.arccos_one]
      have hb0 : triSideB p r q0 = Real.pi := by
        unfold triSideB
        rw [hbarg, Real.arccos_neg_one]
      have hc0 : triSideC p r q0 = Real.pi := by
        unfold triSideC
        rw [hcarg, Real.arccos_neg_one]
      dsimp [F]
      rw [ha0, hb0, hc0]
      nlinarith only [Real.pi_pos, hsumpos]
    · have hnonpos : r*A + p*B < 0 := by
        have hne : r*A + p*B ≠ 0 := by
          intro hz
          have hq0sq : q0^2 = 1 := by nlinarith only [hsq1, hz]
          have hABpos : 0 < A*B := mul_pos hA hB
          have hprlt : p*r < 1 := by nlinarith only [hp, hr, sq_nonneg (p-r)]
          have hq0lt1 : q0 < 1 := by dsimp [q0, s]; linarith only [hABpos, hprlt]
          have hq0eq : q0 = -1 := by nlinarith only [hq0sq, hq0lt1]
          exact hq0_ne hq0eq
        exact lt_of_le_of_ne (le_of_not_gt hpos) hne
      have hbarg : (p*q0 - r) / sqrt ((1-p^2)*(1-q0^2)) = 1 := by
        have hnum_eq : p*q0 - r = -A*(r*A + p*B) := by
          dsimp [q0, s]
          ring_nf
          rw [hsqA]
          ring
        have hden_eq : sqrt ((1-p^2)*(1-q0^2)) = -A*(r*A + p*B) := by
          rw [Real.sqrt_mul (le_of_lt hA2), hroot, abs_of_neg hnonpos]
          change A * (-(r*A + p*B)) = -A*(r*A + p*B)
          ring
        rw [hnum_eq, hden_eq]
        have hdennz' : A*r + p*B ≠ 0 := by linarith only [hnonpos]
        field_simp [hdennz']
      have hcarg : (r*q0 - p) / sqrt ((1-r^2)*(1-q0^2)) = 1 := by
        have hnum_eq : r*q0 - p = -B*(r*A + p*B) := by
          dsimp [q0, s]
          ring_nf
          rw [hsqB]
          ring
        have hden_eq : sqrt ((1-r^2)*(1-q0^2)) = -B*(r*A + p*B) := by
          rw [Real.sqrt_mul (le_of_lt hB2), hroot, abs_of_neg hnonpos]
          change B * (-(r*A + p*B)) = -B*(r*A + p*B)
          ring
        rw [hnum_eq, hden_eq]
        have hdennz' : r*A + B*p ≠ 0 := by linarith only [hnonpos]
        field_simp [hdennz']
      have ha0 : triSideA p r q0 = 0 := by
        unfold triSideA
        rw [hida, Real.arccos_one]
      have hb0 : triSideB p r q0 = 0 := by
        unfold triSideB
        rw [hbarg, Real.arccos_one]
      have hc0 : triSideC p r q0 = 0 := by
        unfold triSideC
        rw [hcarg, Real.arccos_one]
      dsimp [F]
      rw [ha0, hb0, hc0]
      norm_num
  dsimp [F] at hFq0lt
  linarith only [hFq0lt, hFq0]

/-- The first projection sum on the degenerate slice `r = -p`.  Here the lower
    root of `Δ` is `q = -1`, where the arccos arguments of `triSideB`,
    `triSideC` tend to `0` (so the two sides tend to `π/2`) and the boundary
    value of the sum is `0`, not the clean `0` or `π(p+r)` of `aux1`.  We
    recover strict positivity by continuity in `r` from the nondegenerate
    slice `p + r ≠ 0` (which gives `≥ 0` at an interior point) together with
    the strict monotonicity in `q` supplied by `hasDerivAt_sphericalSum`. -/
lemma sphericalProj_aux1_sum_zero (p q : ℝ) (hp : p^2 < 1) (hq : q^2 < 1)
    (hΔ : 0 < 1 + 2*p*(-p)*q - p^2 - (-p)^2 - q^2) :
    0 < triSideA p (-p) q + p * triSideB p (-p) q + (-p) * triSideC p (-p) q := by
  have hp1 : 0 < 1 - p^2 := by linarith
  have hqlo : -1 < q := by nlinarith [hq, sq_nonneg (q+1)]
  have hqhi : q < 1 := by nlinarith [hq, sq_nonneg (q-1)]
  have hqtop : q < 1 - 2*p^2 := by
    have hfac : 1 + 2*p*(-p)*q - p^2 - (-p)^2 - q^2 = (1 - 2*p^2 - q) * (1+q) := by ring
    rw [hfac] at hΔ
    nlinarith
  let x : ℝ := (-1 + q)/2
  have hxlo : -1 < x := by dsimp [x]; linarith
  have hxhi : x < q := by dsimp [x]; linarith
  have hx2lt : x^2 < 1 := by
    nlinarith [hxlo, lt_trans hxhi hqhi, sq_nonneg (x-1), sq_nonneg (x+1)]
  have hΔx : 0 < 1 + 2*p*(-p)*x - p^2 - (-p)^2 - x^2 := by
    have hfac : 1 + 2*p*(-p)*x - p^2 - (-p)^2 - x^2 = (1 - 2*p^2 - x) * (1+x) := by ring
    rw [hfac]
    nlinarith
  -- continuity in the middle dot at `r = -p` of the third-argument-`x` sum
  have hcontA : ContinuousAt (fun s : ℝ => triSideA p s x) (-p) := by
    have hpneg : (-p)^2 = p^2 := by ring
    have hden : Real.sqrt ((1-p^2)*(1-(-p)^2)) ≠ 0 := by rw [hpneg]; positivity
    unfold triSideA
    have hcnum : ContinuousAt (fun s : ℝ => p*s - x) (-p) := by fun_prop
    have hcden : ContinuousAt (fun s : ℝ => Real.sqrt ((1-p^2)*(1-s^2))) (-p) := by fun_prop
    have hdiv := hcnum.div hcden hden
    simpa [Function.comp_def] using Real.continuous_arccos.continuousAt.comp hdiv
  have hcontB : ContinuousAt (fun s : ℝ => triSideB p s x) (-p) := by
    have hden : Real.sqrt ((1-p^2)*(1-x^2)) ≠ 0 := by positivity
    unfold triSideB
    have hcnum : ContinuousAt (fun s : ℝ => p*x - s) (-p) := by fun_prop
    have hcden : ContinuousAt (fun s : ℝ => Real.sqrt ((1-p^2)*(1-x^2))) (-p) := by fun_prop
    have hdiv := hcnum.div hcden hden
    simpa [Function.comp_def] using Real.continuous_arccos.continuousAt.comp hdiv
  have hcontC : ContinuousAt (fun s : ℝ => triSideC p s x) (-p) := by
    have hpneg : (-p)^2 = p^2 := by ring
    have hden : Real.sqrt ((1-(-p)^2)*(1-x^2)) ≠ 0 := by rw [hpneg]; positivity
    unfold triSideC
    have hcnum : ContinuousAt (fun s : ℝ => s*x - p) (-p) := by fun_prop
    have hcden : ContinuousAt (fun s : ℝ => Real.sqrt ((1-s^2)*(1-x^2))) (-p) := by fun_prop
    have hdiv := hcnum.div hcden hden
    simpa [Function.comp_def] using Real.continuous_arccos.continuousAt.comp hdiv
  have hcontF : ContinuousAt
      (fun s : ℝ => triSideA p s x + p * triSideB p s x + s * triSideC p s x) (-p) :=
    (hcontA.add (continuousAt_const.mul hcontB)).add (continuousAt_id.mul hcontC)
  have hev_r : ∀ᶠ s in 𝓝 (-p), s^2 < 1 := by
    have hopen : IsOpen {s : ℝ | s^2 < 1} := isOpen_lt (continuous_id.pow 2) continuous_const
    have hmem : (-p) ∈ {s : ℝ | s^2 < 1} := by dsimp; nlinarith [hp]
    exact hopen.mem_nhds hmem
  have hev_D : ∀ᶠ s in 𝓝 (-p), 0 < 1 + 2*p*s*x - p^2 - s^2 - x^2 := by
    have hcont : Continuous (fun s : ℝ => 1 + 2*p*s*x - p^2 - s^2 - x^2) := by fun_prop
    have hopen : IsOpen {s : ℝ | 0 < 1 + 2*p*s*x - p^2 - s^2 - x^2} :=
      isOpen_lt continuous_const hcont
    exact hopen.mem_nhds hΔx
  have hev : ∀ᶠ s in 𝓝[≠] (-p),
      0 < triSideA p s x + p * triSideB p s x + s * triSideC p s x := by
    filter_upwards [hev_r.filter_mono nhdsWithin_le_nhds,
      hev_D.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs2 hsD hne
    have hsne : s ≠ -p := by simpa using hne
    have hpr : p + s ≠ 0 := by intro h; apply hsne; linarith
    exact sphericalProj_aux1 p s x hp hs2 hx2lt hsD hpr
  have hge : 0 ≤ triSideA p (-p) x + p * triSideB p (-p) x + (-p) * triSideC p (-p) x := by
    have hlim : Filter.Tendsto
        (fun s : ℝ => triSideA p s x + p * triSideB p s x + s * triSideC p s x)
        (𝓝[≠] (-p))
        (𝓝 (triSideA p (-p) x + p * triSideB p (-p) x + (-p) * triSideC p (-p) x)) :=
      hcontF.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (-p) ≤ 𝓝 (-p))
    exact ge_of_tendsto hlim (hev.mono (fun s hs => le_of_lt hs))
  -- strict monotonicity of the sum in the third argument on `[x, q]`
  let F : ℝ → ℝ := fun y =>
    triSideA p (-p) y + p * triSideB p (-p) y + (-p) * triSideC p (-p) y
  have hcontFq : ContinuousOn F (Set.Icc x q) := by
    unfold F triSideA triSideB triSideC
    intro y hy
    have hyge : x ≤ y := hy.1
    have hyle : y ≤ q := hy.2
    have hylt1 : y < 1 := lt_of_le_of_lt hyle hqhi
    have hygtm1 : -1 < y := lt_of_lt_of_le hxlo hyge
    have hy2 : 0 < 1 - y^2 := by nlinarith [sq_nonneg (y-1), sq_nonneg (y+1)]
    have hpneg : (-p)^2 = p^2 := by ring
    have hdenA : Real.sqrt ((1-p^2)*(1-(-p)^2)) ≠ 0 := by rw [hpneg]; positivity
    have hdenB : Real.sqrt ((1-p^2)*(1-y^2)) ≠ 0 := by positivity
    have hdenC : Real.sqrt ((1-(-p)^2)*(1-y^2)) ≠ 0 := by rw [hpneg]; positivity
    fun_prop
  have hderiv : ∀ y ∈ Set.Ioo x q, 0 < deriv F y := by
    intro y hy
    have hylt : y < q := hy.2
    have hygt : x < y := hy.1
    have hylt1 : y < 1 := lt_trans hylt hqhi
    have hygtm1 : -1 < y := lt_trans hxlo hygt
    have hy2 : 0 < 1 - y^2 := by nlinarith [sq_nonneg (y-1), sq_nonneg (y+1)]
    have hΔy : 0 < 1 + 2*p*(-p)*y - p^2 - (-p)^2 - y^2 := by
      have hfac : 1 + 2*p*(-p)*y - p^2 - (-p)^2 - y^2 = (1 - 2*p^2 - y)*(1+y) := by ring
      rw [hfac]
      nlinarith
    have hrneg : (-p)^2 < 1 := by
      have hpneg' : (-p)^2 = p^2 := by ring
      rw [hpneg']
      exact hp
    have hy2lt : y^2 < 1 := by linarith
    have hd := hasDerivAt_sphericalSum p (-p) y hp hrneg hy2lt hΔy
    rw [hd.deriv]
    exact div_pos (Real.sqrt_pos.2 hΔy) hy2
  have hmono : StrictMonoOn F (Set.Icc x q) :=
    strictMonoOn_of_deriv_pos (convex_Icc x q) hcontFq (by
      intro y hy
      rw [interior_Icc] at hy
      exact hderiv y hy)
  have hlt : F x < F q :=
    hmono ⟨le_rfl, le_of_lt hxhi⟩ ⟨le_of_lt hxhi, le_rfl⟩ hxhi
  dsimp [F] at hlt
  linarith only [hlt, hge]

lemma triSideA_swap12 (p r q : ℝ) : triSideA q p r = triSideB p r q := by
  unfold triSideA triSideB
  congr 1
  rw [mul_comm q p]
  congr 1
  rw [mul_comm (1 - q^2) (1 - p^2)]

lemma triSideB_swap12 (p r q : ℝ) : triSideB q p r = triSideC p r q := by
  unfold triSideB triSideC
  congr 1
  rw [mul_comm q r]
  congr 1
  rw [mul_comm (1 - q^2) (1 - r^2)]

lemma triSideC_swap12 (p r q : ℝ) : triSideC q p r = triSideA p r q := by
  unfold triSideC triSideA
  congr 1

lemma triSideA_swap23 (p r q : ℝ) : triSideA r q p = triSideC p r q := by
  unfold triSideA triSideC
  congr 1

lemma triSideB_swap23 (p r q : ℝ) : triSideB r q p = triSideA p r q := by
  unfold triSideB triSideA
  congr 1
  rw [mul_comm r p]
  congr 1
  rw [mul_comm (1 - r^2) (1 - p^2)]

lemma triSideC_swap23 (p r q : ℝ) : triSideC r q p = triSideB p r q := by
  unfold triSideC triSideB
  congr 1
  rw [mul_comm q p]
  congr 1
  rw [mul_comm (1 - q^2) (1 - p^2)]

/-- The general spherical projection inequality for a nondegenerate trihedral
    vertex with distinct side lengths, under the three nondegeneracy conditions
    `p + r ≠ 0`, `p + q ≠ 0`, `r + q ≠ 0`. -/
theorem sphericalProj_general (p r q : ℝ) (hp : p^2 < 1) (hr : r^2 < 1) (hq : q^2 < 1)
    (hΔ : 0 < 1 + 2*p*r*q - p^2 - r^2 - q^2)
    (hpr : p + r ≠ 0) (hpq : p + q ≠ 0) (hqr : q + r ≠ 0) :
    sphericalProj p r q := by
  have h1 := sphericalProj_aux1 p r q hp hr hq hΔ hpr
  have hΔ2 : 0 < 1 + 2*q*p*r - q^2 - p^2 - r^2 := by nlinarith
  have hpq' : q + p ≠ 0 := by simpa [add_comm] using hpq
  have h2 := sphericalProj_aux1 q p r hq hp hr hΔ2 hpq'
  have hΔ3 : 0 < 1 + 2*r*q*p - r^2 - q^2 - p^2 := by nlinarith
  have hqr' : r + q ≠ 0 := by simpa [add_comm] using hqr
  have h3 := sphericalProj_aux1 r q p hr hq hp hΔ3 hqr'
  dsimp [sphericalProj]
  constructor
  · nlinarith only [h1]
  constructor
  · rw [triSideA_swap12 p r q, triSideB_swap12 p r q, triSideC_swap12 p r q] at h2
    nlinarith only [h2]
  · rw [triSideA_swap23 p r q, triSideB_swap23 p r q, triSideC_swap23 p r q] at h3
    nlinarith only [h3]

/-- The spherical projection inequality for **every** nondegenerate trihedral
    vertex: the three hyperplane slices `p+r=0`, `p+q=0`, `r+q=0` are now
    covered by `sphericalProj_aux1_sum_zero` (after the appropriate permutation),
    so the three sum nondegeneracy conditions of `sphericalProj_general` can be
    dropped entirely. -/
theorem sphericalProj_unconditional (p r q : ℝ) (hp : p^2 < 1) (hr : r^2 < 1) (hq : q^2 < 1)
    (hΔ : 0 < 1 + 2*p*r*q - p^2 - r^2 - q^2) :
    sphericalProj p r q := by
  have h1 : triSideA p r q > triSideB p r q * (-p) + triSideC p r q * (-r) := by
    by_cases hpr : p + r = 0
    · have hr_eq : r = -p := by linarith
      subst r
      have hd := sphericalProj_aux1_sum_zero p q hp hq hΔ
      nlinarith [hd]
    · have hd := sphericalProj_aux1 p r q hp hr hq hΔ hpr
      nlinarith [hd]
  have h2 : triSideB p r q > triSideA p r q * (-p) + triSideC p r q * (-q) := by
    by_cases hpq : p + q = 0
    · have hp_eq : p = -q := by linarith
      subst p
      have hΔ2 : 0 < 1 + 2*q*(-q)*r - q^2 - (-q)^2 - r^2 := by nlinarith [hΔ]
      have hd := sphericalProj_aux1_sum_zero q r hq hr hΔ2
      rw [triSideA_swap12 (-q) r q, triSideB_swap12 (-q) r q,
        triSideC_swap12 (-q) r q] at hd
      nlinarith [hd]
    · have hpq' : q + p ≠ 0 := by
        intro h
        apply hpq
        linarith
      have h2' := sphericalProj_aux1 q p r hq hp hr (by nlinarith [hΔ]) hpq'
      rw [triSideA_swap12 p r q, triSideB_swap12 p r q, triSideC_swap12 p r q] at h2'
      nlinarith [h2']
  have h3 : triSideC p r q > triSideA p r q * (-r) + triSideB p r q * (-q) := by
    by_cases hqr : r + q = 0
    · have hr_eq : r = -q := by linarith
      subst r
      have hqneg : (-q)^2 < 1 := by
        have hqneg' : (-q)^2 = q^2 := by ring
        rw [hqneg']
        exact hq
      have hd := sphericalProj_aux1_sum_zero (-q) p hqneg hp (by nlinarith [hΔ])
      simp only [neg_neg] at hd
      rw [triSideA_swap23 p (-q) q, triSideB_swap23 p (-q) q,
        triSideC_swap23 p (-q) q] at hd
      simp only [neg_neg] at hd ⊢
      nlinarith [hd]
    · have h3' := sphericalProj_aux1 r q p hr hq hp (by nlinarith [hΔ]) hqr
      rw [triSideA_swap23 p r q, triSideB_swap23 p r q, triSideC_swap23 p r q] at h3'
      nlinarith [h3']
  exact ⟨h1, h2, h3⟩

/-- `sphericalProj` on the `p + r = 0` slice (`r = -p`).  The first inequality
    is the nontrivial one and is proved by `sphericalProj_aux1_sum_zero`; the
    two cyclic ones follow from `sphericalProj_aux1` (their sums do not vanish
    off the other two hyperplanes). -/
theorem sphericalProj_sum_zero (p q : ℝ) (hp : p^2 < 1) (hq : q^2 < 1)
    (hΔ : 0 < 1 + 2*p*(-p)*q - p^2 - (-p)^2 - q^2) :
    sphericalProj p (-p) q := by
  have hrneg : (-p)^2 < 1 := by
    have hpneg : (-p)^2 = p^2 := by ring
    rw [hpneg]
    exact hp
  exact sphericalProj_unconditional p (-p) q hp hrneg hq hΔ

/-- The geometric seam (S) for an arbitrary nondegenerate trihedral vertex,
    as a directly applicable vector-level theorem: only unit norms and a
    nonzero triple product are required. -/
theorem three_face_face_pos_unconditional (n₁ n₂ n₃ : V3) {p r q : ℝ}
    (h1 : dot n₁ n₁ = 1) (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1)
    (h12 : dot n₁ n₂ = p) (h13 : dot n₁ n₃ = r) (h23 : dot n₂ n₃ = q)
    (htriple : triple n₁ n₂ n₃ ≠ 0) :
    let θ₁ := cornerAngle (isoEdge12 n₁ n₂) (isoEdge13 n₁ n₃)
    let θ₂ := cornerAngle (isoEdge12 n₁ n₂) (isoEdge23 n₂ n₃)
    let θ₃ := cornerAngle (isoEdge13 n₁ n₃) (isoEdge23 n₂ n₃)
    0 < θ₁ * dot n₁ n₁ + θ₂ * dot n₂ n₁ + θ₃ * dot n₃ n₁ ∧
    0 < θ₁ * dot n₁ n₂ + θ₂ * dot n₂ n₂ + θ₃ * dot n₃ n₂ ∧
    0 < θ₁ * dot n₁ n₃ + θ₂ * dot n₂ n₃ + θ₃ * dot n₃ n₃ := by
  have hsq := triple_sq_general n₁ n₂ n₃ h1 h2 h3 h12 h13 h23
  have hΔ : 0 < 1 + 2*p*r*q - p^2 - r^2 - q^2 := by
    have ht : 0 < (triple n₁ n₂ n₃)^2 := sq_pos_of_ne_zero htriple
    nlinarith
  have hlt := dots_sq_lt_one n₁ n₂ n₃ h1 h2 h3 h12 h13 h23 htriple
  exact three_face_face_pos_of_spherical n₁ n₂ n₃ h1 h2 h3 h12 h13 h23 htriple
    (sphericalProj_unconditional p r q hlt.1 hlt.2.1 hlt.2.2 hΔ)

/-- The geometric seam (S) for a non-isosceles trihedral vertex with distinct
    side lengths, as a directly applicable vector-level theorem: the three
    dot products have square < 1, the Gram determinant is positive, and none
    of `p+r`, `p+q`, `r+q` vanishes.  Superseded by
    `three_face_face_pos_unconditional`, which drops the three sum conditions. -/
theorem three_face_face_pos_general (n₁ n₂ n₃ : V3) {p r q : ℝ}
    (h1 : dot n₁ n₁ = 1) (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1)
    (h12 : dot n₁ n₂ = p) (h13 : dot n₁ n₃ = r) (h23 : dot n₂ n₃ = q)
    (htriple : triple n₁ n₂ n₃ ≠ 0)
    (hpr : p + r ≠ 0) (hpq : p + q ≠ 0) (hqr : q + r ≠ 0) :
    let θ₁ := cornerAngle (isoEdge12 n₁ n₂) (isoEdge13 n₁ n₃)
    let θ₂ := cornerAngle (isoEdge12 n₁ n₂) (isoEdge23 n₂ n₃)
    let θ₃ := cornerAngle (isoEdge13 n₁ n₃) (isoEdge23 n₂ n₃)
    0 < θ₁ * dot n₁ n₁ + θ₂ * dot n₂ n₁ + θ₃ * dot n₃ n₁ ∧
    0 < θ₁ * dot n₁ n₂ + θ₂ * dot n₂ n₂ + θ₃ * dot n₃ n₂ ∧
    0 < θ₁ * dot n₁ n₃ + θ₂ * dot n₂ n₃ + θ₃ * dot n₃ n₃ := by
  have hsq := triple_sq_general n₁ n₂ n₃ h1 h2 h3 h12 h13 h23
  have hΔ : 0 < 1 + 2*p*r*q - p^2 - r^2 - q^2 := by
    have ht : 0 < (triple n₁ n₂ n₃)^2 := sq_pos_of_ne_zero htriple
    nlinarith
  have hlt := dots_sq_lt_one n₁ n₂ n₃ h1 h2 h3 h12 h13 h23 htriple
  exact three_face_face_pos_of_spherical n₁ n₂ n₃ h1 h2 h3 h12 h13 h23 htriple
    (sphericalProj_general p r q hlt.1 hlt.2.1 hlt.2.2 hΔ hpr hpq hqr)

/-! ### Status of the trihedral seam, and what remains open

The landed unconditional tiers for the geometric seam (S) are:

  * all pairwise dots `≥ 0` (`Vdb.face_pos_of_nonobtuse` — the cross terms are
    non-negative and the diagonal term is strictly positive);
  * any two equal pairwise dots, i.e. the isosceles vertex figure
    (`iso_three_face_face_pos` / `iso_three_face_S`, re-derived above through
    the general reduction via `sphericalProj_isosceles`);
  * the two-face planar vertex figure (`Vdb.planar_cone_two_face_face_pos`).

On top of these, this module proves the **three-face (trihedral) case in full**:
`three_face_face_pos_unconditional` needs only unit norms and `triple ≠ 0`.

The route is the abstraction seam `sphericalProj p r q`:

    triSideA p r q > triSideB p r q·(-p) + triSideC p r q·(-r)  ∧  …  (cyclic)

where `triSideA/B/C` are the three geometric corner angles of the cone (the
classical spherical-triangle inequality `a > b·cos C + c·cos B`).

`hasDerivAt_sphericalSum` computes the exact q-derivative of the first
projection sum:

    d/dq (triSideA p r q + p·triSideB p r q + r·triSideC p r q)
      = sqrt(Δ) / (1 - q²) > 0,      Δ = 1 + 2p·r·q − p² − r² − q².

Hence the sum is strictly increasing in q between the two roots
`p·r ± sqrt((1-p²)(1-r²))` of Δ.  At the lower root the three sides are
`0, 0, 0` or `0, π, π`, and the sum is `0` or `π(p+r)`, always non-negative.
This gives `sphericalProj_general` / `sphericalProj_aux1` off the three
hyperplanes `p+r = 0`, `p+q = 0`, `r+q = 0` (the cyclic statements come from
`triSideA_swap12`, `triSideA_swap23` and their siblings).

The hyperplane slices are closed by `sphericalProj_aux1_sum_zero`.  With
`r = -p` the lower root of Δ degenerates to `q = -1`: as `q → -1+` the side
`triSideA → 0` while `triSideB, triSideC → π/2`, so the sum tends to
`0 + p·(π/2) + (-p)·(π/2) = 0`.  Rather than formalising that improper endpoint
limit directly, we take an interior point `x = (-1+q)/2` and:

  1. use continuity in the middle dot at `r = -p` (the arccos denominators
     stay nonzero there) together with `sphericalProj_aux1` at nearby
     nondegenerate dots to get the sum at `x` is **≥ 0**;
  2. use the positive q-derivative above and `strictMonoOn_of_deriv_pos` to get
     the sum at `q` strictly larger than at `x`, hence **> 0**.

`sphericalProj_unconditional` assembles the three inequalities by applying this
argument after the appropriate permutation on each of the three hyperplanes;
`three_face_S_of_spherical` then lifts it to the `Fin 3` shape.

**What remains open** is the general `n`-face vertex figure (`n > 3`): the
reduction `three_face_S_of_spherical` is specific to a trihedron, and the
per-face positivity seam for arbitrary convex polyhedra is still the wall of
VS-4a.  Nothing about the three-face case remains conditional.

A bounded follow-up group (`Vdb/AngleNFace`) lands (S) for an arbitrary finite
family modulo the named *discrete spherical Stokes* hypothesis
(`nFace_face_pos_of_sphericalBarycenter`), and proves the `n = 4` case modulo
an explicit fan certificate (`fourFace_face_pos_of_fanCertificate`) using the
unconditional trihedral theorem above.  The general `n > 3` seam itself stays
walled: proving the Stokes identity needs spherical surface measure, and the
fan certificate needs the diagonal-arc/angle-matching geometry. -/

end V3
end Vdb
