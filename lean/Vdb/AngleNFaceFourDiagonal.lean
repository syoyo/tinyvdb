/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  The n = 4 diagonal, CONSTRUCTED from the four boundary co-normals.

  `Vdb/AngleNFaceFourCert.lean` proves that a diagonal co-normal `m` whose two
  trihedra `(n₀,n₁,m)`, `(-m,n₂,n₃)` have the right corner angles yields the n = 4
  face-positivity seam (S).  This module discharges the angle-matching part of
  that hypothesis explicitly, by *constructing* `m`.

  For four unit co-normals `n₀,n₁,n₂,n₃` in cyclic order bounding a convex
  spherical quadrilateral, the two opposite vertices of the vertex figure are

      v10 = normalize (cross n₃ n₀),    v21 = normalize (cross n₁ n₂),

  and the diagonal co-normal is `m = normalize (cross v10 v21)`.  The key
  algebraic fact is the vector triple-product identity

      cross n₀ (cross v10 v21) = (dot n₀ v21) • v10,      (dot n₀ v10 = 0)

  which, together with its three cyclic analogues, says that every edge ray at
  the diagonal is a *positive* scalar multiple of the corresponding original
  vertex of the quadrilateral (positivity is exactly convexity: each opposite
  vertex lies strictly inside the half-space of the edge it is not on).
  Since `cornerAngle` is invariant under positive rescaling of its two rays,
  the six corner-angle matchings follow by rewriting; they are

      (θ₀, θ₁, d)  for  (n₀,n₁,m),      (d, θ₂, θ₃)  for  (-m,n₂,n₃).

  Everything here is machine-checked, with no proof holes.  What remains beyond
  this module is the dual-cone containment `hdu`/`hdv` of
  `fourFace_fanCertificate_of_diagonal` (a separate convexity/transfer step),
  recorded precisely at the end.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.AngleNFaceFourCert

namespace Vdb
namespace V3

open scoped Real
open Real

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 800000

/-! ### 0. Elementary scaling and cross-product algebra -/

@[simp] lemma pnSmul_one (v : V3) : pnSmul 1 v = v := by
  apply V3.ext <;> simp [pnSmul]

@[simp] lemma pnSmul_zeroV (v : V3) : pnSmul 0 v = ⟨0, 0, 0⟩ := by
  apply V3.ext <;> simp [pnSmul]

@[simp] lemma sub_zeroV (v : V3) : V3.sub v ⟨0, 0, 0⟩ = v := by
  apply V3.ext <;> simp [V3.sub]

@[simp] lemma zero_subV (v : V3) : V3.sub ⟨0, 0, 0⟩ v = pnSmul (-1) v := by
  apply V3.ext <;> simp [V3.sub, pnSmul]

lemma pnSmul_pnSmul (s t : ℝ) (v : V3) :
    pnSmul s (pnSmul t v) = pnSmul (s * t) v := by
  apply V3.ext <;> simp [pnSmul] <;> ring

lemma dot_pnSmul_left (s : ℝ) (u v : V3) : dot (pnSmul s u) v = s * dot u v := by
  unfold pnSmul dot
  ring

lemma dot_pnSmul_right (s : ℝ) (u v : V3) : dot u (pnSmul s v) = s * dot u v := by
  unfold pnSmul dot
  ring

lemma cross_pnSmul_right (s : ℝ) (u v : V3) :
    cross u (pnSmul s v) = pnSmul s (cross u v) := by
  apply V3.ext <;> simp [cross, pnSmul] <;> ring

lemma cross_pnSmul_left (s : ℝ) (u v : V3) :
    cross (pnSmul s u) v = pnSmul s (cross u v) := by
  apply V3.ext <;> simp [cross, pnSmul] <;> ring

/-- `a × (b × c) = (a·c) b − (a·b) c` (vector triple product). -/
lemma cross_cross_triple (a b c : V3) :
    cross a (cross b c) = V3.sub (pnSmul (dot a c) b) (pnSmul (dot a b) c) := by
  apply V3.ext <;> simp [cross, pnSmul, dot, V3.sub] <;> ring

/-- Antisymmetry of `cross`, in the form used below. -/
lemma diag_cross_swap (a b : V3) : cross a b = pnSmul (-1) (cross b a) := by
  apply V3.ext <;> simp [cross, pnSmul] <;> ring

/-- `dot v v > 0` for a nonzero `v`. -/
lemma dot_pos_of_ne_zero (v : V3) (hv : v ≠ ⟨0, 0, 0⟩) : 0 < dot v v := by
  have hnn : 0 ≤ dot v v := dot_self_nonneg v
  rcases lt_or_eq_of_le hnn with hpos | hzero
  · exact hpos
  · exfalso
    apply hv
    apply V3.ext
    · have hx2 : v.x ^ 2 = 0 := by
        unfold dot at hzero
        nlinarith [sq_nonneg v.x, sq_nonneg v.y, sq_nonneg v.z]
      exact sq_eq_zero_iff.mp hx2
    · have hy2 : v.y ^ 2 = 0 := by
        unfold dot at hzero
        nlinarith [sq_nonneg v.x, sq_nonneg v.y, sq_nonneg v.z]
      exact sq_eq_zero_iff.mp hy2
    · have hz2 : v.z ^ 2 = 0 := by
        unfold dot at hzero
        nlinarith [sq_nonneg v.x, sq_nonneg v.y, sq_nonneg v.z]
      exact sq_eq_zero_iff.mp hz2

lemma eq_zero_of_norm_eq_zero (v : V3) (h : norm v = 0) : v = ⟨0, 0, 0⟩ := by
  have hdot : dot v v = 0 := by
    have hnn : 0 ≤ dot v v := dot_self_nonneg v
    unfold norm at h
    exact (Real.sqrt_eq_zero hnn).mp h
  apply V3.ext
  · have hx2 : v.x ^ 2 = 0 := by
      unfold dot at hdot
      nlinarith [sq_nonneg v.x, sq_nonneg v.y, sq_nonneg v.z]
    exact sq_eq_zero_iff.mp hx2
  · have hy2 : v.y ^ 2 = 0 := by
      unfold dot at hdot
      nlinarith [sq_nonneg v.x, sq_nonneg v.y, sq_nonneg v.z]
    exact sq_eq_zero_iff.mp hy2
  · have hz2 : v.z ^ 2 = 0 := by
      unfold dot at hdot
      nlinarith [sq_nonneg v.x, sq_nonneg v.y, sq_nonneg v.z]
    exact sq_eq_zero_iff.mp hz2

lemma norm_ne_zero_of_ne_zero (v : V3) (hv : v ≠ ⟨0, 0, 0⟩) : norm v ≠ 0 := by
  intro hn
  exact hv (eq_zero_of_norm_eq_zero v hn)

lemma norm_pos_of_ne_zero_norm (v : V3) (hv : norm v ≠ 0) : 0 < norm v :=
  lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)

lemma norm_pos_of_ne_zero (v : V3) (hv : v ≠ ⟨0, 0, 0⟩) : 0 < norm v :=
  norm_pos_of_ne_zero_norm v (norm_ne_zero_of_ne_zero v hv)

lemma norm_pnSmul (s : ℝ) (v : V3) : norm (pnSmul s v) = |s| * norm v := by
  unfold norm
  rw [dot_pnSmul_left, dot_pnSmul_right]
  rw [show s * (s * dot v v) = s ^ 2 * dot v v by ring]
  rw [Real.sqrt_mul (sq_nonneg s)]
  rw [Real.sqrt_sq_eq_abs]

/-- Normalizing a nonzero vector gives a unit vector. -/
lemma unit_pnSmul_inv_norm (v : V3) (hv : v ≠ ⟨0, 0, 0⟩) :
    dot (pnSmul (1 / norm v) v) (pnSmul (1 / norm v) v) = 1 := by
  have hdot : 0 < dot v v := dot_pos_of_ne_zero v hv
  have hsqrt : Real.sqrt (dot v v) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdot)
  unfold norm
  rw [dot_pnSmul_left, dot_pnSmul_right]
  field_simp [hsqrt, Real.sq_sqrt (le_of_lt hdot)]
  rw [Real.sq_sqrt (le_of_lt hdot)]

/-! ### 1. `cornerAngle` under positive rescaling -/

lemma cornerAngle_smul_pos {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {u v : V3}
    (hu : norm u ≠ 0) (hv : norm v ≠ 0) :
    cornerAngle (pnSmul s u) (pnSmul t v) = cornerAngle u v := by
  unfold cornerAngle
  rw [dot_pnSmul_left, dot_pnSmul_right]
  rw [norm_pnSmul, norm_pnSmul, abs_of_pos hs, abs_of_pos ht]
  congr 1
  field_simp [ne_of_gt hs, ne_of_gt ht, hu, hv]

lemma cornerAngle_smul_right_pos {s : ℝ} (hs : 0 < s) {u v : V3}
    (hu : norm u ≠ 0) (hv : norm v ≠ 0) :
    cornerAngle u (pnSmul s v) = cornerAngle u v := by
  conv_lhs => rw [← pnSmul_one u]
  exact cornerAngle_smul_pos (by norm_num : (0 : ℝ) < 1) hs hu hv

lemma cornerAngle_smul_left_pos {s : ℝ} (hs : 0 < s) {u v : V3}
    (hu : norm u ≠ 0) (hv : norm v ≠ 0) :
    cornerAngle (pnSmul s u) v = cornerAngle u v := by
  conv_lhs => rw [← pnSmul_one v]
  exact cornerAngle_smul_pos hs (by norm_num : (0 : ℝ) < 1) hu hv

/-! ### 2. The constructed diagonal -/

/-- The vertex between the cyclic edges `n₃` and `n₀`, normalized. -/
noncomputable def diagV10 (n3 n0 : V3) : V3 :=
  pnSmul (1 / norm (cross n3 n0)) (cross n3 n0)

/-- The opposite vertex between the edges `n₁` and `n₂`, normalized. -/
noncomputable def diagV21 (n1 n2 : V3) : V3 :=
  pnSmul (1 / norm (cross n1 n2)) (cross n1 n2)

/-- The diagonal co-normal: the great circle through `v10` and `v21`. -/
noncomputable def diagM (n0 n1 n2 n3 : V3) : V3 :=
  pnSmul (1 / norm (cross (diagV10 n3 n0) (diagV21 n1 n2)))
    (cross (diagV10 n3 n0) (diagV21 n1 n2))

noncomputable def diagNW (n0 n1 n2 n3 : V3) : ℝ :=
  norm (cross (diagV10 n3 n0) (diagV21 n1 n2))

lemma diagV10_unit (n3 n0 : V3) (h : cross n3 n0 ≠ ⟨0, 0, 0⟩) :
    dot (diagV10 n3 n0) (diagV10 n3 n0) = 1 :=
  unit_pnSmul_inv_norm (cross n3 n0) h

lemma diagV21_unit (n1 n2 : V3) (h : cross n1 n2 ≠ ⟨0, 0, 0⟩) :
    dot (diagV21 n1 n2) (diagV21 n1 n2) = 1 :=
  unit_pnSmul_inv_norm (cross n1 n2) h

lemma diagM_unit (n0 n1 n2 n3 : V3)
    (h : cross (diagV10 n3 n0) (diagV21 n1 n2) ≠ ⟨0, 0, 0⟩) :
    dot (diagM n0 n1 n2 n3) (diagM n0 n1 n2 n3) = 1 :=
  unit_pnSmul_inv_norm (cross (diagV10 n3 n0) (diagV21 n1 n2)) h

-- Orthogonality of each normalized vertex to the two edges it meets.
lemma diagV10_perp_n0 (n3 n0 : V3) : dot n0 (diagV10 n3 n0) = 0 := by
  unfold diagV10
  rw [dot_pnSmul_right, dot_self_cross_right]
  ring

lemma diagV10_perp_n3 (n3 n0 : V3) : dot n3 (diagV10 n3 n0) = 0 := by
  unfold diagV10
  rw [dot_pnSmul_right, dot_self_cross_left]
  ring

lemma diagV21_perp_n1 (n1 n2 : V3) : dot n1 (diagV21 n1 n2) = 0 := by
  unfold diagV21
  rw [dot_pnSmul_right, dot_self_cross_left]
  ring

lemma diagV21_perp_n2 (n1 n2 : V3) : dot n2 (diagV21 n1 n2) = 0 := by
  unfold diagV21
  rw [dot_pnSmul_right, dot_self_cross_right]
  ring

/-! ### 3. The six edge-ray collinearities (the heart of the construction) -/

lemma diag_cross_n0_w (n0 n1 n2 n3 : V3) :
    cross n0 (cross (diagV10 n3 n0) (diagV21 n1 n2)) =
      pnSmul (dot n0 (diagV21 n1 n2)) (diagV10 n3 n0) := by
  rw [cross_cross_triple, diagV10_perp_n0]
  rw [pnSmul_zeroV, sub_zeroV]

lemma diag_cross_n3_w (n0 n1 n2 n3 : V3) :
    cross n3 (cross (diagV10 n3 n0) (diagV21 n1 n2)) =
      pnSmul (dot n3 (diagV21 n1 n2)) (diagV10 n3 n0) := by
  rw [cross_cross_triple, diagV10_perp_n3]
  rw [pnSmul_zeroV, sub_zeroV]

lemma diag_cross_n1_w (n0 n1 n2 n3 : V3) :
    cross n1 (cross (diagV10 n3 n0) (diagV21 n1 n2)) =
      pnSmul (-(dot n1 (diagV10 n3 n0))) (diagV21 n1 n2) := by
  rw [cross_cross_triple, diagV21_perp_n1]
  rw [pnSmul_zeroV, zero_subV, pnSmul_pnSmul]
  congr 1
  ring

lemma diag_cross_n2_w (n0 n1 n2 n3 : V3) :
    cross n2 (cross (diagV10 n3 n0) (diagV21 n1 n2)) =
      pnSmul (-(dot n2 (diagV10 n3 n0))) (diagV21 n1 n2) := by
  rw [cross_cross_triple, diagV21_perp_n2]
  rw [pnSmul_zeroV, zero_subV, pnSmul_pnSmul]
  congr 1
  ring

lemma diag_neg_cross_n0 (n0 n1 n2 n3 : V3) :
    pnSmul (-1) (cross n0 (diagM n0 n1 n2 n3)) =
      pnSmul (-(dot n0 (diagV21 n1 n2)) /
        (diagNW n0 n1 n2 n3 * norm (cross n3 n0))) (cross n3 n0) := by
  unfold diagM diagNW
  rw [cross_pnSmul_right, diag_cross_n0_w]
  simp only [pnSmul_pnSmul]
  unfold diagV10
  simp only [pnSmul_pnSmul]
  congr 1
  ring

lemma diag_neg_cross_n3 (n0 n1 n2 n3 : V3) :
    pnSmul (-1) (cross n3 (diagM n0 n1 n2 n3)) =
      pnSmul (-(dot n3 (diagV21 n1 n2)) /
        (diagNW n0 n1 n2 n3 * norm (cross n3 n0))) (cross n3 n0) := by
  unfold diagM diagNW
  rw [cross_pnSmul_right, diag_cross_n3_w]
  simp only [pnSmul_pnSmul]
  unfold diagV10
  simp only [pnSmul_pnSmul]
  congr 1
  ring

lemma diag_cross_n1_m (n0 n1 n2 n3 : V3) :
    cross n1 (diagM n0 n1 n2 n3) =
      pnSmul (-(dot n1 (diagV10 n3 n0)) /
        (diagNW n0 n1 n2 n3 * norm (cross n1 n2))) (cross n1 n2) := by
  unfold diagM diagNW
  rw [cross_pnSmul_right, diag_cross_n1_w]
  simp only [pnSmul_pnSmul]
  unfold diagV21
  simp only [pnSmul_pnSmul]
  congr 1
  ring

lemma diag_cross_n2_m (n0 n1 n2 n3 : V3) :
    cross n2 (diagM n0 n1 n2 n3) =
      pnSmul (-(dot n2 (diagV10 n3 n0)) /
        (diagNW n0 n1 n2 n3 * norm (cross n1 n2))) (cross n1 n2) := by
  unfold diagM diagNW
  rw [cross_pnSmul_right, diag_cross_n2_w]
  simp only [pnSmul_pnSmul]
  unfold diagV21
  simp only [pnSmul_pnSmul]
  congr 1
  ring

/-- The rays of the second triangle `(-m, ·)` simplify to the same rays as the
    first. -/
lemma diag_isoEdge12_neg (m n : V3) : cross (pnSmul (-1) m) n = cross n m := by
  rw [cross_pnSmul_left, diag_cross_swap, pnSmul_pnSmul]
  norm_num

lemma diag_isoEdge13_neg (m n : V3) :
    pnSmul (-1) (cross (pnSmul (-1) m) n) = pnSmul (-1) (cross n m) := by
  rw [cross_pnSmul_left, diag_cross_swap, pnSmul_pnSmul]
  norm_num

/-! ### 4. The boundary arc lengths of the quadrilateral -/

/-- Arc of edge `n₀` between its two vertices. -/
noncomputable def quadTheta0 (n0 n1 n3 : V3) : ℝ :=
  cornerAngle (cross n0 n1) (cross n3 n0)
/-- Arc of edge `n₁` between its two vertices. -/
noncomputable def quadTheta1 (n0 n1 n2 : V3) : ℝ :=
  cornerAngle (cross n0 n1) (cross n1 n2)
/-- Arc of edge `n₂` between its two vertices. -/
noncomputable def quadTheta2 (n1 n2 n3 : V3) : ℝ :=
  cornerAngle (cross n1 n2) (cross n2 n3)
/-- Arc of edge `n₃` between its two vertices. -/
noncomputable def quadTheta3 (n2 n3 n0 : V3) : ℝ :=
  cornerAngle (cross n2 n3) (cross n3 n0)
/-- The diagonal arc length between the two opposite vertices. -/
noncomputable def quadDiag (n3 n0 n1 n2 : V3) : ℝ :=
  cornerAngle (cross n3 n0) (cross n1 n2)

/-! ### 5. The six corner-angle matchings -/

/-- **Diagonal angle matching for a convex spherical quadrilateral.**
    Under the four strict convexity conditions (each opposite vertex lies
    strictly inside the half-space of the edge it is not on) together with
    nondegeneracy of the four edge circles and of the diagonal, the
    constructed diagonal `m` has exactly the corner-angle data required by
    `fourFace_fanCertificate_of_diagonal`:

        (n₀,n₁,m) : (θ₀, θ₁, d)
        (-m,n₂,n₃) : (d, θ₂, θ₃). -/
theorem fourDiag_angle_matching
    (n0 n1 n2 n3 : V3)
    (h01 : cross n0 n1 ≠ ⟨0, 0, 0⟩) (h30 : cross n3 n0 ≠ ⟨0, 0, 0⟩)
    (h12 : cross n1 n2 ≠ ⟨0, 0, 0⟩) (h23 : cross n2 n3 ≠ ⟨0, 0, 0⟩)
    (hw : cross (diagV10 n3 n0) (diagV21 n1 n2) ≠ ⟨0, 0, 0⟩)
    (hn0v21 : dot n0 (diagV21 n1 n2) < 0)
    (hn1v10 : dot n1 (diagV10 n3 n0) < 0)
    (hn2v10 : dot n2 (diagV10 n3 n0) < 0)
    (hn3v21 : dot n3 (diagV21 n1 n2) < 0) :
    cornerAngle (isoEdge12 n0 n1) (isoEdge13 n0 (diagM n0 n1 n2 n3)) =
        quadTheta0 n0 n1 n3 ∧
    cornerAngle (isoEdge12 n0 n1) (isoEdge23 n1 (diagM n0 n1 n2 n3)) =
        quadTheta1 n0 n1 n2 ∧
    cornerAngle (isoEdge13 n0 (diagM n0 n1 n2 n3))
        (isoEdge23 n1 (diagM n0 n1 n2 n3)) = quadDiag n3 n0 n1 n2 ∧
    cornerAngle (isoEdge12 (pnSmul (-1) (diagM n0 n1 n2 n3)) n2)
        (isoEdge13 (pnSmul (-1) (diagM n0 n1 n2 n3)) n3) =
          quadDiag n3 n0 n1 n2 ∧
    cornerAngle (isoEdge12 (pnSmul (-1) (diagM n0 n1 n2 n3)) n2)
        (isoEdge23 n2 n3) = quadTheta2 n1 n2 n3 ∧
    cornerAngle (isoEdge13 (pnSmul (-1) (diagM n0 n1 n2 n3)) n3)
        (isoEdge23 n2 n3) = quadTheta3 n2 n3 n0 := by
  have hnwpos : 0 < diagNW n0 n1 n2 n3 := by
    dsimp [diagNW]
    exact norm_pos_of_ne_zero _ hw
  have hnaPos : 0 < norm (cross n3 n0) := norm_pos_of_ne_zero _ h30
  have hnbPos : 0 < norm (cross n1 n2) := norm_pos_of_ne_zero _ h12
  have hn01 : norm (cross n0 n1) ≠ 0 := norm_ne_zero_of_ne_zero _ h01
  have hn30 : norm (cross n3 n0) ≠ 0 := norm_ne_zero_of_ne_zero _ h30
  have hn12 : norm (cross n1 n2) ≠ 0 := norm_ne_zero_of_ne_zero _ h12
  have hn23 : norm (cross n2 n3) ≠ 0 := norm_ne_zero_of_ne_zero _ h23
  have hc0 : 0 < -(dot n0 (diagV21 n1 n2)) /
      (diagNW n0 n1 n2 n3 * norm (cross n3 n0)) :=
    div_pos (neg_pos.mpr hn0v21) (mul_pos hnwpos hnaPos)
  have hc3 : 0 < -(dot n3 (diagV21 n1 n2)) /
      (diagNW n0 n1 n2 n3 * norm (cross n3 n0)) :=
    div_pos (neg_pos.mpr hn3v21) (mul_pos hnwpos hnaPos)
  have hc1 : 0 < -(dot n1 (diagV10 n3 n0)) /
      (diagNW n0 n1 n2 n3 * norm (cross n1 n2)) :=
    div_pos (neg_pos.mpr hn1v10) (mul_pos hnwpos hnbPos)
  have hc2 : 0 < -(dot n2 (diagV10 n3 n0)) /
      (diagNW n0 n1 n2 n3 * norm (cross n1 n2)) :=
    div_pos (neg_pos.mpr hn2v10) (mul_pos hnwpos hnbPos)
  constructor
  · -- hang1a: corner at face n₀ of (n₀,n₁,m) equals arc of edge n₀.
    unfold isoEdge12 isoEdge13 quadTheta0
    rw [diag_neg_cross_n0]
    exact cornerAngle_smul_right_pos hc0 hn01 hn30
  constructor
  · -- hang1b: corner at face n₁ of (n₀,n₁,m) equals arc of edge n₁.
    unfold isoEdge12 isoEdge23 quadTheta1
    rw [diag_cross_n1_m]
    exact cornerAngle_smul_right_pos hc1 hn01 hn12
  constructor
  · -- hang1c: corner at the diagonal m equals the diagonal length d.
    unfold isoEdge13 isoEdge23 quadDiag
    rw [diag_neg_cross_n0, diag_cross_n1_m]
    rw [cornerAngle_smul_pos hc0 hc1 hn30 hn12]
  constructor
  · -- hang2a: corner at the diagonal -m equals d.
    unfold isoEdge12 isoEdge13 quadDiag
    rw [diag_isoEdge12_neg, diag_isoEdge13_neg, diag_cross_n2_m,
      diag_neg_cross_n3]
    rw [cornerAngle_smul_pos hc2 hc3 hn12 hn30]
    exact cornerAngle_comm (cross n1 n2) (cross n3 n0)
  constructor
  · -- hang2b: corner at face n₂ of (-m,n₂,n₃) equals arc of edge n₂.
    unfold isoEdge12 isoEdge23 quadTheta2
    rw [diag_isoEdge12_neg, diag_cross_n2_m]
    exact cornerAngle_smul_left_pos hc2 hn12 hn23
  · -- hang2c: corner at face n₃ of (-m,n₂,n₃) equals arc of edge n₃.
    unfold isoEdge13 isoEdge23 quadTheta3
    rw [diag_isoEdge13_neg, diag_neg_cross_n3]
    rw [cornerAngle_smul_left_pos hc3 hn30 hn23]
    exact cornerAngle_comm (cross n3 n0) (cross n2 n3)

/-! ### 6. Plugging into the landed n = 4 diagonal theorem -/

/-- The constructed diagonal satisfies the unit-norm and nondegeneracy part of
    `fourFace_fanCertificate_of_diagonal` (nondegeneracy of the two triangles is
    taken as the explicit convexity assumption `htri1`/`htri2`).  The remaining
    `hdu`/`hdv` dual-cone containments are still hypotheses here; see the final
    comment. -/
theorem fourDiag_face_pos_of_convex
    (n0 n1 n2 n3 : V3)
    (h0 : dot n0 n0 = 1) (h1 : dot n1 n1 = 1)
    (h2 : dot n2 n2 = 1) (h3 : dot n3 n3 = 1)
    (h01 : cross n0 n1 ≠ ⟨0, 0, 0⟩) (h30 : cross n3 n0 ≠ ⟨0, 0, 0⟩)
    (h12 : cross n1 n2 ≠ ⟨0, 0, 0⟩) (h23 : cross n2 n3 ≠ ⟨0, 0, 0⟩)
    (hw : cross (diagV10 n3 n0) (diagV21 n1 n2) ≠ ⟨0, 0, 0⟩)
    (hn0v21 : dot n0 (diagV21 n1 n2) < 0)
    (hn1v10 : dot n1 (diagV10 n3 n0) < 0)
    (hn2v10 : dot n2 (diagV10 n3 n0) < 0)
    (hn3v21 : dot n3 (diagV21 n1 n2) < 0)
    (htri1 : triple n0 n1 (diagM n0 n1 n2 n3) ≠ 0)
    (htri2 : triple (pnSmul (-1) (diagM n0 n1 n2 n3)) n2 n3 ≠ 0)
    (hdu : ∀ j : Fin 4,
        FanTriangleTransfer ⟨n0, n1, diagM n0 n1 n2 n3,
          quadTheta0 n0 n1 n3, quadTheta1 n0 n1 n2,
          quadDiag n3 n0 n1 n2⟩ (fanFace4 n0 n1 n2 n3 j))
    (hdv : ∀ j : Fin 4,
        FanTriangleTransfer ⟨pnSmul (-1) (diagM n0 n1 n2 n3), n2, n3,
          quadDiag n3 n0 n1 n2, quadTheta2 n1 n2 n3,
          quadTheta3 n2 n3 n0⟩ (fanFace4 n0 n1 n2 n3 j)) :
    ∀ j : Fin 4,
      0 < ∑ i : Fin 4, fourTheta
        (quadTheta0 n0 n1 n3) (quadTheta1 n0 n1 n2)
        (quadTheta2 n1 n2 n3) (quadTheta3 n2 n3 n0) i *
        dot (fanFace4 n0 n1 n2 n3 i) (fanFace4 n0 n1 n2 n3 j) := by
  have hm : dot (diagM n0 n1 n2 n3) (diagM n0 n1 n2 n3) = 1 :=
    diagM_unit n0 n1 n2 n3 hw
  have hang := fourDiag_angle_matching n0 n1 n2 n3
    h01 h30 h12 h23 hw hn0v21 hn1v10 hn2v10 hn3v21
  rcases hang with ⟨ha1, ha2, ha3, hb1, hb2, hb3⟩
  exact fourFace_face_pos_of_diagonal_chain n0 n1 n2 n3 (diagM n0 n1 n2 n3)
    (quadTheta0 n0 n1 n3) (quadTheta1 n0 n1 n2)
    (quadTheta2 n1 n2 n3) (quadTheta3 n2 n3 n0)
    (quadDiag n3 n0 n1 n2)
    h0 h1 h2 h3 hm htri1 htri2 ha1 ha2 ha3 hb1 hb2 hb3 hdu hdv

/-
  PRECISE STATUS / REMAINING STEP

  Landed here (proof-hole-free, `warningAsError` on):

    * the construction `diagV10`, `diagV21`, `diagM` from the four co-normals;
    * `diagV10_unit`, `diagV21_unit`, `diagM_unit`;
    * `diag_neg_cross_n0`, `diag_neg_cross_n3`, `diag_cross_n1_m`,
      `diag_cross_n2_m`: the four edge rays at the diagonal are positive
      scalar multiples of the original quadrilateral vertices;
    * `fourDiag_angle_matching`: the six corner-angle equalities, i.e. the
      angle-matching part of the explicit diagonal hypothesis, discharged under
      convexity sign conditions on the four opposite vertices;
    * `fourDiag_face_pos_of_convex`: the n = 4 seam (S) modulo only the
      dual-cone containments `hdu`, `hdv` and the two triangle nondegeneracy
      facts `htri1`, `htri2`.

  Remaining analytic/convexity step (NOT claimed here):

    (a) dual-cone containment: each boundary co-normal `nⱼ` is a nonnegative
        combination of `n₀,n₁,m` (resp. `-m,n₂,n₃`) with at least one strictly
        positive coefficient (`FanTriangleTransfer`).  For a convex quadrilateral
        this follows from the fact that the diagonal lies inside the polygon,
        i.e. from the same half-space inequalities used above plus the
        polar/cone description; it is a separate convex-cone argument.
    (b) `htri1`/`htri2`: nondegeneracy of the two triangles.  These follow from
        nondegeneracy of the triples `(n₀,n₁,n₂)` and `(n₁,n₂,n₃)` because the
        corresponding diagonal edge rays are positive multiples of `cross n₁ n₂`
        (proved above); they are kept as explicit hypotheses rather than
        re-derived here.
    (c) `triSide`/corner-angle bookkeeping: with the landed `corner12_13_eq`,
        `corner12_23_eq`, `corner13_23_eq` and `dots_sq_lt_one`, each `quadThetaᵢ`
        equals the corresponding `triSideA/B/C` of three consecutive co-normals
        (the "triSide between consecutive co-normals" of the task statement).
        The angle-matching theorem above uses the `cornerAngle` form directly,
        so this identification is not needed for the algebra.

  No existing file was modified by this module.
-/

end V3
end Vdb
