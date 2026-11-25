/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  The n = 5 seam (S), by iterating the n = 4 diagonal construction.

  A convex spherical pentagon with boundary co-normals n₀,..,n₄ is split
  into three spherical triangles by two diagonals:

      T₁ = (n₀, n₁, m₁),   T₂ = (-m₁, n₂, m₂),   T₃ = (-m₂, n₃, n₄).

  The first diagonal m₁ is the n = 4 diagonal of the quadrilateral
  (n₀, n₁, n₂, n₄) (it joins the vertex n₄∩n₀ to the vertex n₁∩n₂);
  the second diagonal m₂ is the n = 4 diagonal of the remaining
  quadrilateral (-m₁, n₂, n₃, n₄).  Thus the whole n = 5 argument is one
  iteration of the already-landed n = 4 algebra: the six corner-angle
  matchings of `fourDiag_angle_matching` and the two cone combination
  identities of `fourDiag_dual_cone` are applied to *both* quadrilaterals,
  and the five "far" dual-cone containments (n₃ in T₁, n₀,n₁ in T₂ and
  in T₃) are obtained by composing those identities.

  The resulting linked `FanChain 2` satisfies the `FanCertificate`
  requirements and `fanChain_face_pos_of_fanCertificate` gives (S).

  No existing file is modified.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.AngleNFaceFourDual

namespace Vdb
namespace V3

open scoped Real
open Real

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-! ### 0. Small vector-algebra helpers -/

lemma five_div_smul (s : ℝ) (hs : s ≠ 0) (v : V3) :
    pnSmul (1 / s) (pnSmul s v) = v := by
  rw [pnSmul_pnSmul]
  have h : (1 / s) * s = 1 := by field_simp [hs]
  rw [h, pnSmul_one]

lemma five_smul_add (s : ℝ) (u v : V3) :
    pnSmul s (V3.add u v) = V3.add (pnSmul s u) (pnSmul s v) := by
  apply V3.ext <;> dsimp [pnSmul, V3.add] <;> ring

lemma five_neg_smul (s : ℝ) (v : V3) : pnSmul s (pnSmul (-1) v) = pnSmul (-s) v := by
  rw [pnSmul_pnSmul]
  congr 1
  ring

lemma five_cross_neg_right (m n : V3) : cross n (pnSmul (-1) m) = cross m n := by
  rw [cross_pnSmul_right, diag_cross_swap, pnSmul_pnSmul]
  norm_num

/-- Solving `T • u = S • v + m` for `u`. -/
lemma five_solved (u v m : V3) (S T : ℝ) (hT : T ≠ 0)
    (h : pnSmul T u = V3.add (pnSmul S v) m) :
    u = V3.add (pnSmul (S / T) v) (pnSmul (1 / T) m) := by
  calc
    u = pnSmul (1 / T) (pnSmul T u) := (five_div_smul T hT u).symm
    _ = pnSmul (1 / T) (V3.add (pnSmul S v) m) := by rw [h]
    _ = V3.add (pnSmul ((1 / T) * S) v) (pnSmul (1 / T) m) := by
      rw [five_smul_add, pnSmul_pnSmul]
    _ = V3.add (pnSmul (S / T) v) (pnSmul (1 / T) m) := by
      apply congrArg₂ V3.add
      · congr 1
        ring
      · rfl

/-! ### 1. The two diagonals and the `FanChain 2` of the pentagon -/

/-- The first diagonal: the n = 4 diagonal of `(n₀,n₁,n₂,n₄)`. -/
noncomputable def pentM1 (n0 n1 n2 n4 : V3) : V3 :=
  diagM n0 n1 n2 n4

/-- The entry co-normal of the remaining quadrilateral. -/
noncomputable def pentA (n0 n1 n2 n4 : V3) : V3 :=
  pnSmul (-1) (pentM1 n0 n1 n2 n4)

/-- The second diagonal: the n = 4 diagonal of `(-m₁,n₂,n₃,n₄)`. -/
noncomputable def pentM2 (n0 n1 n2 n3 n4 : V3) : V3 :=
  diagM (pentA n0 n1 n2 n4) n2 n3 n4

/-- The five boundary weights of the pentagon. -/
def fiveTheta (θ0 θ1 θ2 θ3 θ4 : ℝ) (j : Fin 5) : ℝ :=
  if j = 0 then θ0 else if j = 1 then θ1 else if j = 2 then θ2
  else if j = 3 then θ3 else θ4

/-- The five boundary co-normals of the pentagon. -/
def fanFace5 (n0 n1 n2 n3 n4 : V3) (j : Fin 5) : V3 :=
  if j = 0 then n0 else if j = 1 then n1 else if j = 2 then n2
  else if j = 3 then n3 else n4

/-- The fan triangulation of the pentagon into three linked triangles. -/
noncomputable def pentChain (n0 n1 n2 n3 n4 : V3) : FanChain 2 :=
  FanChain.cons
    ⟨n0, n1, pentM1 n0 n1 n2 n4,
      quadTheta0 n0 n1 n4, quadTheta1 n0 n1 n2, quadDiag n4 n0 n1 n2⟩
    (FanChain.cons
      ⟨pentA n0 n1 n2 n4, n2, pentM2 n0 n1 n2 n3 n4,
        quadDiag n4 n0 n1 n2, quadTheta2 (pentA n0 n1 n2 n4) n2 n3,
        quadDiag n4 (pentA n0 n1 n2 n4) n2 n3⟩
      (FanChain.leaf
        ⟨pnSmul (-1) (pentM2 n0 n1 n2 n3 n4), n3, n4,
          quadDiag n4 (pentA n0 n1 n2 n4) n2 n3, quadTheta2 n2 n3 n4,
          quadTheta3 n3 n4 (pentA n0 n1 n2 n4)⟩))

lemma pentChain_linked (n0 n1 n2 n3 n4 : V3) :
    (pentChain n0 n1 n2 n3 n4).linked := by
  simp [pentChain, FanChain.linked, FanChain.head, pentA, pentM2,
    pnSmul_neg_involutive]

lemma pentChain_boundaryN (n0 n1 n2 n3 n4 : V3) :
    (pentChain n0 n1 n2 n3 n4).boundaryN = fanFace5 n0 n1 n2 n3 n4 := by
  funext j
  fin_cases j <;>
    simp [pentChain, fanFace5, FanChain.boundaryN, FanChain.head]

lemma pentChain_boundaryW (n0 n1 n2 n3 n4 : V3) :
    (pentChain n0 n1 n2 n3 n4).boundaryW =
      fiveTheta (quadTheta0 n0 n1 n4) (quadTheta1 n0 n1 n2)
        (quadTheta2 (pentA n0 n1 n2 n4) n2 n3) (quadTheta2 n2 n3 n4)
        (quadTheta3 n3 n4 (pentA n0 n1 n2 n4)) := by
  funext j
  fin_cases j <;>
    simp [pentChain, fiveTheta, FanChain.boundaryW, FanChain.head]

/-! ### 2. The two cone identities of an explicit n = 4 diagonal -/

/-- The pair of vector identities proved inside `fourDiag_dual_cone`,
    packaged so that it can be instantiated at both quadrilaterals. -/
lemma fiveDiag_comb (p0 p1 p2 p3 : V3)
    (h30 : cross p3 p0 ≠ ⟨0, 0, 0⟩) (h12 : cross p1 p2 ≠ ⟨0, 0, 0⟩)
    (hw : cross (diagV10 p3 p0) (diagV21 p1 p2) ≠ ⟨0, 0, 0⟩)
    (hc0 : 0 < dualC0 p0 p1 p2 p3) (hc1 : 0 < dualC1 p0 p1 p2 p3)
    (hc2 : 0 < dualC2 p0 p1 p2 p3) (hc3 : 0 < dualC3 p0 p1 p2 p3) :
    pnSmul (dualC1 p0 p1 p2 p3) p2 =
        V3.add (pnSmul (dualC2 p0 p1 p2 p3) p1) (diagM p0 p1 p2 p3) ∧
    pnSmul (dualC0 p0 p1 p2 p3) p3 =
        V3.add (pnSmul (dualC3 p0 p1 p2 p3) p0) (diagM p0 p1 p2 p3) := by
  have hm_unit : dot (diagM p0 p1 p2 p3) (diagM p0 p1 p2 p3) = 1 :=
    diagM_unit p0 p1 p2 p3 hw
  have hn3m : cross p3 (diagM p0 p1 p2 p3) =
      pnSmul (-(dualC3 p0 p1 p2 p3)) (cross p3 p0) := by
    have h := congrArg (fun v => pnSmul (-1) v)
      (diag_neg_cross_n3 p0 p1 p2 p3)
    simpa [dualC3, pnSmul_pnSmul] using h
  have hn0m : cross p0 (diagM p0 p1 p2 p3) =
      pnSmul (-(dualC0 p0 p1 p2 p3)) (cross p3 p0) := by
    have h := congrArg (fun v => pnSmul (-1) v)
      (diag_neg_cross_n0 p0 p1 p2 p3)
    simpa [dualC0, pnSmul_pnSmul] using h
  have hn1m : cross p1 (diagM p0 p1 p2 p3) =
      pnSmul (dualC1 p0 p1 p2 p3) (cross p1 p2) := by
    simpa [dualC1] using (diag_cross_n1_m p0 p1 p2 p3)
  have hn2m : cross p2 (diagM p0 p1 p2 p3) =
      pnSmul (dualC2 p0 p1 p2 p3) (cross p1 p2) := by
    simpa [dualC2] using (diag_cross_n2_m p0 p1 p2 p3)
  have hI2v : V3.sub (pnSmul (dualC1 p0 p1 p2 p3) p2)
      (pnSmul (dualC2 p0 p1 p2 p3) p1) = diagM p0 p1 p2 p3 := by
    apply dual_eq_of_parallel_and_cross
      (V3.sub (pnSmul (dualC1 p0 p1 p2 p3) p2)
        (pnSmul (dualC2 p0 p1 p2 p3) p1))
      (diagM p0 p1 p2 p3) p1 hm_unit
    · rw [dual_cross_sub_left, cross_pnSmul_left, cross_pnSmul_left, hn2m, hn1m]
      apply V3.ext <;> dsimp [V3.sub, pnSmul] <;> ring
    · rw [dual_cross_sub_left, cross_pnSmul_left, cross_pnSmul_left]
      rw [show cross p2 p1 = pnSmul (-1 : ℝ) (cross p1 p2) by
        simpa using (diag_cross_swap p2 p1)]
      rw [dual_cross_self]
      rw [diag_cross_swap (diagM p0 p1 p2 p3) p1, hn1m]
      apply V3.ext <;> dsimp [V3.sub, pnSmul] <;> ring
    · rw [diag_cross_swap (diagM p0 p1 p2 p3) p1, hn1m]
      exact dual_pnSmul_ne_zero (-1 : ℝ)
        (pnSmul (dualC1 p0 p1 p2 p3) (cross p1 p2)) (by norm_num)
        (dual_pnSmul_ne_zero (dualC1 p0 p1 p2 p3) (cross p1 p2)
          (ne_of_gt hc1) h12)
  have hI2 : pnSmul (dualC1 p0 p1 p2 p3) p2 =
      V3.add (pnSmul (dualC2 p0 p1 p2 p3) p1) (diagM p0 p1 p2 p3) := by
    apply V3.ext
    · have hx := congrArg V3.x hI2v
      dsimp [V3.sub] at hx
      dsimp [V3.add]
      linarith
    · have hy := congrArg V3.y hI2v
      dsimp [V3.sub] at hy
      dsimp [V3.add]
      linarith
    · have hz := congrArg V3.z hI2v
      dsimp [V3.sub] at hz
      dsimp [V3.add]
      linarith
  have hI3v : V3.sub (pnSmul (dualC0 p0 p1 p2 p3) p3)
      (pnSmul (dualC3 p0 p1 p2 p3) p0) = diagM p0 p1 p2 p3 := by
    apply dual_eq_of_parallel_and_cross
      (V3.sub (pnSmul (dualC0 p0 p1 p2 p3) p3)
        (pnSmul (dualC3 p0 p1 p2 p3) p0))
      (diagM p0 p1 p2 p3) p0 hm_unit
    · rw [dual_cross_sub_left, cross_pnSmul_left, cross_pnSmul_left, hn3m, hn0m]
      apply V3.ext <;> dsimp [V3.sub, pnSmul] <;> ring
    · rw [dual_cross_sub_left, cross_pnSmul_left, cross_pnSmul_left]
      rw [dual_cross_self]
      rw [diag_cross_swap (diagM p0 p1 p2 p3) p0, hn0m]
      apply V3.ext <;> dsimp [V3.sub, pnSmul] <;> ring
    · rw [diag_cross_swap (diagM p0 p1 p2 p3) p0, hn0m]
      exact dual_pnSmul_ne_zero (-1 : ℝ)
        (pnSmul (-(dualC0 p0 p1 p2 p3)) (cross p3 p0)) (by norm_num)
        (dual_pnSmul_ne_zero (-(dualC0 p0 p1 p2 p3)) (cross p3 p0)
          (neg_ne_zero.mpr (ne_of_gt hc0)) h30)
  have hI3 : pnSmul (dualC0 p0 p1 p2 p3) p3 =
      V3.add (pnSmul (dualC3 p0 p1 p2 p3) p0) (diagM p0 p1 p2 p3) := by
    apply V3.ext
    · have hx := congrArg V3.x hI3v
      dsimp [V3.sub] at hx
      dsimp [V3.add]
      linarith
    · have hy := congrArg V3.y hI3v
      dsimp [V3.sub] at hy
      dsimp [V3.add]
      linarith
    · have hz := congrArg V3.z hI3v
      dsimp [V3.sub] at hz
      dsimp [V3.add]
      linarith
  exact ⟨hI2, hI3⟩

/-! ### 3. The unconditional n = 5 seam -/

theorem fiveDiag_face_pos_unconditional
    (n0 n1 n2 n3 n4 : V3)
    (h0 : dot n0 n0 = 1) (h1 : dot n1 n1 = 1)
    (h2 : dot n2 n2 = 1) (h3 : dot n3 n3 = 1)
    (h4 : dot n4 n4 = 1)
    (h01 : cross n0 n1 ≠ ⟨0, 0, 0⟩) (h12 : cross n1 n2 ≠ ⟨0, 0, 0⟩)
    (h23 : cross n2 n3 ≠ ⟨0, 0, 0⟩) (h34 : cross n3 n4 ≠ ⟨0, 0, 0⟩)
    (h40 : cross n4 n0 ≠ ⟨0, 0, 0⟩) (h24 : cross n2 n4 ≠ ⟨0, 0, 0⟩)
    (hw1 : cross (diagV10 n4 n0) (diagV21 n1 n2) ≠ ⟨0, 0, 0⟩)
    (hw2 : cross (diagV10 n4 (pentA n0 n1 n2 n4)) (diagV21 n2 n3) ≠
      ⟨0, 0, 0⟩)
    (hn0v12 : dot n0 (diagV21 n1 n2) < 0)
    (hn1v40 : dot n1 (diagV10 n4 n0) < 0)
    (hn2v40 : dot n2 (diagV10 n4 n0) < 0)
    (hn4v12 : dot n4 (diagV21 n1 n2) < 0)
    (hav23 : dot (pentA n0 n1 n2 n4) (diagV21 n2 n3) < 0)
    (hn2v4a : dot n2 (diagV10 n4 (pentA n0 n1 n2 n4)) < 0)
    (hn3v4a : dot n3 (diagV10 n4 (pentA n0 n1 n2 n4)) < 0)
    (hn4v23 : dot n4 (diagV21 n2 n3) < 0) :
    ∀ j : Fin 5,
      0 < ∑ i : Fin 5,
        fiveTheta (quadTheta0 n0 n1 n4) (quadTheta1 n0 n1 n2)
          (quadTheta2 (pentA n0 n1 n2 n4) n2 n3) (quadTheta2 n2 n3 n4)
          (quadTheta3 n3 n4 (pentA n0 n1 n2 n4)) i *
          dot (fanFace5 n0 n1 n2 n3 n4 i) (fanFace5 n0 n1 n2 n3 n4 j) := by
  let C0 := dualC0 n0 n1 n2 n4
  let C1 := dualC1 n0 n1 n2 n4
  let C2 := dualC2 n0 n1 n2 n4
  let C4 := dualC3 n0 n1 n2 n4
  let Ba := dualC0 (pentA n0 n1 n2 n4) n2 n3 n4
  let B2 := dualC1 (pentA n0 n1 n2 n4) n2 n3 n4
  let B3 := dualC2 (pentA n0 n1 n2 n4) n2 n3 n4
  let B4 := dualC3 (pentA n0 n1 n2 n4) n2 n3 n4
  have hnw1 : 0 < diagNW n0 n1 n2 n4 := by
    dsimp [diagNW]
    exact norm_pos_of_ne_zero _ hw1
  have hnw2 : 0 < diagNW (pentA n0 n1 n2 n4) n2 n3 n4 := by
    dsimp [diagNW]
    exact norm_pos_of_ne_zero _ hw2
  have hna : 0 < norm (cross n4 n0) := norm_pos_of_ne_zero _ h40
  have hnb : 0 < norm (cross n1 n2) := norm_pos_of_ne_zero _ h12
  have hnc : 0 < norm (cross n2 n3) := norm_pos_of_ne_zero _ h23
  have hC0pos : 0 < C0 := by
    dsimp [C0, dualC0]
    exact div_pos (neg_pos.mpr hn0v12) (mul_pos hnw1 hna)
  have hC1pos : 0 < C1 := by
    dsimp [C1, dualC1]
    exact div_pos (neg_pos.mpr hn1v40) (mul_pos hnw1 hnb)
  have hC2pos : 0 < C2 := by
    dsimp [C2, dualC2]
    exact div_pos (neg_pos.mpr hn2v40) (mul_pos hnw1 hnb)
  have hC4pos : 0 < C4 := by
    dsimp [C4, dualC3]
    exact div_pos (neg_pos.mpr hn4v12) (mul_pos hnw1 hna)
  have hm1n4 : cross (pentM1 n0 n1 n2 n4) n4 =
      pnSmul C4 (cross n4 n0) := by
    dsimp [C4, pentM1, dualC3]
    rw [diag_cross_swap]
    exact diag_neg_cross_n3 n0 n1 n2 n4
  have hcross4A : cross n4 (pentA n0 n1 n2 n4) =
      pnSmul C4 (cross n4 n0) := by
    dsimp [pentA]
    rw [five_cross_neg_right, hm1n4]
  have h4anz : cross n4 (pentA n0 n1 n2 n4) ≠ ⟨0, 0, 0⟩ := by
    rw [hcross4A]
    exact dual_pnSmul_ne_zero C4 (cross n4 n0) (ne_of_gt hC4pos) h40
  have hnd : 0 < norm (cross n4 (pentA n0 n1 n2 n4)) :=
    norm_pos_of_ne_zero _ h4anz
  have hBapos : 0 < Ba := by
    dsimp [Ba, dualC0]
    exact div_pos (neg_pos.mpr hav23) (mul_pos hnw2 hnd)
  have hB2pos : 0 < B2 := by
    dsimp [B2, dualC1]
    exact div_pos (neg_pos.mpr hn2v4a) (mul_pos hnw2 hnc)
  have hB3pos : 0 < B3 := by
    dsimp [B3, dualC2]
    exact div_pos (neg_pos.mpr hn3v4a) (mul_pos hnw2 hnc)
  have hB4pos : 0 < B4 := by
    dsimp [B4, dualC3]
    exact div_pos (neg_pos.mpr hn4v23) (mul_pos hnw2 hnd)
  have hm1 : dot (pentM1 n0 n1 n2 n4) (pentM1 n0 n1 n2 n4) = 1 := by
    dsimp [pentM1]
    exact diagM_unit n0 n1 n2 n4 hw1
  have hm2 : dot (pentM2 n0 n1 n2 n3 n4) (pentM2 n0 n1 n2 n3 n4) = 1 := by
    dsimp [pentM2]
    exact diagM_unit (pentA n0 n1 n2 n4) n2 n3 n4 hw2
  have ha2nz : cross (pentA n0 n1 n2 n4) n2 ≠ ⟨0, 0, 0⟩ := by
    have hcoef : cross (pentA n0 n1 n2 n4) n2 =
        pnSmul C2 (cross n1 n2) := by
      dsimp [pentA, pentM1, C2, dualC2]
      rw [diag_isoEdge12_neg, diag_cross_n2_m]
    rw [hcoef]
    exact dual_pnSmul_ne_zero C2 (cross n1 n2) (ne_of_gt hC2pos) h12
  -- Angle matching for the two quadrilaterals.
  have hQ1 := fourDiag_angle_matching n0 n1 n2 n4 h01 h40 h12 h24 hw1
    hn0v12 hn1v40 hn2v40 hn4v12
  rcases hQ1 with ⟨ha1, ha2, ha3, _, _, _⟩
  have hQ2 := fourDiag_angle_matching (pentA n0 n1 n2 n4) n2 n3 n4
    ha2nz h4anz h23 h34 hw2 hav23 hn2v4a hn3v4a hn4v23
  rcases hQ2 with ⟨hb1, hb2, hb3, hc1, hc2, hc3⟩
  -- The arc of the shared edge `-m₁` is the first diagonal length.
  have hcrossA2 : cross (pentA n0 n1 n2 n4) n2 =
      pnSmul C2 (cross n1 n2) := by
    dsimp [pentA, pentM1, C2, dualC2]
    rw [diag_isoEdge12_neg, diag_cross_n2_m]
  have hthetaA : quadTheta0 (pentA n0 n1 n2 n4) n2 n4 =
      quadDiag n4 n0 n1 n2 := by
    unfold quadTheta0 quadDiag
    rw [hcrossA2, hcross4A]
    rw [cornerAngle_smul_pos hC2pos hC4pos
      (norm_ne_zero_of_ne_zero _ h12) (norm_ne_zero_of_ne_zero _ h40)]
    exact cornerAngle_comm (cross n1 n2) (cross n4 n0)
  -- The two cone identities at each quadrilateral.
  have hI1 := fiveDiag_comb n0 n1 n2 n4 h40 h12 hw1
    hC0pos hC1pos hC2pos hC4pos
  have hI2 := fiveDiag_comb (pentA n0 n1 n2 n4) n2 n3 n4 h4anz h23 hw2
    hBapos hB2pos hB3pos hB4pos
  -- Solving the four identities for the vertex co-normals.
  have hn2_t1 : n2 = V3.add (pnSmul (C2 / C1) n1) (pnSmul (1 / C1) (pentM1 n0 n1 n2 n4)) := by
    dsimp [C2, C1]
    exact five_solved n2 n1 (pentM1 n0 n1 n2 n4) (dualC2 n0 n1 n2 n4)
      (dualC1 n0 n1 n2 n4) (ne_of_gt hC1pos) hI1.1
  have hn4_t1 : n4 = V3.add (pnSmul (C4 / C0) n0) (pnSmul (1 / C0) (pentM1 n0 n1 n2 n4)) := by
    dsimp [C4, C0]
    exact five_solved n4 n0 (pentM1 n0 n1 n2 n4) (dualC3 n0 n1 n2 n4)
      (dualC0 n0 n1 n2 n4) (ne_of_gt hC0pos) hI1.2
  have hI1_2' : pnSmul C4 n0 =
      V3.add (pnSmul C0 n4) (pnSmul (-1) (pentM1 n0 n1 n2 n4)) := by
    apply V3.ext
    · have hx := congrArg V3.x hI1.2
      dsimp [C0, C4, pentM1, pnSmul, V3.add] at hx ⊢
      linarith
    · have hy := congrArg V3.y hI1.2
      dsimp [C0, C4, pentM1, pnSmul, V3.add] at hy ⊢
      linarith
    · have hz := congrArg V3.z hI1.2
      dsimp [C0, C4, pentM1, pnSmul, V3.add] at hz ⊢
      linarith
  have hI1_1' : pnSmul C2 n1 =
      V3.add (pnSmul C1 n2) (pnSmul (-1) (pentM1 n0 n1 n2 n4)) := by
    apply V3.ext
    · have hx := congrArg V3.x hI1.1
      dsimp [C1, C2, pentM1, pnSmul, V3.add] at hx ⊢
      linarith
    · have hy := congrArg V3.y hI1.1
      dsimp [C1, C2, pentM1, pnSmul, V3.add] at hy ⊢
      linarith
    · have hz := congrArg V3.z hI1.1
      dsimp [C1, C2, pentM1, pnSmul, V3.add] at hz ⊢
      linarith
  have hn0_t1 : n0 = V3.add (pnSmul (C0 / C4) n4)
      (pnSmul (1 / C4) (pnSmul (-1) (pentM1 n0 n1 n2 n4))) := by
    exact five_solved n0 n4 (pnSmul (-1) (pentM1 n0 n1 n2 n4)) C0 C4
      (ne_of_gt hC4pos) hI1_2'
  have hn1_t2 : n1 = V3.add (pnSmul (C1 / C2) n2)
      (pnSmul (1 / C2) (pnSmul (-1) (pentM1 n0 n1 n2 n4))) := by
    exact five_solved n1 n2 (pnSmul (-1) (pentM1 n0 n1 n2 n4)) C1 C2
      (ne_of_gt hC2pos) hI1_1'
  have hI2_1u : pnSmul B2 n3 =
      V3.add (pnSmul B3 n2) (pentM2 n0 n1 n2 n3 n4) := by
    dsimp [B2, B3]
    exact hI2.1
  have hI2_2u : pnSmul Ba n4 =
      V3.add (pnSmul B4 (pnSmul (-1) (pentM1 n0 n1 n2 n4)))
        (pentM2 n0 n1 n2 n3 n4) := by
    dsimp [Ba, B4]
    simpa [pentA, pentM2] using hI2.2
  have hm2_comb : pentM2 n0 n1 n2 n3 n4 =
      V3.add (pnSmul Ba n4) (pnSmul B4 (pentM1 n0 n1 n2 n4)) := by
    have h := hI2_2u
    rw [five_neg_smul] at h
    apply V3.ext
    · have hx := congrArg V3.x h
      dsimp [pentM2, pnSmul, V3.add] at hx ⊢
      linarith
    · have hy := congrArg V3.y h
      dsimp [pentM2, pnSmul, V3.add] at hy ⊢
      linarith
    · have hz := congrArg V3.z h
      dsimp [pentM2, pnSmul, V3.add] at hz ⊢
      linarith
  have hB2n3 : pnSmul B2 n3 =
      V3.add (pnSmul B3 n2) (V3.add (pnSmul Ba n4)
        (pnSmul B4 (pentM1 n0 n1 n2 n4))) := by
    rw [hI2_1u, hm2_comb]
  have hscale_n2_t1 : pnSmul (B3 / B2) n2 =
      V3.add (pnSmul ((B3 / B2) * (C2 / C1)) n1)
        (pnSmul ((B3 / B2) * (1 / C1)) (pentM1 n0 n1 n2 n4)) := by
    calc
      pnSmul (B3 / B2) n2 = pnSmul (B3 / B2)
          (V3.add (pnSmul (C2 / C1) n1)
            (pnSmul (1 / C1) (pentM1 n0 n1 n2 n4))) := congrArg (fun v => pnSmul (B3 / B2) v) hn2_t1
      _ = V3.add (pnSmul ((B3 / B2) * (C2 / C1)) n1)
            (pnSmul ((B3 / B2) * (1 / C1)) (pentM1 n0 n1 n2 n4)) := by
              rw [five_smul_add, pnSmul_pnSmul, pnSmul_pnSmul]
  have hscale_n4_t1 : pnSmul (Ba / B2) n4 =
      V3.add (pnSmul ((Ba / B2) * (C4 / C0)) n0)
        (pnSmul ((Ba / B2) * (1 / C0)) (pentM1 n0 n1 n2 n4)) := by
    calc
      pnSmul (Ba / B2) n4 = pnSmul (Ba / B2)
          (V3.add (pnSmul (C4 / C0) n0)
            (pnSmul (1 / C0) (pentM1 n0 n1 n2 n4))) := congrArg (fun v => pnSmul (Ba / B2) v) hn4_t1
      _ = V3.add (pnSmul ((Ba / B2) * (C4 / C0)) n0)
            (pnSmul ((Ba / B2) * (1 / C0)) (pentM1 n0 n1 n2 n4)) := by
              rw [five_smul_add, pnSmul_pnSmul, pnSmul_pnSmul]
  have hn3_t1 : n3 = V3.add
      (V3.add (pnSmul ((Ba * C4) / (C0 * B2)) n0)
        (pnSmul ((B3 * C2) / (C1 * B2)) n1))
      (pnSmul (B3 / (C1 * B2) + Ba / (C0 * B2) + B4 / B2)
        (pentM1 n0 n1 n2 n4)) := by
    calc
      n3 = pnSmul (1 / B2) (pnSmul B2 n3) :=
        (five_div_smul B2 (ne_of_gt hB2pos) n3).symm
      _ = pnSmul (1 / B2) (V3.add (pnSmul B3 n2)
            (V3.add (pnSmul Ba n4)
              (pnSmul B4 (pentM1 n0 n1 n2 n4)))) := by rw [hB2n3]
      _ = V3.add (pnSmul (B3 / B2) n2)
            (V3.add (pnSmul (Ba / B2) n4)
              (pnSmul (B4 / B2) (pentM1 n0 n1 n2 n4))) := by
                apply V3.ext <;> dsimp [pnSmul, V3.add] <;>
                  field_simp [ne_of_gt hB2pos]
      _ = V3.add
            (V3.add (pnSmul ((B3 / B2) * (C2 / C1)) n1)
              (pnSmul ((B3 / B2) * (1 / C1)) (pentM1 n0 n1 n2 n4)))
            (V3.add (V3.add
              (pnSmul ((Ba / B2) * (C4 / C0)) n0)
              (pnSmul ((Ba / B2) * (1 / C0)) (pentM1 n0 n1 n2 n4)))
              (pnSmul (B4 / B2) (pentM1 n0 n1 n2 n4))) := by
                rw [hscale_n2_t1, hscale_n4_t1]
      _ = V3.add
            (V3.add (pnSmul ((Ba * C4) / (C0 * B2)) n0)
              (pnSmul ((B3 * C2) / (C1 * B2)) n1))
            (pnSmul (B3 / (C1 * B2) + Ba / (C0 * B2) + B4 / B2)
              (pentM1 n0 n1 n2 n4)) := by
                apply V3.ext <;> dsimp [pnSmul, V3.add] <;> ring
  have hn4_t2 : n4 = V3.add
      (pnSmul (B4 / Ba) (pnSmul (-1) (pentM1 n0 n1 n2 n4)))
      (pnSmul (1 / Ba) (pentM2 n0 n1 n2 n3 n4)) := by
    apply five_solved n4 (pnSmul (-1) (pentM1 n0 n1 n2 n4))
      (pentM2 n0 n1 n2 n3 n4)
      (dualC3 (pentA n0 n1 n2 n4) n2 n3 n4)
      (dualC0 (pentA n0 n1 n2 n4) n2 n3 n4) (ne_of_gt hBapos)
    simpa [pentA, pentM2] using hI2.2
  have hscale_n4_t2 : pnSmul (C0 / C4) n4 =
      V3.add (pnSmul ((C0 / C4) * (B4 / Ba))
        (pnSmul (-1) (pentM1 n0 n1 n2 n4)))
        (pnSmul ((C0 / C4) * (1 / Ba)) (pentM2 n0 n1 n2 n3 n4)) := by
    calc
      pnSmul (C0 / C4) n4 = pnSmul (C0 / C4)
          (V3.add (pnSmul (B4 / Ba) (pnSmul (-1) (pentM1 n0 n1 n2 n4)))
            (pnSmul (1 / Ba) (pentM2 n0 n1 n2 n3 n4))) := congrArg (fun v => pnSmul (C0 / C4) v) hn4_t2
      _ = V3.add (pnSmul ((C0 / C4) * (B4 / Ba))
            (pnSmul (-1) (pentM1 n0 n1 n2 n4)))
            (pnSmul ((C0 / C4) * (1 / Ba)) (pentM2 n0 n1 n2 n3 n4)) := by
               apply V3.ext <;> dsimp [pnSmul, V3.add] <;> ring
  have hn0_t2 : n0 = V3.add
      (V3.add (pnSmul ((C0 / C4) * (B4 / Ba) + 1 / C4)
        (pnSmul (-1) (pentM1 n0 n1 n2 n4))) (pnSmul 0 n2))
      (pnSmul ((C0 / C4) * (1 / Ba)) (pentM2 n0 n1 n2 n3 n4)) := by
    calc
      n0 = V3.add (pnSmul (C0 / C4) n4)
            (pnSmul (1 / C4) (pnSmul (-1) (pentM1 n0 n1 n2 n4))) := hn0_t1
      _ = V3.add (V3.add (pnSmul ((C0 / C4) * (B4 / Ba))
            (pnSmul (-1) (pentM1 n0 n1 n2 n4)))
            (pnSmul ((C0 / C4) * (1 / Ba)) (pentM2 n0 n1 n2 n3 n4)))
            (pnSmul (1 / C4) (pnSmul (-1) (pentM1 n0 n1 n2 n4))) := by
              rw [hscale_n4_t2]
      _ = V3.add
            (V3.add (pnSmul ((C0 / C4) * (B4 / Ba) + 1 / C4)
              (pnSmul (-1) (pentM1 n0 n1 n2 n4))) (pnSmul 0 n2))
            (pnSmul ((C0 / C4) * (1 / Ba)) (pentM2 n0 n1 n2 n3 n4)) := by
              apply V3.ext <;> dsimp [pnSmul, V3.add] <;> ring
  have hI2_2' : pnSmul B4 (pnSmul (-1) (pentM1 n0 n1 n2 n4)) =
      V3.add (pnSmul Ba n4) (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4)) := by
    have h := hI2_2u
    rw [five_neg_smul] at h
    apply V3.ext
    · have hx := congrArg V3.x h
      dsimp [pentM2, pnSmul, V3.add] at hx ⊢
      linarith
    · have hy := congrArg V3.y h
      dsimp [pentM2, pnSmul, V3.add] at hy ⊢
      linarith
    · have hz := congrArg V3.z h
      dsimp [pentM2, pnSmul, V3.add] at hz ⊢
      linarith
  have hnegM1_t3 : pnSmul (-1) (pentM1 n0 n1 n2 n4) =
      V3.add (pnSmul (Ba / B4) n4)
        (pnSmul (1 / B4) (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4))) := by
    exact five_solved (pnSmul (-1) (pentM1 n0 n1 n2 n4)) n4
      (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4)) Ba B4 (ne_of_gt hB4pos) hI2_2'
  have hI2_1' : pnSmul B3 n2 =
      V3.add (pnSmul B2 n3) (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4)) := by
    have h := hI2_1u
    apply V3.ext
    · have hx := congrArg V3.x h
      dsimp [pentM2, pnSmul, V3.add] at hx ⊢
      linarith
    · have hy := congrArg V3.y h
      dsimp [pentM2, pnSmul, V3.add] at hy ⊢
      linarith
    · have hz := congrArg V3.z h
      dsimp [pentM2, pnSmul, V3.add] at hz ⊢
      linarith
  have hn2_t3 : n2 = V3.add (pnSmul (B2 / B3) n3)
      (pnSmul (1 / B3) (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4))) := by
    exact five_solved n2 n3 (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4)) B2 B3
      (ne_of_gt hB3pos) hI2_1'
  have hn1_t2' : n1 = V3.add
      (V3.add (pnSmul (1 / C2) (pnSmul (-1) (pentM1 n0 n1 n2 n4)))
        (pnSmul (C1 / C2) n2)) (pnSmul 0 (pentM2 n0 n1 n2 n3 n4)) := by
    calc
      n1 = V3.add (pnSmul (C1 / C2) n2)
        (pnSmul (1 / C2) (pnSmul (-1) (pentM1 n0 n1 n2 n4))) := hn1_t2
      _ = V3.add
        (V3.add (pnSmul (1 / C2) (pnSmul (-1) (pentM1 n0 n1 n2 n4)))
          (pnSmul (C1 / C2) n2)) (pnSmul 0 (pentM2 n0 n1 n2 n3 n4)) := by
            apply V3.ext <;> dsimp [pnSmul, V3.add] <;> ring
  have hscale_negM1_C4 : pnSmul (1 / C4) (pnSmul (-1) (pentM1 n0 n1 n2 n4)) =
      V3.add (pnSmul ((1 / C4) * (Ba / B4)) n4)
        (pnSmul ((1 / C4) * (1 / B4))
          (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4))) := by
    calc
      pnSmul (1 / C4) (pnSmul (-1) (pentM1 n0 n1 n2 n4)) =
          pnSmul (1 / C4) (V3.add (pnSmul (Ba / B4) n4)
            (pnSmul (1 / B4)
              (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4)))) := congrArg (fun v => pnSmul (1 / C4) v) hnegM1_t3
      _ = V3.add (pnSmul ((1 / C4) * (Ba / B4)) n4)
            (pnSmul ((1 / C4) * (1 / B4))
              (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4))) := by
                rw [five_smul_add, pnSmul_pnSmul, pnSmul_pnSmul]
  have hn0_t3 : n0 = V3.add
      (V3.add
        (pnSmul ((1 / C4) * (1 / B4))
          (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4))) (pnSmul 0 n3))
      (pnSmul (C0 / C4 + (1 / C4) * (Ba / B4)) n4) := by
    calc
      n0 = V3.add (pnSmul (C0 / C4) n4)
            (pnSmul (1 / C4) (pnSmul (-1) (pentM1 n0 n1 n2 n4))) := hn0_t1
      _ = V3.add (pnSmul (C0 / C4) n4)
            (V3.add (pnSmul ((1 / C4) * (Ba / B4)) n4)
              (pnSmul ((1 / C4) * (1 / B4))
                (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4)))) := by
                rw [hscale_negM1_C4]
      _ = V3.add
            (V3.add
              (pnSmul ((1 / C4) * (1 / B4))
                (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4))) (pnSmul 0 n3))
            (pnSmul (C0 / C4 + (1 / C4) * (Ba / B4)) n4) := by
                apply V3.ext <;> dsimp [pnSmul, V3.add] <;> ring
  have hscale_negM1_C2 : pnSmul (1 / C2) (pnSmul (-1) (pentM1 n0 n1 n2 n4)) =
      V3.add (pnSmul ((1 / C2) * (Ba / B4)) n4)
        (pnSmul ((1 / C2) * (1 / B4))
          (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4))) := by
    calc
      pnSmul (1 / C2) (pnSmul (-1) (pentM1 n0 n1 n2 n4)) =
          pnSmul (1 / C2) (V3.add (pnSmul (Ba / B4) n4)
            (pnSmul (1 / B4)
              (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4)))) := congrArg (fun v => pnSmul (1 / C2) v) hnegM1_t3
      _ = V3.add (pnSmul ((1 / C2) * (Ba / B4)) n4)
            (pnSmul ((1 / C2) * (1 / B4))
              (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4))) := by
                rw [five_smul_add, pnSmul_pnSmul, pnSmul_pnSmul]
  have hscale_n2_C1C2 : pnSmul (C1 / C2) n2 =
      V3.add (pnSmul ((C1 / C2) * (B2 / B3)) n3)
        (pnSmul ((C1 / C2) * (1 / B3))
          (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4))) := by
    calc
      pnSmul (C1 / C2) n2 = pnSmul (C1 / C2)
          (V3.add (pnSmul (B2 / B3) n3)
            (pnSmul (1 / B3)
              (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4)))) := congrArg (fun v => pnSmul (C1 / C2) v) hn2_t3
      _ = V3.add (pnSmul ((C1 / C2) * (B2 / B3)) n3)
            (pnSmul ((C1 / C2) * (1 / B3))
              (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4))) := by
                rw [five_smul_add, pnSmul_pnSmul, pnSmul_pnSmul]
  have hn1_t3 : n1 = V3.add
      (V3.add
        (pnSmul ((1 / C2) * (1 / B4) + (C1 / C2) * (1 / B3))
          (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4)))
        (pnSmul ((C1 / C2) * (B2 / B3)) n3))
      (pnSmul ((1 / C2) * (Ba / B4)) n4) := by
    calc
      n1 = V3.add
            (V3.add (pnSmul (1 / C2) (pnSmul (-1) (pentM1 n0 n1 n2 n4)))
              (pnSmul (C1 / C2) n2))
            (pnSmul 0 (pentM2 n0 n1 n2 n3 n4)) := hn1_t2'
      _ = V3.add
            (V3.add (V3.add (pnSmul ((1 / C2) * (Ba / B4)) n4)
              (pnSmul ((1 / C2) * (1 / B4))
                (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4))))
              (V3.add (pnSmul ((C1 / C2) * (B2 / B3)) n3)
                (pnSmul ((C1 / C2) * (1 / B3))
                  (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4)))))
            (pnSmul 0 (pentM2 n0 n1 n2 n3 n4)) := by
              rw [hscale_negM1_C2, hscale_n2_C1C2]
      _ = V3.add
            (V3.add
              (pnSmul ((1 / C2) * (1 / B4) + (C1 / C2) * (1 / B3))
                (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4)))
              (pnSmul ((C1 / C2) * (B2 / B3)) n3))
            (pnSmul ((1 / C2) * (Ba / B4)) n4) := by
                apply V3.ext <;> dsimp [pnSmul, V3.add] <;> ring
  -- Dual-cone containments supplied by the two landed n = 4 theorems.
  have hdu1 := fourDiag_dual_cone n0 n1 n2 n4 h40 h12 hw1
    hn0v12 hn1v40 hn2v40 hn4v12
  have hdu2 := fourDiag_dual_cone (pentA n0 n1 n2 n4) n2 n3 n4
    h4anz h23 hw2 hav23 hn2v4a hn3v4a hn4v23
  have hdu2a : ∀ j : Fin 4,
      FanTriangleTransfer
        ⟨pentA n0 n1 n2 n4, n2, pentM2 n0 n1 n2 n3 n4,
          quadDiag n4 n0 n1 n2, quadTheta2 (pentA n0 n1 n2 n4) n2 n3,
          quadDiag n4 (pentA n0 n1 n2 n4) n2 n3⟩
        (fanFace4 (pentA n0 n1 n2 n4) n2 n3 n4 j) := by
    intro j
    have h := hdu2.1 j
    rw [hthetaA] at h
    simpa [quadTheta1, quadTheta2, pentM2] using h
  -- Build the certificate and conclude.
  apply fanChain_face_pos_of_fanCertificate
  refine ⟨pentChain n0 n1 n2 n3 n4, pentChain_linked n0 n1 n2 n3 n4,
    (pentChain_boundaryN n0 n1 n2 n3 n4).symm,
    (pentChain_boundaryW n0 n1 n2 n3 n4).symm, ?_, ?_⟩
  · constructor
    · exact ⟨h0, h1, hm1,
        fourDiag_tri1_ne n0 n1 n2 n4 hw1 h12 hn0v12 hn1v40,
        ha1, ha2, ha3⟩
    · constructor
      · exact ⟨pnSmul_neg_unit (pentM1 n0 n1 n2 n4) hm1, h2, hm2,
          fourDiag_tri1_ne (pentA n0 n1 n2 n4) n2 n3 n4 hw2 h23
            hav23 hn2v4a,
          (by simpa [hthetaA, pentM2] using hb1), hb2, hb3⟩
      · exact ⟨pnSmul_neg_unit (pentM2 n0 n1 n2 n3 n4) hm2, h3, h4,
          fourDiag_tri2_ne (pentA n0 n1 n2 n4) n2 n3 n4 hw2 h4anz
            hn3v4a hn4v23,
          hc1, hc2, hc3⟩
  · intro j
    fin_cases j <;> dsimp [fanFace5]
    · refine ⟨?_, ?_, ?_⟩
      · exact dual_transfer_a n0 n1 (pentM1 n0 n1 n2 n4)
          (quadTheta0 n0 n1 n4) (quadTheta1 n0 n1 n2)
          (quadDiag n4 n0 n1 n2)
      · exact dual_transfer_of_comb (pentA n0 n1 n2 n4) n2
          (pentM2 n0 n1 n2 n3 n4) n0
          (quadDiag n4 n0 n1 n2) (quadTheta2 (pentA n0 n1 n2 n4) n2 n3)
          (quadDiag n4 (pentA n0 n1 n2 n4) n2 n3)
          ((C0 / C4) * (B4 / Ba) + 1 / C4) 0 ((C0 / C4) * (1 / Ba))
          (le_of_lt (add_pos
            (mul_pos (div_pos hC0pos hC4pos) (div_pos hB4pos hBapos))
            (div_pos zero_lt_one hC4pos)))
          (le_refl 0)
          (le_of_lt (mul_pos (div_pos hC0pos hC4pos)
            (div_pos zero_lt_one hBapos)))
          (Or.inl (add_pos
            (mul_pos (div_pos hC0pos hC4pos) (div_pos hB4pos hBapos))
            (div_pos zero_lt_one hC4pos))) hn0_t2
      · exact dual_transfer_of_comb
          (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4)) n3 n4 n0
          (quadDiag n4 (pentA n0 n1 n2 n4) n2 n3) (quadTheta2 n2 n3 n4)
          (quadTheta3 n3 n4 (pentA n0 n1 n2 n4))
          ((1 / C4) * (1 / B4)) 0 (C0 / C4 + (1 / C4) * (Ba / B4))
          (le_of_lt (mul_pos (div_pos zero_lt_one hC4pos)
              (div_pos zero_lt_one hB4pos)))
          (le_refl 0)
          (le_of_lt (add_pos (div_pos hC0pos hC4pos)
              (mul_pos (div_pos zero_lt_one hC4pos) (div_pos hBapos hB4pos))))
          (Or.inl (mul_pos (div_pos zero_lt_one hC4pos)
              (div_pos zero_lt_one hB4pos))) hn0_t3
    · refine ⟨?_, ?_, ?_⟩
      · exact dual_transfer_b n0 n1 (pentM1 n0 n1 n2 n4)
          (quadTheta0 n0 n1 n4) (quadTheta1 n0 n1 n2)
          (quadDiag n4 n0 n1 n2)
      · exact dual_transfer_of_comb (pentA n0 n1 n2 n4) n2
          (pentM2 n0 n1 n2 n3 n4) n1
          (quadDiag n4 n0 n1 n2) (quadTheta2 (pentA n0 n1 n2 n4) n2 n3)
          (quadDiag n4 (pentA n0 n1 n2 n4) n2 n3)
          (1 / C2) (C1 / C2) 0
          (le_of_lt (div_pos zero_lt_one hC2pos))
          (le_of_lt (div_pos hC1pos hC2pos)) (le_refl 0)
          (Or.inl (div_pos zero_lt_one hC2pos)) hn1_t2'
      · exact dual_transfer_of_comb
          (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4)) n3 n4 n1
          (quadDiag n4 (pentA n0 n1 n2 n4) n2 n3) (quadTheta2 n2 n3 n4)
          (quadTheta3 n3 n4 (pentA n0 n1 n2 n4))
          ((1 / C2) * (1 / B4) + (C1 / C2) * (1 / B3))
          ((C1 / C2) * (B2 / B3))
          ((1 / C2) * (Ba / B4))
          (le_of_lt (add_pos
              (mul_pos (div_pos zero_lt_one hC2pos) (div_pos zero_lt_one hB4pos))
              (mul_pos (div_pos hC1pos hC2pos) (div_pos zero_lt_one hB3pos))))
          (le_of_lt (mul_pos (div_pos hC1pos hC2pos)
              (div_pos hB2pos hB3pos)))
          (le_of_lt (mul_pos (div_pos zero_lt_one hC2pos)
              (div_pos hBapos hB4pos)))
          (Or.inl (add_pos
              (mul_pos (div_pos zero_lt_one hC2pos) (div_pos zero_lt_one hB4pos))
              (mul_pos (div_pos hC1pos hC2pos) (div_pos zero_lt_one hB3pos))))
          hn1_t3
    · refine ⟨?_, ?_, ?_⟩
      · simpa [fanFace4, pentM1] using (hdu1.1 (2 : Fin 4))
      · exact dual_transfer_b (pentA n0 n1 n2 n4) n2
          (pentM2 n0 n1 n2 n3 n4)
          (quadDiag n4 n0 n1 n2) (quadTheta2 (pentA n0 n1 n2 n4) n2 n3)
          (quadDiag n4 (pentA n0 n1 n2 n4) n2 n3)
      · simpa [fanFace4, pentM2, FanChainTransferAt] using (hdu2.2 (1 : Fin 4))
    · refine ⟨?_, ?_, ?_⟩
      · exact dual_transfer_of_comb n0 n1 (pentM1 n0 n1 n2 n4) n3
          (quadTheta0 n0 n1 n4) (quadTheta1 n0 n1 n2)
          (quadDiag n4 n0 n1 n2)
          ((Ba * C4) / (C0 * B2)) ((B3 * C2) / (C1 * B2))
          (B3 / (C1 * B2) + Ba / (C0 * B2) + B4 / B2)
          (le_of_lt (div_pos (mul_pos hBapos hC4pos)
              (mul_pos hC0pos hB2pos)))
          (le_of_lt (div_pos (mul_pos hB3pos hC2pos)
              (mul_pos hC1pos hB2pos)))
          (le_of_lt (add_pos
              (add_pos (div_pos hB3pos (mul_pos hC1pos hB2pos))
                (div_pos hBapos (mul_pos hC0pos hB2pos)))
              (div_pos hB4pos hB2pos)))
          (Or.inl (div_pos (mul_pos hBapos hC4pos)
              (mul_pos hC0pos hB2pos))) hn3_t1
      · simpa [fanFace4] using (hdu2a (2 : Fin 4))
      · exact dual_transfer_b (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4)) n3 n4
          (quadDiag n4 (pentA n0 n1 n2 n4) n2 n3) (quadTheta2 n2 n3 n4)
          (quadTheta3 n3 n4 (pentA n0 n1 n2 n4))
    · refine ⟨?_, ?_, ?_⟩
      · simpa [fanFace4, pentM1] using (hdu1.1 (3 : Fin 4))
      · have hm2eq : diagM (pentA n0 n1 n2 n4) n2 n3 n4 =
            pentM2 n0 n1 n2 n3 n4 := rfl
        have h := hdu2.1 (3 : Fin 4)
        rw [hthetaA, hm2eq] at h
        simpa [fanFace4, FanChainTransferAt, quadTheta1, quadTheta2] using h
      · exact dual_transfer_m (pnSmul (-1) (pentM2 n0 n1 n2 n3 n4)) n3 n4
          (quadDiag n4 (pentA n0 n1 n2 n4) n2 n3) (quadTheta2 n2 n3 n4)
          (quadTheta3 n3 n4 (pentA n0 n1 n2 n4))

/-! ### 4. Status -/

/-
  Landed above (proof-hole-free, `warningAsError` on):

    * `pentM1`, `pentA`, `pentM2`, `fiveTheta`, `fanFace5`, `pentChain`
      and its linking/boundary lemmas;
    * `fiveDiag_comb`: the two cone identities of an explicit n = 4
      diagonal, reused at both quadrilaterals;
    * `fiveDiag_face_pos_unconditional`: (S) for five face normals under
      the explicit convexity and nondegeneracy hypotheses listed in its
      statement.  All nine corner-angle matchings come from applying
      `fourDiag_angle_matching` twice; all fifteen dual-cone containments
      come from `fourDiag_dual_cone` twice plus the five composed identities
      proved here (n₃ in T₁, n₀/n₁ in T₂, n₀/n₁ in T₃).

  No existing file was modified by this module.
-/

end V3
end Vdb
