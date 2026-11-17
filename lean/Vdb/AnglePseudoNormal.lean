/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  Angle-weighted (Bærentzen–Aanæs) vertex pseudo-normals, on the F16
  tetrahedron (`Vdb/PseudoNormal.lean`).

  `mesh_pseudo_normal` in `src/tinyvdb_mesh_conversion.inl` (the F11 fix)
  sums **unweighted** unit face normals at a vertex feature. The F16
  machine-checked counterexample shows that sum pairs negatively with
  `p − q` in the rational tetrahedron — an outside point whose closest
  point is the apex is classified as inside. The classical alternative
  is the angle-weighted pseudo-normal

      ν = Σ_f θ_f · n_f

  with `θ_f` the face's corner angle at the vertex. For the F16
  tetrahedron the apex faces subtend

      face 1 (x ≤ 0):            θ₁ = arccos (3/5)  (cos θ₁ = 3/5)
      face 2 (normal (−2,2,1)):  θ₂ = arccos (4/5)  (cos θ₂ = 4/5)
      face 3 (normal (−2,−2,1)): θ₃ = arccos (4/5)  (cos θ₃ = 4/5)

  and the angle-weighted normal is

      ν = θ₁·n₁ + θ₂·n₂ + θ₃·n₃ = (θ₁ − 4θ/3, 0, 2θ/3),

  pairing with `p = (t, 0, 0)` as `t·(θ₁ − 4θ/3)`. Since
  `cos(3θ₁) = -117/125 < -527/625 = cos(4θ)` on `[0, π]` with `3θ₁ ≤ π`,
  `cos` strictly decreasing gives `3θ₁ > 4θ`, hence `0 < ⟨ν, p − q⟩` —
  **angle weighting fixes the F16 misclassification**
  (`angle_weighted_apex_pairs_pos`).

  What this does **not** show: soundness of angle weighting for general
  convex polyhedra at closest points (that general claim is open; the
  landed F16 rule is the any-incident-face-pairs-positively one, not
  angle weighting); the edge and face-interior features (unweighted
  sums are already sound there, `edge_pairing_nonneg`); any angle-weight
  implementation in C. Corner angles of the two slanted faces are equal
  by the tetrahedron's dihedral symmetry (both `arccos (4/5)`).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.PseudoNormal
import Vdb.WindingDipole
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

open Vdb Vdb.V3

namespace Vdb

open Vdb Vdb.V3

/-! ### Corner angles -/

/-- The angle at the vertex `q` between the two edge vectors `u = q → x`
    and `v = q → y` of a face, in `[0, π]` (via `arccos` of the normalized
    dot). For a nondegenerate face this is the face's corner angle. -/
noncomputable def cornerAngle (u v : V3) : ℝ :=
  Real.arccos (V3.dot u v / (V3.norm u * V3.norm v))

theorem cornerAngle_comm (u v : V3) : cornerAngle u v = cornerAngle v u := by
  rw [cornerAngle, cornerAngle]
  congr 1
  have hd : V3.dot v u = V3.dot u v := by unfold V3.dot; ring
  rw [hd, mul_comm]

theorem cornerAngle_nonneg (u v : V3) : 0 ≤ cornerAngle u v :=
  Real.arccos_nonneg _

/-! ### The F16 tetrahedron apex vertex and faces

Apex `q = (0, 0, 0)`; the three tight side-face corners are
`A = (0, 1/2, -1)`, `B = (0, -1/2, -1)`, `C = (-1/2, 0, -1)`.
Face 1 = `(q A B)` (normal `n₁ = (1, 0, 0)`),
face 2 = `(q A C)` (normal `n₂ = (−2/3, 2/3, 1/3)`),
face 3 = `(q B C)` (normal `n₃ = (−2/3, −2/3, 1/3)`). -/

/-- Apex face 1's far corner. -/
noncomputable def pnApexA : V3 := ⟨0, 1/2, -1⟩
/-- Apex face 1 / 3's shared far corner. -/
noncomputable def pnApexB : V3 := ⟨0, -1/2, -1⟩
/-- Apex face 2 / 3's shared far corner. -/
noncomputable def pnApexC : V3 := ⟨-1/2, 0, -1⟩

theorem pnApexA_sq : V3.dot pnApexA pnApexA = 5 / 4 := by norm_num [pnApexA, V3.dot]
theorem pnApexB_sq : V3.dot pnApexB pnApexB = 5 / 4 := by norm_num [pnApexB, V3.dot]
theorem pnApexC_sq : V3.dot pnApexC pnApexC = 5 / 4 := by norm_num [pnApexC, V3.dot]
theorem pnApexAB_dot : V3.dot pnApexA pnApexB = 3 / 4 := by norm_num [pnApexA, pnApexB, V3.dot]
theorem pnApexAC_dot : V3.dot pnApexA pnApexC = 1 := by norm_num [pnApexA, pnApexC, V3.dot]
theorem pnApexBC_dot : V3.dot pnApexB pnApexC = 1 := by norm_num [pnApexB, pnApexC, V3.dot]

theorem pnApexA_norm : V3.norm pnApexA = Real.sqrt (5/4) := by unfold V3.norm; rw [pnApexA_sq]
theorem pnApexB_norm : V3.norm pnApexB = Real.sqrt (5/4) := by unfold V3.norm; rw [pnApexB_sq]
theorem pnApexC_norm : V3.norm pnApexC = Real.sqrt (5/4) := by unfold V3.norm; rw [pnApexC_sq]

/-- `√(5/4) * √(5/4) = 5/4`. -/
theorem sqrt54_mul_self : Real.sqrt (5/4) * Real.sqrt (5/4) = 5 / 4 := by
  rw [← pow_two, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5/4)]

theorem cornerAngle_face1 : cornerAngle pnApexA pnApexB = Real.arccos (3 / 5 : ℝ) := by
  rw [cornerAngle, pnApexAB_dot, pnApexA_norm, pnApexB_norm, sqrt54_mul_self]
  norm_num

theorem cornerAngle_face2 : cornerAngle pnApexA pnApexC = Real.arccos (4 / 5 : ℝ) := by
  rw [cornerAngle, pnApexAC_dot, pnApexA_norm, pnApexC_norm, sqrt54_mul_self]
  norm_num

theorem cornerAngle_face3 : cornerAngle pnApexB pnApexC = Real.arccos (4 / 5 : ℝ) := by
  rw [cornerAngle, pnApexBC_dot, pnApexB_norm, pnApexC_norm, sqrt54_mul_self]
  norm_num

/-! ### The key trigonometric comparison

`3 * arccos (3/5) > 4 * arccos (4/5)`, i.e. `arccos (3/5) > 4/3 * arccos (4/5)`.
Both sides lie in `(0, π]`; `cos` is strictly decreasing there, and
`cos (3θ₁) = -117/125 < -527/625 = cos (4θ)`. -/

theorem cos_three_mul' (x : ℝ) : Real.cos (3 * x) = 4 * Real.cos x ^ 3 - 3 * Real.cos x := by
  have h2 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := Real.cos_two_mul x
  have hs : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := Real.sin_two_mul x
  have s2 : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
    have h := Real.sin_sq_add_cos_sq x
    linarith
  rw [show (3:ℝ) * x = 2 * x + x by ring, Real.cos_add, h2, hs]
  calc (2 * Real.cos x ^ 2 - 1) * Real.cos x - 2 * Real.sin x * Real.cos x * Real.sin x
      = (2 * Real.cos x ^ 2 - 1) * Real.cos x - 2 * Real.cos x * Real.sin x ^ 2 := by ring
    _ = (2 * Real.cos x ^ 2 - 1) * Real.cos x - 2 * Real.cos x * (1 - Real.cos x ^ 2) := by
        rw [s2]
    _ = 4 * Real.cos x ^ 3 - 3 * Real.cos x := by ring

theorem cos_four_mul' (x : ℝ) :
    Real.cos (4 * x) = 2 * (2 * Real.cos x ^ 2 - 1) ^ 2 - 1 := by
  have h1 : Real.cos (2 * (2 * x)) = 2 * Real.cos (2 * x) ^ 2 - 1 := Real.cos_two_mul (2 * x)
  have h2 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := Real.cos_two_mul x
  rw [show (4:ℝ) * x = 2 * (2 * x) by ring, h1, h2]

/-- The trigonometric heart of the angle-weighted F16 fix:
    `arccos (3/5) > (4/3) * arccos (4/5)`. -/
theorem arccos_three_fifths_gt : Real.arccos (3 / 5 : ℝ) > 4 / 3 * Real.arccos (4 / 5 : ℝ) := by
  have hcos1 : Real.cos (Real.arccos (3 / 5 : ℝ)) = 3 / 5 :=
    Real.cos_arccos (by norm_num) (by norm_num)
  have hcos2 : Real.cos (Real.arccos (4 / 5 : ℝ)) = 4 / 5 :=
    Real.cos_arccos (by norm_num) (by norm_num)
  have ht1_nonneg : 0 ≤ Real.arccos (3 / 5 : ℝ) := Real.arccos_nonneg _
  have ht_nonneg : 0 ≤ Real.arccos (4 / 5 : ℝ) := Real.arccos_nonneg _
  have ht1_le : Real.arccos (3 / 5 : ℝ) ≤ Real.pi := Real.arccos_le_pi _
  have ht_le : Real.arccos (4 / 5 : ℝ) ≤ Real.pi := Real.arccos_le_pi _
  have ht1_le_pi3 : Real.arccos (3 / 5 : ℝ) ≤ Real.pi / 3 := by
    by_contra hcon
    push Not at hcon
    have hlt : Real.cos (Real.arccos (3 / 5 : ℝ)) < Real.cos (Real.pi / 3) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) ht1_le hcon
    rw [Real.cos_pi_div_three, hcos1] at hlt
    norm_num at hlt
  have ht_le_pi4 : Real.arccos (4 / 5 : ℝ) ≤ Real.pi / 4 := by
    rw [Real.arccos_le_pi_div_four]
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h8 : Real.sqrt 2 ≤ 8 / 5 := by
      have h2 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      nlinarith [hsq]
    nlinarith [h8, Real.sqrt_nonneg 2]
  have hcos3 : Real.cos (3 * Real.arccos (3 / 5 : ℝ)) = -117 / 125 := by
    rw [cos_three_mul', hcos1]
    norm_num
  have hcos4 : Real.cos (4 * Real.arccos (4 / 5 : ℝ)) = -527 / 625 := by
    rw [cos_four_mul', hcos2]
    norm_num
  have key : 4 * Real.arccos (4 / 5 : ℝ) < 3 * Real.arccos (3 / 5 : ℝ) := by
    by_contra hle
    push Not at hle
    have h4t_le : 4 * Real.arccos (4 / 5 : ℝ) ≤ Real.pi := by linarith
    have hle2 : Real.cos (4 * Real.arccos (4 / 5 : ℝ)) ≤ Real.cos (3 * Real.arccos (3 / 5 : ℝ)) :=
      Real.cos_le_cos_of_nonneg_of_le_pi
        (by positivity : (0:ℝ) ≤ 3 * Real.arccos (3 / 5 : ℝ)) h4t_le hle
    rw [hcos4, hcos3] at hle2
    norm_num at hle2
  linarith

/-! ### The angle-weighted pseudo-normal pairs positively

`ν = θ₁·n₁ + θ₂·n₂ + θ₃·n₃` with `θ₁ = arccos (3/5)`, `θ₂ = θ₃ = arccos (4/5)`
is `(θ₁ − 4θ/3, 0, 2θ/3)`, and `⟨ν, (t, 0, 0)⟩ = t · (θ₁ − 4θ/3)`. -/

/-- The angle-weighted apex pseudo-normal (Bærentzen–Aanæs). -/
noncomputable def angleWeightedApex : V3 :=
  V3.add
    (V3.add (pnSmul (cornerAngle pnApexA pnApexB) pnN1)
      (pnSmul (cornerAngle pnApexA pnApexC) pnN2))
    (pnSmul (cornerAngle pnApexB pnApexC) pnN3)

/-- The pairing of the angle-weighted pseudo-normal with `p = (t, 0, 0)`
    (the F16 outside point) is strictly positive for every `t > 0` — while
    the unweighted sum pairs negatively (`unweighted_vertex_pseudo_normal_
    misclassifies`). Angle weighting fixes the misclassification on the
    F16 tetrahedron. -/
theorem angle_weighted_apex_pairs_pos {t : ℝ} (ht : 0 < t) :
    0 < V3.dot angleWeightedApex (pnP t) := by
  rw [angleWeightedApex, cornerAngle_face1, cornerAngle_face2, cornerAngle_face3]
  have hgt := arccos_three_fifths_gt
  norm_num [pnSmul, pnN1, pnN2, pnN3, pnP, V3.add, V3.dot]
  nlinarith [hgt, ht]

/-- Explicit form: `⟨ν, (t, 0, 0)⟩ = t · (θ₁ − 4θ/3)`. -/
theorem angle_weighted_apex_dot_eq {t : ℝ} :
    V3.dot angleWeightedApex (pnP t)
      = t * (Real.arccos (3 / 5 : ℝ) - 4 / 3 * Real.arccos (4 / 5 : ℝ)) := by
  rw [angleWeightedApex, cornerAngle_face1, cornerAngle_face2, cornerAngle_face3]
  norm_num [pnSmul, pnN1, pnN2, pnN3, pnP, V3.add, V3.dot]
  ring

end Vdb
