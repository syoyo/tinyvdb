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
import Vdb.ConeClosed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

open Vdb Vdb.V3

namespace Vdb

open Vdb Vdb.V3
open Classical
open scoped RealInnerProductSpace

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

/-! ### General angle-weighted pairing (lane VS-4a)

This section lifts the F16 instance to a *general* inner-product-space
statement. The cone expansion is already available exactly
(`ConeClosed.farkas_closest_direction_exact`): an outside point's closest
direction is a finite nonneg combination `p − q = Σ λᵢ nᵢ` of the tight
face normals. The angle-weighted normal `ν = Σ θᵢ nᵢ` then pairs as

    ⟪ν, p − q⟫ = Σⱼ λⱼ · (Σᵢ θᵢ ⟪nᵢ, nⱼ⟫).                       (∗)

So positivity follows as soon as each *face* pairing `Σᵢ θᵢ ⟪nᵢ, nⱼ⟫`
is strictly positive. That per-face strict positivity is the hard seam of
the general convex claim (it fails for the unweighted sum on F16, and is
what the `arccos` comparison establishes there); it is **not** claimed
here in full generality. Instead:

* `angleWeightedNormal_pairs_pos` proves (∗) and the conclusion from the
  per-face hypothesis (escalation tier 3: the hard step is an explicit
  premise);
* `angleWeighted_convex_pairs_pos_of_face_pos` assembles this with the
  exact cone expansion into the general convex theorem under that named
  premise;
* `face_pos_of_nonobtuse` discharges the premise unconditionally when the
  tight normals are pairwise non-obtuse, giving an unconditional convex
  theorem for acute/non-obtuse vertices;
* `planar_cone_two_face_pairs_pos` and `planar_cone_two_face_face_pos`
  discharge it in the two-face planar vertex figure with equal (symmetric)
  corner-angle weights — the bounded/planar tier for the obtuse case.
-/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The angle-weighted (Bærentzen–Aanæs) normal with weights `θ` on the
    unit face normals `n`. -/
noncomputable def angleWeightedNormal {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (n : ι → F) : F := ∑ i, θ i • n i

/-- The exact pairing identity `⟪ν, Σ λⱼ nⱼ⟫ = Σⱼ λⱼ (Σᵢ θᵢ ⟪nᵢ, nⱼ⟫)`
    (using symmetry `⟪nᵢ, nⱼ⟫ = ⟪nⱼ, nᵢ⟫` of the real inner product). -/
theorem angleWeightedNormal_inner_conic {ι : Type*} [Fintype ι]
    (θ ell : ι → ℝ) (n : ι → F) :
    ⟪angleWeightedNormal θ n, ∑ j, ell j • n j⟫ =
      ∑ j, ell j * (∑ i, θ i * ⟪n i, n j⟫) := by
  unfold angleWeightedNormal
  rw [inner_sum Finset.univ (fun j => ell j • n j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_smul_right]
  congr 1
  rw [sum_inner Finset.univ (fun i => θ i • n i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_left]

/-- **Cone pairing lemma (hard seam as an explicit premise)**: if
    `p − q = Σ λᵢ nᵢ` with `λᵢ ≥ 0`, not all zero, and each face pairing
    `Σᵢ θᵢ ⟪nᵢ, nⱼ⟫` is strictly positive, then the angle-weighted normal
    pairs strictly positively with `p − q`. -/
theorem angleWeightedNormal_pairs_pos {ι : Type*} [Fintype ι]
    (θ ell : ι → ℝ) (n : ι → F)
    (hell : ∀ j, 0 ≤ ell j) (hellpos : ∃ j, 0 < ell j)
    (hface : ∀ j, 0 < ∑ i, θ i * ⟪n i, n j⟫) :
    0 < ⟪angleWeightedNormal θ n, ∑ j, ell j • n j⟫ := by
  rw [angleWeightedNormal_inner_conic]
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (hell j) (le_of_lt (hface j))
  · obtain ⟨j, hj⟩ := hellpos
    exact ⟨j, Finset.mem_univ j, mul_pos hj (hface j)⟩

/-- The per-face positivity holds unconditionally when the face normals
    are pairwise non-obtuse (every dihedral angle is at most a right
    angle): the diagonal term `θⱼ·1` is positive and all other terms are
    nonneg. -/
theorem face_pos_of_nonobtuse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : ι → ℝ) (hθ : ∀ i, 0 < θ i) (n : ι → F) (hn : ∀ i, ‖n i‖ = 1)
    (hnonobtuse : ∀ i j, i ≠ j → 0 ≤ ⟪n i, n j⟫) (j : ι) :
    0 < ∑ i, θ i * ⟪n i, n j⟫ := by
  apply Finset.sum_pos'
  · intro i _
    by_cases hij : i = j
    · rw [hij, real_inner_self_eq_norm_sq, hn j, one_pow, mul_one]
      exact le_of_lt (hθ j)
    · exact mul_nonneg (le_of_lt (hθ i)) (hnonobtuse i j hij)
  · refine ⟨j, Finset.mem_univ j, ?_⟩
    rw [real_inner_self_eq_norm_sq, hn j, one_pow, mul_one]
    exact hθ j

/-! ### The general convex theorem, modulo the named face-positivity seam -/

/-- **General convex angle-weighted sign theorem (conditional)**: for a
    convex polyhedron `K` with nonempty interior, an outside point `p`
    whose closest point `q` is a vertex with tight faces and strictly
    positive corner-angle weights `θ`, the angle-weighted pseudo-normal
    `ν = Σ θᵢ nᵢ` pairs strictly positively with `p − q`. The single
    hypothesis `hface` is the hard seam (per-face strict positivity of the
    quadratic form); everything else — the exact cone expansion, the
    outside/closest-point setup and the pairing algebra — is proved. -/
theorem angleWeighted_convex_pairs_pos_of_face_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {n : ι → F} {b : ι → ℝ} {p q : F}
    (θ : {i // Tight n b q i} → ℝ) (hθ : ∀ i, 0 < θ i)
    (hq : q ∈ halfSpaces n b)
    (hint : ∃ r ∈ halfSpaces n b, ∀ i, ⟪n i, r⟫ < b i)
    (hm : ‖p - q‖ = ⨅ w : (halfSpaces n b), ‖p - w‖)
    (hp : p ∉ halfSpaces n b)
    (hface : ∀ j, 0 < ∑ i, θ i * ⟪tightNormals n b q i, tightNormals n b q j⟫) :
    0 < ⟪angleWeightedNormal θ (tightNormals n b q), p - q⟫ := by
  classical
  have _ := hθ
  have hpq_ne : p - q ≠ 0 := by
    intro h
    apply hp
    have heq : p = q := sub_eq_zero.mp h
    simpa [heq] using hq
  obtain ⟨ell, hell0, helleq⟩ := farkas_closest_direction_exact hq hint hm
  have hellpos : ∃ j, 0 < ell j := by
    by_contra hcon
    push Not at hcon
    have hellz : ∀ j, ell j = 0 := fun j => le_antisymm (hcon j) (hell0 j)
    have hzero : p - q = 0 := by
      rw [helleq]
      simp [hellz]
    exact hpq_ne hzero
  rw [helleq]
  exact angleWeightedNormal_pairs_pos θ ell (tightNormals n b q) hell0 hellpos hface

/-- **Unconditional corollary** for non-obtuse tight normals: the angle
    sign rule is sound at any such vertex of a convex polyhedron. -/
theorem angleWeighted_convex_pairs_pos_nonobtuse
    {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {n : ι → F} {b : ι → ℝ} {p q : F}
    (θ : {i // Tight n b q i} → ℝ) (hθ : ∀ i, 0 < θ i)
    (hnunit : ∀ i, ‖n i‖ = 1)
    (hnonobtuse : ∀ i j : {i // Tight n b q i}, i ≠ j →
      ⟪tightNormals n b q i, tightNormals n b q j⟫ ≥ 0)
    (hq : q ∈ halfSpaces n b)
    (hint : ∃ r ∈ halfSpaces n b, ∀ i, ⟪n i, r⟫ < b i)
    (hm : ‖p - q‖ = ⨅ w : (halfSpaces n b), ‖p - w‖)
    (hp : p ∉ halfSpaces n b) :
    0 < ⟪angleWeightedNormal θ (tightNormals n b q), p - q⟫ := by
  classical
  apply angleWeighted_convex_pairs_pos_of_face_pos θ hθ hq hint hm hp
  exact fun j => face_pos_of_nonobtuse θ hθ (tightNormals n b q)
    (fun i => hnunit i) hnonobtuse j

/-! ### The two-face planar vertex figure (obtuse case, bounded tier)

At a planar cone vertex with two incident faces, the hard seam reduces to
two scalar inequalities. With symmetric (equal) corner-angle weights the
seam is discharged by the single geometric fact that two distinct unit
normals are not antipodal (`-1 < ⟪n₁, n₂⟫`), so the whole pairing is
positive — including obtuse dihedral angles such as the F16 tetrahedron's
apex (`⟪n₁, n₂⟫ = -2/3`). -/

/-- The two-face face-positivities with equal weights `θ` and a non-antipodal
    pair of unit normals. -/
theorem planar_cone_two_face_face_pos
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (n₁ n₂ : F) (hn₁ : ‖n₁‖ = 1) (hn₂ : ‖n₂‖ = 1)
    (hc : -1 < ⟪n₁, n₂⟫) (θ : ℝ) (hθ : 0 < θ) :
    0 < θ * ⟪n₁, n₁⟫ + θ * ⟪n₂, n₁⟫ ∧
      0 < θ * ⟪n₁, n₂⟫ + θ * ⟪n₂, n₂⟫ := by
  have h11 : ⟪n₁, n₁⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn₁]; norm_num
  have h22 : ⟪n₂, n₂⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn₂]; norm_num
  have h21 : ⟪n₂, n₁⟫ = ⟪n₁, n₂⟫ := real_inner_comm _ _
  constructor
  · rw [h11, h21]
    nlinarith
  · rw [h22]
    nlinarith

/-- **Planar (two-face) vertex-figure lemma**: with equal angle weights a
    two-face vertex has a strictly positive pairing with every nonneg
    combination `λ₁ n₁ + λ₂ n₂` that is not zero, even when the two
    outward normals are obtuse. -/
theorem planar_cone_two_face_pairs_pos
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (n₁ n₂ : F) (hn₁ : ‖n₁‖ = 1) (hn₂ : ‖n₂‖ = 1)
    (hc : -1 < ⟪n₁, n₂⟫) (θ : ℝ) (hθ : 0 < θ)
    (e1 e2 : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (hepos : 0 < e1 ∨ 0 < e2) :
    0 < ⟪θ • n₁ + θ • n₂, e1 • n₁ + e2 • n₂⟫ := by
  have hseam := planar_cone_two_face_face_pos n₁ n₂ hn₁ hn₂ hc θ hθ
  have h11 : ⟪n₁, n₁⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn₁]; norm_num
  have h22 : ⟪n₂, n₂⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn₂]; norm_num
  have h21 : ⟪n₂, n₁⟫ = ⟪n₁, n₂⟫ := real_inner_comm _ _
  rw [inner_add_left, inner_add_right, inner_add_right]
  simp_rw [real_inner_smul_left, real_inner_smul_right]
  rw [h11, h22, h21]
  rw [h11, h22, h21] at hseam
  have hs : 0 < θ * (1 + ⟪n₁, n₂⟫) := by nlinarith [hseam.1]
  have hcpos : 0 < 1 + ⟪n₁, n₂⟫ := pos_of_mul_pos_right hs (le_of_lt hθ)
  have hsum : 0 < e1 + e2 := by rcases hepos with hpos | hpos <;> nlinarith
  have hgoal :
      θ * (e1 * 1) + θ * (e2 * ⟪n₁, n₂⟫) + (θ * (e1 * ⟪n₁, n₂⟫) + θ * (e2 * 1))
        = θ * (e1 + e2) * (1 + ⟪n₁, n₂⟫) := by ring
  rw [hgoal]
  exact mul_pos (mul_pos hθ hsum) hcpos

/-! ### Remaining gap (recorded for `lean/VERIFICATION.md`)

**Statement not proved** (the hard seam, tier-4 wall for this slice): for
a finite family of unit vectors `n : ι → F` that positively span a pointed
cone with nonempty interior (the tight normals of a convex vertex) and
strictly positive *geometric* corner angles `θ`, prove

    ∀ j : ι, 0 < ∑ i, θ i * ⟪n i, n j⟫.                              (S)

Given (S), `angleWeighted_convex_pairs_pos_of_face_pos` completes the full
general convex theorem; the F16 instance and the two-face planar figure
verify (S) in their respective cases, and `face_pos_of_nonobtuse` proves it
when all dihedral angles are non-obtuse.

**Why it is not automatic**: `∑ i, θ i ⟪n i, n j⟫` is a quadratic form whose
off-diagonal terms are negative for obtuse dihedral angles (F16:
`⟪n₁, n₂⟫ = -2/3`), so the diagonal positivity alone is insufficient. The
geometric content is spherical: the vertex figure is a convex spherical
polygon with edges of length `θᵢ` and outward co-normals `nᵢ`, and the
identity `∑ θᵢ nᵢ = -2 ∫_P x dA` makes (S) equivalent to the elementary
spherical fact `∫_P ⟪x, nⱼ⟫ dA < 0`. Formalizing that identity needs the
spherical Stokes/divergence theorem and surface measure, which is outside
this proof group's budget (no such lemma is available in the imported
mathlib slice).

**Budget record** (plan-lean.md §4.0): `cd lean && timeout 600 lake build
Vdb.AnglePseudoNormal` — no timeout, ~7 s of Lean compilation (12 s wall
including dependency replay); the 10-minute cap was not approached. No
proof holes introduced; `warningAsError` on. -/

end Vdb
