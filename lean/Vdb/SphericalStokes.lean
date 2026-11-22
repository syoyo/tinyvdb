/-
  TinyVDB - Lean 4 formalization of the `.vdb` file format and volume operators.

  VS-4a, A-section: the spherical Stokes wall.  Rigorous partial results and
  the precisely-named analytic identity that is NOT provable from the imported
  mathlib slice.

  WHAT IS LANDED HERE (all sorry-free, `warningAsError` on):

    * `planarSectorVectorArea_eq`: the vector area of the *planar* cone sector
      over a great-circle arc, computed from its parametrization by an
      explicit iterated interval integral: it is `(θ/2) • n`.  Combined with
      the already-landed `arcBoundaryFlux_eq` this gives
      `arcBoundaryFlux_eq_twice_planarSector`, i.e. the Stokes identity
      `∮ x × dx = 2 ∫ (sector normal) dS` holds exactly on each flat face of
      the cone, by pure analysis of the 1-D interval integral.  The polygon
      version `polygonBoundaryFlux_eq_twice_polygonPlanarSector` sums the faces.

    * `hStokes_with_interior_iff_facePos`: the analytic hypothesis `hStokes`
      PLUS the cone-interior condition `⟪u,nⱼ⟫ < 0` is *equivalent* to the
      face-positivity seam (S).  Both directions are proved from the landed
      AngleNFace/Tangent theorems with no analysis.  Consequently a
      non-circular proof of `hStokes` in this generality is exactly as hard as
      (S) itself: there is no cheaper algebraic shortcut.

    * `exists_hStokes_interior_triangle`: for a spherical TRIANGLE with its
      genuine geometric corner angles, `hStokes` + interior is satisfiable —
      discharged using the unconditional trihedral theorem
      `three_face_face_pos_unconditional` and the equivalence above.
      (The witness is the algebraic certificate `-W/2`, NOT the geometric
      surface integral; this is an existential discharge, not an analytic
      proof of the integral identity.)

    * `sphericalStokes_implies_facePos`: names the missing analytic identity
      and records its exact consequence for (S).

  THE WALL (stated honestly; NOT proved here):

      ∮_∂P x × dx  =  -2 ∫_P x dA                                  (★)

  for the spherical polygon `P = C ∩ S²` cut out of a pointed cone `C` by the
  unit sphere.  On `S²` the outward unit normal at `x` is `x`, so (★) is the
  vector-area form of Stokes, `∫_P n dA = (1/2) ∮_∂P x × dx`.  The imported
  mathlib slice exposes

      Mathlib.MeasureTheory.Integral.DivergenceTheorem:
        MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable

  which is a theorem about a *box* `Box.Icc I ⊆ ℝⁿ⁺¹` only.  It contains no
  surface measure on `S²`, no general Stokes theorem, and no divergence
  theorem for the truncated cone `R = {t x : 0 ≤ t ≤ 1, x ∈ P}` (which is not
  a box).  Applying the box theorem to a box containing `R` and to the test
  fields that would isolate `∫_P x dA` (e.g. `F(y)=y(c·y)`, `div F = 4(c·y)`)
  only reproduces the cone volume identity `∫_P c·x dA = 4∫_R c·y dV`, which
  collapses to itself once `dV = t² dt dA` is used — no new information.  The
  missing analytic step is therefore irreducible with the available imports.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.AngleNFaceTangent
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Vdb
namespace V3

open scoped Real
open Real

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! ### 0. A scalar integral constant -/

/-- `∫₀¹ t dt = 1/2`, from the imported `intervalIntegral.integral_id`. -/
lemma integral_id_zero_one : (∫ t in (0 : ℝ)..1, t) = 1 / 2 := by
  rw [integral_id]
  norm_num

/-- The component integral used by the planar sector computation. -/
lemma iterated_sector_component (c θ : ℝ) :
    (∫ t in (0 : ℝ)..1, ∫ _ in (0 : ℝ)..θ, t * c) = (θ / 2) * c := by
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_mul_const]
  rw [integral_id_zero_one]
  ring

/-! ### 1. The planar sector of the cone: Stokes holds on a flat face -/

/-- Scalar multiplication in the second slot of `cross`: `v × (t • w) = t • (v × w)`. -/
theorem cross_pnSmul_right (t : ℝ) (v w : V3) :
    cross v (pnSmul t w) = pnSmul t (cross v w) := by
  apply V3.ext <;> dsimp [cross, pnSmul] <;> ring

/-- A `V3`-valued iterated interval integral: integrate each real component
    first in `s`, then in `t`.  This avoids any need for Bochner integration
    over `ℝ²` (Fubini) or a surface measure: the vector area of a parametrized
    patch is defined directly by its Jacobian. -/
noncomputable def iteratedIntegralV3 (f : ℝ → ℝ → V3) (t0 t1 s0 s1 : ℝ) : V3 :=
  ⟨∫ t in t0..t1, ∫ s in s0..s1, (f t s).x,
   ∫ t in t0..t1, ∫ s in s0..s1, (f t s).y,
   ∫ t in t0..t1, ∫ s in s0..s1, (f t s).z⟩

/-- The vector area of the planar sector `{ t · gcArc a b s | 0 ≤ t ≤ 1,
    0 ≤ s ≤ θ }` (the flat face of the cone over a great-circle arc), defined
    as the iterated integral of its Jacobian `∂ₜy × ∂ₛy = t • n`. -/
noncomputable def planarSectorVectorArea (a b : V3) (θ : ℝ) : V3 :=
  iteratedIntegralV3
    (fun t s => cross (gcArc a b s) (pnSmul t (gcArcDeriv a b s))) 0 1 0 θ

/-- The planar cone sector over an arc of length `θ` has vector area
    `(θ/2) • n`, where `n = cross a b` is its co-normal.  This is a genuine
    computation: the Jacobian of `y(t,s) = t · gcArc a b s` is
    `∂ₜy × ∂ₛy = t • n` (by `cross_gcArc_gcArcDeriv`), and
    `∫₀¹ t dt = 1/2`. -/
theorem planarSectorVectorArea_eq (a b n : V3) (hcross : cross a b = n) (θ : ℝ) :
    planarSectorVectorArea a b θ = pnSmul (θ / 2) n := by
  have hJ : ∀ (t s : ℝ),
      cross (gcArc a b s) (pnSmul t (gcArcDeriv a b s)) = pnSmul t n := by
    intro t s
    rw [cross_pnSmul_right, cross_gcArc_gcArcDeriv a b n hcross s]
  have hJx : ∀ t s, (cross (gcArc a b s) (pnSmul t (gcArcDeriv a b s))).x = t * n.x := by
    intro t s
    rw [hJ]
    rfl
  have hJy : ∀ t s, (cross (gcArc a b s) (pnSmul t (gcArcDeriv a b s))).y = t * n.y := by
    intro t s
    rw [hJ]
    rfl
  have hJz : ∀ t s, (cross (gcArc a b s) (pnSmul t (gcArcDeriv a b s))).z = t * n.z := by
    intro t s
    rw [hJ]
    rfl
  apply V3.ext
  · dsimp [planarSectorVectorArea, iteratedIntegralV3]
    simp_rw [hJx]
    exact iterated_sector_component n.x θ
  · dsimp [planarSectorVectorArea, iteratedIntegralV3]
    simp_rw [hJy]
    exact iterated_sector_component n.y θ
  · dsimp [planarSectorVectorArea, iteratedIntegralV3]
    simp_rw [hJz]
    exact iterated_sector_component n.z θ

/-- **Stokes on one flat face of the cone.**  The boundary line integral of
    one arc equals twice the vector area of the planar sector it bounds:
    `∮ x × dx = 2 ∫ (sector normal) dS`.  This is the exact algebraic/analytic
    half of (★) that lives on the planar boundary of the truncated cone; it
    uses only the already-landed `arcBoundaryFlux_eq` and the integral above. -/
theorem arcBoundaryFlux_eq_twice_planarSector (a b n : V3) (hcross : cross a b = n) (θ : ℝ) :
    arcBoundaryFlux a b θ = pnSmul 2 (planarSectorVectorArea a b θ) := by
  rw [arcBoundaryFlux_eq a b n hcross θ, planarSectorVectorArea_eq a b n hcross θ]
  apply V3.ext <;> dsimp [pnSmul] <;> ring

/-- Vector area of all the planar faces of a finite spherical polygon. -/
noncomputable def polygonPlanarSectorArea {ι : Type*} [Fintype ι]
    (a b : ι → V3) (θ : ι → ℝ) : V3 :=
  ⟨∑ i, (planarSectorVectorArea (a i) (b i) (θ i)).x,
   ∑ i, (planarSectorVectorArea (a i) (b i) (θ i)).y,
   ∑ i, (planarSectorVectorArea (a i) (b i) (θ i)).z⟩

/-- The polygon boundary integral is twice the total planar sector area:
    `polygonBoundaryFlux = 2 Σᵢ (θᵢ/2) nᵢ`.  Together with
    `polygonBoundaryFlux_eq_weightedNormalSum`, this says
    `Σᵢ θᵢ nᵢ = 2 Σᵢ (planar sector vector areas)`. -/
theorem polygonBoundaryFlux_eq_twice_polygonPlanarSector {ι : Type*} [Fintype ι]
    (n a b : ι → V3) (θ : ι → ℝ) (hcross : ∀ i, cross (a i) (b i) = n i) :
    polygonBoundaryFlux a b θ = pnSmul 2 (polygonPlanarSectorArea a b θ) := by
  apply V3.ext
  · dsimp [polygonBoundaryFlux, polygonPlanarSectorArea, pnSmul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [arcBoundaryFlux_eq_twice_planarSector (a i) (b i) (n i) (hcross i) (θ i)]
    rfl
  · dsimp [polygonBoundaryFlux, polygonPlanarSectorArea, pnSmul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [arcBoundaryFlux_eq_twice_planarSector (a i) (b i) (n i) (hcross i) (θ i)]
    rfl
  · dsimp [polygonBoundaryFlux, polygonPlanarSectorArea, pnSmul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [arcBoundaryFlux_eq_twice_planarSector (a i) (b i) (n i) (hcross i) (θ i)]
    rfl

/-! ### 2. The missing analytic identity is exactly (S) -/

/-- The analytic Stokes hypothesis together with the cone-interior condition
    is EQUIVALENT to the face-positivity seam (S).  Both directions are pure
    algebra from the landed AngleNFace/Tangent theorems.

    This is the precise sense in which the wall cannot be bypassed: producing
    a geometric `u = ∫_P x dA` satisfying `hStokes` and `⟪u,nⱼ⟫ < 0` is the
    same task as proving (S) itself. -/
theorem hStokes_with_interior_iff_facePos {ι : Type*} [Fintype ι]
    (n a b : ι → V3) (θ : ι → ℝ) (hcross : ∀ i, cross (a i) (b i) = n i) :
    (∃ u : V3, (∀ j, dot u (n j) < 0) ∧
      polygonBoundaryFlux a b θ = pnSmul (-2) u) ↔
    (∀ j, 0 < ∑ i, θ i * dot (n i) (n j)) := by
  constructor
  · rintro ⟨u, hu, hStokes⟩
    have hw : weightedNormalSum θ n = pnSmul (-2) u :=
      coNormalFlux_of_boundaryStokes n a b θ u hcross hStokes
    exact face_pos_of_coNormalFlux n θ u hu hw
  · intro hface
    refine ⟨pnSmul (-1 / 2 : ℝ) (weightedNormalSum θ n), ?_, ?_⟩
    · intro j
      rw [dot_pnSmul_left]
      rw [dot_commV (weightedNormalSum θ n) (n j), dot_weightedNormalSum]
      simp_rw [dot_commV (n j)]
      nlinarith [hface j]
    · rw [polygonBoundaryFlux_eq_weightedNormalSum n a b θ hcross]
      apply V3.ext <;> dsimp [pnSmul] <;> ring

/-- Given (S), the `hStokes` hypothesis of `coNormalFlux_of_boundaryStokes` is
    satisfiable (with the algebraic witness `-W/2`).  This is the converse
    direction of the equivalence, unpacked for direct use. -/
theorem hStokes_exists_of_facePos {ι : Type*} [Fintype ι]
    (n a b : ι → V3) (θ : ι → ℝ) (hcross : ∀ i, cross (a i) (b i) = n i)
    (hface : ∀ j, 0 < ∑ i, θ i * dot (n i) (n j)) :
    ∃ u : V3, (∀ j, dot u (n j) < 0) ∧
      polygonBoundaryFlux a b θ = pnSmul (-2) u := by
  exact (hStokes_with_interior_iff_facePos n a b θ hcross).2 hface

/-- **Spherical triangle: `hStokes` is dischargeable.**  For three unit outward
    normals spanning a nondegenerate trihedral cone, with their genuine corner
    angles as the weights, the existential form of the Stokes hypothesis
    (boundary flux = `-2 u`, `u` strictly inside every supporting half-space)
    holds.  The discharge uses the unconditional trihedral seam and the
    equivalence above; no spherical surface measure is constructed. -/
theorem exists_hStokes_interior_triangle
    (n₁ n₂ n₃ : V3) {p r q : ℝ}
    (h1 : dot n₁ n₁ = 1) (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1)
    (h12 : dot n₁ n₂ = p) (h13 : dot n₁ n₃ = r) (h23 : dot n₂ n₃ = q)
    (htriple : triple n₁ n₂ n₃ ≠ 0)
    (a b : Fin 3 → V3)
    (hcross : ∀ i : Fin 3, cross (a i) (b i) =
      (if i = 0 then n₁ else if i = 1 then n₂ else n₃)) :
    let v : Fin 3 → V3 := fun j => if j = 0 then n₁ else if j = 1 then n₂ else n₃
    let θ : Fin 3 → ℝ := fun j =>
      if j = 0 then cornerAngle (isoEdge12 n₁ n₂) (isoEdge13 n₁ n₃)
      else if j = 1 then cornerAngle (isoEdge12 n₁ n₂) (isoEdge23 n₂ n₃)
      else cornerAngle (isoEdge13 n₁ n₃) (isoEdge23 n₂ n₃)
    ∃ u : V3, (∀ j, dot u (v j) < 0) ∧
      polygonBoundaryFlux a b θ = pnSmul (-2) u := by
  dsimp
  let v : Fin 3 → V3 := fun j => if j = 0 then n₁ else if j = 1 then n₂ else n₃
  let θ : Fin 3 → ℝ := fun j =>
    if j = 0 then cornerAngle (isoEdge12 n₁ n₂) (isoEdge13 n₁ n₃)
    else if j = 1 then cornerAngle (isoEdge12 n₁ n₂) (isoEdge23 n₂ n₃)
    else cornerAngle (isoEdge13 n₁ n₃) (isoEdge23 n₂ n₃)
  have ht := three_face_face_pos_unconditional n₁ n₂ n₃ h1 h2 h3
    h12 h13 h23 htriple
  dsimp at ht
  apply hStokes_exists_of_facePos v a b θ hcross
  exact face_pos_fin3_of_conj
    (cornerAngle (isoEdge12 n₁ n₂) (isoEdge13 n₁ n₃))
    (cornerAngle (isoEdge12 n₁ n₂) (isoEdge23 n₂ n₃))
    (cornerAngle (isoEdge13 n₁ n₃) (isoEdge23 n₂ n₃))
    n₁ n₂ n₃ ht.1 ht.2.1 ht.2.2

/-! ### 3. The wall, named -/

/-- **The missing analytic identity (named, conditional).**  With
    `u = ∫_P x dA` the geometric vector area of the spherical polygon
    `P = C ∩ S²`, the spherical Stokes theorem (★) reads
    `polygonBoundaryFlux a b θ = pnSmul (-2) u`.  This lemma records its exact
    consequence for the seam (S): combined with the interior condition
    `⟪u,nⱼ⟫ < 0` (the cap meets the interior of every supporting half-space),
    it yields (S) by the landed algebra.  The identity itself is NOT proved:
    no surface measure on `S²` and no general Stokes theorem exist in the
    imported mathlib slice (only the box divergence theorem), see the module
    header.  This is the precise analytic wall of VS-4a. -/
theorem sphericalStokes_implies_facePos {ι : Type*} [Fintype ι]
    (n a b : ι → V3) (θ : ι → ℝ) (u : V3)
    (hcross : ∀ i, cross (a i) (b i) = n i)
    (hStokes : polygonBoundaryFlux a b θ = pnSmul (-2) u)
    (hinterior : ∀ j, dot u (n j) < 0) :
    ∀ j, 0 < ∑ i, θ i * dot (n i) (n j) := by
  exact face_pos_of_coNormalFlux n θ u hinterior
    (coNormalFlux_of_boundaryStokes n a b θ u hcross hStokes)

end V3
end Vdb
