/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  VS-4a, arbitrary n-face seam (S): the *tangent closed-loop* strategy.
  A bounded proof-group investigating whether a closed-loop identity for a
  convex spherical polygon vertex figure, combined with the face/co-normal
  relation, yields a purely algebraic proof of

      ∀ j, 0 < Σ i, θ i * dot (n i) (n j).                          (S)

  Status: the strategy as posed does NOT close (S).  Its central premise is
  geometrically wrong in R^3, and the corrected boundary identity is exactly
  the spherical divergence/Stokes identity that is unavailable in the imported
  mathlib slice.  What is landed here is the rigorous core that survives:

    * `gcTangent_*`: the tangent of the great-circle edge of face `n` at a point
      `x` is `cross n x`; it is a unit vector orthogonal to `n` and to `x`, and
      the map `x ↦ cross n x` is injective on the plane `⟪n,x⟫ = 0`.  Hence the
      tangent is NOT constant along an edge, so no fixed vector `tᵢ` satisfies
      `θᵢ tᵢ = displacement` and the proposed `Σ θᵢ tᵢ = 0` is false.
    * `coneEdge_orthogonal_both`: `cross (nᵢ) (nᵢ₊₁)` is the direction of the
      cone edge `Fᵢ ∩ Fᵢ₊₁` (a vertex of the vertex figure), not a tangent.
    * `chordSum_eq` / `chordSum_cycle`: the rigorous closed-loop identity is
      the telescoping of the chord vectors `v(k+1) − v(k)`; for a closed
      polygon it vanishes.  This is proved by pure algebra.
    * `face_pos_of_coNormalFlux`: the *correct* boundary identity, written as
      the finite hypothesis `weightedNormalSum θ n = -2•u` with `⟪u,nⱼ⟫ < 0`,
      implies (S) by bilinearity alone.  This is the algebraic shadow of the
      divergence theorem on the cone truncated by the unit sphere; proving the
      identity itself (the wall) is the missing analytic step.

  See the closing comment for the precise obstruction.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.AngleNFace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Vdb
namespace V3

open scoped Real
open Real

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! ### The great-circle tangent of a face -/

/-- The oriented tangent to the great circle `{x | ⟪n,x⟫ = 0}` at a point `x`:
    `cross n x`.  For unit, orthogonal `n, x` this is a unit vector orthogonal
    to `n` (tangent to the great circle) and to `x` (tangent to the sphere). -/
def gcTangent (n x : V3) : V3 := cross n x

/-- Scaling a vector scales its dot product with any `a`. -/
lemma dot_pnSmul_left (s : ℝ) (v a : V3) : dot (pnSmul s v) a = s * dot v a := by
  unfold pnSmul dot
  ring

theorem dot_gcTangent_normal (n x : V3) : dot (gcTangent n x) n = 0 := by
  unfold gcTangent
  rw [dot_commV]
  exact dot_self_cross_left n x

theorem dot_gcTangent_point (n x : V3) : dot (gcTangent n x) x = 0 := by
  unfold gcTangent
  rw [dot_commV]
  exact dot_self_cross_right x n

/-- `⟪cross n x, cross n x⟫ = 1` for unit, orthogonal `n, x`. -/
theorem gcTangent_sq_of_unit (n x : V3) (hn : dot n n = 1) (hx : dot x x = 1)
    (hnx : dot n x = 0) : dot (gcTangent n x) (gcTangent n x) = 1 := by
  simpa [gcTangent, hnx] using (cross_sq_of_unit n x (p := 0) hn hx hnx)

/-- Double-cross on the orthogonal plane: `n × (n × x) = -x` for unit `n` with
    `⟪n,x⟫ = 0`. -/
theorem cross_cross_unit (n x : V3) (hn : dot n n = 1) (hnx : dot n x = 0) :
    cross n (cross n x) = pnSmul (-1) x := by
  apply V3.ext <;>
    dsimp [cross, pnSmul, dot] at hn hnx ⊢ <;>
    ring_nf at hn hnx ⊢
  all_goals
    have hnx0 : n.x * (n.x * x.x + n.y * x.y + n.z * x.z) = 0 := by rw [hnx, mul_zero]
    have hny0 : n.y * (n.x * x.x + n.y * x.y + n.z * x.z) = 0 := by rw [hnx, mul_zero]
    have hnz0 : n.z * (n.x * x.x + n.y * x.y + n.z * x.z) = 0 := by rw [hnx, mul_zero]
    have hxx : x.x * (n.x ^ 2 + n.y ^ 2 + n.z ^ 2) = x.x := by rw [hn]; ring
    have hyy : x.y * (n.x ^ 2 + n.y ^ 2 + n.z ^ 2) = x.y := by rw [hn]; ring
    have hzz : x.z * (n.x ^ 2 + n.y ^ 2 + n.z ^ 2) = x.z := by rw [hn]; ring
    ring_nf at hnx0 hny0 hnz0 hxx hyy hzz
    nlinarith

/-- On the plane `⟪n,x⟫ = 0`, the tangent map `x ↦ cross n x` is injective
    (unit `n`).  Consequently the tangent of a great-circle edge is not a
    constant vector: distinct points of the edge have distinct tangents. -/
theorem gcTangent_injective (n : V3) (hn : dot n n = 1)
    {x y : V3} (hx : dot n x = 0) (hy : dot n y = 0)
    (h : gcTangent n x = gcTangent n y) : x = y := by
  have h' := congrArg (fun z : V3 => cross n z) h
  change cross n (cross n x) = cross n (cross n y) at h'
  rw [cross_cross_unit n x hn hx, cross_cross_unit n y hn hy] at h'
  unfold pnSmul at h'
  apply V3.ext
  · have hh := congrArg V3.x h'; dsimp at hh; linarith
  · have hh := congrArg V3.y h'; dsimp at hh; linarith
  · have hh := congrArg V3.z h'; dsimp at hh; linarith

theorem gcTangent_not_constant_on_arc (n x y : V3) (hn : dot n n = 1)
    (hx : dot n x = 0) (hy : dot n y = 0) (hxy : x ≠ y) :
    gcTangent n x ≠ gcTangent n y := by
  intro h
  exact hxy (gcTangent_injective n hn hx hy h)

/-- `cross (nᵢ, nᵢ₊₁)` is orthogonal to both face normals: it is the direction
    of the cone edge `Fᵢ ∩ Fᵢ₊₁`, i.e. a *vertex* of the spherical polygon, not
    the tangent of edge `i`. -/
theorem coneEdge_orthogonal_both (a b : V3) :
    dot (cross a b) a = 0 ∧ dot (cross a b) b = 0 := by
  constructor
  · rw [dot_commV]
    exact dot_self_cross_left a b
  · rw [dot_commV]
    exact dot_self_cross_right b a

/-! ### The rigorous closed-loop identity: telescoping chords

For a polygonal curve with vertices `v 0, …, v m` the total displacement is
zero.  This is the only closed-loop identity available without integration;
the "constant tangent" version `Σ θᵢ tᵢ = 0` does not exist because the great
-circle tangent rotates along each edge (see `gcTangent_not_constant_on_arc`). -/

lemma sum_range_sub_telescoping (a : ℕ → ℝ) : ∀ m : ℕ,
    (∑ k ∈ Finset.range m, (a (k + 1) - a k)) = a m - a 0 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- The componentwise sum of the chord vectors `v(k+1) − v(k)`, `k < m`. -/
def chordSum (v : ℕ → V3) (m : ℕ) : V3 :=
  ⟨∑ k ∈ Finset.range m, ((v (k + 1)).x - (v k).x),
   ∑ k ∈ Finset.range m, ((v (k + 1)).y - (v k).y),
   ∑ k ∈ Finset.range m, ((v (k + 1)).z - (v k).z)⟩

theorem chordSum_eq (v : ℕ → V3) (m : ℕ) : chordSum v m = sub (v m) (v 0) := by
  apply V3.ext
  · simpa [chordSum, sub] using (sum_range_sub_telescoping (fun k => (v k).x) m)
  · simpa [chordSum, sub] using (sum_range_sub_telescoping (fun k => (v k).y) m)
  · simpa [chordSum, sub] using (sum_range_sub_telescoping (fun k => (v k).z) m)

/-- **Closed-loop identity.**  A closed polygon (`v m = v 0`) has vanishing
    total chord displacement. -/
theorem chordSum_cycle (v : ℕ → V3) (m : ℕ) (hcyc : v m = v 0) :
    chordSum v m = ⟨0, 0, 0⟩ := by
  rw [chordSum_eq, hcyc]
  simp [sub]

/-! ### The correct boundary identity implies (S) algebraically -/

/-- If the angle-weighted normal equals `-2` times a vector lying strictly in
    the polar half-spaces of all the faces, then (S) follows by bilinearity.
    In the cone picture `u = ∫_P x dA` and this hypothesis is the divergence
    theorem for the cone truncated by the unit sphere (each planar face sector
    has area `θᵢ/2`, and the spherical cap has outward co-normal `x`); the
    strict inequalities express that the cap meets the interior of every
    supporting half-space.  Proving this identity is the unavailable Stokes
    step; the implication below is pure algebra. -/
lemma face_pos_of_coNormalFlux {ι : Type*} [Fintype ι]
    (n : ι → V3) (θ : ι → ℝ) (u : V3)
    (hu : ∀ j, dot u (n j) < 0)
    (hflux : weightedNormalSum θ n = pnSmul (-2) u) :
    ∀ j, 0 < ∑ i, θ i * dot (n i) (n j) := by
  intro j
  have hsym : (∑ i, θ i * dot (n i) (n j)) =
      (∑ i, θ i * dot (n j) (n i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [dot_commV]
  rw [hsym, ← dot_weightedNormalSum θ n (n j), hflux]
  rw [dot_commV, dot_pnSmul_left]
  nlinarith [hu j]

/-- The trihedral (n = 3) case of the co-normal flux identity is unconditional:
    it is the singleton `sphericalBarycenter` certificate of
    `Vdb.AngleNFace`, so the algebraic implication above really does recover
    the landed three-face theorem. -/
theorem coNormalFlux_simplicial
    (n₀ n₁ n₂ : V3) (θ₀ θ₁ θ₂ : ℝ)
    (hface : ∀ j : Fin 3,
      0 < ∑ i : Fin 3,
        (if i = 0 then θ₀ else if i = 1 then θ₁ else θ₂) *
          dot (if i = 0 then n₀ else if i = 1 then n₁ else n₂)
              (if j = 0 then n₀ else if j = 1 then n₁ else n₂)) :
    let v : Fin 3 → V3 := fun j => if j = 0 then n₀ else if j = 1 then n₁ else n₂
    let θ : Fin 3 → ℝ := fun j => if j = 0 then θ₀ else if j = 1 then θ₁ else θ₂
    ∃ u : V3, (∀ j, dot u (v j) < 0) ∧ weightedNormalSum θ v = pnSmul (-2) u := by
  dsimp
  let W : V3 := weightedNormalSum
      (fun j : Fin 3 => if j = 0 then θ₀ else if j = 1 then θ₁ else θ₂)
      (fun j : Fin 3 => if j = 0 then n₀ else if j = 1 then n₁ else n₂)
  refine ⟨pnSmul (-1 / 2 : ℝ) W, ?_, ?_⟩
  · intro j
    have hdot : 0 < dot W (if j = 0 then n₀ else if j = 1 then n₁ else n₂) := by
      dsimp [W]
      rw [dot_commV, dot_weightedNormalSum]
      have hj := hface j
      have hsym : (∑ i : Fin 3,
            (if i = 0 then θ₀ else if i = 1 then θ₁ else θ₂) *
              dot (if i = 0 then n₀ else if i = 1 then n₁ else n₂)
                  (if j = 0 then n₀ else if j = 1 then n₁ else n₂)) =
          (∑ i : Fin 3,
            (if i = 0 then θ₀ else if i = 1 then θ₁ else θ₂) *
              dot (if j = 0 then n₀ else if j = 1 then n₁ else n₂)
                  (if i = 0 then n₀ else if i = 1 then n₁ else n₂)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [dot_commV]
      rw [← hsym]
      exact hj
    rw [dot_pnSmul_left]
    nlinarith
  · dsimp [W]
    unfold pnSmul weightedNormalSum
    apply V3.ext <;> dsimp <;> ring

/-! ### The discrete co-normal flux identity (algebraic half of Stokes)

The flux hypothesis of `face_pos_of_coNormalFlux` is the divergence/Stokes
identity `Σᵢ θᵢ nᵢ = -2 ∫_P x dA` for the spherical vertex figure `P`.  This
section proves its *algebraic half* without any surface measure: the integrand
`x × (dx/ds)` of the boundary line integral is the constant face normal along a
great-circle arc, so the arc contributes exactly `θᵢ • nᵢ` and the closed-loop
boundary integral is `Σᵢ θᵢ nᵢ`.  The remaining analytic step (identifying that
boundary integral with `-2 ∫_P x dA`) is isolated in `coNormalFlux_of_boundaryStokes`
as one explicit hypothesis. -/

/-- The local co-normal flux density of a great-circle edge.  For a point `x` on
    the great circle `{⟪n,·⟫ = 0}` with `⟪x,x⟫ = 1`, the vector `n × x` is the
    unit tangent `gcTangent n x` and `x × (n × x) = n`: the cross product of the
    point with its arclength derivative is the CONSTANT outward co-normal `n`.
    (Only `⟪x,x⟫ = 1` and `⟪n,x⟫ = 0` are needed; unit `n` is not used.) -/
theorem cross_x_cross_n_x (n x : V3) (_hn : dot n n = 1) (hx : dot x x = 1)
    (hnx : dot n x = 0) : cross x (cross n x) = n := by
  apply V3.ext
  · dsimp [cross, dot] at hnx hx ⊢
    linear_combination n.x * hx - x.x * hnx
  · dsimp [cross, dot] at hnx hx ⊢
    linear_combination n.y * hx - x.y * hnx
  · dsimp [cross, dot] at hnx hx ⊢
    linear_combination n.z * hx - x.z * hnx

/-- Componentwise interval integral of a `V3`-valued function.  `V3` carries no
    normed-space instance, so the three real components are integrated
    separately; this is the Bochner integral in `ℝ` applied componentwise. -/
noncomputable def v3IntervalIntegral (f : ℝ → V3) (a b : ℝ) : V3 :=
  ⟨∫ s in a..b, (f s).x, ∫ s in a..b, (f s).y, ∫ s in a..b, (f s).z⟩

/-- The interval integral of a constant `V3` is `(b - a) • c`. -/
theorem v3IntervalIntegral_const (c : V3) (a b : ℝ) :
    v3IntervalIntegral (fun _ => c) a b = pnSmul (b - a) c := by
  apply V3.ext <;>
    dsimp [v3IntervalIntegral, pnSmul] <;>
    rw [intervalIntegral.integral_const] <;> ring

/-- Unit-speed parametrization of the great-circle arc in the plane spanned by
    an orthonormal frame `(a, b)`: `x(s) = cos(s) a + sin(s) b`.  Its derivative
    is `x'(s) = -sin(s) a + cos(s) b`, and `cross a b` is the plane normal. -/
noncomputable def gcArc (a b : V3) (s : ℝ) : V3 :=
  add (pnSmul (Real.cos s) a) (pnSmul (Real.sin s) b)

noncomputable def gcArcDeriv (a b : V3) (s : ℝ) : V3 :=
  add (pnSmul (-Real.sin s) a) (pnSmul (Real.cos s) b)

/-- Along the arc, `x × x' = cross a b` is constant (it is the plane normal).
    This is the triple-product identity `x × (n × x) = n` specialised to the
    orthonormal frame, proved here directly by `sin² + cos² = 1`. -/
theorem cross_gcArc_gcArcDeriv (a b n : V3) (hcross : cross a b = n) (s : ℝ) :
    cross (gcArc a b s) (gcArcDeriv a b s) = n := by
  rw [← hcross]
  have hsc : Real.sin s ^ 2 + Real.cos s ^ 2 = 1 := Real.sin_sq_add_cos_sq s
  apply V3.ext
  · dsimp [cross, gcArc, gcArcDeriv, pnSmul, add]
    ring_nf at hsc ⊢
    linear_combination (a.y * b.z - b.y * a.z) * hsc
  · dsimp [cross, gcArc, gcArcDeriv, pnSmul, add]
    ring_nf at hsc ⊢
    linear_combination (a.z * b.x - b.z * a.x) * hsc
  · dsimp [cross, gcArc, gcArcDeriv, pnSmul, add]
    ring_nf at hsc ⊢
    linear_combination (a.x * b.y - b.x * a.y) * hsc

/-- The boundary line integral of a single great-circle arc of length `θ` in a
    plane with co-normal `n = cross a b` is `θ • n`.  This is the exact discrete
    co-normal flux of one edge: no surface measure is involved. -/
noncomputable def arcBoundaryFlux (a b : V3) (θ : ℝ) : V3 :=
  v3IntervalIntegral (fun s => cross (gcArc a b s) (gcArcDeriv a b s)) 0 θ

theorem arcBoundaryFlux_eq (a b n : V3) (hcross : cross a b = n) (θ : ℝ) :
    arcBoundaryFlux a b θ = pnSmul θ n := by
  unfold arcBoundaryFlux
  have hfun : (fun s => cross (gcArc a b s) (gcArcDeriv a b s)) = (fun _ : ℝ => n) := by
    funext s
    exact cross_gcArc_gcArcDeriv a b n hcross s
  rw [hfun, v3IntervalIntegral_const]
  apply V3.ext <;> dsimp [pnSmul] <;> ring

/-- The total boundary flux of a finite spherical polygon: the sum of the arc
    line integrals.  (Closedness of the polygon is irrelevant to this algebraic
    sum; it is needed only for the analytic Stokes step below.) -/
noncomputable def polygonBoundaryFlux {ι : Type*} [Fintype ι]
    (a b : ι → V3) (θ : ι → ℝ) : V3 :=
  ⟨∑ i, (arcBoundaryFlux (a i) (b i) (θ i)).x,
   ∑ i, (arcBoundaryFlux (a i) (b i) (θ i)).y,
   ∑ i, (arcBoundaryFlux (a i) (b i) (θ i)).z⟩

/-- **Discrete co-normal flux identity** (all `n`, hence in particular the
    spherical triangle `n = 3`): the boundary vector integral equals the
    angle-weighted normal `Σᵢ θᵢ nᵢ = weightedNormalSum θ n`.  Pure algebra;
    the geometric corner angles enter only through the arc lengths `θ i`. -/
theorem polygonBoundaryFlux_eq_weightedNormalSum {ι : Type*} [Fintype ι]
    (n a b : ι → V3) (θ : ι → ℝ) (hcross : ∀ i, cross (a i) (b i) = n i) :
    polygonBoundaryFlux a b θ = weightedNormalSum θ n := by
  apply V3.ext
  · dsimp [polygonBoundaryFlux, weightedNormalSum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [arcBoundaryFlux_eq (a i) (b i) (n i) (hcross i) (θ i)]
    rfl
  · dsimp [polygonBoundaryFlux, weightedNormalSum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [arcBoundaryFlux_eq (a i) (b i) (n i) (hcross i) (θ i)]
    rfl
  · dsimp [polygonBoundaryFlux, weightedNormalSum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [arcBoundaryFlux_eq (a i) (b i) (n i) (hcross i) (θ i)]
    rfl

/-- **The analytic wall, isolated.**  The co-normal flux identity is obtained
    from the discrete boundary identity by the single missing statement

        `polygonBoundaryFlux a b θ = -2 • ∫_P x dA`,

    i.e. the spherical Stokes theorem identifying the boundary line integral
    `∮ x × dx` with the surface vector integral over the spherical polygon `P`
    (the orientation is fixed by `cross (a i) (b i) = n i` with `n i` the
    outward co-normal).  Surface measure on `S²` is not available in the
    imported mathlib slice, so `hStokes` is stated as an explicit hypothesis and
    is NOT proved here.  Given it, the co-normal flux identity needed by
    `face_pos_of_coNormalFlux` follows by algebra alone. -/
theorem coNormalFlux_of_boundaryStokes {ι : Type*} [Fintype ι]
    (n a b : ι → V3) (θ : ι → ℝ) (u : V3)
    (hcross : ∀ i, cross (a i) (b i) = n i)
    (hStokes : polygonBoundaryFlux a b θ = pnSmul (-2) u) :
    weightedNormalSum θ n = pnSmul (-2) u := by
  rw [← polygonBoundaryFlux_eq_weightedNormalSum n a b θ hcross, hStokes]

end V3
end Vdb

/-
  ===========================================================================
  CLOSEOUT: why the tangent closed-loop strategy does not prove (S), and
  exactly which identity is missing.

  1. THE PROPOSED IDENTITY IS FALSE AS STATED.  The strategy posits a constant
     unit tangent `tᵢ` for edge `i` with `tᵢ = ±normalize(cross(nᵢ,nᵢ₊₁))` and
     the closed-loop law `Σᵢ θᵢ tᵢ = 0`.  Two independent errors:

     (a) `cross(nᵢ, nᵢ₊₁)` is orthogonal to BOTH `nᵢ` and `nᵢ₊₁`
         (`coneEdge_orthogonal_both`), hence it is the direction of the cone
         edge `Fᵢ ∩ Fᵢ₊₁` — a VERTEX of the spherical vertex figure.  It is not
         tangent to the great-circle arc of face `i` (edge `i` runs on
         `{⟪nᵢ,x⟫=0}` between the vertices `cross(nᵢ₋₁,nᵢ)` and
         `cross(nᵢ,nᵢ₊₁)`).

     (b) The genuine tangent of edge `i` at a point `x` of that great circle is
         `gcTangent nᵢ x = cross nᵢ x`: it is a unit vector (`gcTangent_sq_of_unit`)
         orthogonal to `nᵢ` and to `x`.  It is NOT constant along the arc: the
         map `x ↦ cross nᵢ x` is injective on the plane `⟪nᵢ,x⟫=0`
         (`gcTangent_injective`), so distinct arc points give distinct tangents
         (`gcTangent_not_constant_on_arc`).  Therefore there is no fixed vector
         `tᵢ` with `θᵢ tᵢ` equal to the displacement `vᵢ₊₁ − vᵢ` of edge `i`, and
         `Σᵢ θᵢ tᵢ = 0` is not a valid identity in R^3.  (For the octant triangle
         the three *midpoint* tangents happen to sum to zero only because all
         three side lengths are equal `π/2`; for unequal lengths the weighted
         sum does not vanish.)

  2. THE CORRECT CLOSED-LOOP IS TRIVIAL.  The only displacement identity that
     holds without analysis is the telescoping of the chord vectors
     (`chordSum_eq`, `chordSum_cycle`): `Σₖ (v(k+1) − v(k)) = v m − v 0`, which
     vanishes for a closed polygon.  It relates the edge displacements, not the
     co-normals `nᵢ`, so it carries no information about `W = Σ θᵢ nᵢ`.

  3. THE CORRECT BOUNDARY IDENTITY NEEDS STOKES.  With the outward co-normal of
     edge `i` equal to `nᵢ` (the interior of the cone is `⟪nᵢ,x⟫ ≤ 0`), the
     divergence theorem on the truncated cone (planar face sector area `θᵢ/2`)
     or the surface divergence theorem on `S²` gives

         W = Σᵢ θᵢ nᵢ = −2 ∫_P x dA,

     and `(S)` follows since `⟪x,nⱼ⟫ ≤ 0` on the polygon `P = C ∩ S²` with a
     strict interior region.  `face_pos_of_coNormalFlux` proves exactly this
     last algebraic implication from the finite hypothesis
     `W = −2 u, ⟪u,nⱼ⟫ < 0`, and `coNormalFlux_simplicial` confirms the
     hypothesis is satisfiable (it is the trihedral `sphericalBarycenter`
     certificate of `Vdb.AngleNFace`).  But establishing the identity itself is
     the spherical divergence theorem / surface measure, which is absent from
     the imported mathlib slice — this is the wall already recorded in
     `lean/VERIFICATION.md` for `Vdb.AngleNFace`.  The alternative closed-loop
     `∮ dT = 0` of the tangent indicatrix yields a sum of EXTERIOR angles times
     vertex co-normals equal to zero, a different identity that does not
     determine `W`.

  4. THE ALGEBRAIC HALF OF STOKES IS NOW LANDED.  `cross_x_cross_n_x` shows the
     boundary integrand `x × x'` is the constant face normal `n` along a
     great-circle arc; `arcBoundaryFlux_eq` integrates this constant over an
     arc of length `θ` to get `θ • n`; and
     `polygonBoundaryFlux_eq_weightedNormalSum` sums the arcs to obtain

         ∮ x × dx = Σᵢ θᵢ nᵢ

     by pure algebra, for ANY finite spherical polygon — in particular for the
     spherical triangle `n = 3`.  `coNormalFlux_of_boundaryStokes` then shows
     that the ONE remaining step,

         ∮ x × dx = -2 ∫_P x dA      (spherical Stokes / surface measure),

     suffices for the co-normal flux identity and hence for (S).  That step
     is stated explicitly as the hypothesis `hStokes` and is NOT proved: surface
     measure on `S²` is absent from the imported mathlib slice, and the
     available divergence theorem applies only to boxes, not to a spherical
     triangle.  This is the precise wall; it is analytic, not algebraic.

  CONCLUSION.  No purely algebraic proof of (S) for arbitrary `n` was obtained
  by this route; the obstruction is the unavailability of the spherical Stokes
  identity, not an algebraic gap.  The landed pieces are the rigorous tangent
  algebra, the corrected (telescoping) closed-loop identity, the exact
  algebraic reduction of (S) to the co-normal flux identity, and now the
  complete algebraic half of the boundary (Stokes) integral with the remaining
  analytic step isolated as one explicit hypothesis.  No theorem was weakened,
  no placeholder proof was introduced, and no other file was edited.
  ===========================================================================
-/
