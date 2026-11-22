/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  Arbitrary n-face geometric seam (S), as a bounded VS-4a proof group.

  For a finite family of unit normals `n : ι → V3` positively spanning a
  pointed full-dimensional cone, with the genuine geometric corner angles
  `θ i > 0` of the cone's edge rays, the perimeter seam is

      ∀ j, 0 < Σ i, θ i * dot (n i) (n j).                          (S)

  This module lands two rigorous tiers toward (S) beyond the trihedral case
  of `Vdb/AngleVertexFigure.lean`:

  * `sphericalBarycenter` packages the *discrete* form of the spherical Stokes
    identity `Σ θᵢ nᵢ = -2 ∫_P x dA` (a positive finite combination of points
    of the vertex figure).  `nFace_face_pos_of_sphericalBarycenter` and
    `nFace_conic_pairs_pos_of_sphericalBarycenter` prove (S) and its cone
    pairing form from it.  The hypothesis itself is the named hard step:
    proving it needs spherical surface measure / Stokes, unavailable in the
    imported mathlib slice (escalation tier 3 of plan-lean.md §4.0).

  * `fourFace_face_pos_of_fanCertificate` proves the n = 4 case modulo a
    *fan certificate*: a diagonal normal `m` splitting the quadrilateral
    vertex figure into two spherical triangles whose corner angles match
    `θ`, together with the dual-cone membership of every face normal in both
    triangles.  The diagonal contributions cancel algebraically; the two
    triangle pairings are discharged by `three_face_face_pos_unconditional`.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.AngleVertexFigure

namespace Vdb
namespace V3

open scoped Real
open Real

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! ### Finite sum algebra over `V3` -/

/-- If `v` pairs positively with every generator `n i`, it pairs positively
    with any nonnegative combination `Σ ell i n i` that is not identically
    zero.  This is the dual-cone transfer step of the fan reduction. -/
lemma pos_on_nonneg_combination {ι : Type*} [Fintype ι]
    (v : V3) (n : ι → V3) (hv : ∀ i, 0 < dot v (n i))
    (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i) (hellpos : ∃ i, 0 < ell i) :
    0 < ∑ i, ell i * dot v (n i) := by
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (hell i) (le_of_lt (hv i))
  · obtain ⟨i, hi⟩ := hellpos
    exact ⟨i, Finset.mem_univ i, mul_pos hi (hv i)⟩

/-! ### Tier 3: (S) modulo the discrete spherical Stokes identity -/

/-- **Discrete spherical Stokes / vertex-figure centroid hypothesis.**
    `sphericalBarycenter n θ u α` says the angle-weighted normal `Σ θᵢ nᵢ`
    equals minus twice a strictly positive combination `Σ αₖ uₖ` of vectors
    of the cone `C = {x | ∀ j, ⟪nⱼ, x⟫ ≤ 0}`, and every face `j` has a
    representative `uₖ` lying strictly inside its supporting half-space.

    This is the finite form of the Bochner-integral identity
        Σᵢ θᵢ nᵢ = -2 ∫_P x dA,     P = C ∩ S²,
    obtained by writing the integral as a limit of positive Riemann sums.
    The genuine geometric corner angles are the side lengths of `P`, so each
    `uₖ ∈ P` satisfies `⟪uₖ, nⱼ⟫ ≤ 0`; `P` meeting the interior of each face
    gives the strict representative.  Proving the identity is the hard step
    (spherical Stokes + surface measure) and is NOT claimed here. -/
def sphericalBarycenter {ι κ : Type*} [Fintype ι] [Fintype κ]
    (n : ι → V3) (θ : ι → ℝ) (u : κ → V3) (α : κ → ℝ) : Prop :=
  (∀ k, 0 < α k) ∧
  (∀ k j, dot (u k) (n j) ≤ 0) ∧
  (∀ j, ∃ k, dot (u k) (n j) < 0) ∧
  (∀ j, (∑ i, θ i * dot (n i) (n j)) =
    -2 * (∑ k, α k * dot (u k) (n j)))

/-- The face pairing is positive once the discrete spherical Stokes
    decomposition is available: `-2` times a negative combination of cone
    points is a positive combination in the opposite direction. -/
lemma sphericalBarycenter_face_pos {ι κ : Type*} [Fintype ι] [Fintype κ]
    (n : ι → V3) (θ : ι → ℝ) (u : κ → V3) (α : κ → ℝ)
    (hb : sphericalBarycenter n θ u α) (j : ι) :
    0 < ∑ i, θ i * dot (n i) (n j) := by
  rw [hb.2.2.2 j]
  have hnonpos : ∀ k, α k * dot (u k) (n j) ≤ 0 := by
    intro k
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hb.1 k)) (hb.2.1 k j)
  have hstrict : ∃ k, α k * dot (u k) (n j) < 0 := by
    obtain ⟨k, hk⟩ := hb.2.2.1 j
    exact ⟨k, mul_neg_of_pos_of_neg (hb.1 k) hk⟩
  have hpos : 0 < ∑ k, -(α k * dot (u k) (n j)) := by
    apply Finset.sum_pos'
    · intro k _
      exact neg_nonneg.mpr (hnonpos k)
    · obtain ⟨k, hk⟩ := hstrict
      exact ⟨k, Finset.mem_univ k, neg_pos.mpr hk⟩
  rw [Finset.sum_neg_distrib] at hpos
  nlinarith

/-- **Arbitrary n-face seam (S), conditional on the discrete spherical Stokes
    identity.**  This is tier 3: the geometric hard step is the named premise
    `sphericalBarycenter`; everything downstream is proved. -/
theorem nFace_face_pos_of_sphericalBarycenter {ι κ : Type*} [Fintype ι] [Fintype κ]
    (n : ι → V3) (θ : ι → ℝ) (u : κ → V3) (α : κ → ℝ)
    (hb : sphericalBarycenter n θ u α) :
    ∀ j, 0 < ∑ i, θ i * dot (n i) (n j) := by
  exact sphericalBarycenter_face_pos n θ u α hb

/-- The conic pairing form: an arbitrary nonnegative combination of the face
    normals that is not zero pairs positively with the angle-weighted normal.
    Composes with `angleWeightedNormal_pairs_pos` once (S) is available. -/
theorem nFace_conic_pairs_pos_of_sphericalBarycenter
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (n : ι → V3) (θ : ι → ℝ) (u : κ → V3) (α : κ → ℝ)
    (hb : sphericalBarycenter n θ u α)
    (ell : ι → ℝ) (hell : ∀ i, 0 ≤ ell i) (hellpos : ∃ i, 0 < ell i) :
    0 < ∑ i, ell i * (∑ j, θ j * dot (n j) (n i)) := by
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (hell i) (le_of_lt (nFace_face_pos_of_sphericalBarycenter n θ u α hb i))
  · obtain ⟨i, hi⟩ := hellpos
    exact ⟨i, Finset.mem_univ i,
      mul_pos hi (nFace_face_pos_of_sphericalBarycenter n θ u α hb i)⟩

/-! ### Tier 2: the n = 4 fan certificate -/

/-- Weighted sum of the three faces of a trihedral fan piece. -/
noncomputable def fanWeighted (a b m : V3) (wa wb d : ℝ) : V3 :=
  V3.add (V3.add (pnSmul wa a) (pnSmul wb b)) (pnSmul d m)

theorem dot_fanWeighted (x a b m : V3) (wa wb d : ℝ) :
    dot x (fanWeighted a b m wa wb d) =
      wa * dot x a + wb * dot x b + d * dot x m := by
  unfold fanWeighted pnSmul V3.add V3.dot
  ring

/-- The four-face weighted sum splits across a diagonal normal `m`:
    the two diagonal contributions cancel, leaving `Σ θᵢ nᵢ`. -/
theorem dot_fan_sum_four (x n₀ n₁ n₂ n₃ m : V3)
    (θ₀ θ₁ θ₂ θ₃ d : ℝ) :
    dot x (fanWeighted n₀ n₁ m θ₀ θ₁ d) +
      dot x (fanWeighted (pnSmul (-1) m) n₂ n₃ d θ₂ θ₃) =
        θ₀ * dot x n₀ + θ₁ * dot x n₁ + θ₂ * dot x n₂ + θ₃ * dot x n₃ := by
  rw [dot_fanWeighted, dot_fanWeighted]
  unfold pnSmul V3.dot
  ring

/-- One triangle of the fan: if the three geometric corner angles of the
    trihedral cone `(a,b,m)` match the weights `(wa,wb,d)`, the landed
    three-face theorem makes its weighted normal pair positively with each of
    its generators; the dual-cone transfer then gives positivity against any
    vector `x` whose direction is a nonnegative combination of those
    generators. -/
lemma fanTriangle_pair_pos (a b m x : V3) (wa wb d : ℝ)
    (ha : dot a a = 1) (hb : dot b b = 1) (hm : dot m m = 1)
    (htri : triple a b m ≠ 0)
    (hang1 : cornerAngle (isoEdge12 a b) (isoEdge13 a m) = wa)
    (hang2 : cornerAngle (isoEdge12 a b) (isoEdge23 b m) = wb)
    (hang3 : cornerAngle (isoEdge13 a m) (isoEdge23 b m) = d)
    (ell0 ell1 ellm : ℝ)
    (hell0 : 0 ≤ ell0) (hell1 : 0 ≤ ell1) (hellm : 0 ≤ ellm)
    (hellpos : 0 < ell0 ∨ 0 < ell1 ∨ 0 < ellm)
    (hdual : dot x (fanWeighted a b m wa wb d) =
      ell0 * dot a (fanWeighted a b m wa wb d) +
      ell1 * dot b (fanWeighted a b m wa wb d) +
      ellm * dot m (fanWeighted a b m wa wb d)) :
    0 < dot x (fanWeighted a b m wa wb d) := by
  have ht := three_face_face_pos_unconditional a b m ha hb hm
      (by rfl : dot a b = dot a b) (by rfl : dot a m = dot a m)
      (by rfl : dot b m = dot b m) htri
  dsimp at ht
  rw [hang1, hang2, hang3] at ht
  rcases ht with ⟨hA, hB, hC⟩
  have hva : 0 < dot a (fanWeighted a b m wa wb d) := by
    rw [dot_fanWeighted]
    rw [← dot_commV b a, ← dot_commV m a]
    nlinarith
  have hvb : 0 < dot b (fanWeighted a b m wa wb d) := by
    rw [dot_fanWeighted]
    rw [← dot_commV a b, ← dot_commV m b]
    nlinarith
  have hvm : 0 < dot m (fanWeighted a b m wa wb d) := by
    rw [dot_fanWeighted]
    rw [← dot_commV a m, ← dot_commV b m]
    nlinarith
  rw [hdual]
  rcases hellpos with h0 | h1 | hmpos
  · have h1' : 0 ≤ ell1 * dot b (fanWeighted a b m wa wb d) :=
      mul_nonneg hell1 (le_of_lt hvb)
    have hm' : 0 ≤ ellm * dot m (fanWeighted a b m wa wb d) :=
      mul_nonneg hellm (le_of_lt hvm)
    nlinarith [mul_pos h0 hva]
  · have h0' : 0 ≤ ell0 * dot a (fanWeighted a b m wa wb d) :=
      mul_nonneg hell0 (le_of_lt hva)
    have hm' : 0 ≤ ellm * dot m (fanWeighted a b m wa wb d) :=
      mul_nonneg hellm (le_of_lt hvm)
    nlinarith [mul_pos h1 hvb]
  · have h0' : 0 ≤ ell0 * dot a (fanWeighted a b m wa wb d) :=
      mul_nonneg hell0 (le_of_lt hva)
    have h1' : 0 ≤ ell1 * dot b (fanWeighted a b m wa wb d) :=
      mul_nonneg hell1 (le_of_lt hvb)
    nlinarith [mul_pos hmpos hvm]

/-- Unit-norm statement for the negated diagonal normal `pnSmul (-1) m`. -/
theorem pnSmul_neg_unit (m : V3) (hm : dot m m = 1) :
    dot (pnSmul (-1) m) (pnSmul (-1) m) = 1 := by
  dsimp [pnSmul, dot] at hm ⊢
  nlinarith

/-- **Arbitrary 4-face seam (S) with a fan certificate.**  The certificate
    consists of: a diagonal normal `m` splitting the vertex figure into the
    two trihedra `(n₀,n₁,m)` and `(-m,n₂,n₃)`; matching of the geometric corner
    angles with the weights `(θ₀,θ₁,d)` and `(d,θ₂,θ₃)`; nondegeneracy of both
    trihedra; and, for every face `j` and each of the two trihedra, a
    nonnegative combination of that trihedron's normals with at least one
    positive coefficient representing the direction of `n j` (this is
    `C° ⊆ C₁° ∩ C₂°`, the dual-cone containment of the fan). -/
theorem fourFace_face_pos_of_fanCertificate
    (n₀ n₁ n₂ n₃ m : V3) (θ₀ θ₁ θ₂ θ₃ d : ℝ)
    (h0 : dot n₀ n₀ = 1) (h1 : dot n₁ n₁ = 1)
    (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1) (hm : dot m m = 1)
    (htri1 : triple n₀ n₁ m ≠ 0) (htri2 : triple (pnSmul (-1) m) n₂ n₃ ≠ 0)
    (hang1a : cornerAngle (isoEdge12 n₀ n₁) (isoEdge13 n₀ m) = θ₀)
    (hang1b : cornerAngle (isoEdge12 n₀ n₁) (isoEdge23 n₁ m) = θ₁)
    (hang1c : cornerAngle (isoEdge13 n₀ m) (isoEdge23 n₁ m) = d)
    (hang2a : cornerAngle (isoEdge12 (pnSmul (-1) m) n₂)
        (isoEdge13 (pnSmul (-1) m) n₃) = d)
    (hang2b : cornerAngle (isoEdge12 (pnSmul (-1) m) n₂)
        (isoEdge23 n₂ n₃) = θ₂)
    (hang2c : cornerAngle (isoEdge13 (pnSmul (-1) m) n₃)
        (isoEdge23 n₂ n₃) = θ₃)
    -- dual-cone membership, for each face j in each of the two trihedra
    (hdu : ∀ x : V3, ∃ a₀ a₁ am : ℝ,
        0 ≤ a₀ ∧ 0 ≤ a₁ ∧ 0 ≤ am ∧ (0 < a₀ ∨ 0 < a₁ ∨ 0 < am) ∧
        dot x (fanWeighted n₀ n₁ m θ₀ θ₁ d) =
          a₀ * dot n₀ (fanWeighted n₀ n₁ m θ₀ θ₁ d) +
          a₁ * dot n₁ (fanWeighted n₀ n₁ m θ₀ θ₁ d) +
          am * dot m (fanWeighted n₀ n₁ m θ₀ θ₁ d))
    (hdv : ∀ x : V3, ∃ b0 b₂ b₃ : ℝ,
        0 ≤ b0 ∧ 0 ≤ b₂ ∧ 0 ≤ b₃ ∧ (0 < b0 ∨ 0 < b₂ ∨ 0 < b₃) ∧
        dot x (fanWeighted (pnSmul (-1) m) n₂ n₃ d θ₂ θ₃) =
          b0 * dot (pnSmul (-1) m) (fanWeighted (pnSmul (-1) m) n₂ n₃ d θ₂ θ₃) +
          b₂ * dot n₂ (fanWeighted (pnSmul (-1) m) n₂ n₃ d θ₂ θ₃) +
          b₃ * dot n₃ (fanWeighted (pnSmul (-1) m) n₂ n₃ d θ₂ θ₃)) :
    let v : Fin 4 → V3 := fun j =>
      if j = 0 then n₀ else if j = 1 then n₁ else if j = 2 then n₂ else n₃
    ∀ j : Fin 4,
      0 < θ₀ * dot n₀ (v j) + θ₁ * dot n₁ (v j) +
          θ₂ * dot n₂ (v j) + θ₃ * dot n₃ (v j) := by
  dsimp
  intro j
  let x : V3 := if j = 0 then n₀ else if j = 1 then n₁ else if j = 2 then n₂ else n₃
  have hp1 : 0 < dot x (fanWeighted n₀ n₁ m θ₀ θ₁ d) := by
    obtain ⟨a₀, a₁, am, ha₀, ha₁, ham, hpos, hd⟩ := hdu x
    exact fanTriangle_pair_pos n₀ n₁ m x θ₀ θ₁ d h0 h1 hm htri1
      hang1a hang1b hang1c a₀ a₁ am ha₀ ha₁ ham hpos hd
  have hp2 : 0 < dot x (fanWeighted (pnSmul (-1) m) n₂ n₃ d θ₂ θ₃) := by
    obtain ⟨b0, b₂, b₃, hb0, hb₂, hb₃, hpos, hd⟩ := hdv x
    exact fanTriangle_pair_pos (pnSmul (-1) m) n₂ n₃ x d θ₂ θ₃
      (pnSmul_neg_unit m hm) h2 h3 htri2 hang2a hang2b hang2c
      b0 b₂ b₃ hb0 hb₂ hb₃ hpos hd
  have hsplit : θ₀ * dot n₀ x + θ₁ * dot n₁ x + θ₂ * dot n₂ x + θ₃ * dot n₃ x =
      dot x (fanWeighted n₀ n₁ m θ₀ θ₁ d) +
        dot x (fanWeighted (pnSmul (-1) m) n₂ n₃ d θ₂ θ₃) := by
    rw [dot_fan_sum_four x n₀ n₁ n₂ n₃ m θ₀ θ₁ θ₂ θ₃ d]
    rw [← dot_commV n₀ x, ← dot_commV n₁ x, ← dot_commV n₂ x, ← dot_commV n₃ x]
  have hsum : 0 < θ₀ * dot n₀ x + θ₁ * dot n₁ x +
      θ₂ * dot n₂ x + θ₃ * dot n₃ x := by
    rw [hsplit]
    exact add_pos hp1 hp2
  fin_cases j <;> dsimp [x] at hsum ⊢ <;> simpa using hsum

/-! ### A non-vacuous form of the n = 4 fan theorem

The landed `fourFace_face_pos_of_fanCertificate` quantifies its dual-cone
transfer hypotheses `hdu`, `hdv` over *all* `x : V3`.  Since the fan weights
`W₁ = Σ θᵢ nᵢ` and `W₂` are nonzero (each has a strictly positive pairing with
its generators), choosing `x = -W₁` makes the hypothesis contradictory: the
left side is `-⟪W₁,W₁⟫ < 0` while the right side is a nonnegative combination
of strictly positive numbers.  So that theorem is vacuous, although its
diagonal-cancellation proof is sound.  The corrected version below requires
the transfer only at the four face normals, which is the intended dual-cone
containment and is satisfiable. -/

/-- The four normals of the fan indexed by `Fin 4`. -/
def fanFace4 (n₀ n₁ n₂ n₃ : V3) (j : Fin 4) : V3 :=
  if j = 0 then n₀ else if j = 1 then n₁ else if j = 2 then n₂ else n₃

/-- **Non-vacuous n = 4 seam with a fan certificate.**  Same diagonal
    cancellation as `fourFace_face_pos_of_fanCertificate`, but the dual-cone
    transfer is required only at the four face normals. -/
theorem fourFace_face_pos_of_fanCertificate_faces
    (n₀ n₁ n₂ n₃ m : V3) (θ₀ θ₁ θ₂ θ₃ d : ℝ)
    (h0 : dot n₀ n₀ = 1) (h1 : dot n₁ n₁ = 1)
    (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1) (hm : dot m m = 1)
    (htri1 : triple n₀ n₁ m ≠ 0) (htri2 : triple (pnSmul (-1) m) n₂ n₃ ≠ 0)
    (hang1a : cornerAngle (isoEdge12 n₀ n₁) (isoEdge13 n₀ m) = θ₀)
    (hang1b : cornerAngle (isoEdge12 n₀ n₁) (isoEdge23 n₁ m) = θ₁)
    (hang1c : cornerAngle (isoEdge13 n₀ m) (isoEdge23 n₁ m) = d)
    (hang2a : cornerAngle (isoEdge12 (pnSmul (-1) m) n₂)
        (isoEdge13 (pnSmul (-1) m) n₃) = d)
    (hang2b : cornerAngle (isoEdge12 (pnSmul (-1) m) n₂)
        (isoEdge23 n₂ n₃) = θ₂)
    (hang2c : cornerAngle (isoEdge13 (pnSmul (-1) m) n₃)
        (isoEdge23 n₂ n₃) = θ₃)
    (hdu : ∀ j : Fin 4, ∃ a₀ a₁ am : ℝ,
        0 ≤ a₀ ∧ 0 ≤ a₁ ∧ 0 ≤ am ∧ (0 < a₀ ∨ 0 < a₁ ∨ 0 < am) ∧
        dot (fanFace4 n₀ n₁ n₂ n₃ j) (fanWeighted n₀ n₁ m θ₀ θ₁ d) =
          a₀ * dot n₀ (fanWeighted n₀ n₁ m θ₀ θ₁ d) +
          a₁ * dot n₁ (fanWeighted n₀ n₁ m θ₀ θ₁ d) +
          am * dot m (fanWeighted n₀ n₁ m θ₀ θ₁ d))
    (hdv : ∀ j : Fin 4, ∃ b0 b₂ b₃ : ℝ,
        0 ≤ b0 ∧ 0 ≤ b₂ ∧ 0 ≤ b₃ ∧ (0 < b0 ∨ 0 < b₂ ∨ 0 < b₃) ∧
        dot (fanFace4 n₀ n₁ n₂ n₃ j)
            (fanWeighted (pnSmul (-1) m) n₂ n₃ d θ₂ θ₃) =
          b0 * dot (pnSmul (-1) m)
            (fanWeighted (pnSmul (-1) m) n₂ n₃ d θ₂ θ₃) +
          b₂ * dot n₂ (fanWeighted (pnSmul (-1) m) n₂ n₃ d θ₂ θ₃) +
          b₃ * dot n₃ (fanWeighted (pnSmul (-1) m) n₂ n₃ d θ₂ θ₃)) :
    ∀ j : Fin 4,
      0 < θ₀ * dot n₀ (fanFace4 n₀ n₁ n₂ n₃ j) +
          θ₁ * dot n₁ (fanFace4 n₀ n₁ n₂ n₃ j) +
          θ₂ * dot n₂ (fanFace4 n₀ n₁ n₂ n₃ j) +
          θ₃ * dot n₃ (fanFace4 n₀ n₁ n₂ n₃ j) := by
  intro j
  let x : V3 := fanFace4 n₀ n₁ n₂ n₃ j
  change 0 < θ₀ * dot n₀ x + θ₁ * dot n₁ x + θ₂ * dot n₂ x + θ₃ * dot n₃ x
  have hp1 : 0 < dot x (fanWeighted n₀ n₁ m θ₀ θ₁ d) := by
    obtain ⟨a₀, a₁, am, ha₀, ha₁, ham, hpos, hd⟩ := hdu j
    exact fanTriangle_pair_pos n₀ n₁ m x θ₀ θ₁ d h0 h1 hm htri1
      hang1a hang1b hang1c a₀ a₁ am ha₀ ha₁ ham hpos hd
  have hp2 : 0 < dot x (fanWeighted (pnSmul (-1) m) n₂ n₃ d θ₂ θ₃) := by
    obtain ⟨b0, b₂, b₃, hb0, hb₂, hb₃, hpos, hd⟩ := hdv j
    exact fanTriangle_pair_pos (pnSmul (-1) m) n₂ n₃ x d θ₂ θ₃
      (pnSmul_neg_unit m hm) h2 h3 htri2 hang2a hang2b hang2c
      b0 b₂ b₃ hb0 hb₂ hb₃ hpos hd
  have hsplit : θ₀ * dot n₀ x + θ₁ * dot n₁ x + θ₂ * dot n₂ x + θ₃ * dot n₃ x =
      dot x (fanWeighted n₀ n₁ m θ₀ θ₁ d) +
        dot x (fanWeighted (pnSmul (-1) m) n₂ n₃ d θ₂ θ₃) := by
    rw [dot_fan_sum_four x n₀ n₁ n₂ n₃ m θ₀ θ₁ θ₂ θ₃ d]
    rw [← dot_commV n₀ x, ← dot_commV n₁ x, ← dot_commV n₂ x, ← dot_commV n₃ x]
  rw [hsplit]
  exact add_pos hp1 hp2

/-! ### Tier 3 made concrete: (S) ⇔ `sphericalBarycenter`

The "discrete spherical Stokes" hypothesis is in fact *equivalent* to the
face-positivity seam (S) itself; no surface measure is needed for either
direction.  The forward direction is the existing
`sphericalBarycenter_face_pos`.  Conversely, from (S) one takes the singleton
certificate `u = -Σᵢ θᵢ nᵢ`, `α = 1/2`: the vector `-Σᵢ θᵢ nᵢ` lies in the
cone `C = {x | ∀ j, ⟪nⱼ,x⟫ ≤ 0}` exactly when (S) holds, and it meets every
supporting half-space strictly.  The identity is pure bilinearity of `dot`.

Consequently every unconditional tier of (S) yields an unconditional instance
of `sphericalBarycenter`, including the simplicial (trihedral) case proved by
`three_face_face_pos_unconditional` and the arbitrary-n non-obtuse case. -/

/-- The angle-weighted normal as an explicit `V3` (componentwise Finset sum). -/
noncomputable def weightedNormalSum {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (n : ι → V3) : V3 :=
  ⟨∑ i, θ i * (n i).x, ∑ i, θ i * (n i).y, ∑ i, θ i * (n i).z⟩

/-- Bilinearity: `⟪x, Σᵢ θᵢ nᵢ⟫ = Σᵢ θᵢ ⟪x, nᵢ⟫`. -/
lemma dot_weightedNormalSum {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (n : ι → V3) (x : V3) :
    dot x (weightedNormalSum θ n) = ∑ i, θ i * dot x (n i) := by
  unfold weightedNormalSum dot
  calc
    x.x * (∑ i, θ i * (n i).x) + x.y * (∑ i, θ i * (n i).y) +
        x.z * (∑ i, θ i * (n i).z)
        = (∑ i, x.x * (θ i * (n i).x)) + (∑ i, x.y * (θ i * (n i).y)) +
            (∑ i, x.z * (θ i * (n i).z)) := by
              rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    _ = ∑ i, (x.x * (θ i * (n i).x) + x.y * (θ i * (n i).y) +
            x.z * (θ i * (n i).z)) := by
              rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    _ = ∑ i, θ i * (x.x * (n i).x + x.y * (n i).y + x.z * (n i).z) := by
              apply Finset.sum_congr rfl
              intro i _
              ring

/-- **The discrete Stokes hypothesis is equivalent to (S).**  From the
    per-face positivity of `Σᵢ θᵢ nᵢ` we build the strict cone-point
    certificate with no spherical integration: take `κ = PUnit`,
    `u = -Σᵢ θᵢ nᵢ` and `α = 1/2`. -/
lemma sphericalBarycenter_of_face_pos {ι : Type*} [Fintype ι]
    (n : ι → V3) (θ : ι → ℝ)
    (hface : ∀ j, 0 < ∑ i, θ i * dot (n i) (n j)) :
    sphericalBarycenter n θ
      (fun _ : PUnit => pnSmul (-1) (weightedNormalSum θ n))
      (fun _ : PUnit => (1 / 2 : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    norm_num
  · intro k j
    rw [dot_pnSmul_neg_left, dot_commV (weightedNormalSum θ n) (n j),
      dot_weightedNormalSum]
    simp_rw [dot_commV (n j)]
    exact neg_nonpos.mpr (le_of_lt (hface j))
  · intro j
    refine ⟨PUnit.unit, ?_⟩
    rw [dot_pnSmul_neg_left, dot_commV (weightedNormalSum θ n) (n j),
      dot_weightedNormalSum]
    simp_rw [dot_commV (n j)]
    exact neg_lt_zero.mpr (hface j)
  · intro j
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_punit,
      nsmul_eq_mul]
    rw [dot_pnSmul_neg_left, dot_commV (weightedNormalSum θ n) (n j),
      dot_weightedNormalSum]
    simp_rw [dot_commV (n j)]
    ring

/-- Package three face-positivities into the `Fin 3` sum shape of (S). -/
lemma face_pos_fin3_of_conj (θ₁ θ₂ θ₃ : ℝ) (n₁ n₂ n₃ : V3)
    (hA : 0 < θ₁ * dot n₁ n₁ + θ₂ * dot n₂ n₁ + θ₃ * dot n₃ n₁)
    (hB : 0 < θ₁ * dot n₁ n₂ + θ₂ * dot n₂ n₂ + θ₃ * dot n₃ n₂)
    (hC : 0 < θ₁ * dot n₁ n₃ + θ₂ * dot n₂ n₃ + θ₃ * dot n₃ n₃) :
    ∀ j : Fin 3, 0 < ∑ i : Fin 3,
      (if i = 0 then θ₁ else if i = 1 then θ₂ else θ₃) *
        dot (if i = 0 then n₁ else if i = 1 then n₂ else n₃)
            (if j = 0 then n₁ else if j = 1 then n₂ else n₃) := by
  intro j
  fin_cases j <;> simp [Fin.sum_univ_three, hA, hB, hC]

/-- **Simplicial (trihedral) case of the discrete Stokes hypothesis**, proved
    without any Stokes/surface-measure input: the three-face seam is already
    unconditional in `Vdb.AngleVertexFigure`, and the certificate above converts
    it into `sphericalBarycenter` by bilinearity. -/
theorem sphericalBarycenter_simplicial
    (n₁ n₂ n₃ : V3) {p r q : ℝ}
    (h1 : dot n₁ n₁ = 1) (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1)
    (h12 : dot n₁ n₂ = p) (h13 : dot n₁ n₃ = r) (h23 : dot n₂ n₃ = q)
    (htriple : triple n₁ n₂ n₃ ≠ 0) :
    let v : Fin 3 → V3 := fun j =>
      if j = 0 then n₁ else if j = 1 then n₂ else n₃
    let θ : Fin 3 → ℝ := fun j =>
      if j = 0 then cornerAngle (isoEdge12 n₁ n₂) (isoEdge13 n₁ n₃)
      else if j = 1 then cornerAngle (isoEdge12 n₁ n₂) (isoEdge23 n₂ n₃)
      else cornerAngle (isoEdge13 n₁ n₃) (isoEdge23 n₂ n₃)
    sphericalBarycenter v θ
      (fun _ : PUnit => pnSmul (-1) (weightedNormalSum θ v))
      (fun _ : PUnit => (1 / 2 : ℝ)) := by
  dsimp
  have ht := three_face_face_pos_unconditional n₁ n₂ n₃ h1 h2 h3
    h12 h13 h23 htriple
  dsimp at ht
  exact
    (sphericalBarycenter_of_face_pos
      (fun j : Fin 3 => if j = 0 then n₁ else if j = 1 then n₂ else n₃)
      (fun j : Fin 3 =>
        if j = 0 then cornerAngle (isoEdge12 n₁ n₂) (isoEdge13 n₁ n₃)
        else if j = 1 then cornerAngle (isoEdge12 n₁ n₂) (isoEdge23 n₂ n₃)
        else cornerAngle (isoEdge13 n₁ n₃) (isoEdge23 n₂ n₃))
      (face_pos_fin3_of_conj
        (cornerAngle (isoEdge12 n₁ n₂) (isoEdge13 n₁ n₃))
        (cornerAngle (isoEdge12 n₁ n₂) (isoEdge23 n₂ n₃))
        (cornerAngle (isoEdge13 n₁ n₃) (isoEdge23 n₂ n₃))
        n₁ n₂ n₃ ht.1 ht.2.1 ht.2.2))

/-- The `V3` version of `face_pos_of_nonobtuse`: the diagonal term is `θⱼ` and
    every off-diagonal term is nonnegative. -/
lemma face_pos_nonobtuse_V3 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : ι → ℝ) (hθ : ∀ i, 0 < θ i) (n : ι → V3)
    (hn : ∀ i, dot (n i) (n i) = 1)
    (hnonobtuse : ∀ i j, i ≠ j → 0 ≤ dot (n i) (n j)) :
    ∀ j, 0 < ∑ i, θ i * dot (n i) (n j) := by
  intro j
  apply Finset.sum_pos'
  · intro i _
    by_cases hij : i = j
    · rw [hij, hn j, mul_one]
      exact le_of_lt (hθ j)
    · exact mul_nonneg (le_of_lt (hθ i)) (hnonobtuse i j hij)
  · refine ⟨j, Finset.mem_univ j, ?_⟩
    rw [hn j, mul_one]
    exact hθ j

/-- **Unconditional arbitrary-n instance of the discrete Stokes hypothesis.**
    For any finite family of unit normals with pairwise nonnegative dots and
    positive weights, the singleton certificate above works. -/
theorem sphericalBarycenter_nonobtuse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : ι → ℝ) (hθ : ∀ i, 0 < θ i) (n : ι → V3)
    (hn : ∀ i, dot (n i) (n i) = 1)
    (hnonobtuse : ∀ i j, i ≠ j → 0 ≤ dot (n i) (n j)) :
    sphericalBarycenter n θ
      (fun _ : PUnit => pnSmul (-1) (weightedNormalSum θ n))
      (fun _ : PUnit => (1 / 2 : ℝ)) := by
  exact sphericalBarycenter_of_face_pos n θ
    (face_pos_nonobtuse_V3 θ hθ n hn hnonobtuse)

/-! ### Status of this group and the precise remaining gap

Landed here (all sorry-free, `warningAsError` on):

  * `nFace_face_pos_of_sphericalBarycenter` and
    `nFace_conic_pairs_pos_of_sphericalBarycenter`: (S) and its conic form for
    an arbitrary finite family, modulo the named discrete spherical Stokes
    hypothesis `sphericalBarycenter`.
  * `fourFace_face_pos_of_fanCertificate`: the n = 4 case modulo an explicit
    fan certificate (diagonal normal, angle matching, nondegeneracy, dual-cone
    membership).  The diagonal cancellation `dot_fan_sum_four` is proved by
    ring; both triangle pairings come from `three_face_face_pos_unconditional`.
    Its `hdu`/`hdv` hypotheses quantify over all `x : V3` and are therefore
    vacuous; the non-vacuous corrected form is
    `fourFace_face_pos_of_fanCertificate_faces` (transfer required only at the
    four face normals).
  * `sphericalBarycenter_of_face_pos` and its converse
    `sphericalBarycenter_face_pos`: the discrete Stokes hypothesis is
    *equivalent* to (S), via the singleton certificate `κ = PUnit`,
    `u = -Σᵢ θᵢ nᵢ`, `α = 1/2`.  No surface measure is needed in either
    direction.
  * `sphericalBarycenter_simplicial`: the trihedral case of the barycenter
    hypothesis, unconditional, from `three_face_face_pos_unconditional`.
  * `sphericalBarycenter_nonobtuse`: an unconditional arbitrary-n instance of
    the barycenter hypothesis for pairwise nonnegative normal dots.

Precise remaining gap (the wall of VS-4a):

  1. Prove (S) itself for arbitrary n and geometric corner angles.  Since
     `sphericalBarycenter ⇔ (S)`, this is the real hard step; the former
     framing as a spherical-Stokes identity `Σ θᵢ nᵢ = -2 ∫_P x dA` needs the
     spherical divergence theorem and surface measure (absent from the imported
     mathlib slice), so no progress was made on it here.
  2. Prove the n = 4 fan certificate from geometry: existence of a diagonal
     great-circle arc splitting the spherical quadrilateral into two
     nondegenerate spherical triangles, equality of the boundary arc lengths
     with the corner angles of the two trihedra, and the dual-cone containment
     `C° ⊆ C₁° ∩ C₂°` at the four face normals.  (For n > 4, iterate the fan and
     use induction; the diagonal contributions cancel telescopically exactly
     as in `dot_fan_sum_four`.)
  3. Drop the "strict representative" clause of `sphericalBarycenter` when
     the cone is pointed and full-dimensional (then every face has an interior
     point of `C` in its supporting half-space).

No landed theorem was weakened or deleted; the trihedral results in
`Vdb/AngleVertexFigure.lean` are untouched. -/

end V3
end Vdb
