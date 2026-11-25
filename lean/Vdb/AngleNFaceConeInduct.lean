/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  Composed dual-cone containments for the general-n fan induction.

  `Vdb/AngleNFaceGeneral.lean` transports a `FanCertificate` from a chain `F`
  to the chain obtained by prepending a new triangle `(a,b,m)`.  The only
  geometric inputs that were left explicit there were the two composed
  dual-cone containments

      htrF_a : FanChainTransferAt F a
      htrF_b : FanChainTransferAt F b .

  This module proves those two containments from the abstract ingredients
  already available in the n = 4 / n = 5 tiers: the convexity dot-signs give
  strictly positive ray coefficients c₀..c₃, and the ray identities give the
  exact vector identities

      c₀ • p₃ = c₃ • p₀ + m        c₁ • p₂ = c₂ • p₁ + m .

  Solving them yields three "split" identities

      p₀ = α • r + β • (-m)
      p₁ = γ • q' + δ • (-m)
      r  = ε • p₀ + ζ • m

  with all six coefficients strictly positive (r is the last boundary
  co-normal of the suffix polygon, q' its second boundary co-normal).  These
  are exactly the identities worked out by hand for the pentagon in
  `AngleNFaceFive.lean`.

  The induction is carried by two invariants on a vector x:

      InCone2 x (lastN F) (head F).a
      InCone3 x (lastN F) (head F).a (head F).b .

  At a `cons` the split identities rewrite `head.a` and `head.b` into the
  next diagonal, so each invariant propagates to the tail; and `hr` puts the
  last boundary normal into the current triangle's cone.  Applying the two
  invariants to a and b (whose base representations come from the quadrilateral
  cut off by the new triangle) gives `FanChainTransferAt F a` and
  `FanChainTransferAt F b` for an arbitrary chain F.  For a leaf F this
  specializes to the ordinary n = 4 `fourDiag_dual_cone` containments.

  No existing file is modified.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
 -/
import Vdb.AngleNFaceFive
import Vdb.AngleNFaceFan

namespace Vdb
namespace V3

open scoped Real
open Real

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-! ### 0. The last boundary co-normal of a chain -/

/-- The last boundary co-normal of a fan chain.  For a leaf it is the exit
    co-normal; prepending a triangle leaves it unchanged. -/
def ChainLastN : FanChain k → V3
  | FanChain.leaf T => T.m
  | FanChain.cons _ F => ChainLastN F

@[simp] lemma ChainLastN_leaf (T : FanTriangle) :
    ChainLastN (FanChain.leaf T) = T.m := rfl

@[simp] lemma ChainLastN_cons (T : FanTriangle) (F : FanChain k) :
    ChainLastN (FanChain.cons T F) = ChainLastN F := rfl

/-! ### 1. Cone combination predicates -/

/-- `x` is a nonnegative combination of two vectors with at least one
    strictly positive coefficient. -/
def InCone2 (x u v : V3) : Prop :=
  ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ (0 < s ∨ 0 < t) ∧
    x = V3.add (pnSmul s u) (pnSmul t v)

/-- `x` is a nonnegative combination of three vectors with at least one
    strictly positive coefficient. -/
def InCone3 (x u v w : V3) : Prop :=
  ∃ s t r : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ 0 ≤ r ∧ (0 < s ∨ 0 < t ∨ 0 < r) ∧
    x = V3.add (V3.add (pnSmul s u) (pnSmul t v)) (pnSmul r w)

/-- The three split identities, with strictly positive coefficients. -/
structure SplitConeData (p q m r q' : V3) : Type where
  α : ℝ
  β : ℝ
  γ : ℝ
  δ : ℝ
  ε : ℝ
  ζ : ℝ
  hα : 0 < α
  hβ : 0 < β
  hγ : 0 < γ
  hδ : 0 < δ
  hε : 0 < ε
  hζ : 0 < ζ
  hp : p = V3.add (pnSmul α r) (pnSmul β (pnSmul (-1) m))
  hq : q = V3.add (pnSmul γ q') (pnSmul δ (pnSmul (-1) m))
  hr : r = V3.add (pnSmul ε p) (pnSmul ζ m)

/-- Split data for every triangle of a chain. -/
def ChainSplitData : FanChain k → Type
  | FanChain.leaf _ => PUnit
  | FanChain.cons T F =>
      SplitConeData T.a T.b T.m (ChainLastN F) F.head.b × ChainSplitData F

/-! ### 2. Extracting the split data from the convexity signs -/

/-- From the four strict convexity signs of a quadrilateral (in the form of
    the positivity of the ray coefficients) and the ray identities, build the
    split data.  This is the bridge from the hypotheses of
    `fourDiag_dual_cone` to the abstract composition lemma. -/
noncomputable def splitConeData_of_dualC
    (p0 p1 p2 p3 : V3)
    (h30 : cross p3 p0 ≠ ⟨0, 0, 0⟩) (h12 : cross p1 p2 ≠ ⟨0, 0, 0⟩)
    (hw : cross (diagV10 p3 p0) (diagV21 p1 p2) ≠ ⟨0, 0, 0⟩)
    (hc0 : 0 < dualC0 p0 p1 p2 p3)
    (hc1 : 0 < dualC1 p0 p1 p2 p3)
    (hc2 : 0 < dualC2 p0 p1 p2 p3)
    (hc3 : 0 < dualC3 p0 p1 p2 p3) :
    SplitConeData p0 p1 (diagM p0 p1 p2 p3) p3 p2 := by
  let c0 := dualC0 p0 p1 p2 p3
  let c1 := dualC1 p0 p1 p2 p3
  let c2 := dualC2 p0 p1 p2 p3
  let c3 := dualC3 p0 p1 p2 p3
  have hc0p : 0 < c0 := hc0
  have hc1p : 0 < c1 := hc1
  have hc2p : 0 < c2 := hc2
  have hc3p : 0 < c3 := hc3
  have hcomb := fiveDiag_comb p0 p1 p2 p3 h30 h12 hw hc0 hc1 hc2 hc3
  -- The two identities (kept in the `let` scope for readability).
  have hI2 : pnSmul c1 p2 = V3.add (pnSmul c2 p1) (diagM p0 p1 p2 p3) := hcomb.1
  have hI3 : pnSmul c0 p3 = V3.add (pnSmul c3 p0) (diagM p0 p1 p2 p3) := hcomb.2
  have hp : p0 = V3.add (pnSmul (c0 / c3) p3)
      (pnSmul (1 / c3) (pnSmul (-1) (diagM p0 p1 p2 p3))) := by
    have h' : pnSmul c3 p0 =
        V3.add (pnSmul c0 p3) (pnSmul (-1) (diagM p0 p1 p2 p3)) := by
      apply V3.ext
      · have hx := congrArg V3.x hI3
        dsimp [pnSmul, V3.add] at hx ⊢
        linarith
      · have hy := congrArg V3.y hI3
        dsimp [pnSmul, V3.add] at hy ⊢
        linarith
      · have hz := congrArg V3.z hI3
        dsimp [pnSmul, V3.add] at hz ⊢
        linarith
    exact five_solved p0 p3 (pnSmul (-1) (diagM p0 p1 p2 p3)) c0 c3
      (ne_of_gt hc3p) h'
  have hq : p1 = V3.add (pnSmul (c1 / c2) p2)
      (pnSmul (1 / c2) (pnSmul (-1) (diagM p0 p1 p2 p3))) := by
    have h' : pnSmul c2 p1 =
        V3.add (pnSmul c1 p2) (pnSmul (-1) (diagM p0 p1 p2 p3)) := by
      apply V3.ext
      · have hx := congrArg V3.x hI2
        dsimp [pnSmul, V3.add] at hx ⊢
        linarith
      · have hy := congrArg V3.y hI2
        dsimp [pnSmul, V3.add] at hy ⊢
        linarith
      · have hz := congrArg V3.z hI2
        dsimp [pnSmul, V3.add] at hz ⊢
        linarith
    exact five_solved p1 p2 (pnSmul (-1) (diagM p0 p1 p2 p3)) c1 c2
      (ne_of_gt hc2p) h'
  have hr : p3 = V3.add (pnSmul (c3 / c0) p0)
      (pnSmul (1 / c0) (diagM p0 p1 p2 p3)) := by
    exact five_solved p3 p0 (diagM p0 p1 p2 p3) c3 c0 (ne_of_gt hc0p) hI3
  refine ⟨c0 / c3, 1 / c3, c1 / c2, 1 / c2, c3 / c0, 1 / c0,
    div_pos hc0p hc3p, div_pos zero_lt_one hc3p,
    div_pos hc1p hc2p, div_pos zero_lt_one hc2p,
    div_pos hc3p hc0p, div_pos zero_lt_one hc0p, hp, hq, hr⟩

/-- The strict convexity dot-signs give the four positive ray coefficients.
    Together with `splitConeData_of_dualC` this is the exact passage from the
    hypotheses of `fourDiag_dual_cone` to the abstract split data. -/
lemma dualC_positives_of_convex
    (p0 p1 p2 p3 : V3)
    (h30 : cross p3 p0 ≠ ⟨0, 0, 0⟩) (h12 : cross p1 p2 ≠ ⟨0, 0, 0⟩)
    (hw : cross (diagV10 p3 p0) (diagV21 p1 p2) ≠ ⟨0, 0, 0⟩)
    (hn0v21 : dot p0 (diagV21 p1 p2) < 0)
    (hn1v10 : dot p1 (diagV10 p3 p0) < 0)
    (hn2v10 : dot p2 (diagV10 p3 p0) < 0)
    (hn3v21 : dot p3 (diagV21 p1 p2) < 0) :
    0 < dualC0 p0 p1 p2 p3 ∧ 0 < dualC1 p0 p1 p2 p3 ∧
    0 < dualC2 p0 p1 p2 p3 ∧ 0 < dualC3 p0 p1 p2 p3 := by
  have hnw : 0 < diagNW p0 p1 p2 p3 := by
    dsimp [diagNW]
    exact norm_pos_of_ne_zero _ hw
  have ha : 0 < norm (cross p3 p0) := norm_pos_of_ne_zero _ h30
  have hb : 0 < norm (cross p1 p2) := norm_pos_of_ne_zero _ h12
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [dualC0]
    exact div_pos (neg_pos.mpr hn0v21) (mul_pos hnw ha)
  · dsimp [dualC1]
    exact div_pos (neg_pos.mpr hn1v10) (mul_pos hnw hb)
  · dsimp [dualC2]
    exact div_pos (neg_pos.mpr hn2v10) (mul_pos hnw hb)
  · dsimp [dualC3]
    exact div_pos (neg_pos.mpr hn3v21) (mul_pos hnw ha)

/-! ### 3. Propagating the two cone invariants along a chain -/

lemma inCone2_head_transfer {k : ℕ} (F : FanChain k)
    (hdata : ChainSplitData F) (hlink : F.linked)
    (x : V3) (hx : InCone2 x (ChainLastN F) F.head.a) :
    FanChainTransferAt F x := by
  induction F generalizing x with
  | leaf T =>
      rcases hx with ⟨s, t, hs, ht, hpos, hx⟩
      unfold FanChainTransferAt
      apply dual_transfer_of_comb T.a T.b T.m x T.wa T.wb T.d t 0 s
        ht (le_refl 0) hs
      · cases hpos with
        | inl hsp => exact Or.inr (Or.inr hsp)
        | inr htp => exact Or.inl htp
      · rw [hx]
        apply V3.ext <;> dsimp [V3.add, pnSmul, FanChain.head, ChainLastN] <;> ring
  | cons T F ih =>
      rcases hdata with ⟨hsplit, hdataF⟩
      rcases hsplit with ⟨α, β, γ, δ, ε, ζ,
        hα, hβ, hγ, hδ, hε, hζ, hp, hq, hr⟩
      rcases hx with ⟨s, t, hs, ht, hpos, hx⟩
      dsimp [ChainLastN, FanChain.head] at hx
      have hnegTm : pnSmul (-1) T.m = F.head.a := by
        rw [hlink.1]
        exact pnSmul_neg_involutive _
      constructor
      · -- the current triangle: x = s • lastN + t • T.a, and
        -- lastN = ε • T.a + ζ • T.m.
        apply dual_transfer_of_comb T.a T.b T.m x T.wa T.wb T.d
          (s * ε + t) 0 (s * ζ)
          (add_nonneg (mul_nonneg hs (le_of_lt hε)) ht)
          (le_refl 0)
          (mul_nonneg hs (le_of_lt hζ))
        · cases hpos with
          | inl hsp => exact Or.inl (add_pos_of_pos_of_nonneg (mul_pos hsp hε) ht)
          | inr htp =>
              exact Or.inl (add_pos_of_nonneg_of_pos
                (mul_nonneg hs (le_of_lt hε)) htp)
        · rw [hx, hr]
          apply V3.ext <;> dsimp [V3.add, pnSmul, FanChain.head, ChainLastN] <;> ring
      · -- the tail: rewrite T.a = α • lastN + β • (-T.m).
        apply ih hdataF hlink.2.2
        refine ⟨s + t * α, t * β,
          add_nonneg hs (mul_nonneg ht (le_of_lt hα)),
          mul_nonneg ht (le_of_lt hβ), ?_, ?_⟩
        · cases hpos with
          | inl hsp => exact Or.inl (add_pos_of_pos_of_nonneg hsp
              (mul_nonneg ht (le_of_lt hα)))
          | inr htp => exact Or.inr (mul_pos htp hβ)
        · rw [hx, hp, hnegTm]
          apply V3.ext <;> dsimp [V3.add, pnSmul, FanChain.head, ChainLastN] <;> ring

lemma inCone3_head_transfer {k : ℕ} (F : FanChain k)
    (hdata : ChainSplitData F) (hlink : F.linked)
    (x : V3) (hx : InCone3 x (ChainLastN F) F.head.a F.head.b) :
    FanChainTransferAt F x := by
  induction F generalizing x with
  | leaf T =>
      rcases hx with ⟨s, t, u, hs, ht, hu, hpos, hx⟩
      unfold FanChainTransferAt
      apply dual_transfer_of_comb T.a T.b T.m x T.wa T.wb T.d t u s
        ht hu hs
      · cases hpos with
        | inl hsp => exact Or.inr (Or.inr hsp)
        | inr hrest => cases hrest with
          | inl htp => exact Or.inl htp
          | inr hup => exact Or.inr (Or.inl hup)
      · rw [hx]
        apply V3.ext <;> dsimp [V3.add, pnSmul, FanChain.head, ChainLastN] <;> ring
  | cons T F ih =>
      rcases hdata with ⟨hsplit, hdataF⟩
      rcases hsplit with ⟨α, β, γ, δ, ε, ζ,
        hα, hβ, hγ, hδ, hε, hζ, hp, hq, hr⟩
      rcases hx with ⟨s, t, u, hs, ht, hu, hpos, hx⟩
      dsimp [ChainLastN, FanChain.head] at hx
      have hnegTm : pnSmul (-1) T.m = F.head.a := by
        rw [hlink.1]
        exact pnSmul_neg_involutive _
      constructor
      · -- the current triangle: rewrite lastN into T.a and T.m.
        apply dual_transfer_of_comb T.a T.b T.m x T.wa T.wb T.d
          (s * ε + t) u (s * ζ)
          (add_nonneg (mul_nonneg hs (le_of_lt hε)) ht)
          hu
          (mul_nonneg hs (le_of_lt hζ))
        · cases hpos with
          | inl hsp => exact Or.inl (add_pos_of_pos_of_nonneg (mul_pos hsp hε) ht)
          | inr hrest => cases hrest with
            | inl htp =>
                exact Or.inl (add_pos_of_nonneg_of_pos
                  (mul_nonneg hs (le_of_lt hε)) htp)
            | inr hup => exact Or.inr (Or.inl hup)
        · rw [hx, hr]
          apply V3.ext <;> dsimp [V3.add, pnSmul, FanChain.head, ChainLastN] <;> ring
      · -- the tail: rewrite both T.a and T.b into the next diagonal.
        apply ih hdataF hlink.2.2
        refine ⟨s + t * α, t * β + u * δ, u * γ,
          add_nonneg hs (mul_nonneg ht (le_of_lt hα)),
          add_nonneg (mul_nonneg ht (le_of_lt hβ))
            (mul_nonneg hu (le_of_lt hδ)),
          mul_nonneg hu (le_of_lt hγ), ?_, ?_⟩
        · cases hpos with
          | inl hsp => exact Or.inl (add_pos_of_pos_of_nonneg hsp
              (mul_nonneg ht (le_of_lt hα)))
          | inr hrest => cases hrest with
            | inl htp => exact Or.inr (Or.inl
                (add_pos_of_pos_of_nonneg (mul_pos htp hβ)
                  (mul_nonneg hu (le_of_lt hδ))))
            | inr hup => exact Or.inr (Or.inr (mul_pos hup hγ))
        · rw [hx, hp, hq, hnegTm]
          apply V3.ext <;> dsimp [V3.add, pnSmul, FanChain.head, ChainLastN] <;> ring

/-! ### 4. The composed containments for the two new boundary normals -/

/-- **General-n composed dual-cone containment.**  Given the split data for
    every triangle of an arbitrary chain `F` and the split data for the new
    quadrilateral cut off by `(a,b,m)`, the two new boundary co-normals a, b
    lie in the dual cone of every triangle of `F`.

    This is exactly the pair `htrF_a`/`htrF_b` required by
    `extendFanCertificate` in `Vdb/AngleNFaceGeneral`.  For `F` a leaf the
    statement reduces to the two `fourDiag_dual_cone` containments of the
    quadrilateral `(a,b,F.head.b,ChainLastN F)`. -/
theorem fan_head_transfer_composed {k : ℕ} (F : FanChain k)
    (hdata : ChainSplitData F) (hlink : F.linked)
    (a b m : V3) (hm : m = pnSmul (-1) F.head.a)
    (hnew : SplitConeData a b m (ChainLastN F) F.head.b) :
    FanChainTransferAt F a ∧ FanChainTransferAt F b := by
  have hnegm : pnSmul (-1) m = F.head.a := by
    rw [hm]
    exact pnSmul_neg_involutive _
  constructor
  · apply inCone2_head_transfer F hdata hlink a
    rcases hnew with ⟨α, β, γ, δ, ε, ζ, hα, hβ, hγ, hδ, hε, hζ, hp, hq, hr⟩
    refine ⟨α, β, le_of_lt hα, le_of_lt hβ, Or.inl hα, ?_⟩
    rw [hp, hnegm]
  · apply inCone3_head_transfer F hdata hlink b
    rcases hnew with ⟨α, β, γ, δ, ε, ζ, hα, hβ, hγ, hδ, hε, hζ, hp, hq, hr⟩
    refine ⟨0, δ, γ, le_refl 0, le_of_lt hδ, le_of_lt hγ,
      Or.inr (Or.inl hδ), ?_⟩
    rw [hq, hnegm]
    apply V3.ext <;> dsimp [V3.add, pnSmul] <;> ring

/-! ### 5. The head (leaf) specialization -/

/-- The two-composed-cone lemma for a leaf chain `F`: this is the ordinary
    n = 4 dual-cone containment of `fourDiag_dual_cone`, stated in the form
    consumed by `fan_head_transfer_composed`.  Landed explicitly so the
    induction base is available without importing the full duality theorem. -/
theorem fan_head_transfer_leaf
    (a b m q' r : V3) (wa wb d : ℝ) (hnew : SplitConeData a b m r q') :
    FanTriangleTransfer ⟨pnSmul (-1) m, q', r, wa, wb, d⟩ a ∧
    FanTriangleTransfer ⟨pnSmul (-1) m, q', r, wa, wb, d⟩ b := by
  rcases hnew with ⟨α, β, γ, δ, ε, ζ, hα, hβ, hγ, hδ, hε, hζ, hp, hq, hr⟩
  constructor
  · apply dual_transfer_of_comb (pnSmul (-1) m) q' r a wa wb d β 0 α
      (le_of_lt hβ) (le_refl 0) (le_of_lt hα)
    · exact Or.inl hβ
    · rw [hp]
      apply V3.ext <;> dsimp [V3.add, pnSmul] <;> ring
  · apply dual_transfer_of_comb (pnSmul (-1) m) q' r b wa wb d δ γ 0
      (le_of_lt hδ) (le_of_lt hγ) (le_refl 0)
    · exact Or.inl hδ
    · rw [hq]
      apply V3.ext <;> dsimp [V3.add, pnSmul] <;> ring

/-! ### 6. Forward propagation: old boundary normals into the new triangle -/

/-- The three generators of a triangle lie in its own cone. -/
lemma inCone3_a (a b m : V3) : InCone3 a a b m := by
  refine ⟨1, 0, 0, zero_le_one, le_refl 0, le_refl 0, Or.inl zero_lt_one, ?_⟩
  apply V3.ext <;> dsimp [V3.add, pnSmul] <;> ring

lemma inCone3_b (a b m : V3) : InCone3 b a b m := by
  refine ⟨0, 1, 0, le_refl 0, zero_le_one, le_refl 0,
    Or.inr (Or.inl zero_lt_one), ?_⟩
  apply V3.ext <;> dsimp [V3.add, pnSmul] <;> ring

lemma inCone3_m (a b m : V3) : InCone3 m a b m := by
  refine ⟨0, 0, 1, le_refl 0, le_refl 0, zero_le_one,
    Or.inr (Or.inr zero_lt_one), ?_⟩
  apply V3.ext <;> dsimp [V3.add, pnSmul] <;> ring

/-- A positive scaling keeps a vector in a cone. -/
lemma inCone3_smul_pos {x u v w : V3} (t : ℝ) (ht : 0 < t)
    (hx : InCone3 x u v w) : InCone3 (pnSmul t x) u v w := by
  rcases hx with ⟨s, r, q, hs, hr, hq, hpos, hx⟩
  refine ⟨t * s, t * r, t * q,
    mul_nonneg (le_of_lt ht) hs, mul_nonneg (le_of_lt ht) hr,
    mul_nonneg (le_of_lt ht) hq, ?_, ?_⟩
  · cases hpos with
    | inl hsp => exact Or.inl (mul_pos ht hsp)
    | inr hrest => cases hrest with
      | inl hrp => exact Or.inr (Or.inl (mul_pos ht hrp))
      | inr hqp => exact Or.inr (Or.inr (mul_pos ht hqp))
  · rw [hx]
    apply V3.ext <;> dsimp [V3.add, pnSmul] <;> ring

/-- The sum of two cone members is in the cone; strict positivity survives
    from either summand. -/
lemma inCone3_add {x y u v w : V3} (hx : InCone3 x u v w) (hy : InCone3 y u v w) :
    InCone3 (V3.add x y) u v w := by
  rcases hx with ⟨s1, r1, q1, hs1, hr1, hq1, hpos1, hx⟩
  rcases hy with ⟨s2, r2, q2, hs2, hr2, hq2, hpos2, hy⟩
  refine ⟨s1 + s2, r1 + r2, q1 + q2,
    add_nonneg hs1 hs2, add_nonneg hr1 hr2, add_nonneg hq1 hq2, ?_, ?_⟩
  · cases hpos1 with
    | inl hp => exact Or.inl (add_pos_of_pos_of_nonneg hp hs2)
    | inr hrest1 => cases hrest1 with
      | inl hp => exact Or.inr (Or.inl (add_pos_of_pos_of_nonneg hp hr2))
      | inr hp => exact Or.inr (Or.inr (add_pos_of_pos_of_nonneg hp hq2))
  · rw [hx, hy]
    apply V3.ext <;> dsimp [V3.add, pnSmul] <;> ring

/-- Convert an explicit cone representation into `FanTriangleTransfer`. -/
lemma fanTransfer_of_inCone3 (T : FanTriangle) (x : V3)
    (hx : InCone3 x T.a T.b T.m) : FanTriangleTransfer T x := by
  rcases hx with ⟨s, t, u, hs, ht, hu, hpos, hx⟩
  exact dual_transfer_of_comb T.a T.b T.m x T.wa T.wb T.d
    s t u hs ht hu hpos hx

/-- **Forward propagation.**  If the second boundary normal and the last
    boundary normal of a chain already lie in the cone of a triangle `T` whose
    exit co-normal is the negative of the chain's entry, then *every* boundary
    normal of the chain except its (now internal) entry lies in that cone.

    Together with `splitConeData_of_dualC` applied to the quadrilateral cut
    off by the new triangle, this discharges the `htr_rest` hypotheses of
    `extendFanCertificate` for an arbitrary chain. -/
lemma fan_old_faces_cone3_aux {k : ℕ} (F : FanChain k)
    (hdata : ChainSplitData F) (hlink : F.linked)
    (a b m : V3)
    (hentry : InCone3 (pnSmul (-1) F.head.a) a b m)
    (hheadb : InCone3 F.head.b a b m)
    (hlast : InCone3 (ChainLastN F) a b m) :
    ∀ j : Fin (k + 2), InCone3 (F.boundaryN j.succ) a b m := by
  induction F with
  | leaf T =>
      intro j
      fin_cases j
      · simpa [FanChain.boundaryN, FanChain.head] using hheadb
      · simpa [FanChain.boundaryN, ChainLastN, FanChain.head] using hlast
  | cons U F' ih =>
      rcases hdata with ⟨hsplit, hdataF⟩
      rcases hsplit with ⟨α, β, γ, δ, ε, ζ,
        hα, hβ, hγ, hδ, hε, hζ, hp, hq, hr⟩
      have hlast' : InCone3 (ChainLastN F') a b m := by
        simpa [ChainLastN] using hlast
      -- U.m = (1/β) • (-(U.a)) + (α/β) • ChainLastN F' .
      have hUm_eq : U.m = V3.add (pnSmul (1 / β) (pnSmul (-1) U.a))
          (pnSmul (α / β) (ChainLastN F')) := by
        apply V3.ext
        · have hx := congrArg V3.x hp
          dsimp [pnSmul, V3.add] at hx ⊢
          field_simp [ne_of_gt hβ]
          nlinarith
        · have hy := congrArg V3.y hp
          dsimp [pnSmul, V3.add] at hy ⊢
          field_simp [ne_of_gt hβ]
          nlinarith
        · have hz := congrArg V3.z hp
          dsimp [pnSmul, V3.add] at hz ⊢
          field_simp [ne_of_gt hβ]
          nlinarith
      have hUm : InCone3 U.m a b m := by
        rw [hUm_eq]
        exact inCone3_add
          (inCone3_smul_pos (1 / β) (div_pos zero_lt_one hβ) (by
            simpa [FanChain.head] using hentry))
          (inCone3_smul_pos (α / β) (div_pos hα hβ) hlast')
      -- F'.head.b = (1/γ) • U.b + (δ/γ) • U.m .
      have hheadb'_eq : F'.head.b = V3.add (pnSmul (1 / γ) U.b)
          (pnSmul (δ / γ) U.m) := by
        apply V3.ext
        · have hx := congrArg V3.x hq
          dsimp [pnSmul, V3.add] at hx ⊢
          field_simp [ne_of_gt hγ]
          nlinarith
        · have hy := congrArg V3.y hq
          dsimp [pnSmul, V3.add] at hy ⊢
          field_simp [ne_of_gt hγ]
          nlinarith
        · have hz := congrArg V3.z hq
          dsimp [pnSmul, V3.add] at hz ⊢
          field_simp [ne_of_gt hγ]
          nlinarith
      have hheadb' : InCone3 F'.head.b a b m := by
        rw [hheadb'_eq]
        exact inCone3_add
          (inCone3_smul_pos (1 / γ) (div_pos zero_lt_one hγ) (by
            simpa [FanChain.head] using hheadb))
          (inCone3_smul_pos (δ / γ) (div_pos hδ hγ) hUm)
      have hentry' : InCone3 (pnSmul (-1) F'.head.a) a b m := by
        rw [← hlink.1]
        exact hUm
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simpa [FanChain.boundaryN, FanChain.head] using hheadb
      · rw [FanChain.boundaryN_succ_succ U F' i]
        exact ih hdataF hlink.2.2 hentry' hheadb' hlast' i

/-- The forward propagation in `FanTriangleTransfer` form: the composed
    containments of all old boundary faces in the new triangle. -/
theorem fan_old_faces_transfer {k : ℕ} (F : FanChain k)
    (hdata : ChainSplitData F) (hlink : F.linked)
    (a b m : V3) (wa wb d : ℝ) (hm : m = pnSmul (-1) F.head.a)
    (hnew : SplitConeData a b m (ChainLastN F) F.head.b) :
    ∀ i : Fin (k + 2), FanTriangleTransfer ⟨a, b, m, wa, wb, d⟩
      (F.boundaryN i.succ) := by
  rcases hnew with ⟨α, β, γ, δ, ε, ζ, hα, hβ, hγ, hδ, hε, hζ, hp, hq, hr⟩
  have hheadb : InCone3 F.head.b a b m := by
    have hq' : F.head.b = V3.add (pnSmul (1 / γ) b) (pnSmul (δ / γ) m) := by
      apply V3.ext
      · have hx := congrArg V3.x hq
        dsimp [pnSmul, V3.add] at hx ⊢
        field_simp [ne_of_gt hγ]
        nlinarith
      · have hy := congrArg V3.y hq
        dsimp [pnSmul, V3.add] at hy ⊢
        field_simp [ne_of_gt hγ]
        nlinarith
      · have hz := congrArg V3.z hq
        dsimp [pnSmul, V3.add] at hz ⊢
        field_simp [ne_of_gt hγ]
        nlinarith
    rw [hq']
    exact inCone3_add
      (inCone3_smul_pos (1 / γ) (div_pos zero_lt_one hγ) (inCone3_b a b m))
      (inCone3_smul_pos (δ / γ) (div_pos hδ hγ) (inCone3_m a b m))
  have hlast : InCone3 (ChainLastN F) a b m := by
    rw [hr]
    exact inCone3_add
      (inCone3_smul_pos ε hε (inCone3_a a b m))
      (inCone3_smul_pos ζ hζ (inCone3_m a b m))
  have hentry : InCone3 (pnSmul (-1) F.head.a) a b m := by
    rw [← hm]
    exact inCone3_m a b m
  intro i
  apply fanTransfer_of_inCone3
  exact fan_old_faces_cone3_aux F hdata hlink a b m hentry hheadb hlast i

end V3
end Vdb
