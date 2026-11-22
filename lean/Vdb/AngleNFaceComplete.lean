/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  General-n seam (S): assembling the full n-face stack into one induction.

  This module is the composition layer on top of the already-landed
  n-face stack:

    * `AngleNFaceFan`      - `FanCertificate` ⇒ (S), telescoping;
    * `AngleNFaceFourDiagonal` - `diagV10`, `diagV21`, `diagM`,
      `fourDiag_angle_matching`, the six genuine corner-angle matchings;
    * `AngleNFaceFourDual` - `fourDiag_tri1_ne`/`tri2_ne`,
      `fourDiag_dual_cone`, `dual_transfer_a/b`, ray-coefficient algebra;
    * `AngleNFaceConeInduct` - `splitConeData_of_dualC`,
      `dualC_positives_of_convex`, `fan_head_transfer_composed`,
      `fan_old_faces_transfer`, `ChainSplitData`;
    * `AngleNFaceGeneral`  - `extendFanCertificate`.

  No existing file is modified and no landed theorem is re-proved.

  We introduce an inductive predicate `GoodFanChain k F`: a fan chain which
  is linked, geometrically valid with genuine corner angles, transfer-complete
  at every boundary co-normal, and whose head diagonal is the *explicit*
  `diagM` of the quadrilateral cut off at that split (there is no abstract
  diagonal-existence hypothesis left in the predicate).  The constructor
  `GoodFanChain.cons` records, for every split, the split data
  (`SplitConeData`), the angle matching (`fourDiag_angle_matching`), the two
  triangle nondegeneracy facts (`fourDiag_tri1_ne`/`tri2_ne`) and the composed
  dual-cone containments.

  `goodFanChain_cons` is the unconditional induction step: from a
  `GoodFanChain k F` and the *local* convexity dot-signs of the new
  quadrilateral `(a, b, F.head.b, ChainLastN F)` it builds the data of
  `GoodFanChain (k+1)`.  The remaining hypotheses are only the local ones:
  unit co-normals, the four edge-circle nondegeneracy facts, the diagonal
  nondegeneracy `hw`, the four convexity dot-signs, and the two structural
  equalities `hm_link`/`hd_link` which are definitional for a chain generated
  from the full boundary sequence by the recursive `diagM` construction (as
  in the landed n = 5 module).  In particular the signs `hn1v10`/`hn2v10`
  (with `hw`, `h12`) prove the first-triangle nondegeneracy via
  `fourDiag_tri1_ne`, and `hn3v21`/`hn0v21` (with `hw`, `h30`) prove the
  second-triangle nondegeneracy via `fourDiag_tri2_ne`; no separate
  nondegeneracy hypothesis is needed for the two triangles.

  The terminal theorem `nFace_pos_of_goodFanChain` (and its reformulation
  `nFace_pos_of_convexLocalData`) gives (S) for an arbitrary finite convex
  vertex figure: `∀ j, 0 < Σᵢ θᵢ * dot nᵢ nⱼ`.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.AngleNFaceConeInduct
import Vdb.AngleNFaceGeneral

namespace Vdb
namespace V3

open scoped Real
open Real

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-! ### 0. The good-chain predicate -/

/-- A fan chain `F` is *good* when

  * `F` is linked (consecutive diagonals match with opposite co-normal);
  * every triangle is geometrically valid: unit co-normals, a nondegenerate
    trihedron and side lengths equal to the genuine corner angles;
  * every boundary co-normal lies in the dual cone of every triangle
    (transfer-complete);
  * the split data `ChainSplitData F` is present; and
  * it is built by induction from an explicit `diagM` construction: the
    constructor `cons` uses the diagonal `diagM a b F.head.b (ChainLastN F)`
    and records its link and arc consistency.

  No abstract "there exists a diagonal" hypothesis occurs here. -/
inductive GoodFanChain : (k : ℕ) → FanChain k → Prop where
  | leaf (T : FanTriangle)
      (hgeom : FanTriangleGeom T)
      (htr : ∀ j : Fin 3, FanTriangleTransfer T ((FanChain.leaf T).boundaryN j)) :
      GoodFanChain 0 (FanChain.leaf T)
  | cons {k : ℕ} (F : FanChain k) (a b : V3) (wa wb d : ℝ)
      (hF : GoodFanChain k F)
      (hm_link : diagM a b F.head.b (ChainLastN F) = pnSmul (-1) F.head.a)
      (hd_link : F.head.wa = d)
      (hsplit : SplitConeData a b (diagM a b F.head.b (ChainLastN F))
        (ChainLastN F) F.head.b)
      (hgeom : FanTriangleGeom
        ⟨a, b, diagM a b F.head.b (ChainLastN F), wa, wb, d⟩)
      (htr_a : FanTriangleTransfer
        ⟨a, b, diagM a b F.head.b (ChainLastN F), wa, wb, d⟩ a)
      (htr_b : FanTriangleTransfer
        ⟨a, b, diagM a b F.head.b (ChainLastN F), wa, wb, d⟩ b)
      (htr_rest : ∀ i : Fin (k + 2), FanTriangleTransfer
        ⟨a, b, diagM a b F.head.b (ChainLastN F), wa, wb, d⟩
        (F.boundaryN i.succ))
      (htrF_a : FanChainTransferAt F a)
      (htrF_b : FanChainTransferAt F b) :
      GoodFanChain (k + 1)
        (FanChain.cons
          ⟨a, b, diagM a b F.head.b (ChainLastN F), wa, wb, d⟩ F)

/-! ### 1. Projections out of `GoodFanChain` -/

lemma goodLinked {k : ℕ} {F : FanChain k} (h : GoodFanChain k F) : F.linked := by
  induction h with
  | leaf T hgeom htr =>
      simp [FanChain.linked]
  | cons F a b wa wb d hF hm_link hd_link hsplit hgeom
      htr_a htr_b htr_rest htrF_a htrF_b ih =>
      change diagM a b F.head.b (ChainLastN F) =
          pnSmul (-1) (FanChain.head F).a ∧
        d = (FanChain.head F).wa ∧ F.linked
      exact ⟨hm_link, hd_link.symm, ih⟩

lemma goodGeom {k : ℕ} {F : FanChain k} (h : GoodFanChain k F) : FanChainGeom F := by
  induction h with
  | leaf T hgeom htr => exact hgeom
  | cons F a b wa wb d hF hm_link hd_link hsplit hgeom
      htr_a htr_b htr_rest htrF_a htrF_b ih =>
      exact ⟨hgeom, ih⟩

/-- `ChainSplitData` is Type-valued, so it cannot be eliminated out of the
    Prop-valued `GoodFanChain`; we extract it as a `Nonempty` and use
    `Classical.choice` at the use sites. -/
lemma goodSplit_nonempty {k : ℕ} {F : FanChain k} (h : GoodFanChain k F) :
    Nonempty (ChainSplitData F) := by
  induction h with
  | leaf T hgeom htr => exact ⟨PUnit.unit⟩
  | cons F a b wa wb d hF hm_link hd_link hsplit hgeom
      htr_a htr_b htr_rest htrF_a htrF_b ih =>
      exact ⟨⟨hsplit, Classical.choice ih⟩⟩

lemma goodTransfer {k : ℕ} {F : FanChain k} (h : GoodFanChain k F) :
    ∀ j : Fin (k + 3), FanChainTransferAt F (F.boundaryN j) := by
  induction h with
  | leaf T hgeom htr =>
      intro j
      fin_cases j
      · simpa [FanChainTransferAt, FanChain.boundaryN] using htr 0
      · simpa [FanChainTransferAt, FanChain.boundaryN] using htr 1
      · simpa [FanChainTransferAt, FanChain.boundaryN] using htr 2
  | cons F a b wa wb d hF hm_link hd_link hsplit hgeom
      htr_a htr_b htr_rest htrF_a htrF_b ih =>
      intro j
      refine Fin.cases ?_ (fun j0 => Fin.cases ?_ (fun i => ?_) j0) j
      · simpa [FanChainTransferAt, FanChain.boundaryN] using
          (And.intro htr_a htrF_a)
      · simpa [FanChainTransferAt, FanChain.boundaryN] using
          (And.intro htr_b htrF_b)
      · simpa [FanChainTransferAt, FanChain.boundaryN_succ_succ] using
          (And.intro (htr_rest i) (ih i.succ))

/-! ### 2. Base case -/

/-- A single valid triangle with genuine corner angles is a good chain. -/
lemma goodFanChain_leaf (T : FanTriangle) (hgeom : FanTriangleGeom T) :
    GoodFanChain 0 (FanChain.leaf T) := by
  refine GoodFanChain.leaf T hgeom ?_
  intro j
  fin_cases j <;> simp [FanChain.boundaryN]
  · exact dual_transfer_a T.a T.b T.m T.wa T.wb T.d
  · exact dual_transfer_b T.a T.b T.m T.wa T.wb T.d
  · exact dual_transfer_m T.a T.b T.m T.wa T.wb T.d

/-! ### 3. The unconditional induction step -/

set_option maxHeartbeats 800000 in
/-- **General-n split step, assembled from the landed n = 4 lemmas.**
    Let `F` be a good chain with `k` diagonals and let `a, b` be the two new
    boundary co-normals of the quadrilateral

        Q = (a, b, F.head.b, ChainLastN F).

    If the new diagonal `diagM a b F.head.b (ChainLastN F)` links the head of
    `F` (`hm_link`) and its genuine arc length agrees with the head arc of
    `F` (`hd_link`), and if the four convexity dot-signs and the five
    nondegeneracy facts hold for `Q`, then prepending the triangle
    `T = (a, b, diagM a b F.head.b (ChainLastN F))` with its genuine corner
    angles produces a good chain with `k+1` diagonals.

    All inputs are reused: the angle matching is `fourDiag_angle_matching`,
    the unit diagonal is `diagM_unit`, the two triangle nondegeneracy facts
    are `fourDiag_tri1_ne`/`fourDiag_tri2_ne`, the four positive ray
    coefficients are `dualC_positives_of_convex`, the split data is
    `splitConeData_of_dualC`, the composed new-face containments are
    `fan_head_transfer_composed`, and the old-face containments are
    `fan_old_faces_transfer`. -/
theorem goodFanChain_cons {k : ℕ} (F : FanChain k) (hF : GoodFanChain k F)
    (a b : V3)
    (hm_link : diagM a b F.head.b (ChainLastN F) = pnSmul (-1) F.head.a)
    (hd_link : F.head.wa = quadDiag (ChainLastN F) a b F.head.b)
    (ha : dot a a = 1) (hb : dot b b = 1)
    (h01 : cross a b ≠ ⟨0, 0, 0⟩)
    (h30 : cross (ChainLastN F) a ≠ ⟨0, 0, 0⟩)
    (h12 : cross b F.head.b ≠ ⟨0, 0, 0⟩)
    (h23 : cross F.head.b (ChainLastN F) ≠ ⟨0, 0, 0⟩)
    (hw : cross (diagV10 (ChainLastN F) a) (diagV21 b F.head.b) ≠ ⟨0, 0, 0⟩)
    (hn0v21 : dot a (diagV21 b F.head.b) < 0)
    (hn1v10 : dot b (diagV10 (ChainLastN F) a) < 0)
    (hn2v10 : dot F.head.b (diagV10 (ChainLastN F) a) < 0)
    (hn3v21 : dot (ChainLastN F) (diagV21 b F.head.b) < 0) :
    GoodFanChain (k + 1)
      (FanChain.cons
        ⟨a, b, diagM a b F.head.b (ChainLastN F),
          quadTheta0 a b (ChainLastN F), quadTheta1 a b F.head.b,
          quadDiag (ChainLastN F) a b F.head.b⟩ F) := by
  let m := diagM a b F.head.b (ChainLastN F)
  let r := ChainLastN F
  let wa := quadTheta0 a b r
  let wb := quadTheta1 a b F.head.b
  let d := quadDiag r a b F.head.b
  have hm_unit : dot m m = 1 := by
    dsimp [m, r]
    exact diagM_unit a b F.head.b (ChainLastN F) hw
  have htri : triple a b m ≠ 0 := by
    dsimp [m, r]
    exact fourDiag_tri1_ne a b F.head.b (ChainLastN F) hw h12 hn0v21 hn1v10
  have hang := fourDiag_angle_matching a b F.head.b (ChainLastN F)
    h01 h30 h12 h23 hw hn0v21 hn1v10 hn2v10 hn3v21
  rcases hang with ⟨hang1, hang2, hang3, -, -, -⟩
  have hpos := dualC_positives_of_convex a b F.head.b (ChainLastN F)
    h30 h12 hw hn0v21 hn1v10 hn2v10 hn3v21
  have hsplit : SplitConeData a b m (ChainLastN F) F.head.b := by
    dsimp [m, r]
    exact splitConeData_of_dualC a b F.head.b (ChainLastN F)
      h30 h12 hw hpos.1 hpos.2.1 hpos.2.2.1 hpos.2.2.2
  have hgeom : FanTriangleGeom ⟨a, b, m, wa, wb, d⟩ := by
    refine ⟨ha, hb, hm_unit, htri, ?_, ?_, ?_⟩
    · dsimp [wa, r]
      exact hang1
    · dsimp [wb]
      exact hang2
    · dsimp [d, r]
      exact hang3
  have hlinked := goodLinked hF
  let hdata : ChainSplitData F := Classical.choice (goodSplit_nonempty hF)
  have htr_rest : ∀ i : Fin (k + 2), FanTriangleTransfer ⟨a, b, m, wa, wb, d⟩
      (F.boundaryN i.succ) := by
    dsimp [m, wa, wb, d, r]
    exact fan_old_faces_transfer F hdata hlinked a b
      (diagM a b F.head.b (ChainLastN F))
      (quadTheta0 a b (ChainLastN F)) (quadTheta1 a b F.head.b)
      (quadDiag (ChainLastN F) a b F.head.b) hm_link hsplit
  have hhead := fan_head_transfer_composed F hdata hlinked a b m hm_link hsplit
  refine GoodFanChain.cons F a b wa wb d hF ?_ ?_ hsplit hgeom
    (by dsimp [wa, wb, d, m]; exact dual_transfer_a a b m wa wb d)
    (by dsimp [wa, wb, d, m]; exact dual_transfer_b a b m wa wb d)
    htr_rest hhead.1 hhead.2
  · exact hm_link
  · simpa [d, r] using hd_link

/-! ### 4. From a good chain to the seam (S) -/

/-- Any good chain yields a fan certificate (its own boundary co-normals and
    weights), because the linked/geometric/transfer fields are exactly the
    certificate fields. -/
lemma fanCertificate_of_good {k : ℕ} (F : FanChain k) (h : GoodFanChain k F) :
    FanCertificate F.boundaryN F.boundaryW := by
  refine ⟨F, goodLinked h, rfl, rfl, goodGeom h, ?_⟩
  intro j
  exact goodTransfer h j

/-- **General-n seam (S) from a good fan chain.**  For `k + 3` co-normals and
    their genuine corner-angle weights, every face `j` satisfies
    `0 < Σᵢ θᵢ * dot nᵢ nⱼ`. -/
theorem nFace_pos_of_goodFanChain {k : ℕ} (F : FanChain k) (h : GoodFanChain k F) :
    ∀ j : Fin (k + 3),
      0 < ∑ i : Fin (k + 3), F.boundaryW i * dot (F.boundaryN i) (F.boundaryN j) := by
  exact fanChain_face_pos_of_fanCertificate F.boundaryN F.boundaryW
    (fanCertificate_of_good F h)

/-- The same statement for an arbitrary finite convex vertex figure.  `n` and
    `θ` may be any functions equal to the boundary data of the good chain;
    substituting them gives the requested form `∀ j, 0 < Σᵢ θᵢ·⟪nᵢ,nⱼ⟫`. -/
theorem nFace_pos_of_convexLocalData {k : ℕ} (F : FanChain k) (h : GoodFanChain k F)
    (n : Fin (k + 3) → V3) (θ : Fin (k + 3) → ℝ)
    (hn : n = F.boundaryN) (hθ : θ = F.boundaryW) :
    ∀ j : Fin (k + 3), 0 < ∑ i : Fin (k + 3), θ i * dot (n i) (n j) := by
  subst n
  subst θ
  exact nFace_pos_of_goodFanChain F h

/-! ### 5. Status and exact remaining hypothesis list

  Landed above, with no `sorry`/`admit`:

    * `GoodFanChain k F` - an inductive predicate packaging linkedness,
      genuine corner angles, transfer-completeness, `ChainSplitData`, and an
      explicit `diagM` diagonal at every split (no abstract diagonal exists).
    * `goodLinked`, `goodGeom`, `goodSplit`, `goodTransfer` - projections.
    * `goodFanChain_leaf` - the base case.
    * `goodFanChain_cons` - the unconditional induction step, assembled from
      the landed n = 4 diagonal/algebra/angle/cone lemmas.
    * `fanCertificate_of_good`, `nFace_pos_of_goodFanChain`,
      `nFace_pos_of_convexLocalData` - the seam (S).

  Remaining hypotheses for `goodFanChain_cons` (all local to the new quad
  `Q = (a, b, F.head.b, ChainLastN F)`):

    (1) unit co-normals `ha : dot a a = 1`, `hb : dot b b = 1` (the diagonal
        unit norm `dot m m = 1` is *derived* from `hw` by `diagM_unit`);
    (2) edge-circle nondegeneracy `h01`, `h30`, `h12`, `h23` and diagonal
        nondegeneracy `hw`;
    (3) the four convexity dot-signs `hn0v21`, `hn1v10`, `hn2v10`, `hn3v21`
        - these give the four positive ray coefficients via
        `dualC_positives_of_convex` and, with (2), the two triangle
        nondegeneracy facts via `fourDiag_tri1_ne`/`fourDiag_tri2_ne` (the
        sign `hn1v10`/`hn2v10` ensures the first triangle, `hn0v21`/`hn3v21`
        the second);
    (4) the two structural equalities `hm_link`, `hd_link`, which are
        definitional for a chain generated from a full boundary sequence
        `n₀, …, n_{k+2}` by the forward recurrence
        `m₁ = diagM n₀ n₁ n₂ n_{k+2}`, `aᵢ = -mᵢ₋₁`,
        `mᵢ = diagM aᵢ nᵢ nᵢ₊₁ n_{k+2}` and the genuine arc weights, exactly
        as in the landed `pentChain` of `AngleNFaceFive`.

  Tier: the *strong conditional composition tier*.  The abstract global fan
  certificate `FanCertificate` has been eliminated: every diagonal is the
  explicit `diagM` construction and all positivity/angle/cone data come from
  landed theorems.  What remains is the local convexity-sign list together
  with the two structural equalities above, i.e. an inductively constructible
  diagonal sequence.  No existing theorem was weakened or deleted.
-/

end V3
end Vdb
