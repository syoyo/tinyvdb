/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  General-n fan induction: the unconditional diagonal-split step.

  `Vdb/AngleNFaceFan.lean` proves that a `FanCertificate` for a convex
  spherical `(k+3)`-gon gives the seam (S):

      ∀ j, 0 < Σ i, θᵢ * dot nᵢ nⱼ .

  `Vdb/AngleNFaceFourCert.lean` / `AngleNFaceFourDiagonal.lean` /
  `AngleNFaceFourDual.lean` discharge the certificate for k = 1 (four faces)
  from an explicit diagonal, and `Vdb/AngleNFaceFive.lean` does the same for
  k = 2 (five faces) by splitting off two triangles and composing the
  dual-cone containments of the two quadrilaterals.

  This module lands the general-n *induction step* in a form independent of
  the concrete diagonal algebra: it prepends one geometric triangle to an
  arbitrary chain that already carries the certificate data, and transports
  the certificate (and hence (S)) to the enlarged `(k+4)`-face polygon.  The
  old first boundary co-normal becomes the internal diagonal; `linked`
  transports the old diagonal co-normal and length, and `FanChainGeom` /
  `FanChainTransferAt` are the corresponding conjunctions.

  The per-split geometric input is exactly the n = 4 input already proved for
  the first split: unit co-normals, nondegeneracy, the three corner-angle
  matchings, and dual-cone containment of the two new faces in the new
  triangle.  The only additional data are the two containments of the new
  faces in the *old* chain's dual cones (`htrF_a`, `htrF_b` below); these are
  precisely the composed cone containments worked out by hand for the
  pentagon in `AngleNFaceFive.lean`.  Repeated application of
  `extendFanCertificate` therefore reduces the general-n seam (S) to one such
  step per triangle, with no further algebraic work.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.AngleNFaceFan

namespace Vdb
namespace V3

open scoped Real
open Real

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

/-! ### 0. Extending the boundary by one prepended triangle -/

/-- The `k+4` boundary co-normals obtained by prepending a triangle whose first
    two co-normals are `a, b` to a chain with `k+3` boundary co-normals.  The
    former first co-normal of `F` is the internal diagonal and drops off the
    boundary.  Defined through a dummy chain so that it is definitionally the
    boundary map of any `FanChain.cons` with entry co-normals `a, b`. -/
def prependFaceN (a b : V3) {k : ℕ} (F : FanChain k) : Fin (k + 4) → V3 :=
  (FanChain.cons ⟨a, b, (⟨0, 0, 0⟩ : V3), 0, 0, 0⟩ F).boundaryN

/-- The `k+4` boundary arc lengths after the same prepending step. -/
def prependFaceW (wa wb : ℝ) {k : ℕ} (F : FanChain k) : Fin (k + 4) → ℝ :=
  (FanChain.cons ⟨(⟨0, 0, 0⟩ : V3), (⟨0, 0, 0⟩ : V3),
    (⟨0, 0, 0⟩ : V3), wa, wb, 0⟩ F).boundaryW

lemma prependFaceN_zero (a b : V3) {k : ℕ} (F : FanChain k) :
    prependFaceN a b F 0 = a := by
  rfl

lemma prependFaceN_one (a b : V3) {k : ℕ} (F : FanChain k) :
    prependFaceN a b F 1 = b := by
  rfl

lemma prependFaceW_zero (wa wb : ℝ) {k : ℕ} (F : FanChain k) :
    prependFaceW wa wb F 0 = wa := by
  rfl

lemma prependFaceW_one (wa wb : ℝ) {k : ℕ} (F : FanChain k) :
    prependFaceW wa wb F 1 = wb := by
  rfl

lemma prependFaceN_succ_succ (a b : V3) {k : ℕ} (F : FanChain k)
    (i : Fin (k + 2)) :
    prependFaceN a b F i.succ.succ = F.boundaryN i.succ := by
  exact FanChain.boundaryN_succ_succ ⟨a, b, (⟨0, 0, 0⟩ : V3), 0, 0, 0⟩ F i

lemma prependFaceW_succ_succ (wa wb : ℝ) {k : ℕ} (F : FanChain k)
    (i : Fin (k + 2)) :
    prependFaceW wa wb F i.succ.succ = F.boundaryW i.succ := by
  exact FanChain.boundaryW_succ_succ
    ⟨(⟨0, 0, 0⟩ : V3), (⟨0, 0, 0⟩ : V3), (⟨0, 0, 0⟩ : V3), wa, wb, 0⟩ F i

/-! ### 1. The induction step -/

/-- **Induction step for the fan certificate.**  If `F` carries the
    certificate data for its `k+3` boundary faces and the remaining arguments
    are the data of one diagonal split, then `FanChain.cons` with the new
    triangle carries the certificate for the `k+4` polygon
    `prependFaceN a b F` with weights `prependFaceW wa wb F`.

    This is a pure transport theorem: `linked` is the explicit diagonal
    matching, the boundary maps are the prepended maps, `FanChainGeom` and
    `FanChainTransferAt` are the corresponding conjunctions.  No diagonal
    algebra is repeated here. -/
theorem extendFanCertificate {k : ℕ} (F : FanChain k) (hlink : F.linked)
    (hgeomF : FanChainGeom F)
    (htransF : ∀ j : Fin (k + 3), FanChainTransferAt F (F.boundaryN j))
    (a b m : V3) (wa wb d : ℝ)
    (hm_link : m = pnSmul (-1) F.head.a)
    (hd_link : d = F.head.wa)
    (ha : dot a a = 1) (hb : dot b b = 1) (hm_unit : dot m m = 1)
    (htri : triple a b m ≠ 0)
    (hang1 : cornerAngle (isoEdge12 a b) (isoEdge13 a m) = wa)
    (hang2 : cornerAngle (isoEdge12 a b) (isoEdge23 b m) = wb)
    (hang3 : cornerAngle (isoEdge13 a m) (isoEdge23 b m) = d)
    (htr_a : FanTriangleTransfer ⟨a, b, m, wa, wb, d⟩ a)
    (htr_b : FanTriangleTransfer ⟨a, b, m, wa, wb, d⟩ b)
    (htr_rest : ∀ i : Fin (k + 2),
      FanTriangleTransfer ⟨a, b, m, wa, wb, d⟩ (F.boundaryN i.succ))
    (htrF_a : FanChainTransferAt F a)
    (htrF_b : FanChainTransferAt F b) :
    FanCertificate (prependFaceN a b F) (prependFaceW wa wb F) := by
  let T : FanTriangle := ⟨a, b, m, wa, wb, d⟩
  refine ⟨FanChain.cons T F, ?_, ?_, ?_, ?_, ?_⟩
  · change T.m = pnSmul (-1) F.head.a ∧ T.d = F.head.wa ∧ F.linked
    exact ⟨hm_link, hd_link, hlink⟩
  · rfl
  · rfl
  · change FanTriangleGeom T ∧ FanChainGeom F
    exact ⟨⟨ha, hb, hm_unit, htri, hang1, hang2, hang3⟩, hgeomF⟩
  · intro j
    refine Fin.cases ?_ (fun j0 => Fin.cases ?_ (fun i => ?_) j0) j
    · change FanTriangleTransfer T (prependFaceN a b F 0) ∧
        FanChainTransferAt F (prependFaceN a b F 0)
      change FanTriangleTransfer ⟨a, b, m, wa, wb, d⟩ a ∧ FanChainTransferAt F a
      exact ⟨htr_a, htrF_a⟩
    · change FanTriangleTransfer T (prependFaceN a b F 1) ∧
        FanChainTransferAt F (prependFaceN a b F 1)
      change FanTriangleTransfer ⟨a, b, m, wa, wb, d⟩ b ∧ FanChainTransferAt F b
      exact ⟨htr_b, htrF_b⟩
    · change FanTriangleTransfer T (prependFaceN a b F i.succ.succ) ∧
        FanChainTransferAt F (prependFaceN a b F i.succ.succ)
      rw [prependFaceN_succ_succ a b F i]
      exact ⟨htr_rest i, htransF i.succ⟩

/-- **General-n seam (S) by one diagonal-split induction step.**  Under the
    certificate data for a `(k+3)`-face chain and the per-split geometric data
    listed below, every face of the resulting `(k+4)`-face polygon satisfies

        ∀ j : Fin (k+4), 0 < Σ i, θᵢ * dot nᵢ nⱼ .

    Iterating this theorem (starting from the landed n = 4 and n = 5 cases)
    closes the seam (S) for any finite face count, with one split per triangle.
    The hypotheses `htrF_a`, `htrF_b` are the composed dual-cone containments
    proved explicitly for the pentagon in `AngleNFaceFive.lean`. -/
theorem fanChain_face_pos_of_extended {k : ℕ} (F : FanChain k) (hlink : F.linked)
    (hgeomF : FanChainGeom F)
    (htransF : ∀ j : Fin (k + 3), FanChainTransferAt F (F.boundaryN j))
    (a b m : V3) (wa wb d : ℝ)
    (hm_link : m = pnSmul (-1) F.head.a)
    (hd_link : d = F.head.wa)
    (ha : dot a a = 1) (hb : dot b b = 1) (hm_unit : dot m m = 1)
    (htri : triple a b m ≠ 0)
    (hang1 : cornerAngle (isoEdge12 a b) (isoEdge13 a m) = wa)
    (hang2 : cornerAngle (isoEdge12 a b) (isoEdge23 b m) = wb)
    (hang3 : cornerAngle (isoEdge13 a m) (isoEdge23 b m) = d)
    (htr_a : FanTriangleTransfer ⟨a, b, m, wa, wb, d⟩ a)
    (htr_b : FanTriangleTransfer ⟨a, b, m, wa, wb, d⟩ b)
    (htr_rest : ∀ i : Fin (k + 2),
      FanTriangleTransfer ⟨a, b, m, wa, wb, d⟩ (F.boundaryN i.succ))
    (htrF_a : FanChainTransferAt F a)
    (htrF_b : FanChainTransferAt F b) :
    ∀ j : Fin (k + 4),
      0 < ∑ i : Fin (k + 4),
        prependFaceW wa wb F i *
          dot (prependFaceN a b F i) (prependFaceN a b F j) := by
  exact fanChain_face_pos_of_fanCertificate
    (prependFaceN a b F) (prependFaceW wa wb F)
    (extendFanCertificate F hlink hgeomF htransF a b m wa wb d
      hm_link hd_link ha hb hm_unit htri hang1 hang2 hang3
      htr_a htr_b htr_rest htrF_a htrF_b)

end V3
end Vdb
