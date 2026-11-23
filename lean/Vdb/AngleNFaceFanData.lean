/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  §4.0 group: certificate-carrying fan data. The earlier n=6 attempt failed
  because equality of boundary maps does not transport FanChainGeom / transfer
  data. This module packages the chain with its proof data as a Prop, proves
  the FanCertificate it induces, and re-packages the landed extension theorem
  as a reusable step. The geometric construction of the sixth diagonal is still
  the open wall; no weakened claim is made.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.AngleNFaceGeneral

namespace Vdb
namespace V3

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-- A fan chain together with the proofs a FanCertificate needs. -/
def FanData (k : ℕ) : Prop :=
  ∃ chain : FanChain k,
    chain.linked ∧ FanChainGeom chain ∧
      ∀ j : Fin (k + 3), FanChainTransferAt chain (chain.boundaryN j)

theorem FanData.certificate {k : ℕ} (D : FanData k) :
    ∃ chain : FanChain k,
      chain.linked ∧ chain.boundaryN = chain.boundaryN ∧
        chain.boundaryW = chain.boundaryW ∧ FanChainGeom chain ∧
          ∀ j : Fin (k + 3), FanChainTransferAt chain (chain.boundaryN j) := by
  rcases D with ⟨chain, hlink, hgeom, htrans⟩
  exact ⟨chain, hlink, rfl, rfl, hgeom, htrans⟩

/-- The seam (S) for any extended fan with geometric split data. This is the
    reusable n -> n+1 step; the missing ingredient remains the actual diagonal
    data for the hexagon. -/
theorem face_pos_of_extend {k : ℕ} (D : FanData k)
    (a b m : V3) (wa wb d : ℝ)
    (hm_link : m = pnSmul (-1) (Classical.choose D).head.a)
    (hd_link : d = (Classical.choose D).head.wa)
    (ha : dot a a = 1) (hb : dot b b = 1) (hm_unit : dot m m = 1)
    (htri : triple a b m ≠ 0)
    (hang1 : cornerAngle (isoEdge12 a b) (isoEdge13 a m) = wa)
    (hang2 : cornerAngle (isoEdge12 a b) (isoEdge23 b m) = wb)
    (hang3 : cornerAngle (isoEdge13 a m) (isoEdge23 b m) = d)
    (htr_a : FanTriangleTransfer ⟨a, b, m, wa, wb, d⟩ a)
    (htr_b : FanTriangleTransfer ⟨a, b, m, wa, wb, d⟩ b)
    (htr_rest : ∀ i : Fin (k + 2),
      FanTriangleTransfer ⟨a, b, m, wa, wb, d⟩ ((Classical.choose D).boundaryN i.succ))
    (htrD_a : FanChainTransferAt (Classical.choose D) a)
    (htrD_b : FanChainTransferAt (Classical.choose D) b) :
    ∀ j : Fin (k + 4),
      0 < ∑ i : Fin (k + 4),
        (prependFaceW wa wb (Classical.choose D)) i *
          dot ((prependFaceN a b (Classical.choose D)) i)
            ((prependFaceN a b (Classical.choose D)) j) := by
  let F := Classical.choose D
  have hF := Classical.choose_spec D
  rcases hF with ⟨hlink, hgeom, htrans⟩
  have hc := extendFanCertificate F hlink hgeom htrans
    a b m wa wb d hm_link hd_link ha hb hm_unit htri hang1 hang2 hang3
    htr_a htr_b htr_rest htrD_a htrD_b
  exact fanChain_face_pos_of_fanCertificate
    (prependFaceN a b F) (prependFaceW wa wb F) hc

end V3
end Vdb
