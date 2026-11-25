/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  The n = 4 fan certificate: discharging `FanCertificate` at k = 1.

  This module is the smallest remaining n-face crack.  It builds the k = 1
  `FanChain` directly from the raw geometric diagonal data of a convex
  spherical quadrilateral and proves that this chain satisfies
  `FanCertificate`.  Face positivity then follows *by the already-landed*
  `fanChain_face_pos_of_fanCertificate`; nothing downstream is re-proved.

  The split is the one of `Vdb/AngleNFace.lean`:

      T₁ = (n₀, n₁, m ; θ₀, θ₁, d)
      T₂ = (-m, n₂, n₃ ; d, θ₂, θ₃)

  linked along the internal diagonal `m / -m` with common length `d`.
  Its boundary co-normals are `(n₀, n₁, n₂, n₃)` and its boundary weights
  are `(θ₀, θ₁, θ₂, θ₃)`, so the telescoping identity of the chain is exactly
  the landed `V3.dot_fan_sum_four` (reused by name, not duplicated).

  The diagonal **existence** step -- a great-circle arc splitting the spherical
  quadrilateral into two nondegenerate spherical triangles whose corner
  angles equal the boundary arc lengths, with dual-cone containment at the
  four face normals -- is the one remaining geometric hypothesis.  It is named
  explicitly below; everything after it is proved.  No unconditional claim is
  made, and the already-landed conditional tier
  `fourFace_face_pos_of_fanCertificate_faces` is not restated as new.

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
set_option maxHeartbeats 800000

/-! ### The two data projections of the quadrilateral -/

/-- The four boundary arc lengths of the quadrilateral, indexed by `Fin 4`
    in the same order as the landed `fanFace4`. -/
def fourTheta (θ₀ θ₁ θ₂ θ₃ : ℝ) (j : Fin 4) : ℝ :=
  if j = 0 then θ₀ else if j = 1 then θ₁ else if j = 2 then θ₂ else θ₃

/-! ### The k = 1 fan chain built from a diagonal -/

/-- The k = 1 fan chain determined by a diagonal co-normal `m`, its length
    `d`, and the two triangles `(n₀,n₁,m)` and `(-m,n₂,n₃)`. -/
noncomputable def fanChainFour (n₀ n₁ n₂ n₃ m : V3)
    (θ₀ θ₁ θ₂ θ₃ d : ℝ) : FanChain 1 :=
  FanChain.cons
    ⟨n₀, n₁, m, θ₀, θ₁, d⟩
    (FanChain.leaf ⟨pnSmul (-1) m, n₂, n₃, d, θ₂, θ₃⟩)

/-- The chain is linked: the exit diagonal `m` of `T₁` is `-(pnSmul (-1) m)`,
    i.e. the opposite co-normal of the entry diagonal of `T₂`, and the two
    copies carry the same length `d`. -/
lemma fanChainFour_linked (n₀ n₁ n₂ n₃ m : V3)
    (θ₀ θ₁ θ₂ θ₃ d : ℝ) : (fanChainFour n₀ n₁ n₂ n₃ m θ₀ θ₁ θ₂ θ₃ d).linked := by
  simp [fanChainFour, FanChain.linked, FanChain.head, pnSmul_neg_involutive]

/-- Boundary co-normals of the chain are exactly `(n₀,n₁,n₂,n₃)`. -/
lemma fanChainFour_boundaryN (n₀ n₁ n₂ n₃ m : V3)
    (θ₀ θ₁ θ₂ θ₃ d : ℝ) :
    (fanChainFour n₀ n₁ n₂ n₃ m θ₀ θ₁ θ₂ θ₃ d).boundaryN =
      fanFace4 n₀ n₁ n₂ n₃ := by
  funext j
  fin_cases j <;> simp [fanChainFour, fanFace4, FanChain.boundaryN]

/-- Boundary weights of the chain are exactly `(θ₀,θ₁,θ₂,θ₃)`. -/
lemma fanChainFour_boundaryW (n₀ n₁ n₂ n₃ m : V3)
    (θ₀ θ₁ θ₂ θ₃ d : ℝ) :
    (fanChainFour n₀ n₁ n₂ n₃ m θ₀ θ₁ θ₂ θ₃ d).boundaryW =
      fourTheta θ₀ θ₁ θ₂ θ₃ := by
  funext j
  fin_cases j <;> simp [fanChainFour, fourTheta, FanChain.boundaryW]

/-! ### Diagonal cancellation, reused from the landed algebra -/

/-- The k = 1 diagonal cancellation in the shape of `dot_fan_sum_four`.
    This is **not** a new algebraic theorem: it is exactly the landed
    `dot_fan_sum_four`, applied to the `total` of the constructed chain
    (equivalently the k = 1 case of `fanChain_dot_total`). -/
lemma fanChainFour_dot_total (n₀ n₁ n₂ n₃ m : V3)
    (θ₀ θ₁ θ₂ θ₃ d : ℝ) (x : V3) :
    dot x (fanChainFour n₀ n₁ n₂ n₃ m θ₀ θ₁ θ₂ θ₃ d).total =
      θ₀ * dot x n₀ + θ₁ * dot x n₁ + θ₂ * dot x n₂ + θ₃ * dot x n₃ := by
  change dot x (V3.add
      (fanWeighted n₀ n₁ m θ₀ θ₁ d)
      (fanWeighted (pnSmul (-1) m) n₂ n₃ d θ₂ θ₃)) = _
  rw [dot_add_right]
  exact dot_fan_sum_four x n₀ n₁ n₂ n₃ m θ₀ θ₁ θ₂ θ₃ d

/-! ### The certificate for k = 1 -/

/-- **The n = 4 diagonal hypothesis, packaged.**  Given unit outward
    co-normals of the four sides, a diagonal co-normal `m` with arc length
    `d`, nondegeneracy of the two spherical triangles, equality of their
    corner angles with the boundary arc lengths, and dual-cone containment of
    every face normal in both triangles, the k = 1 `FanChain` is a
    `FanCertificate`.

    This is the exact remaining geometric input; the existence of such an
    `m` (with the corner-angle matching and the dual-cone containment) is
    *not* proved here and is not claimed unconditionally. -/
lemma fourFace_fanCertificate_of_diagonal
    (n₀ n₁ n₂ n₃ m : V3) (θ₀ θ₁ θ₂ θ₃ d : ℝ)
    (h0 : dot n₀ n₀ = 1) (h1 : dot n₁ n₁ = 1)
    (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1) (hm : dot m m = 1)
    (htri1 : triple n₀ n₁ m ≠ 0)
    (htri2 : triple (pnSmul (-1) m) n₂ n₃ ≠ 0)
    (hang1a : cornerAngle (isoEdge12 n₀ n₁) (isoEdge13 n₀ m) = θ₀)
    (hang1b : cornerAngle (isoEdge12 n₀ n₁) (isoEdge23 n₁ m) = θ₁)
    (hang1c : cornerAngle (isoEdge13 n₀ m) (isoEdge23 n₁ m) = d)
    (hang2a : cornerAngle (isoEdge12 (pnSmul (-1) m) n₂)
        (isoEdge13 (pnSmul (-1) m) n₃) = d)
    (hang2b : cornerAngle (isoEdge12 (pnSmul (-1) m) n₂)
        (isoEdge23 n₂ n₃) = θ₂)
    (hang2c : cornerAngle (isoEdge13 (pnSmul (-1) m) n₃)
        (isoEdge23 n₂ n₃) = θ₃)
    (hdu : ∀ j : Fin 4,
        FanTriangleTransfer ⟨n₀, n₁, m, θ₀, θ₁, d⟩
          (fanFace4 n₀ n₁ n₂ n₃ j))
    (hdv : ∀ j : Fin 4,
        FanTriangleTransfer ⟨pnSmul (-1) m, n₂, n₃, d, θ₂, θ₃⟩
          (fanFace4 n₀ n₁ n₂ n₃ j)) :
    FanCertificate (fanFace4 n₀ n₁ n₂ n₃) (fourTheta θ₀ θ₁ θ₂ θ₃) := by
  refine ⟨fanChainFour n₀ n₁ n₂ n₃ m θ₀ θ₁ θ₂ θ₃ d, ?_, ?_, ?_, ?_, ?_⟩
  · exact fanChainFour_linked n₀ n₁ n₂ n₃ m θ₀ θ₁ θ₂ θ₃ d
  · exact (fanChainFour_boundaryN n₀ n₁ n₂ n₃ m θ₀ θ₁ θ₂ θ₃ d).symm
  · exact (fanChainFour_boundaryW n₀ n₁ n₂ n₃ m θ₀ θ₁ θ₂ θ₃ d).symm
  · constructor
    · exact ⟨h0, h1, hm, htri1, hang1a, hang1b, hang1c⟩
    · exact ⟨pnSmul_neg_unit m hm, h2, h3, htri2, hang2a, hang2b, hang2c⟩
  · intro j
    change FanTriangleTransfer ⟨n₀, n₁, m, θ₀, θ₁, d⟩
        (fanFace4 n₀ n₁ n₂ n₃ j) ∧
      FanTriangleTransfer ⟨pnSmul (-1) m, n₂, n₃, d, θ₂, θ₃⟩
        (fanFace4 n₀ n₁ n₂ n₃ j)
    exact ⟨hdu j, hdv j⟩

/-! ### The n = 4 positivity theorem -/

/-- **Four-face seam (S) from the k = 1 fan certificate.**  Under exactly
    the geometric diagonal hypothesis above, every face of the convex
    spherical quadrilateral satisfies

        ∀ j : Fin 4, 0 < Σ i : Fin 4, θᵢ · dot (nᵢ) (nⱼ).

    The proof constructs the k = 1 `FanCertificate` and applies the
    already-landed `fanChain_face_pos_of_fanCertificate`; the two triangle
    pairings are discharged there by `three_face_face_pos_unconditional` and
    the diagonal cancels by `fanChain_dot_total` (the k = 1 case of which is
    `dot_fan_sum_four`).

    Positivity of the arc lengths is part of the convex-quadrilateral input;
    it is implied by the angle-matching and nondegeneracy hypotheses (the
    corner angles of a nondegenerate trihedron lie in `(0, π)`) and is not
    needed by the algebraic downstream, so it is deliberately *not* added as
    an extra hypothesis here. -/
theorem fourFace_face_pos_of_diagonal_chain
    (n₀ n₁ n₂ n₃ m : V3) (θ₀ θ₁ θ₂ θ₃ d : ℝ)
    (h0 : dot n₀ n₀ = 1) (h1 : dot n₁ n₁ = 1)
    (h2 : dot n₂ n₂ = 1) (h3 : dot n₃ n₃ = 1) (hm : dot m m = 1)
    (htri1 : triple n₀ n₁ m ≠ 0)
    (htri2 : triple (pnSmul (-1) m) n₂ n₃ ≠ 0)
    (hang1a : cornerAngle (isoEdge12 n₀ n₁) (isoEdge13 n₀ m) = θ₀)
    (hang1b : cornerAngle (isoEdge12 n₀ n₁) (isoEdge23 n₁ m) = θ₁)
    (hang1c : cornerAngle (isoEdge13 n₀ m) (isoEdge23 n₁ m) = d)
    (hang2a : cornerAngle (isoEdge12 (pnSmul (-1) m) n₂)
        (isoEdge13 (pnSmul (-1) m) n₃) = d)
    (hang2b : cornerAngle (isoEdge12 (pnSmul (-1) m) n₂)
        (isoEdge23 n₂ n₃) = θ₂)
    (hang2c : cornerAngle (isoEdge13 (pnSmul (-1) m) n₃)
        (isoEdge23 n₂ n₃) = θ₃)
    (hdu : ∀ j : Fin 4,
        FanTriangleTransfer ⟨n₀, n₁, m, θ₀, θ₁, d⟩
          (fanFace4 n₀ n₁ n₂ n₃ j))
    (hdv : ∀ j : Fin 4,
        FanTriangleTransfer ⟨pnSmul (-1) m, n₂, n₃, d, θ₂, θ₃⟩
          (fanFace4 n₀ n₁ n₂ n₃ j)) :
    ∀ j : Fin 4,
      0 < ∑ i : Fin 4, fourTheta θ₀ θ₁ θ₂ θ₃ i *
        dot (fanFace4 n₀ n₁ n₂ n₃ i) (fanFace4 n₀ n₁ n₂ n₃ j) := by
  exact fanChain_face_pos_of_fanCertificate
    (fanFace4 n₀ n₁ n₂ n₃) (fourTheta θ₀ θ₁ θ₂ θ₃)
    (fourFace_fanCertificate_of_diagonal
      n₀ n₁ n₂ n₃ m θ₀ θ₁ θ₂ θ₃ d
      h0 h1 h2 h3 hm htri1 htri2
      hang1a hang1b hang1c hang2a hang2b hang2c hdu hdv)

end V3
end Vdb
