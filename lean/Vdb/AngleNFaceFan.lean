/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  Arbitrary-n fan certificate: a bounded generalization of the n = 4 fan
  reduction of `Vdb/AngleNFace.lean` to a convex spherical (k+3)-gon, k >= 0.

  A fan triangulation of a convex spherical polygon is a chain of spherical
  triangles joined along internal diagonals.  For `k` diagonals there are
  `k+1` triangles and `k+3` boundary sides.  Each internal diagonal is
  represented twice, once with co-normal `m` and once with co-normal `-m`,
  with the same arc length; hence the two contributions cancel and the
  weighted boundary sum telescopes:

      Σ_i θ_i • n_i = Σ_T Σ_e len_e • conormal_e .

  Given a certificate (the fan exists, is linked, every triangle is
  nondegenerate with its side lengths equal to the genuine corner angles, and
  every face normal lies in the dual cone of every triangle), (S)

      ∀ j, 0 < Σ_i θ_i * dot (n_i) (n_j)

  follows unconditionally: each triangle contributes a strictly positive
  pairing by `three_face_face_pos_unconditional` plus dual-cone transfer, and
  the diagonal cancellation above identifies the sum with the boundary sum.

  For k = 1 the chain is the pair `(n₀,n₁,m)`, `(-m,n₂,n₃)` and the
  telescoping identity is exactly `V3.dot_fan_sum_four`; this module generalizes
  that algebraic step and does not re-prove the landed n = 4 theorem.

  The *geometric existence* of such a fan (a diagonal great-circle arc splitting
  the polygon into nondegenerate spherical triangles with matching corner
  angles and dual-cone containment) remains an explicit named hypothesis, as
  in the n = 4 tier.  Everything downstream of it is proved here.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.AngleNFace

namespace Vdb
namespace V3

open scoped Real
open Real

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-- One triangle of a fan.  `a, b` are the two "entry" co-normals and `m` is
    the "exit" diagonal co-normal; `wa, wb, d` are the corresponding side arc
    lengths (weights). -/
structure FanTriangle where
  a : V3
  b : V3
  m : V3
  wa : ℝ
  wb : ℝ
  d : ℝ

/-- Recursive fan triangulation.  `FanChain k` has `k` internal diagonals and
    `k+1` triangles: `leaf` is a single triangle (k = 0) and `cons T F` prepends
    a triangle to a chain with one fewer diagonal.  Linking of consecutive
    triangles is a separate recursive predicate (`FanChain.linked`). -/
inductive FanChain : ℕ → Type where
  | leaf (T : FanTriangle) : FanChain 0
  | cons (T : FanTriangle) (F : FanChain k) : FanChain (k + 1)

namespace FanChain

/-- The first triangle of a nonempty chain. -/
def head : FanChain k → FanTriangle
  | leaf T => T
  | cons T _ => T

/-- A chain is linked when each exit diagonal matches the entry diagonal of
    the next triangle with the opposite co-normal and the same length. -/
def linked : FanChain k → Prop
  | leaf _ => True
  | cons T F =>
      T.m = pnSmul (-1) (head F).a ∧ T.d = (head F).wa ∧ linked F

/-- The `k+3` boundary co-normals of the fan.  For `cons T F` the first two
    are `T.a, T.b` and the rest are the boundary co-normals of `F` (whose
    first entry is the internal diagonal, already supplied by `T`). -/
def boundaryN : FanChain k → Fin (k + 3) → V3
  | leaf T, j => if j = 0 then T.a else if j = 1 then T.b else T.m
  | cons T F, j =>
      if j = 0 then T.a
      else if j = 1 then T.b
      else F.boundaryN ⟨j.val - 1, by omega⟩

/-- The `k+3` boundary arc lengths, indexed in the same way as `boundaryN`. -/
def boundaryW : FanChain k → Fin (k + 3) → ℝ
  | leaf T, j => if j = 0 then T.wa else if j = 1 then T.wb else T.d
  | cons T F, j =>
      if j = 0 then T.wa
      else if j = 1 then T.wb
      else F.boundaryW ⟨j.val - 1, by omega⟩

/-- The sum of the `fanWeighted` vectors over all triangles of the chain. -/
noncomputable def total : FanChain k → V3
  | leaf T => fanWeighted T.a T.b T.m T.wa T.wb T.d
  | cons T F => V3.add (fanWeighted T.a T.b T.m T.wa T.wb T.d) (total F)

end FanChain

/-! ### Elementary algebraic facts -/

/-- `dot` is additive in its second argument. -/
lemma dot_add_right (x u v : V3) : dot x (V3.add u v) = dot x u + dot x v := by
  unfold V3.add dot
  ring

/-- Negation of a co-normal is an involution. -/
lemma pnSmul_neg_involutive (v : V3) : pnSmul (-1) (pnSmul (-1) v) = v := by
  apply V3.ext <;> simp [pnSmul]

lemma FanChain.boundaryN_zero (F : FanChain k) : F.boundaryN 0 = F.head.a := by
  cases F with
  | leaf T => simp [FanChain.boundaryN, FanChain.head]
  | cons T F => simp [FanChain.boundaryN, FanChain.head]

lemma FanChain.boundaryW_zero (F : FanChain k) : F.boundaryW 0 = F.head.wa := by
  cases F with
  | leaf T => simp [FanChain.boundaryW, FanChain.head]
  | cons T F => simp [FanChain.boundaryW, FanChain.head]

lemma FanChain.boundaryN_succ_succ (T : FanTriangle) (F : FanChain k)
    (i : Fin (k + 2)) :
    (FanChain.cons T F).boundaryN i.succ.succ = F.boundaryN i.succ := by
  have hne : (i.succ.succ : Fin (k + 4)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
  simp [FanChain.boundaryN, hne]
  apply congrArg F.boundaryN
  apply Fin.ext
  simp

lemma FanChain.boundaryW_succ_succ (T : FanTriangle) (F : FanChain k)
    (i : Fin (k + 2)) :
    (FanChain.cons T F).boundaryW i.succ.succ = F.boundaryW i.succ := by
  have hne : (i.succ.succ : Fin (k + 4)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
  simp [FanChain.boundaryW, hne]
  apply congrArg F.boundaryW
  apply Fin.ext
  simp

/-! ### Requirement 1: the weighted sum telescopes -/

/-- **Diagonal cancellation / telescoping.**  For a linked chain,
    `dot x (Σ_T fanWeighted T) = Σ_i θ_i dot x n_i`: each internal diagonal
    appears once as `len • m` and once as `len • (-m)`, so the two terms
    cancel.  At the vector level this is `Σ_i θ_i • n_i = Σ_T Σ_e len_e • c_e`. -/
lemma fanChain_dot_total (F : FanChain k) (hF : F.linked) (x : V3) :
    dot x F.total = ∑ i : Fin (k + 3), F.boundaryW i * dot x (F.boundaryN i) := by
  induction F with
  | leaf T =>
      simp [FanChain.total, FanChain.boundaryN, FanChain.boundaryW,
        Fin.sum_univ_three, dot_fanWeighted]
  | cons T F ih =>
      rw [FanChain.total, dot_add_right, dot_fanWeighted]
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp_rw [FanChain.boundaryN_succ_succ, FanChain.boundaryW_succ_succ]
      simp [FanChain.boundaryN, FanChain.boundaryW]
      rw [Fin.sum_univ_succ] at ih
      rw [FanChain.boundaryN_zero, FanChain.boundaryW_zero] at ih
      rw [ih hF.2.2]
      have hlink : T.m = pnSmul (-1) F.head.a := hF.1
      have hlinkw : T.d = F.head.wa := hF.2.1
      have hhead : F.head.a = pnSmul (-1) T.m := by
        calc
          F.head.a = pnSmul (-1) (pnSmul (-1) F.head.a) := (pnSmul_neg_involutive _).symm
          _ = pnSmul (-1) T.m := by rw [← hlink]
      rw [hhead, dot_pnSmul_neg, hlinkw]
      ring

/-- The vector-level form of the telescoping identity:
    `Σ_i θ_i • n_i = Σ_T Σ_e len_e • conormal_e`.  This follows from
    `fanChain_dot_total` by testing against the three coordinate vectors. -/
lemma fanChain_weightedNormalSum_eq_total (F : FanChain k) (hF : F.linked) :
    weightedNormalSum F.boundaryW F.boundaryN = F.total := by
  apply V3.ext
  · simpa [weightedNormalSum, dot] using
      (fanChain_dot_total F hF (⟨1, 0, 0⟩ : V3)).symm
  · simpa [weightedNormalSum, dot] using
      (fanChain_dot_total F hF (⟨0, 1, 0⟩ : V3)).symm
  · simpa [weightedNormalSum, dot] using
      (fanChain_dot_total F hF (⟨0, 0, 1⟩ : V3)).symm

/-- The same telescoping identity with the dot product in the order used by
    (S): `dot n_j (Σ_T fanWeighted T) = Σ_i θ_i dot n_i n_j`. -/
lemma fanChain_dot_total_comm (F : FanChain k) (hF : F.linked) (x : V3) :
    dot x F.total = ∑ i : Fin (k + 3), F.boundaryW i * dot (F.boundaryN i) x := by
  rw [fanChain_dot_total F hF x]
  apply Finset.sum_congr rfl
  intro i _
  rw [dot_commV x (F.boundaryN i)]

/-! ### Requirement 2: positivity of each triangle and of the whole fan -/

/-- Geometric certificate for one fan triangle: unit co-normals, a
    nondegenerate cone, and side lengths equal to the genuine corner angles
    of that trihedron. -/
structure FanTriangleGeom (T : FanTriangle) : Prop where
  ha : dot T.a T.a = 1
  hb : dot T.b T.b = 1
  hm : dot T.m T.m = 1
  htri : triple T.a T.b T.m ≠ 0
  hang1 : cornerAngle (isoEdge12 T.a T.b) (isoEdge13 T.a T.m) = T.wa
  hang2 : cornerAngle (isoEdge12 T.a T.b) (isoEdge23 T.b T.m) = T.wb
  hang3 : cornerAngle (isoEdge13 T.a T.m) (isoEdge23 T.b T.m) = T.d

/-- Dual-cone transfer at a vector `x`: `x` is a nonnegative combination of
    the triangle's co-normals with at least one strictly positive coefficient.
    This is the `hdu`/`hdv` condition of the n = 4 tier, generalized to one
    triangle of the fan. -/
def FanTriangleTransfer (T : FanTriangle) (x : V3) : Prop :=
  ∃ l0 l1 lm : ℝ, 0 ≤ l0 ∧ 0 ≤ l1 ∧ 0 ≤ lm ∧
    (0 < l0 ∨ 0 < l1 ∨ 0 < lm) ∧
    dot x (fanWeighted T.a T.b T.m T.wa T.wb T.d) =
      l0 * dot T.a (fanWeighted T.a T.b T.m T.wa T.wb T.d) +
      l1 * dot T.b (fanWeighted T.a T.b T.m T.wa T.wb T.d) +
      lm * dot T.m (fanWeighted T.a T.b T.m T.wa T.wb T.d)

/-- Geometric conditions for all triangles of a chain. -/
def FanChainGeom : FanChain k → Prop
  | FanChain.leaf T => FanTriangleGeom T
  | FanChain.cons T F => FanTriangleGeom T ∧ FanChainGeom F

/-- Dual-cone transfer at `x` for all triangles of a chain. -/
def FanChainTransferAt : FanChain k → V3 → Prop
  | FanChain.leaf T, x => FanTriangleTransfer T x
  | FanChain.cons T F, x => FanTriangleTransfer T x ∧ FanChainTransferAt F x

/-- Every triangle of a geometrically valid chain has a strictly positive
    pairing with any vector in the dual cone of the chain, by the landed
    unconditional three-face theorem and dual-cone transfer.  The whole chain
    then has a strictly positive pairing, by summing the (positive)
    triangle contributions; the internal diagonals cancel exactly in
    `fanChain_dot_total`. -/
lemma FanChain.total_pos (F : FanChain k) (hg : FanChainGeom F) (x : V3)
    (hx : FanChainTransferAt F x) : 0 < dot x F.total := by
  induction F with
  | leaf T =>
      rcases hx with ⟨l0, l1, lm, hl0, hl1, hlm, hpos, hdot⟩
      exact fanTriangle_pair_pos T.a T.b T.m x T.wa T.wb T.d
        hg.ha hg.hb hg.hm hg.htri hg.hang1 hg.hang2 hg.hang3
        l0 l1 lm hl0 hl1 hlm hpos hdot
  | cons T F ih =>
      rw [FanChain.total, dot_add_right]
      rcases hx.1 with ⟨l0, l1, lm, hl0, hl1, hlm, hpos, hdot⟩
      exact add_pos
        (fanTriangle_pair_pos T.a T.b T.m x T.wa T.wb T.d
          hg.1.ha hg.1.hb hg.1.hm hg.1.htri hg.1.hang1 hg.1.hang2 hg.1.hang3
          l0 l1 lm hl0 hl1 hlm hpos hdot)
        (ih hg.2 hx.2)

/-! ### The arbitrary-n seam (S) modulo the fan certificate -/

/-- **Fan certificate** for a convex spherical (k+3)-gon.  It packages the
    existence of a linked fan triangulation of the boundary `(n, θ)`, the
    geometric validity of each triangle, and the dual-cone containment at
    every face normal.  The geometric existence of the fan is the named hard
    step; everything downstream is proved. -/
def FanCertificate {k : ℕ} (n : Fin (k + 3) → V3) (θ : Fin (k + 3) → ℝ) : Prop :=
  ∃ (chain : FanChain k),
    chain.linked ∧
    n = chain.boundaryN ∧
    θ = chain.boundaryW ∧
    FanChainGeom chain ∧
    ∀ j : Fin (k + 3), FanChainTransferAt chain (n j)

/-- **Arbitrary-n seam (S) from a fan certificate.**  For every face `j`,
    `Σ_i θ_i dot (n_i) (n_j) > 0`, proved by applying
    `three_face_face_pos_unconditional` to each fan triangle and summing the
    positive contributions; the diagonal terms cancel by telescoping. -/
theorem fanChain_face_pos_of_fanCertificate {k : ℕ}
    (n : Fin (k + 3) → V3) (θ : Fin (k + 3) → ℝ)
    (hc : FanCertificate n θ) :
    ∀ j : Fin (k + 3), 0 < ∑ i : Fin (k + 3), θ i * dot (n i) (n j) := by
  rcases hc with ⟨chain, hlink, hn, hθ, hgeom, htransfer⟩
  subst n
  subst θ
  intro j
  have hpos : 0 < dot (chain.boundaryN j) chain.total :=
    chain.total_pos hgeom (chain.boundaryN j) (htransfer j)
  rw [fanChain_dot_total_comm chain hlink (chain.boundaryN j)] at hpos
  exact hpos

end V3
end Vdb
