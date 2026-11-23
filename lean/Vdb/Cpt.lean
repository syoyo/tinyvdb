/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Closest-point transform (`tvdb_cpt`): one step `p ↦ p − φ(p)·g(p)`, where
  `g` is the (unit) gradient direction. This is the projection step used when a
  signed distance field is turned into contact points or a collision proxy.

  The module proves the algebraic contracts that do not require differentiating
  `φ`: the fixed points, the exact displacement bound, and — given an attained
  nearest surface point `q` with exact distance magnitude — that the step with
  the corresponding unit direction lands on `q` exactly. The last theorem is
  the specification of "project onto the surface" for a collision query; it
  takes the nearest point and its sign as hypotheses rather than claiming they
  are computed by the C gradient.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Vdb.LevelSet

noncomputable section

open scoped RealInnerProductSpace

namespace Vdb

/-- One closest-point-transform step. -/
def cpt (φ : Point → ℝ) (g : Point → Point) (p : Point) : Point :=
  p - φ p • g p

@[simp] theorem cpt_fixed_of_zero {φ : Point → ℝ} {g : Point → Point} {p : Point}
    (h : φ p = 0) : cpt φ g p = p := by
  simp [cpt, h]

theorem cpt_eq_self_iff {φ : Point → ℝ} {g : Point → Point} {p : Point} :
    cpt φ g p = p ↔ φ p = 0 ∨ g p = 0 := by
  rw [cpt, sub_eq_self]
  exact smul_eq_zero

/-- The step displaces `p` by at most `|φ p| · ‖g p‖`. -/
theorem dist_cpt_le (φ : Point → ℝ) (g : Point → Point) (p : Point) :
    dist (cpt φ g p) p ≤ |φ p| * ‖g p‖ := by
  rw [cpt, dist_eq_norm]
  have hsub : p - φ p • g p - p = -(φ p • g p) := by abel
  rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs]

/-- With a unit direction the displacement is bounded by the field magnitude. -/
theorem dist_cpt_le_of_unit {φ : Point → ℝ} {g : Point → Point} {p : Point}
    (hg : ‖g p‖ = 1) : dist (cpt φ g p) p ≤ |φ p| := by
  simpa [hg] using dist_cpt_le φ g p

/-- The field value changes by at most the displacement (a restatement of
    1-Lipschitzness for applications to contact manifolds). -/
theorem abs_cpt_sub_le (hf : IsSDF φ) (g : Point → Point) (p : Point) :
    |φ (cpt φ g p) - φ p| ≤ dist (cpt φ g p) p :=
  hf (cpt φ g p) p

/-- **Exact surface projection.** If `q` is a surface point attaining the exact
    absolute field value at `p`, then stepping along the unit direction toward
    `q` (with the sign of `φ p`) lands on `q`. This is the contract a collision
    projection relies on; the nearest point itself is supplied as a hypothesis. -/
theorem cpt_of_closest_point {φ : Point → ℝ} {p q : Point}
    (hq : φ q = 0) (habs : |φ p| = dist p q) (hp : φ p ≠ 0) :
    cpt φ (fun x => (if 0 ≤ φ p then (1 : ℝ) else -1) •
        ((‖x - q‖)⁻¹ • (x - q))) p = q := by
  have hpq : p ≠ q := by
    intro heq
    subst q
    exact hp hq
  have hn : ‖p - q‖ ≠ 0 := by
    simpa [norm_eq_zero, sub_eq_zero] using hpq
  have hdist : dist p q = ‖p - q‖ := dist_eq_norm p q
  have hsign : (φ p * (if 0 ≤ φ p then (1 : ℝ) else -1)) = ‖p - q‖ := by
    by_cases hpos : 0 ≤ φ p
    · have hφpos : φ p = ‖p - q‖ := by
        have : |φ p| = φ p := abs_of_nonneg hpos
        linarith
      simp [hφpos]
    · have hneg : φ p < 0 := lt_of_not_ge hpos
      have hφneg : -φ p = ‖p - q‖ := by
        have : |φ p| = -φ p := abs_of_neg hneg
        linarith
      simp [hpos, hφneg]
  have hsmul : φ p • ((if 0 ≤ φ p then (1 : ℝ) else -1) •
      ((‖p - q‖)⁻¹ • (p - q))) = p - q := by
    calc
      φ p • ((if 0 ≤ φ p then (1 : ℝ) else -1) • ((‖p - q‖)⁻¹ • (p - q)))
          = (φ p * (if 0 ≤ φ p then (1 : ℝ) else -1)) • ((‖p - q‖)⁻¹ • (p - q)) := by
              rw [smul_smul]
      _ = ‖p - q‖ • ((‖p - q‖)⁻¹ • (p - q)) := by rw [hsign]
      _ = (‖p - q‖ * (‖p - q‖)⁻¹) • (p - q) := by rw [smul_smul]
      _ = p - q := by rw [mul_inv_cancel₀ hn, one_smul]
  unfold cpt
  rw [hsmul]
  abel

end Vdb
