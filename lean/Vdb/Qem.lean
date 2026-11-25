/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  PH-2: the quadric error metric (QEM) used to rank edge collapses when a
  collision proxy is simplified. A quadric is stored as the ten symmetric
  coefficients of `vᵀ A v + 2 b·v + c`; a triangle's plane with unit normal `n`
  and offset `d` contributes `(⟪n,v⟫ − d)²`. The module proves the algebra the
  C implementation relies on: plane evaluation is exactly the squared distance
  to the plane, accumulation is coefficientwise, evaluation is additive, and a
  sum of planes with non-negative weights is non-negative everywhere.

  The collapse target chosen by the C implementation is the edge midpoint —
  documented deviation from the full QEM optimum — so no linear solve or
  PSD-invertibility theorem is needed here: the ranking cost is still the
  accumulated quadric evaluated at that midpoint.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Vdb.LevelSet

noncomputable section

open scoped RealInnerProductSpace

namespace Vdb

/-- The ten independent coefficients of a symmetric 3×3 quadric. -/
structure Quadric where
  a00 : ℝ
  a01 : ℝ
  a02 : ℝ
  a11 : ℝ
  a12 : ℝ
  a22 : ℝ
  b0 : ℝ
  b1 : ℝ
  b2 : ℝ
  c : ℝ

namespace Quadric

/-- The zero quadric. -/
def zero : Quadric := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Coefficientwise addition (quadrics accumulate over incident triangles). -/
def add (q r : Quadric) : Quadric :=
  ⟨q.a00 + r.a00, q.a01 + r.a01, q.a02 + r.a02,
   q.a11 + r.a11, q.a12 + r.a12, q.a22 + r.a22,
   q.b0 + r.b0, q.b1 + r.b1, q.b2 + r.b2, q.c + r.c⟩

instance : Add Quadric := ⟨add⟩
instance : Zero Quadric := ⟨zero⟩

/-- The plane quadric of a unit normal `n` and offset `d`:
    `n ⊗ n` with linear term `-d·n` and constant `d²`. -/
def plane (n : Point) (d : ℝ) : Quadric :=
  ⟨n 0 * n 0, n 0 * n 1, n 0 * n 2,
   n 1 * n 1, n 1 * n 2, n 2 * n 2,
   -d * n 0, -d * n 1, -d * n 2, d * d⟩

/-- Scale every coefficient by `k`. -/
def scale (k : ℝ) (q : Quadric) : Quadric :=
  ⟨k * q.a00, k * q.a01, k * q.a02, k * q.a11, k * q.a12, k * q.a22,
   k * q.b0, k * q.b1, k * q.b2, k * q.c⟩

end Quadric

/-- Evaluate a quadric at a point. -/
def qEval (q : Quadric) (v : Point) : ℝ :=
  q.a00 * v 0 * v 0 + 2 * q.a01 * v 0 * v 1 + 2 * q.a02 * v 0 * v 2 +
  q.a11 * v 1 * v 1 + 2 * q.a12 * v 1 * v 2 + q.a22 * v 2 * v 2 +
  2 * (q.b0 * v 0 + q.b1 * v 1 + q.b2 * v 2) + q.c

@[simp] theorem qEval_zero (v : Point) : qEval 0 v = 0 := by
  change qEval Quadric.zero v = 0
  simp [qEval, Quadric.zero]

theorem qEval_add (q r : Quadric) (v : Point) :
    qEval (Quadric.add q r) v = qEval q v + qEval r v := by
  simp [qEval, Quadric.add] ; ring_nf

/-- A plane quadric evaluates to the squared signed distance when the normal
    is a unit vector. This is the contract connecting the algebraic form to
    the geometric cost the simplifier ranks by. -/
theorem qEval_plane {n : Point} (hn : ⟪n, n⟫ = 1) (d : ℝ) (v : Point) :
    qEval (Quadric.plane n d) v = (⟪n, v⟫ - d) ^ 2 := by
  have hsum : n 0 * n 0 + n 1 * n 1 + n 2 * n 2 = 1 := by
    rw [PiLp.inner_apply] at hn
    simp only [Real.inner_apply, Fin.sum_univ_three] at hn
    nlinarith
  have hinner : ⟪n, v⟫ = n 0 * v 0 + n 1 * v 1 + n 2 * v 2 := by
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply, Fin.sum_univ_three]
  simp only [qEval, Quadric.plane]
  rw [hinner]
  nlinarith [hsum]

/-- The plane quadric evaluates to `(⟪n,v⟫ − d)²` for *any* normal, not just a
    unit one. This is the form used by the executable twin, which divides the
    coefficients by `⟪n,n⟫` instead of taking a square root. -/
theorem qEval_plane_general (n : Point) (d : ℝ) (v : Point) :
    qEval (Quadric.plane n d) v = (⟪n, v⟫ - d) ^ 2 := by
  have hinner : ⟪n, v⟫ = n 0 * v 0 + n 1 * v 1 + n 2 * v 2 := by
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply, Fin.sum_univ_three]
  simp only [qEval, Quadric.plane]
  rw [hinner]
  ring

theorem qEval_scale (k : ℝ) (q : Quadric) (v : Point) :
    qEval (Quadric.scale k q) v = k * qEval q v := by
  simp [qEval, Quadric.scale]
  ring

theorem qEval_plane_normalized {n : Point} (hn : ⟪n, n⟫ ≠ 0) (d : ℝ) (v : Point) :
    qEval (Quadric.scale (⟪n, n⟫)⁻¹ (Quadric.plane n d)) v =
      (⟪n, v⟫ - d) ^ 2 / ⟪n, n⟫ := by
  rw [qEval_scale, qEval_plane_general]
  field_simp [hn]

/-- Accumulating weighted plane quadrics: the C implementation sums the ten
    coefficients with double weights; here we package each plane as a function
    `Point → ℝ` returning its contribution to `qEval`. -/
def planesCost (ps : List (Point × ℝ × ℝ)) (v : Point) : ℝ :=
  (ps.map fun p => p.2.2 * (⟪p.1, v⟫ - p.2.1) ^ 2).sum

theorem planesCost_nonneg (ps : List (Point × ℝ × ℝ)) (v : Point)
    (hw : ∀ p ∈ ps, 0 ≤ p.2.2) : 0 ≤ planesCost ps v := by
  unfold planesCost
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hp := hw p (by simp)
      have ht : 0 ≤ (⟪p.1, v⟫ - p.2.1) ^ 2 := sq_nonneg _
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg (mul_nonneg hp ht) (ih (by intro q hq; exact hw q (by simp [hq])))

/-- The collapse cost of an edge with accumulated quadric `q` and collapse
    target `v` is simply the quadric's value at `v`. -/
def collapseCost (q : Quadric) (v : Point) : ℝ := qEval q v

/-- The quadric accumulated from a list of weighted planes. -/
def quadricOfPlanes (ps : List (Point × ℝ × ℝ)) : Quadric :=
  (ps.map fun p => Quadric.plane p.1 p.2.1).foldr Quadric.add Quadric.zero

theorem quadricOfPlanes_cons (p : Point × ℝ × ℝ) (ps : List (Point × ℝ × ℝ)) :
    quadricOfPlanes (p :: ps) = Quadric.add (Quadric.plane p.1 p.2.1) (quadricOfPlanes ps) := by
  rfl

theorem collapseCost_nonneg_of_planes (ps : List (Point × ℝ × ℝ)) (v : Point)
    (hw : ∀ p ∈ ps, 0 ≤ p.2.2 ∧ ⟪p.1, p.1⟫ = 1) :
    0 ≤ collapseCost (quadricOfPlanes ps) v := by
  unfold collapseCost quadricOfPlanes
  induction ps with
  | nil => simp [qEval, Quadric.zero]
  | cons p ps ih =>
      simp only [List.map_cons, List.foldr_cons]
      rw [qEval_add]
      have hp := hw p (by simp)
      exact add_nonneg (by rw [qEval_plane hp.2]; exact sq_nonneg _)
        (ih (by intro q hq; exact hw q (by simp [hq])))

/-- Evaluation is quadratic, so the two orderings of a midpoint agree. -/
theorem qEval_midpoint_symm (q : Quadric) (p r : Point) :
    qEval q ((2 : ℝ)⁻¹ • (p + r)) = qEval q ((2 : ℝ)⁻¹ • (r + p)) := by
  congr 1
  abel_nf

end Vdb
