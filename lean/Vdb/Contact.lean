/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  PH-4: the geometry of a rigid-body contact. A contact is a point on a
  collision surface, a unit normal pointing from the surface toward the other
  body, and a positive penetration depth. The module proves the local
  contracts used by a narrowphase — positivity, unit normals, translation
  equivariance and the sphere/triangle sign rule — taking the closest-point
  property as an explicit premise (the closest-point machinery itself lives in
  `Vdb/MeshDistance.lean`).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Vdb.LevelSet
import Vdb.MeshDistance

set_option maxHeartbeats 800000

noncomputable section

open scoped RealInnerProductSpace

namespace Vdb

/-- A contact point of a sphere touching a triangle mesh. -/
structure Contact where
  point : Point          -- closest point on the triangle
  normal : Point         -- unit direction from the surface toward the sphere
  depth : ℝ              -- radius − distance, positive when touching
  face : ℕ               -- source face index
  deriving Inhabited

/-- A contact is well-formed: strictly penetrating and carrying a unit normal. -/
def Contact.WellFormed (c : Contact) : Prop :=
  0 < c.depth ∧ ‖c.normal‖ = 1

/-- A sphere/triangle contact built from a nearest triangle point. The nearest
    point `q`, the sphere center `p` and the radius determine everything. -/
def sphereContact (p q : Point) (radius : ℝ) (face : ℕ) : Contact :=
  if p = q then
    { point := q, normal := 0, depth := radius, face := face }
  else
    let n := (‖p - q‖)⁻¹ • (p - q)
    { point := q, normal := n, depth := radius - dist p q, face := face }

theorem unit_dir {p q : Point} (hpq : p ≠ q) :
    ‖(‖p - q‖)⁻¹ • (p - q)‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpq))

theorem sphereContact_normal_unit {p q : Point} (hpq : p ≠ q) :
    ‖(sphereContact p q 1 0).normal‖ = 1 := by
  simpa [sphereContact, hpq] using unit_dir hpq

theorem sphereContact_depth {p q : Point} (hpq : p ≠ q) (radius : ℝ) :
    (sphereContact p q radius 0).depth = radius - dist p q := by
  simp [sphereContact, hpq]

theorem sphereContact_wellFormed {p q : Point} (hpq : p ≠ q) {radius : ℝ}
    (hpen : dist p q < radius) : (sphereContact p q radius 0).WellFormed := by
  constructor
  · rw [sphereContact_depth hpq]
    linarith
  · simpa [sphereContact, hpq] using unit_dir hpq

/-- Contact data is translation equivariant: moving both bodies by `t` moves
    the contact point and keeps the normal and depth. -/
theorem sphereContact_translate {p q t : Point} (hpq : p ≠ q) (radius : ℝ) :
    sphereContact (p + t) (q + t) radius 0 =
      let c := sphereContact p q radius 0
      { point := c.point + t, normal := c.normal, depth := c.depth, face := c.face } := by
  have hne : p + t ≠ q + t := by
    intro h
    apply hpq
    simpa using congrArg (fun x => x - t) h
  simp [sphereContact, hne, hpq, dist_eq_norm, sub_eq_add_neg, add_assoc, add_comm]

/-- Only a positive-depth contact contributes to a manifold. -/
theorem contact_of_depth_pos {c : Contact} (h : 0 < c.depth) : c.WellFormed ↔ ‖c.normal‖ = 1 := by
  simp [Contact.WellFormed, h]

end Vdb
