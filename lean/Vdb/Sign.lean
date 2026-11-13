/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  The closest-point-normal sign convention for mesh-to-volume distance
  fields (the sign the C dense mesh-to-SDF uses, F11): a surface is given by a
  nearest-point map and an outward normal field, and a point is outside when
  it lies on the outward side of its nearest surface point.

  The signed field vanishes exactly at the projection, and for the plane it
  is the exact signed distance (`signedByNormal_plane`), so the convention
  agrees with the analytic SDF where the latter is known.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.LevelSet
import Mathlib.Tactic
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace
open Vdb

namespace Vdb

/-- A surface with a nearest-point map and an outward normal field. -/
structure NormalSurface where
  proj : Point → Point
  normal : Point → Point

/-- **Signed distance by the closest-point normal convention** (the C reader's
    F11 heuristic): positive when the point lies on the outward side of the
    nearest surface point, negative otherwise. -/
noncomputable def signedByNormal (S : NormalSurface) (p : Point) : ℝ :=
  if 0 ≤ ⟪p - S.proj p, S.normal (S.proj p)⟫ then dist p (S.proj p)
  else -dist p (S.proj p)

/-- The signed field vanishes exactly at the projection. -/
theorem signedByNormal_eq_zero_iff (S : NormalSurface) (p : Point) :
    signedByNormal S p = 0 ↔ p = S.proj p := by
  unfold signedByNormal
  split <;> simp [dist_eq_zero]

theorem signedByNormal_ne_zero_iff (S : NormalSurface) (p : Point) :
    signedByNormal S p ≠ 0 ↔ p ≠ S.proj p := by
  rw [Ne, signedByNormal_eq_zero_iff]

/-- The plane surface: orthogonal projection and the unit normal. -/
noncomputable def planeSurface (n : Point) (d : ℝ) : NormalSurface :=
  { proj := fun p => planeProject n d p, normal := fun _ => n }

/-- **The closest-normal sign of a plane is the exact plane SDF.** -/
theorem signedByNormal_plane (n : Point) (d : ℝ) (hn : ‖n‖ = 1) (p : Point) :
    signedByNormal (planeSurface n d) p = sdfPlane n d p := by
  have hdist := planeProject_dist n d hn p
  have hsub : p - planeProject n d p = sdfPlane n d p • n := by
    unfold planeProject sdfPlane
    abel
  have hdot : ⟪p - planeProject n d p, n⟫ = sdfPlane n d p := by
    rw [hsub, real_inner_smul_left, real_inner_self_unit hn, mul_one]
  unfold signedByNormal planeSurface
  rw [hdot, hdist]
  by_cases h : 0 ≤ sdfPlane n d p
  · rw [ite_eq_left h, abs_of_nonneg h]
  · rw [ite_eq_right h, abs_of_neg (not_le.mp h)]
    ring

end Vdb
