/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Level sets and signed distance fields: the geometry layer the volume
  operators (volume-to-mesh, mesh-to-volume) are stated over.

  A `LevelSet` is a scalar field whose zero set is the surface. A signed
  *distance* field is additionally 1-Lipschitz, which is exactly what makes
  the narrow band and the sign convention meaningful: the magnitude of the
  field at a point bounds the distance to every point of the surface.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-!
  Level sets and signed distance fields (the geometry side of the volume ops).

  A `LevelSet` is a scalar field whose zero set is the surface; a signed
  distance field is a 1-Lipschitz scalar field, which is what makes the band
  and the sign convention useful. This module proves the basic facts for the
  sphere, plane and (Chebyshev) box fields; the marching-cubes/DMC tables and
  the mesh-to-volume build on these.
-/

open scoped RealInnerProductSpace

namespace Vdb

/-- Points in 3D (the volume domain). -/
abbrev Point : Type := EuclideanSpace ℝ (Fin 3)

/-- The zero level set (surface) of a scalar field. -/
def levelSet (f : Point → ℝ) (c : ℝ) : Set Point := {p | f p = c}

/-- A scalar field is 1-Lipschitz: the property that makes a signed field a
    *distance* field (the value bounds the distance to the surface). -/
def IsSDF (f : Point → ℝ) : Prop := ∀ p q, |f p - f q| ≤ dist p q

theorem IsSDF.continuous {f : Point → ℝ} (hf : IsSDF f) : Continuous f := by
  rw [Metric.continuous_iff]
  intro p ε hε
  refine ⟨ε, hε, ?_⟩
  intro q hq
  rw [Real.dist_eq]
  have h := hf p q
  have hq' : dist p q < ε := by rwa [dist_comm] at hq
  have habs : |f q - f p| = |f p - f q| := abs_sub_comm _ _
  rw [habs]
  linarith

/-- The value of a 1-Lipschitz field bounds the distance to every surface
    point: this is the lower half of "the field is the distance". -/
theorem IsSDF.abs_le_dist_of_eq {f : Point → ℝ} (hf : IsSDF f)
    {p q : Point} (hq : f q = 0) : |f p| ≤ dist p q := by
  have h := hf p q
  rw [hq, sub_zero] at h
  exact h

/-- **Sphere field**: signed distance to the sphere of radius `r`. -/
noncomputable def sdfSphere (r : ℝ) (p : Point) : ℝ := ‖p‖ - r

theorem sdfSphere_zero_iff (r : ℝ) (p : Point) :
    sdfSphere r p = 0 ↔ ‖p‖ = r := by
  unfold sdfSphere; constructor <;> intro h <;> linarith

theorem sdfSphere_neg_iff (r : ℝ) (p : Point) :
    sdfSphere r p < 0 ↔ ‖p‖ < r := by
  unfold sdfSphere; constructor <;> intro h <;> linarith

theorem sdfSphere_pos_iff (r : ℝ) (p : Point) :
    0 < sdfSphere r p ↔ r < ‖p‖ := by
  unfold sdfSphere; constructor <;> intro h <;> linarith

theorem sdfSphere_isSDF (r : ℝ) : IsSDF (sdfSphere r) := by
  intro p q
  unfold sdfSphere
  have h := abs_norm_sub_norm_le p q
  have h' : |‖p‖ - r - (‖q‖ - r)| = |‖p‖ - ‖q‖| := by
    congr 1; ring
  rw [h']
  exact h

theorem sdfSphere_abs_le_dist (r : ℝ) {p q : Point} (hq : ‖q‖ = r) :
    |sdfSphere r p| ≤ dist p q :=
  (sdfSphere_isSDF r).abs_le_dist_of_eq (by
    unfold sdfSphere; rw [hq, sub_self])

/-- **Plane field** with a unit normal. -/
noncomputable def sdfPlane (n : Point) (d : ℝ) (p : Point) : ℝ := ⟪n, p⟫ - d

theorem sdfPlane_zero_iff (n : Point) (d : ℝ) (p : Point) :
    sdfPlane n d p = 0 ↔ ⟪n, p⟫ = d := by
  unfold sdfPlane; constructor <;> intro h <;> linarith

theorem sdfPlane_isSDF {n : Point} (hn : ‖n‖ = 1) (d : ℝ) : IsSDF (sdfPlane n d) := by
  intro p q
  unfold sdfPlane
  have h' : |⟪n, p⟫ - d - (⟪n, q⟫ - d)| = |⟪n, p - q⟫| := by
    congr 1
    rw [inner_sub_right]
    ring
  rw [h']
  calc |⟪n, p - q⟫| ≤ ‖n‖ * ‖p - q‖ := abs_real_inner_le_norm _ _
    _ = ‖p - q‖ := by rw [hn, one_mul]
    _ = dist p q := rfl

/-- **Chebyshev box field**: `max_i (|p_i| - h_i)`. Its zero set is the
    surface of the axis-aligned box with half-extents `h` (nonnegative). The
    sign is the exact inside/outside test; the magnitude is the L∞ distance to
    the box surface (not the Euclidean one). -/
noncomputable def sdfBox (h : Point) (p : Point) : ℝ :=
  max (|p 0| - h 0) (max (|p 1| - h 1) (|p 2| - h 2))

theorem sdfBox_le_zero_iff (h p : Point) :
    sdfBox h p ≤ 0 ↔ |p 0| ≤ h 0 ∧ |p 1| ≤ h 1 ∧ |p 2| ≤ h 2 := by
  unfold sdfBox
  constructor
  · intro hle
    have h0 : |p 0| - h 0 ≤ 0 := le_trans (le_max_left _ _) hle
    have h12 : max (|p 1| - h 1) (|p 2| - h 2) ≤ 0 := le_trans (le_max_right _ _) hle
    have h1 : |p 1| - h 1 ≤ 0 := le_trans (le_max_left _ _) h12
    have h2 : |p 2| - h 2 ≤ 0 := le_trans (le_max_right _ _) h12
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2⟩
    apply max_le <;> [linarith; apply max_le <;> linarith]


/-- Each coordinate difference is bounded by the Euclidean distance. -/
theorem abs_coord_le_dist (p q : Point) (i : Fin 3) : |p i - q i| ≤ dist p q := by
  rw [dist_eq_norm]
  have h := PiLp.norm_apply_le (p - q) i
  simpa [PiLp.sub_apply] using h

theorem sdfBox_isSDF (h : Point) : IsSDF (sdfBox h) := by
  intro p q
  have h0 : |(|p 0| - h 0) - (|q 0| - h 0)| ≤ dist p q := by
    have hc := abs_coord_le_dist p q 0
    have he : |(|p 0| - h 0) - (|q 0| - h 0)| = abs (|p 0| - |q 0|) := by
      congr 1; ring
    rw [he]
    exact le_trans (abs_abs_sub_abs_le_abs_sub _ _) hc
  have h1 : |(|p 1| - h 1) - (|q 1| - h 1)| ≤ dist p q := by
    have hc := abs_coord_le_dist p q 1
    have he : |(|p 1| - h 1) - (|q 1| - h 1)| = abs (|p 1| - |q 1|) := by
      congr 1; ring
    rw [he]
    exact le_trans (abs_abs_sub_abs_le_abs_sub _ _) hc
  have h2 : |(|p 2| - h 2) - (|q 2| - h 2)| ≤ dist p q := by
    have hc := abs_coord_le_dist p q 2
    have he : |(|p 2| - h 2) - (|q 2| - h 2)| = abs (|p 2| - |q 2|) := by
      congr 1; ring
    rw [he]
    exact le_trans (abs_abs_sub_abs_le_abs_sub _ _) hc
  unfold sdfBox
  refine le_trans (abs_max_sub_max_le_max _ _ _ _) ?_
  refine max_le h0 ?_
  exact le_trans (abs_max_sub_max_le_max _ _ _ _) (max_le h1 h2)

/-- The sphere field's zero level set is the sphere. -/
theorem sdfSphere_levelSet (r : ℝ) :
    levelSet (sdfSphere r) 0 = {p : Point | ‖p‖ = r} := by
  ext p
  simp [levelSet, sdfSphere_zero_iff]

/-- The plane field's zero level set is the plane. -/
theorem sdfPlane_levelSet (n : Point) (d : ℝ) :
    levelSet (sdfPlane n d) 0 = {p : Point | ⟪n, p⟫ = d} := by
  ext p
  simp [levelSet, sdfPlane_zero_iff]

end Vdb
