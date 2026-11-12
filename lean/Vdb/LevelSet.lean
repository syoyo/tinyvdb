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


/-! ### Band and sign regions -/


/-- The narrow band: points whose field value is closer than `band` to zero.
    These are the voxels the marching-cubes pass has to visit. -/
def activeSet (f : Point → ℝ) (band : ℝ) : Set Point := {p | |f p| < band}

/-- The interior (negative) side of a signed field. -/
def insideSet (f : Point → ℝ) : Set Point := {p | f p < 0}

/-- The exterior (positive) side. -/
def outsideSet (f : Point → ℝ) : Set Point := {p | 0 < f p}

/-- The surface. -/
def surface (f : Point → ℝ) : Set Point := levelSet f 0

@[simp] theorem mem_activeSet {f : Point → ℝ} {band : ℝ} {p : Point} :
    p ∈ activeSet f band ↔ |f p| < band := Iff.rfl

@[simp] theorem mem_insideSet {f : Point → ℝ} {p : Point} :
    p ∈ insideSet f ↔ f p < 0 := Iff.rfl

@[simp] theorem mem_outsideSet {f : Point → ℝ} {p : Point} :
    p ∈ outsideSet f ↔ 0 < f p := Iff.rfl

@[simp] theorem mem_surface {f : Point → ℝ} {p : Point} :
    p ∈ surface f ↔ f p = 0 := Iff.rfl

/-- The three regions are disjoint and cover the space. -/
theorem surface_disjoint (f : Point → ℝ) :
    Disjoint (insideSet f) (outsideSet f) := by
  rw [Set.disjoint_left]
  intro p hp hq
  simp at hp hq
  linarith

theorem not_mem_surface_of_inside {f : Point → ℝ} {p : Point} (h : f p < 0) :
    p ∉ surface f := by
  simp [h.ne]

theorem not_mem_surface_of_outside {f : Point → ℝ} {p : Point} (h : 0 < f p) :
    p ∉ surface f := by
  simp [h.ne']

/-- The surface sits between the two sides. -/
theorem surface_subset_compl (f : Point → ℝ) :
    surface f = (insideSet f ∪ outsideSet f)ᶜ := by
  ext p
  simp only [mem_surface, Set.mem_compl_iff, Set.mem_union, mem_insideSet, mem_outsideSet,
    not_or]
  constructor
  · intro h; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; linarith

/-- Any surface point is at distance at least the field magnitude away from
    the band complement, i.e. the band is a superset of the surface for any
    positive width. -/
theorem surface_subset_activeSet {f : Point → ℝ} {band : ℝ} (hb : 0 < band) :
    surface f ⊆ activeSet f band := by
  intro p hp
  simp only [mem_surface] at hp
  simp [hp, hb]

/-- For the sphere field the band is the spherical shell
    `r - band < |p| < r + band`. -/
theorem sdfSphere_activeSet_eq (r band : ℝ) :
    activeSet (sdfSphere r) band = {p : Point | r - band < ‖p‖ ∧ ‖p‖ < r + band} := by
  ext p
  simp only [mem_activeSet, sdfSphere, Set.mem_ofPred_eq, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- The sphere band lies inside the ball of radius `r + band`. -/
theorem sdfSphere_activeSet_subset (r band : ℝ) :
    activeSet (sdfSphere r) band ⊆ {p : Point | ‖p‖ < r + band} := by
  intro p hp
  rw [sdfSphere_activeSet_eq] at hp
  exact hp.2


/-! ### Exact distance: the plane -/

/-- The point of the plane nearest to `p` (the orthogonal projection). -/
noncomputable def planeProject (n : Point) (d : ℝ) (p : Point) : Point :=
  p - sdfPlane n d p • n

theorem real_inner_self_unit {n : Point} (hn : ‖n‖ = 1) : ⟪n, n⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, hn]
  norm_num

/-- The projection lies on the plane. -/
theorem planeProject_mem (n : Point) (d : ℝ) (hn : ‖n‖ = 1) (p : Point) :
    sdfPlane n d (planeProject n d p) = 0 := by
  unfold planeProject sdfPlane
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_unit hn]
  ring

/-- The projection is at distance exactly the field magnitude. -/
theorem planeProject_dist (n : Point) (d : ℝ) (hn : ‖n‖ = 1) (p : Point) :
    dist p (planeProject n d p) = |sdfPlane n d p| := by
  unfold planeProject
  rw [dist_eq_norm]
  have h : p - (p - sdfPlane n d p • n) = sdfPlane n d p • n := by abel
  rw [h, norm_smul, Real.norm_eq_abs, hn, mul_one]

/-- The field magnitude is a lower bound for the distance to any plane point. -/
theorem sdfPlane_abs_le_dist {n : Point} (hn : ‖n‖ = 1) (d : ℝ) (p q : Point)
    (hq : ⟪n, q⟫ = d) : |sdfPlane n d p| ≤ dist p q :=
  (sdfPlane_isSDF hn d).abs_le_dist_of_eq (by unfold sdfPlane; rw [hq, sub_self])

/-- **Plane field is the exact distance to the plane**: the projection attains
    the lower bound, so the magnitude of the field equals the distance. -/
theorem sdfPlane_exact (n : Point) (d : ℝ) (hn : ‖n‖ = 1) (p : Point) :
    sdfPlane n d (planeProject n d p) = 0 ∧
      dist p (planeProject n d p) = |sdfPlane n d p| ∧
      ∀ q : Point, ⟪n, q⟫ = d → |sdfPlane n d p| ≤ dist p q :=
  ⟨planeProject_mem n d hn p, planeProject_dist n d hn p,
    fun q hq => sdfPlane_abs_le_dist hn d p q hq⟩

end Vdb
