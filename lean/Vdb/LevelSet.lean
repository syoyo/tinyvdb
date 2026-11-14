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
/-- For `r < band` the sphere band is the open ball of radius `r + band`
    (the inner hole vanished: `|‖p‖ − r| < band` already follows from
    `‖p‖ < r + band`). -/
theorem sdfSphere_activeSet_eq_ball (r band : ℝ) (hb : r < band) :
    activeSet (sdfSphere r) band = {p : Point | ‖p‖ < r + band} := by
  ext p
  simp only [mem_activeSet, sdfSphere, Set.mem_ofPred_eq, abs_lt]
  constructor
  · rintro ⟨-, h2⟩
    linarith
  · rintro h'
    have h1 : r - band < ‖p‖ := by linarith [h', hb, norm_nonneg p]
    exact ⟨by linarith, by linarith⟩

/-- For `band < r` the sphere band is the annulus `r - band < ‖p‖ < r + band`:
    the inner open ball of radius `r - band` is *not* active (in particular
    `‖p‖ ≤ r - band` points are excluded, band-limited sweeps leave the solid
    core alone). -/
theorem sdfSphere_activeSet_annulus (r band : ℝ) (_hb : band < r) :
    ∀ p : Point, ‖p‖ ≤ r - band → p ∉ activeSet (sdfSphere r) band := by
  intro p hp hmem
  simp only [mem_activeSet, sdfSphere, abs_lt] at hmem
  have hnn : 0 ≤ ‖p‖ := norm_nonneg p
  linarith [hmem.1, hp, hnn]



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


/-! ### Exact distance: the sphere -/

/-- A fixed unit vector of the space. -/
noncomputable def e0 : Point := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

theorem norm_e0 : ‖e0‖ = 1 := by
  unfold e0
  exact (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin 3)).1 0

/-- **The sphere field is the exact distance to the sphere**: a nearest point
    exists and attains the field magnitude, and no sphere point is closer. -/
theorem sdfSphere_exact (r : ℝ) (hr : 0 ≤ r) (p : Point) :
    (∃ q : Point, ‖q‖ = r ∧ dist p q = |sdfSphere r p|) ∧
      (∀ q : Point, ‖q‖ = r → |sdfSphere r p| ≤ dist p q) := by
  constructor
  · by_cases hp : p = 0
    · refine ⟨r • e0, ?_, ?_⟩
      · rw [norm_smul, norm_e0, Real.norm_eq_abs, abs_of_nonneg hr, mul_one]
      · subst hp
        rw [dist_eq_norm]
        have hz : (0 : Point) - r • e0 = -(r • e0) := by abel
        rw [hz, norm_neg, norm_smul, norm_e0, Real.norm_eq_abs, abs_of_nonneg hr, mul_one]
        unfold sdfSphere
        rw [show ‖(0 : Point)‖ = 0 from norm_zero]
        rw [show (0 : ℝ) - r = -r from by ring, abs_neg, abs_of_nonneg hr]
    · refine ⟨(r / ‖p‖) • p, ?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg hr,
          abs_of_pos (norm_pos_iff.mpr hp), div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hp)]
      · rw [dist_eq_norm]
        have hsub : p - (r / ‖p‖) • p = (1 - r / ‖p‖) • p := by
          rw [sub_smul, one_smul]
        rw [hsub, norm_smul, Real.norm_eq_abs]
        unfold sdfSphere
        have hpos : (0 : ℝ) < ‖p‖ := norm_pos_iff.mpr hp
        have heq : 1 - r / ‖p‖ = (‖p‖ - r) / ‖p‖ := by field_simp
        calc |1 - r / ‖p‖| * ‖p‖ = |(‖p‖ - r) / ‖p‖| * ‖p‖ := by rw [heq]
          _ = (|‖p‖ - r| / ‖p‖) * ‖p‖ := by rw [abs_div, abs_of_pos hpos]
          _ = |‖p‖ - r| := by
                field_simp
  · intro q hq
    exact sdfSphere_abs_le_dist r hq


/-! ### Level sets of signed distance fields -/

/-- The zero set (or any level set) of a signed distance field is closed. -/
theorem IsSDF.isClosed_levelSet {f : Point → ℝ} (hf : IsSDF f) (c : ℝ) :
    IsClosed (levelSet f c) :=
  isClosed_eq hf.continuous continuous_const

/-- A 1-Lipschitz field's value bounds the distance to every point of its
    level set. -/
theorem IsSDF.abs_sub_le_dist_of_level {f : Point → ℝ} (hf : IsSDF f) {c : ℝ}
    {p q : Point} (hq : q ∈ levelSet f c) : |f p - c| ≤ dist p q := by
  have h := hf p q
  rw [levelSet] at hq
  rw [hq] at h
  exact h

/-- **The field value bounds the distance to the level set**: for every point,
    `|f p - c|` is at most the infimum distance to the level set. This is the
    lower half of "the field is the distance to the surface". -/
theorem IsSDF.abs_sub_le_infDist {f : Point → ℝ} (hf : IsSDF f) {c : ℝ}
    (hne : (levelSet f c).Nonempty) (p : Point) :
    |f p - c| ≤ Metric.infDist p (levelSet f c) := by
  rw [Metric.le_infDist hne]
  intro q hq
  exact hf.abs_sub_le_dist_of_level hq

/-- In a proper space the nearest level-set point is attained. -/
theorem IsSDF.exists_nearest_levelSet {f : Point → ℝ} (hf : IsSDF f) {c : ℝ}
    (hne : (levelSet f c).Nonempty) (p : Point) :
    ∃ q : Point, q ∈ levelSet f c ∧ Metric.infDist p (levelSet f c) = dist p q :=
  (hf.isClosed_levelSet c).exists_infDist_eq_dist hne p


/-! ### Plane bands and the box surface -/

/-- The plane band is the slab between the two offset planes. -/
theorem sdfPlane_activeSet_eq (n : Point) (d band : ℝ) :
    activeSet (sdfPlane n d) band =
      {p : Point | d - band < ⟪n, p⟫ ∧ ⟪n, p⟫ < d + band} := by
  ext p
  simp only [mem_activeSet, sdfPlane, Set.mem_ofPred_eq, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- **The box surface**: `sdfBox` vanishes exactly on the boundary of the box,
    i.e. inside-or-on the box with at least one coordinate on a face. -/
theorem sdfBox_eq_zero_iff (h p : Point) :
    sdfBox h p = 0 ↔ (∀ i : Fin 3, |p i| ≤ h i) ∧ ∃ i : Fin 3, |p i| = h i := by
  constructor
  · intro h0
    obtain ⟨hb0, hb1, hb2⟩ := (sdfBox_le_zero_iff h p).mp (le_of_eq h0)
    have hle : ∀ i : Fin 3, |p i| ≤ h i := by
      intro i
      fin_cases i
      · exact hb0
      · exact hb1
      · exact hb2
    have hge : 0 ≤ sdfBox h p := le_of_eq h0.symm
    unfold sdfBox at hge
    rcases le_max_iff.mp hge with hA | hBC
    · refine ⟨hle, 0, ?_⟩
      have : |p 0| - h 0 = 0 := le_antisymm (by linarith [hle 0]) hA
      linarith
    · rcases le_max_iff.mp hBC with hB | hC
      · refine ⟨hle, 1, ?_⟩
        have : |p 1| - h 1 = 0 := le_antisymm (by linarith [hle 1]) hB
        linarith
      · refine ⟨hle, 2, ?_⟩
        have : |p 2| - h 2 = 0 := le_antisymm (by linarith [hle 2]) hC
        linarith
  · rintro ⟨hle, i, hi⟩
    refine le_antisymm ((sdfBox_le_zero_iff h p).mpr ⟨hle 0, hle 1, hle 2⟩) ?_
    unfold sdfBox
    fin_cases i
    · have hi0 : |p 0| = h 0 := by simpa using hi
      have h0 : |p 0| - h 0 = 0 := by linarith
      calc (0 : ℝ) = |p 0| - h 0 := h0.symm
        _ ≤ max (|p 0| - h 0) (max (|p 1| - h 1) (|p 2| - h 2)) := le_max_left _ _
    · have hi1 : |p 1| = h 1 := by simpa using hi
      have h1 : |p 1| - h 1 = 0 := by linarith
      calc (0 : ℝ) = |p 1| - h 1 := h1.symm
        _ ≤ max (|p 1| - h 1) (|p 2| - h 2) := le_max_left _ _
        _ ≤ max (|p 0| - h 0) (max (|p 1| - h 1) (|p 2| - h 2)) := le_max_right _ _
    · have hi2 : |p 2| = h 2 := by simpa using hi
      have h2 : |p 2| - h 2 = 0 := by linarith
      calc (0 : ℝ) = |p 2| - h 2 := h2.symm
        _ ≤ max (|p 1| - h 1) (|p 2| - h 2) := le_max_right _ _
        _ ≤ max (|p 0| - h 0) (max (|p 1| - h 1) (|p 2| - h 2)) := le_max_right _ _

end Vdb
