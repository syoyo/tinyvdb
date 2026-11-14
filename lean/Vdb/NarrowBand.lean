/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  T-BAND-COMPLETE: covering bound for the narrow-band mesh→level-set
  candidate set (`tvdb_mesh_to_level_set` in `src/tinyvdb_sparse_tools.c`).

  The C implementation, in voxel units (`h` = voxel size):

  * **Seeds**: every triangle of the mesh is sampled on a barycentric grid
    with edge spacing at most `h` (sample spacing is `l / n` with
    `n = ceil(2 l / h)`, i.e. at most `h/2`), so every point of a face is
    within `h/(2√3)` of a sample (the circumradius of a sub-triangle of side
    `s ≤ h/2` is `s/√3`). Each sample is snapped to the nearest voxel center,
    moving the point by at most half a voxel diagonal, `h·√3/2`. Hence every
    point of the mesh surface is within `d = h/(2√3) + h√3/2 = 2h/√3` of a
    seed voxel.
  * **Dilation**: the seed set is dilated by `k = ceil(√3 · max(outside,
    inside) / h) + 2` 6-neighbor layers. Each 6-neighbor layer extends the
    reachable set by one voxel in L1 distance, so after `k` layers every
    voxel within L1 distance `k·h` of a seed is a candidate.
  * **Claim**: every voxel center within Euclidean distance `W` (the band
    width, `min(outside, inside)`) of the mesh surface is in the candidate
    set.

  This module proves the covering bound over `ℝ³`, in voxel units (`h = 1`;
  scale is irrelevant because all statements are homogeneous):

  * `cs_3` — the 3D Cauchy–Schwarz inequality `(∑|xᵢ|)² ≤ 3·∑xᵢ²`;
  * `l1_le_sqrt3_distSq` — `∑|xᵢ| ≤ √3 · √(∑xᵢ²)` (i.e. `L1 ≤ √3 · L2` in 3D);
  * `sqrt_sum_sq_add_sq_le` — Minkowski (triangle inequality) for the
    Euclidean norm on `ℝ³`, proved from `cs_3`;
  * `edist_triangle` — the triangle inequality for `edist`;
  * **`band_complete`** — if every point of a set `F ⊆ ℝ³` is within
    `2/√3` of some lattice seed, then every lattice point `v` within
    Euclidean distance `< width` of `F` satisfies an L1 bound of at most
    `⌈√3·width⌉ + 2` — exactly the dilation radius used in the C code
    (`ceil(√3·width) + 2` layers);
  * `candidate_six_neighbor_equiv` is *not* claimed here; the L1-ball form
    is what the 6-neighbor dilation computes, layer by layer.

  What is *not* proved here: the two coverage hypotheses are modeling steps,
  not verified geometry. The `h/(2√3)` sample covering radius and the
  `h·√3/2` nearest-voxel radius are the standard facts from the C code
  (spacing `≤ h/2` gives circumradius `≤ h/(2√3)`; snapping to a voxel
  center moves a point by at most half the voxel diagonal); they are taken
  as the single hypothesis `hcover`. The claim verified here is the
  *completeness* of the dilation relative to that seed coverage: no voxel
  within band distance of the surface is ever dropped.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

set_option linter.unusedSectionVars false

namespace Vdb

/-- A point of ℝ³. -/
abbrev P3R := Fin 3 → ℝ

/-- The lattice of voxel centers (in voxel units). -/
abbrev Lattice := Fin 3 → ℤ

/-- The Euclidean embedding of a lattice point. -/
def embed (p : Lattice) : P3R := fun i => (p i : ℝ)

/-- Squared Euclidean distance. -/
def distSq (a b : P3R) : ℝ := ∑ i, (a i - b i) ^ 2

/-- Euclidean distance (not a typeclass metric, to keep everything explicit). -/
noncomputable def edist (a b : P3R) : ℝ := Real.sqrt (distSq a b)

/-- L1 distance (one unit per unit axis). -/
def l1dist (a b : P3R) : ℝ := ∑ i, |a i - b i|

theorem distSq_nonneg (a b : P3R) : 0 ≤ distSq a b :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem edist_nonneg (a b : P3R) : 0 ≤ edist a b := Real.sqrt_nonneg _

theorem l1dist_nonneg (a b : P3R) : 0 ≤ l1dist a b :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **3D Cauchy–Schwarz**: `(∑|xᵢ|)² ≤ 3 · ∑xᵢ²`. -/
theorem cs_3 (x : P3R) : (∑ i, |x i|) ^ 2 ≤ 3 * ∑ i, x i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
    (fun i => |x i|) (fun _ => (1 : ℝ))
  have h2 : (∑ i, |x i| * 1) = ∑ i, |x i| :=
    Finset.sum_congr rfl fun _ _ => mul_one _
  have h3 : (∑ i, |x i| ^ 2) = ∑ i, x i ^ 2 :=
    Finset.sum_congr rfl fun i _ => sq_abs _
  have h4 : (∑ _i : Fin 3, (1 : ℝ) ^ 2) = 3 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  rw [h2, h3, h4] at h
  nlinarith [h]

/-- **L1 ≤ √3 · L2** in 3D. -/
theorem l1_le_sqrt3_distSq (x : P3R) :
    ∑ i, |x i| ≤ Real.sqrt 3 * Real.sqrt (∑ i, x i ^ 2) := by
  have h3 : (0:ℝ) ≤ 3 := by norm_num
  have hnn : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc ∑ i, |x i| ≤ Real.sqrt (3 * ∑ i, x i ^ 2) :=
        (Real.le_sqrt hnn (by positivity)).mpr (cs_3 x)
    _ = Real.sqrt 3 * Real.sqrt (∑ i, x i ^ 2) := Real.sqrt_mul h3 _

/-- **Minkowski** (triangle inequality) for the Euclidean norm on `ℝ³`. -/
theorem sqrt_sum_sq_add_sq_le (x y : P3R) :
    Real.sqrt (∑ i, (x i + y i) ^ 2) ≤
      Real.sqrt (∑ i, x i ^ 2) + Real.sqrt (∑ i, y i ^ 2) := by
  have hx : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hy : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum : ∑ i, (x i + y i) ^ 2 =
      (∑ i, x i ^ 2) + (∑ i, y i ^ 2) + 2 * ∑ i, x i * y i := by
    have e : ∀ i, (x i + y i) ^ 2 = x i ^ 2 + y i ^ 2 + 2 * (x i * y i) := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcs : (∑ i, x i * y i) ^ 2 ≤ (∑ i, x i ^ 2) * (∑ i, y i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hsq : ∑ i, x i * y i ≤ Real.sqrt ((∑ i, x i ^ 2) * (∑ i, y i ^ 2)) := by
    by_cases hs : ∑ i, x i * y i ≤ 0
    · exact le_trans hs (Real.sqrt_nonneg _)
    · exact (Real.le_sqrt (le_of_lt (not_le.mp hs)) (by positivity)).mpr hcs
  have eX : Real.sqrt (∑ i, x i ^ 2) ^ 2 = ∑ i, x i ^ 2 := Real.sq_sqrt hx
  have eY : Real.sqrt (∑ i, y i ^ 2) ^ 2 = ∑ i, y i ^ 2 := Real.sq_sqrt hy
  have hpc : Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2) =
      Real.sqrt ((∑ i, x i ^ 2) * (∑ i, y i ^ 2)) := by
    rw [← Real.sqrt_mul hx]
  have hfin : ∑ i, (x i + y i) ^ 2 ≤
      (Real.sqrt (∑ i, x i ^ 2) + Real.sqrt (∑ i, y i ^ 2)) ^ 2 := by
    have h1 : (Real.sqrt (∑ i, x i ^ 2) + Real.sqrt (∑ i, y i ^ 2)) ^ 2 =
        ∑ i, x i ^ 2 + ∑ i, y i ^ 2 +
          2 * Real.sqrt ((∑ i, x i ^ 2) * (∑ i, y i ^ 2)) := by
      have e2 : Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2) =
          Real.sqrt ((∑ i, x i ^ 2) * (∑ i, y i ^ 2)) := (Real.sqrt_mul hx _).symm
      nlinarith [eX, eY, e2]
    rw [hsum, h1]
    linarith [hsq]
  calc Real.sqrt (∑ i, (x i + y i) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ i, x i ^ 2) + Real.sqrt (∑ i, y i ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hfin
    _ = Real.sqrt (∑ i, x i ^ 2) + Real.sqrt (∑ i, y i ^ 2) := by
        rw [Real.sqrt_sq_eq_abs,
          abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]

/-- **Triangle inequality** for `edist`. -/
theorem edist_triangle (a b c : P3R) : edist a b ≤ edist a c + edist c b := by
  have h : ∑ i, (a i - b i) ^ 2 = ∑ i, ((a i - c i) + (c i - b i)) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  unfold edist distSq
  rw [h]
  exact sqrt_sum_sq_add_sq_le _ _

/-- **The narrow-band candidate predicate**: a voxel that is within L1 distance
    `layers` of some seed. A `k`-layer 6-neighbor dilation of the seeds is
    exactly this set (each layer adds exactly the shell at L1 distance `k`). -/
def inCandidate (seeds : Finset Lattice) (layers : ℕ) (v : Lattice) : Prop :=
  ∃ s ∈ seeds, l1dist (embed v) (embed s) ≤ (layers : ℝ)

/-- **T-BAND-COMPLETE** (the covering bound).

    Let `F ⊆ ℝ³` be the mesh surface, and suppose every point of `F` is within
    Euclidean distance `2/√3` (in voxel units) of some seed lattice point — the
    covering radius obtained by sampling every triangle at spacing ≤ `h/2` and
    snapping to nearest voxels. Then every lattice point `v` within Euclidean
    distance `< width` of the surface is a candidate:

    `∃ s ∈ S, l1dist(v, s) ≤ ⌈√3·width⌉ + 2`,

    i.e. the `⌈√3·width⌉ + 2` dilation layers of the C kernel reach it. -/
theorem band_complete (F : Set P3R) (S : Finset Lattice) {width : ℝ}
    (hcover : ∀ q ∈ F, ∃ s ∈ S, edist q (embed s) ≤ 2 / Real.sqrt 3)
    {v : Lattice} {q : P3R} (hqF : q ∈ F) (hv : edist (embed v) q < width) :
    inCandidate S (Nat.ceil (Real.sqrt 3 * width) + 2) v := by
  obtain ⟨s, hsS, hsq⟩ := hcover q hqF
  refine ⟨s, hsS, ?_⟩
  have h3 : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have h3n : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hsum : Real.sqrt 3 * (2 / Real.sqrt 3) = 2 := by field_simp
  have hdist : edist (embed v) (embed s) ≤ edist (embed v) q + edist q (embed s) :=
    edist_triangle _ _ _
  have hlev : l1dist (embed v) (embed s) ≤ Real.sqrt 3 * edist (embed v) (embed s) :=
    l1_le_sqrt3_distSq (fun i => embed v i - embed s i)
  have hlt : edist (embed v) q + edist q (embed s) < width + 2 / Real.sqrt 3 := by
    linarith
  calc l1dist (embed v) (embed s)
      ≤ Real.sqrt 3 * edist (embed v) (embed s) := hlev
    _ ≤ Real.sqrt 3 * (width + 2 / Real.sqrt 3) :=
        mul_le_mul_of_nonneg_left (le_trans hdist (le_of_lt hlt)) h3
    _ = Real.sqrt 3 * width + 2 := by rw [mul_add, hsum]
    _ ≤ ((Nat.ceil (Real.sqrt 3 * width) : ℝ)) + 2 := by
        have hceil := Nat.le_ceil (Real.sqrt 3 * width)
        linarith [hceil]
    _ = ((Nat.ceil (Real.sqrt 3 * width) + 2 : ℕ) : ℝ) := by
        push_cast
        ring


/-- **Tree-variant band completeness** (`tvdb_mesh_to_level_set`'s sparse path,
    whose candidate set is exactly the `⌈√3·width⌉ + 2`-layer dilation this
    module bounds): every voxel within Euclidean distance `< width` of the
    surface lies in the candidate/active set, i.e. the sparse tree covers the
    true band before the Eikonal solve starts. The coverage hypothesis and
    the conclusion are the same as the dense path — the candidate generator
    is shared; what differs is only that inactive voxels are treated as
    `∞` by the subsequent tree fast sweeping, which is *not* covered by
    this theorem (see VERIFICATION.md, open items). -/
theorem band_complete_tree {F : Set P3R} (S : Finset Lattice) {width : ℝ}
    (hcover : ∀ q ∈ F, ∃ s ∈ S, edist q (embed s) ≤ 2 / Real.sqrt 3)
    {v : Lattice} {q : P3R} (hqF : q ∈ F) (hv : edist (embed v) q < width) :
    inCandidate S (Nat.ceil (Real.sqrt 3 * width) + 2) v :=
  band_complete F S hcover hqF hv

end Vdb
