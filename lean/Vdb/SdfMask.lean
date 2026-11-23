/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Pointwise models of the two dense SDF utility grids used by the physics
  pipeline: the fog volume (`tvdb_sdf_to_fog_volume`) and the interior mask
  (`tvdb_sdf_interior_mask`). Both are pointwise functions of a single sample,
  so their contracts are exact order statements over ℝ; aliasing safety is
  `congr` of the underlying field. The band parameter is `half_width *
  voxel_size` in the C API, and is required to be strictly positive here.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.LevelSet

noncomputable section

open scoped RealInnerProductSpace

namespace Vdb

/-- Fog density `clamp(-φ/band, 0, 1)` for a strictly positive band. -/
def fogVolume (φ : Point → ℝ) (band : ℝ) (p : Point) : ℝ :=
  max (min (-φ p / band) 1) 0

theorem fogVolume_nonneg (φ : Point → ℝ) (band : ℝ) (p : Point) :
    0 ≤ fogVolume φ band p := by
  unfold fogVolume
  exact le_max_right _ _

theorem fogVolume_le_one (φ : Point → ℝ) (band : ℝ) (p : Point) :
    fogVolume φ band p ≤ 1 := by
  unfold fogVolume
  exact max_le (min_le_right _ _) zero_le_one

theorem fogVolume_eq_zero_of_nonneg {φ : Point → ℝ} {band : ℝ} {p : Point}
    (hb : 0 < band) (hφ : 0 ≤ φ p) : fogVolume φ band p = 0 := by
  unfold fogVolume
  have hx : -φ p / band ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hφ) (le_of_lt hb)
  exact max_eq_right (le_trans (min_le_left _ _) hx)

/-- The fog volume is positive exactly at strictly negative samples. -/
theorem fogVolume_pos_iff {φ : Point → ℝ} {band : ℝ} {p : Point} (hb : 0 < band) :
    0 < fogVolume φ band p ↔ φ p < 0 := by
  constructor
  · intro h
    rw [fogVolume, lt_max_iff] at h
    rcases h with hmin | hzero
    · have hx : 0 < -φ p / band := lt_of_lt_of_le hmin (min_le_left _ _)
      have hx' := mul_lt_mul_of_pos_right hx hb
      rw [zero_mul, div_mul_cancel₀ _ (ne_of_gt hb)] at hx'
      linarith
    · exact (lt_irrefl (0 : ℝ) hzero).elim
  · intro hφ
    rw [fogVolume, lt_max_iff]
    exact Or.inl (lt_min (div_pos (neg_pos.mpr hφ) hb) zero_lt_one)

/-- The fog volume saturates at one exactly at samples at least one band deep. -/
theorem fogVolume_eq_one_iff {φ : Point → ℝ} {band : ℝ} {p : Point} (hb : 0 < band) :
    fogVolume φ band p = 1 ↔ φ p ≤ -band := by
  constructor
  · intro h
    unfold fogVolume at h
    have hge : 0 ≤ min (-φ p / band) 1 := by
      by_contra hn
      have hle : min (-φ p / band) 1 ≤ 0 := le_of_not_ge hn
      have hz : max (min (-φ p / band) 1) 0 = 0 := max_eq_right hle
      rw [hz] at h
      norm_num at h
    have hmin : min (-φ p / band) 1 = 1 := by
      apply le_antisymm (min_le_right _ _)
      have hm : max (min (-φ p / band) 1) 0 = min (-φ p / band) 1 := max_eq_left hge
      have hm_eq : min (-φ p / band) 1 = 1 := by rwa [hm] at h
      exact le_of_eq hm_eq.symm
    have hone : 1 ≤ -φ p / band := min_eq_right_iff.mp hmin
    have hmul := mul_le_mul_of_nonneg_right hone (le_of_lt hb)
    rw [one_mul, div_mul_cancel₀ _ (ne_of_gt hb)] at hmul
    linarith
  · intro hφ
    unfold fogVolume
    have hone : 1 ≤ -φ p / band := (le_div_iff₀ hb).mpr (by nlinarith)
    rw [min_eq_right hone, max_eq_left zero_le_one]

theorem fogVolume_pointwise {φ ψ : Point → ℝ} {band : ℝ} {p : Point}
    (h : φ p = ψ p) : fogVolume φ band p = fogVolume ψ band p := by
  simp [fogVolume, h]

theorem fogVolume_congr {φ ψ : Point → ℝ} {band : ℝ} (h : ∀ p, φ p = ψ p) :
    fogVolume φ band = fogVolume ψ band := by
  funext p
  exact fogVolume_pointwise (h p)

/-- Interior mask: `1` where `φ < c`, else `0` (`tvdb_sdf_interior_mask`). -/
def interiorMask (φ : Point → ℝ) (c : ℝ) (p : Point) : ℝ :=
  if φ p < c then 1 else 0

theorem interiorMask_eq_one_iff {φ : Point → ℝ} {c : ℝ} {p : Point} :
    interiorMask φ c p = 1 ↔ φ p < c := by
  by_cases h : φ p < c <;> simp [interiorMask, h]

theorem interiorMask_eq_zero_iff {φ : Point → ℝ} {c : ℝ} {p : Point} :
    interiorMask φ c p = 0 ↔ ¬ φ p < c := by
  by_cases h : φ p < c <;> simp [interiorMask, h]

theorem interiorMask_nonneg (φ : Point → ℝ) (c : ℝ) (p : Point) :
    0 ≤ interiorMask φ c p := by
  by_cases h : φ p < c <;> simp [interiorMask, h]

theorem interiorMask_le_one (φ : Point → ℝ) (c : ℝ) (p : Point) :
    interiorMask φ c p ≤ 1 := by
  by_cases h : φ p < c <;> simp [interiorMask, h]

theorem interiorMask_pointwise {φ ψ : Point → ℝ} {c : ℝ} {p : Point}
    (h : φ p = ψ p) : interiorMask φ c p = interiorMask ψ c p := by
  simp [interiorMask, h]

theorem interiorMask_congr {φ ψ : Point → ℝ} {c : ℝ} (h : ∀ p, φ p = ψ p) :
    interiorMask φ c = interiorMask ψ c := by
  funext p
  exact interiorMask_pointwise (h p)

end Vdb
