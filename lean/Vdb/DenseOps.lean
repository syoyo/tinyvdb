/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Ops/Dense remainder (`plan-lean.md` §3.2): the `v = (w − o)/h − 0.5`
  coordinate change, the `[-1, dim−1]` clamp used by every C sampling path
  (`tvdb_sample_coord` / `tvdb_sample_floor`), the gradient Lipschitz bound
  of the trilinear interpolant, and the connection to the C `tvdb_at`
  accessor.

  * `sampleCoord` is the rational model of `tvdb_sample_coord`: `v < -1 ↦ -1`,
    `v ≥ dim − 1 ↦ dim − 1`, else `v` (NaN ↦ 0 in C is out of scope —
    `Vdb/FloatNan.lean` covers NaN semantics).
  * `sampleFloor` is the rational model of `tvdb_sample_floor`: `-1` below
    the grid, `dim − 1` at/above the last voxel, `⌊x⌋` strictly inside.
  * `worldToVoxel`/`voxelToWorld` pin the world↔voxel maps to each other
    (`w = o + (i + 1/2)·h ↔ v = (w − o)/h − 1/2`); `cellCenter_eq_voxelToWorld`
    and the round trips make the connection to `crid` sampling explicit.
  * **Gradient Lipschitz bound**: trilinear interpolation is affine in each
    axis with slope a convex combination of the four relevant edge
    differences, hence bounded by their max (`trilinear_lipschitz_x/_y/_z`
    `trilinear_lipschitz`).
  * Connection to `tvdb_at`: `clampIdx`/`atClamped` (in `Vdb/Sample.lean`)
    model the C edge-clamped accessor and its in-bounds equality law; this
    module's `worldToVoxel`/`voxelToWorld` are the world↔voxel adapters the
    C sampling uses to reach it, and `sampleCoord_mem_Icc` is the exact
    `[-1, dim−1]` invariant behind `tvdb_sample_coord`.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Sample
import Mathlib.Tactic

namespace Vdb

/-! ## The coordinate change world ↔ voxel -/

/-- Voxel-index coordinate of world position `w` on a grid starting at `o`
    with voxel size `h`: `v = (w − o)/h − 0.5`. -/
def worldToVoxel (o h : ℚ) (w : ℚ) : ℚ := (w - o) / h - 1 / 2

/-- World position of voxel-centre index `i` (`o + (i + 1/2)·h`). -/
def voxelToWorld (o h : ℚ) (i : ℚ) : ℚ := o + (i + 1 / 2) * h

/-- The `tvdb_sample_coord` clamp (rational model; NaN is out of scope). -/
def sampleCoord (x : ℚ) (dim : ℕ) : ℚ :=
  if x < -1 then -1 else if x ≥ (dim : ℚ) - 1 then (dim : ℚ) - 1 else x

/-- `sampleCoord` lands in `[-1, dim−1]` — the invariant the C clamps
    establish before any indexing. -/
theorem sampleCoord_mem_Icc (x : ℚ) (dim : ℕ) :
    -1 ≤ sampleCoord x dim ∧ sampleCoord x dim ≤ (dim : ℚ) - 1 := by
  unfold sampleCoord
  split_ifs with h1 h2
  · constructor <;> linarith
  · constructor <;> linarith
  · constructor <;> linarith

/-- Inside the grid, `sampleCoord` is the identity. -/
theorem sampleCoord_eq_self (x : ℚ) (dim : ℕ) (h0 : -1 ≤ x) (h1 : x ≤ (dim : ℚ) - 1) :
    sampleCoord x dim = x := by
  unfold sampleCoord
  split_ifs with h h2
  · linarith
  · linarith
  · rfl

/-- The C `tvdb_sample_floor` (rational model; NaN is out of scope). -/
def sampleFloor (x : ℚ) (dim : ℕ) : ℤ :=
  if x < 0 then -1 else if x ≥ (dim : ℚ) - 1 then ((dim : ℤ) - 1) else ⌊x⌋

/-- `sampleFloor` lands in `[-1, dim−1]` for `dim ≥ 1`. -/
theorem sampleFloor_bounds (x : ℚ) (dim : ℕ) (hd : 1 ≤ dim) :
    -1 ≤ sampleFloor x dim ∧ sampleFloor x dim ≤ (dim : ℤ) - 1 := by
  unfold sampleFloor
  split_ifs with h1 h2
  · constructor <;> omega
  · constructor <;> omega
  · constructor
    · have hcast : (-1 : ℚ) ≤ x := by linarith
      exact Int.le_floor.mpr (by exact_mod_cast hcast)
    · have hlt : x < (dim : ℚ) - 1 := by linarith
      have hflq : ((⌊x⌋ : ℤ) : ℚ) ≤ x := by
        have := Int.floor_le x
        exact_mod_cast this
      have hcastd : (1 : ℚ) ≤ (dim : ℚ) := by exact_mod_cast hd
      have hlt' : ((⌊x⌋ : ℤ) : ℚ) < (dim : ℚ) - 1 := by linarith
      have : (⌊x⌋ : ℤ) < dim - 1 := by exact_mod_cast hlt'
      omega

/-- The world→voxel→world round trip is the identity (as rationals). -/
theorem voxelToWorld_worldToVoxel (o h : ℚ) (w : ℚ) (hh : h ≠ 0) :
    voxelToWorld o h (worldToVoxel o h w) = w := by
  unfold worldToVoxel voxelToWorld
  field_simp
  ring

/-- The world→voxel→world round trip is the identity (as rationals). -/
theorem worldToVoxel_voxelToWorld (o h : ℚ) (i : ℚ) (hh : h ≠ 0) :
    worldToVoxel o h (voxelToWorld o h i) = i := by
  unfold worldToVoxel voxelToWorld
  field_simp
  ring

/-- `cellCenter o h i = voxelToWorld o h i` for natural `i`. -/
theorem cellCenter_eq_voxelToWorld (o h : ℚ) (i : ℕ) :
    cellCenter o h i = voxelToWorld o h (i : ℚ) := by
  unfold cellCenter voxelToWorld
  ring

/-! ## The gradient Lipschitz bound -/

/-- Edge differences of one cell: `xEdgeLip` bounds the four x-parallel
    edges, `yEdgeLip` the four y-parallel edges, `zEdgeLip` the four
    z-parallel edges. -/
def xEdgeLip (g : Fin 2 → Fin 2 → Fin 2 → ℚ) : ℚ :=
  max (max (max |g 1 0 0 - g 0 0 0| |g 1 0 1 - g 0 0 1|)
           (max |g 1 1 0 - g 0 1 0| |g 1 1 1 - g 0 1 1|)) 0

def yEdgeLip (g : Fin 2 → Fin 2 → Fin 2 → ℚ) : ℚ :=
  max (max (max |g 0 1 0 - g 0 0 0| |g 0 1 1 - g 0 0 1|)
           (max |g 1 1 0 - g 1 0 0| |g 1 1 1 - g 1 0 1|)) 0

def zEdgeLip (g : Fin 2 → Fin 2 → Fin 2 → ℚ) : ℚ :=
  max (max (max |g 0 0 1 - g 0 0 0| |g 0 1 1 - g 0 1 0|)
           (max |g 1 0 1 - g 1 0 0| |g 1 1 1 - g 1 1 0|)) 0

private theorem le_edgeLip_x00 (g : Fin 2 → Fin 2 → Fin 2 → ℚ) :
    |g 1 0 0 - g 0 0 0| ≤ xEdgeLip g :=
  le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))

private theorem le_edgeLip_x01 (g : Fin 2 → Fin 2 → Fin 2 → ℚ) :
    |g 1 0 1 - g 0 0 1| ≤ xEdgeLip g :=
  le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))

private theorem le_edgeLip_x10 (g : Fin 2 → Fin 2 → Fin 2 → ℚ) :
    |g 1 1 0 - g 0 1 0| ≤ xEdgeLip g :=
  le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))

private theorem le_edgeLip_x11 (g : Fin 2 → Fin 2 → Fin 2 → ℚ) :
    |g 1 1 1 - g 0 1 1| ≤ xEdgeLip g :=
  le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))

private theorem le_edgeLip_y00 (g : Fin 2 → Fin 2 → Fin 2 → ℚ) :
    |g 0 1 0 - g 0 0 0| ≤ yEdgeLip g :=
  le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))

private theorem le_edgeLip_y01 (g : Fin 2 → Fin 2 → Fin 2 → ℚ) :
    |g 0 1 1 - g 0 0 1| ≤ yEdgeLip g :=
  le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))

private theorem le_edgeLip_y10 (g : Fin 2 → Fin 2 → Fin 2 → ℚ) :
    |g 1 1 0 - g 1 0 0| ≤ yEdgeLip g :=
  le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))

private theorem le_edgeLip_y11 (g : Fin 2 → Fin 2 → Fin 2 → ℚ) :
    |g 1 1 1 - g 1 0 1| ≤ yEdgeLip g :=
  le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))

private theorem le_edgeLip_z00 (g : Fin 2 → Fin 2 → Fin 2 → ℚ) :
    |g 0 0 1 - g 0 0 0| ≤ zEdgeLip g :=
  le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))

private theorem le_edgeLip_z01 (g : Fin 2 → Fin 2 → Fin 2 → ℚ) :
    |g 0 1 1 - g 0 1 0| ≤ zEdgeLip g :=
  le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))

private theorem le_edgeLip_z10 (g : Fin 2 → Fin 2 → Fin 2 → ℚ) :
    |g 1 0 1 - g 1 0 0| ≤ zEdgeLip g :=
  le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))

private theorem le_edgeLip_z11 (g : Fin 2 → Fin 2 → Fin 2 → ℚ) :
    |g 1 1 1 - g 1 1 0| ≤ zEdgeLip g :=
  le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))

/-- Four non-negative coefficients summing to 1 map a bounded family into
    the bound. -/
private theorem quad_abs_le {w00 w01 w10 w11 : ℚ}
    (h00 : 0 ≤ w00) (h01 : 0 ≤ w01) (h10 : 0 ≤ w10) (h11 : 0 ≤ w11)
    (hsum : w00 + w01 + w10 + w11 = 1)
    {e00 e01 e10 e11 : ℚ} {M : ℚ} (h00c : |e00| ≤ M) (h01c : |e01| ≤ M)
    (h10c : |e10| ≤ M) (h11c : |e11| ≤ M) :
    |w00 * e00 + w01 * e01 + w10 * e10 + w11 * e11| ≤ M := by
  have e00le : |w00 * e00| ≤ w00 * M := by
    rw [abs_mul, abs_of_nonneg h00]
    exact mul_le_mul_of_nonneg_left h00c h00
  have e01le : |w01 * e01| ≤ w01 * M := by
    rw [abs_mul, abs_of_nonneg h01]
    exact mul_le_mul_of_nonneg_left h01c h01
  have e10le : |w10 * e10| ≤ w10 * M := by
    rw [abs_mul, abs_of_nonneg h10]
    exact mul_le_mul_of_nonneg_left h10c h10
  have e11le : |w11 * e11| ≤ w11 * M := by
    rw [abs_mul, abs_of_nonneg h11]
    exact mul_le_mul_of_nonneg_left h11c h11
  calc |w00 * e00 + w01 * e01 + w10 * e10 + w11 * e11|
      ≤ |w00 * e00 + w01 * e01 + w10 * e10| + |w11 * e11| := abs_add_le _ _
    _ ≤ (|w00 * e00 + w01 * e01| + |w10 * e10|) + |w11 * e11| := by
        have := abs_add_le (w00 * e00 + w01 * e01) (w10 * e10)
        linarith
    _ ≤ (|w00 * e00| + |w01 * e01| + |w10 * e10|) + |w11 * e11| := by
        have := abs_add_le (w00 * e00) (w01 * e01)
        linarith
    _ ≤ (w00 * M + w01 * M + w10 * M) + w11 * M := by linarith
    _ = w00 * M + w01 * M + w10 * M + w11 * M := by ring
    _ = M * (w00 + w01 + w10 + w11) := by ring
    _ = M := by rw [hsum, mul_one]

/-- **Gradient Lipschitz bound, x axis**: at fixed `y, z ∈ [0, 1]` the
    trilinear interpolant is affine in `x` with slope bounded by the largest
    x-edge difference. -/
theorem trilinear_lipschitz_x (g : Fin 2 → Fin 2 → Fin 2 → ℚ)
    (y z : ℚ) (hy : 0 ≤ y) (hy' : y ≤ 1) (hz : 0 ≤ z) (hz' : z ≤ 1)
    (x₁ x₂ : ℚ) :
    |trilinear g x₁ y z - trilinear g x₂ y z| ≤ xEdgeLip g * |x₁ - x₂| := by
  have h01 : (0 : ℚ) ≤ 1 - y := by linarith
  have hz01 : (0 : ℚ) ≤ 1 - z := by linarith
  have hsum : ((1 - y) * (1 - z)) + (y * (1 - z)) + ((1 - y) * z) + (y * z) = 1 := by
    nlinarith
  have hslope : |(1 - y) * (1 - z) * (g 1 0 0 - g 0 0 0) +
      y * (1 - z) * (g 1 1 0 - g 0 1 0) +
      (1 - y) * z * (g 1 0 1 - g 0 0 1) +
      y * z * (g 1 1 1 - g 0 1 1)| ≤ xEdgeLip g :=
    quad_abs_le (mul_nonneg h01 hz01) (mul_nonneg hy hz01) (mul_nonneg h01 hz) (mul_nonneg hy hz)
      hsum (le_edgeLip_x00 g) (le_edgeLip_x10 g) (le_edgeLip_x01 g) (le_edgeLip_x11 g)
  have h1 : trilinear g x₁ y z =
      (1 - x₁) * ((1 - y) * (1 - z) * g 0 0 0 + y * (1 - z) * g 0 1 0 +
                  (1 - y) * z * g 0 0 1 + y * z * g 0 1 1) +
      x₁ * ((1 - y) * (1 - z) * g 1 0 0 + y * (1 - z) * g 1 1 0 +
            (1 - y) * z * g 1 0 1 + y * z * g 1 1 1) := by
    simp [trilinear]; ring
  have h2 : trilinear g x₂ y z =
      (1 - x₂) * ((1 - y) * (1 - z) * g 0 0 0 + y * (1 - z) * g 0 1 0 +
                  (1 - y) * z * g 0 0 1 + y * z * g 0 1 1) +
      x₂ * ((1 - y) * (1 - z) * g 1 0 0 + y * (1 - z) * g 1 1 0 +
            (1 - y) * z * g 1 0 1 + y * z * g 1 1 1) := by
    simp [trilinear]; ring
  have hdiff : trilinear g x₁ y z - trilinear g x₂ y z =
      ((1 - y) * (1 - z) * (g 1 0 0 - g 0 0 0) +
       y * (1 - z) * (g 1 1 0 - g 0 1 0) +
       (1 - y) * z * (g 1 0 1 - g 0 0 1) +
       y * z * (g 1 1 1 - g 0 1 1)) * (x₁ - x₂) := by
    rw [h1, h2]; ring
  rw [hdiff, abs_mul]
  exact mul_le_mul_of_nonneg_right hslope (abs_nonneg _)

/-- **Gradient Lipschitz bound, y axis**. -/
theorem trilinear_lipschitz_y (g : Fin 2 → Fin 2 → Fin 2 → ℚ)
    (x z : ℚ) (hx : 0 ≤ x) (hx' : x ≤ 1) (hz : 0 ≤ z) (hz' : z ≤ 1)
    (y₁ y₂ : ℚ) :
    |trilinear g x y₁ z - trilinear g x y₂ z| ≤ yEdgeLip g * |y₁ - y₂| := by
  have h01 : (0 : ℚ) ≤ 1 - x := by linarith
  have hz01 : (0 : ℚ) ≤ 1 - z := by linarith
  have hsum : ((1 - x) * (1 - z)) + (x * (1 - z)) + ((1 - x) * z) + (x * z) = 1 := by
    nlinarith
  have hslope : |(1 - x) * (1 - z) * (g 0 1 0 - g 0 0 0) +
      x * (1 - z) * (g 1 1 0 - g 1 0 0) +
      (1 - x) * z * (g 0 1 1 - g 0 0 1) +
      x * z * (g 1 1 1 - g 1 0 1)| ≤ yEdgeLip g :=
    quad_abs_le (mul_nonneg h01 hz01) (mul_nonneg hx hz01) (mul_nonneg h01 hz) (mul_nonneg hx hz)
      hsum (le_edgeLip_y00 g) (le_edgeLip_y10 g) (le_edgeLip_y01 g) (le_edgeLip_y11 g)
  have h1 : trilinear g x y₁ z =
      (1 - y₁) * ((1 - x) * (1 - z) * g 0 0 0 + x * (1 - z) * g 1 0 0 +
                  (1 - x) * z * g 0 0 1 + x * z * g 1 0 1) +
      y₁ * ((1 - x) * (1 - z) * g 0 1 0 + x * (1 - z) * g 1 1 0 +
            (1 - x) * z * g 0 1 1 + x * z * g 1 1 1) := by
    simp [trilinear]; ring
  have h2 : trilinear g x y₂ z =
      (1 - y₂) * ((1 - x) * (1 - z) * g 0 0 0 + x * (1 - z) * g 1 0 0 +
                  (1 - x) * z * g 0 0 1 + x * z * g 1 0 1) +
      y₂ * ((1 - x) * (1 - z) * g 0 1 0 + x * (1 - z) * g 1 1 0 +
            (1 - x) * z * g 0 1 1 + x * z * g 1 1 1) := by
    simp [trilinear]; ring
  have hdiff : trilinear g x y₁ z - trilinear g x y₂ z =
      ((1 - x) * (1 - z) * (g 0 1 0 - g 0 0 0) +
       x * (1 - z) * (g 1 1 0 - g 1 0 0) +
       (1 - x) * z * (g 0 1 1 - g 0 0 1) +
       x * z * (g 1 1 1 - g 1 0 1)) * (y₁ - y₂) := by
    rw [h1, h2]; ring
  rw [hdiff, abs_mul]
  exact mul_le_mul_of_nonneg_right hslope (abs_nonneg _)

/-- **Gradient Lipschitz bound, z axis**. -/
theorem trilinear_lipschitz_z (g : Fin 2 → Fin 2 → Fin 2 → ℚ)
    (x y : ℚ) (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ 1)
    (z₁ z₂ : ℚ) :
    |trilinear g x y z₁ - trilinear g x y z₂| ≤ zEdgeLip g * |z₁ - z₂| := by
  have h01 : (0 : ℚ) ≤ 1 - x := by linarith
  have hy01 : (0 : ℚ) ≤ 1 - y := by linarith
  have hsum : ((1 - x) * (1 - y)) + (x * (1 - y)) + ((1 - x) * y) + (x * y) = 1 := by
    nlinarith
  have hslope : |(1 - x) * (1 - y) * (g 0 0 1 - g 0 0 0) +
      x * (1 - y) * (g 1 0 1 - g 1 0 0) +
      (1 - x) * y * (g 0 1 1 - g 0 1 0) +
      x * y * (g 1 1 1 - g 1 1 0)| ≤ zEdgeLip g :=
    quad_abs_le (mul_nonneg h01 hy01) (mul_nonneg hx hy01) (mul_nonneg h01 hy) (mul_nonneg hx hy)
      hsum (le_edgeLip_z00 g) (le_edgeLip_z10 g) (le_edgeLip_z01 g) (le_edgeLip_z11 g)
  have h1 : trilinear g x y z₁ =
      (1 - z₁) * ((1 - x) * (1 - y) * g 0 0 0 + x * (1 - y) * g 1 0 0 +
                  (1 - x) * y * g 0 1 0 + x * y * g 1 1 0) +
      z₁ * ((1 - x) * (1 - y) * g 0 0 1 + x * (1 - y) * g 1 0 1 +
            (1 - x) * y * g 0 1 1 + x * y * g 1 1 1) := by
    simp [trilinear]; ring
  have h2 : trilinear g x y z₂ =
      (1 - z₂) * ((1 - x) * (1 - y) * g 0 0 0 + x * (1 - y) * g 1 0 0 +
                  (1 - x) * y * g 0 1 0 + x * y * g 1 1 0) +
      z₂ * ((1 - x) * (1 - y) * g 0 0 1 + x * (1 - y) * g 1 0 1 +
            (1 - x) * y * g 0 1 1 + x * y * g 1 1 1) := by
    simp [trilinear]; ring
  have hdiff : trilinear g x y z₁ - trilinear g x y z₂ =
      ((1 - x) * (1 - y) * (g 0 0 1 - g 0 0 0) +
       x * (1 - y) * (g 1 0 1 - g 1 0 0) +
       (1 - x) * y * (g 0 1 1 - g 0 1 0) +
       x * y * (g 1 1 1 - g 1 1 0)) * (z₁ - z₂) := by
    rw [h1, h2]; ring
  rw [hdiff, abs_mul]
  exact mul_le_mul_of_nonneg_right hslope (abs_nonneg _)

/-- **Gradient Lipschitz bound (full)**: for `x, x', y, y', z, z' ∈ [0, 1]`,
    the trilinear interpolant satisfies
    `|f(p) − f(q)| ≤ xLip·|Δx| + yLip·|Δy| + zLip·|Δz|`. -/
theorem trilinear_lipschitz (g : Fin 2 → Fin 2 → Fin 2 → ℚ)
    (x₁ x₂ y₁ y₂ z₁ z₂ : ℚ)
    (_hx₁ : 0 ≤ x₁) (_hx₁' : x₁ ≤ 1) (hx₂ : 0 ≤ x₂) (hx₂' : x₂ ≤ 1)
    (hy₁ : 0 ≤ y₁) (hy₁' : y₁ ≤ 1) (hy₂ : 0 ≤ y₂) (hy₂' : y₂ ≤ 1)
    (hz₁ : 0 ≤ z₁) (hz₁' : z₁ ≤ 1) (_hz₂ : 0 ≤ z₂) (_hz₂' : z₂ ≤ 1) :
    |trilinear g x₁ y₁ z₁ - trilinear g x₂ y₂ z₂|
      ≤ xEdgeLip g * |x₁ - x₂| + yEdgeLip g * |y₁ - y₂| + zEdgeLip g * |z₁ - z₂| := by
  have hexp : trilinear g x₁ y₁ z₁ - trilinear g x₂ y₂ z₂ =
      (trilinear g x₁ y₁ z₁ - trilinear g x₂ y₁ z₁) +
      (trilinear g x₂ y₁ z₁ - trilinear g x₂ y₂ z₁) +
      (trilinear g x₂ y₂ z₁ - trilinear g x₂ y₂ z₂) := by ring
  have hxy1 : |trilinear g x₁ y₁ z₁ - trilinear g x₂ y₁ z₁| ≤ xEdgeLip g * |x₁ - x₂| :=
    trilinear_lipschitz_x g y₁ z₁ hy₁ hy₁' hz₁ hz₁' x₁ x₂
  have hyy : |trilinear g x₂ y₁ z₁ - trilinear g x₂ y₂ z₁| ≤ yEdgeLip g * |y₁ - y₂| :=
    trilinear_lipschitz_y g x₂ z₁ hx₂ hx₂' hz₁ hz₁' y₁ y₂
  have hzz : |trilinear g x₂ y₂ z₁ - trilinear g x₂ y₂ z₂| ≤ zEdgeLip g * |z₁ - z₂| :=
    trilinear_lipschitz_z g x₂ y₂ hx₂ hx₂' hy₂ hy₂' z₁ z₂
  rw [hexp]
  calc |(trilinear g x₁ y₁ z₁ - trilinear g x₂ y₁ z₁) +
        (trilinear g x₂ y₁ z₁ - trilinear g x₂ y₂ z₁) +
        (trilinear g x₂ y₂ z₁ - trilinear g x₂ y₂ z₂)|
      ≤ |trilinear g x₁ y₁ z₁ - trilinear g x₂ y₁ z₁| +
        |trilinear g x₂ y₁ z₁ - trilinear g x₂ y₂ z₁| +
        |trilinear g x₂ y₂ z₁ - trilinear g x₂ y₂ z₂| := by
        have h1 := abs_add_le (trilinear g x₁ y₁ z₁ - trilinear g x₂ y₁ z₁ +
          (trilinear g x₂ y₁ z₁ - trilinear g x₂ y₂ z₁))
          (trilinear g x₂ y₂ z₁ - trilinear g x₂ y₂ z₂)
        have h2 := abs_add_le (trilinear g x₁ y₁ z₁ - trilinear g x₂ y₁ z₁)
          (trilinear g x₂ y₁ z₁ - trilinear g x₂ y₂ z₁)
        linarith [h1, h2]
    _ ≤ xEdgeLip g * |x₁ - x₂| + yEdgeLip g * |y₁ - y₂| + zEdgeLip g * |z₁ - z₂| := by
        linarith [hxy1, hyy, hzz]

end Vdb
