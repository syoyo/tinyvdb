/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Geometry base — dense grids and trilinear sampling (plan-lean.md, §3.1).

  This module formalizes, over ℚ:

  * the dense grid model: dimensions, the x-fastest linear index bijection
    (`GridDims.index` / `GridDims.unindex`, with both round trips),
    cell-centred voxel positions, and the edge-clamped grid accessor
    (`atClamped`, the `tvdb_at`-style clamp);
  * trilinear interpolation over one cell: the eight corner weights,
    every corner weight non-negative on the unit cube, their **sum is 1**
    (partition of unity), the interpolant **interpolates at voxel centres**
    (integer fractional coordinates hit the corner values), its value lies
    between the minimum and maximum of the eight corners (convex
    combination), and the **splat is the adjoint of the sample** — the
    identity `s * trilinear g x y z = cornerInner g (splat x y z s)`, which
    is exactly what a mesh-to-grid scatter/gather pair needs.

  What is *not* modelled yet: the `v = (w - o)/h - 0.5` coordinate change
  and the `[-1, dim-1]` clamp (they are arithmetic rewrites, planned with
  the full dense grid model in a follow-up), the gradient Lipschitz bound,
  and any connection to the `tvdb_at` C implementation.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

set_option linter.unusedSectionVars false

namespace Vdb

/-! ## The dense grid model -/

/-- Dimensions of a dense grid. -/
structure GridDims where
  nx : ℕ
  ny : ℕ
  nz : ℕ

/-- The x-fastest linear index of voxel `(x, y, z)`. -/
def GridDims.index (d : GridDims) (x y z : ℕ) : ℕ :=
  x + y * d.nx + z * (d.nx * d.ny)

/-- The inverse of `GridDims.index`. -/
def GridDims.unindex (d : GridDims) (i : ℕ) : ℕ × ℕ × ℕ :=
  (i % d.nx, (i / d.nx) % d.ny, i / (d.nx * d.ny))

theorem GridDims.index_lt (d : GridDims) {x y z : ℕ} (hx : x < d.nx) (hy : y < d.ny)
    (hz : z < d.nz) : d.index x y z < d.nx * d.ny * d.nz := by
  have hx' : (x : ℝ) + 1 ≤ (d.nx : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr hx
  have hy' : (y : ℝ) + 1 ≤ (d.ny : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr hy
  have hz' : (z : ℝ) + 1 ≤ (d.nz : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr hz
  have hnx : (0 : ℝ) ≤ d.nx := Nat.cast_nonneg _
  have hny : (0 : ℝ) ≤ d.ny := Nat.cast_nonneg _
  have hnz : (0 : ℝ) ≤ d.nz := Nat.cast_nonneg _
  have hx1 : (x : ℝ) ≤ (d.nx : ℝ) - 1 := by linarith
  have hy1 : (y : ℝ) ≤ (d.ny : ℝ) - 1 := by linarith
  have h1 : (x : ℝ) + (y : ℝ) * (d.nx : ℝ) ≤ (d.nx : ℝ) * (d.ny : ℝ) - 1 := by
    have hynx := mul_le_mul_of_nonneg_right hy1 hnx
    nlinarith [hx1, hynx]
  have hz1 : (1 : ℝ) ≤ (d.nz : ℝ) - (z : ℝ) := by linarith
  have hprod : (d.nx : ℝ) * (d.ny : ℝ) ≤ ((d.nz : ℝ) - (z : ℝ)) * ((d.nx : ℝ) * (d.ny : ℝ)) := by
    calc (d.nx : ℝ) * (d.ny : ℝ) = 1 * ((d.nx : ℝ) * (d.ny : ℝ)) := by ring
      _ ≤ ((d.nz : ℝ) - (z : ℝ)) * ((d.nx : ℝ) * (d.ny : ℝ)) :=
          mul_le_mul_of_nonneg_right hz1 (mul_nonneg hnx hny)
  have h2 : (z : ℝ) * (d.nx : ℝ) * (d.ny : ℝ) + (d.nx : ℝ) * (d.ny : ℝ) ≤
      (d.nx : ℝ) * (d.ny : ℝ) * (d.nz : ℝ) := by
    nlinarith [hprod]
  have h : (d.index x y z : ℝ) ≤ (d.nx : ℝ) * (d.ny : ℝ) * (d.nz : ℝ) - 1 := by
    unfold GridDims.index
    push_cast
    nlinarith [h1, h2]
  have : (d.index x y z : ℝ) < (d.nx : ℝ) * (d.ny : ℝ) * (d.nz : ℝ) := by linarith
  exact_mod_cast this

theorem GridDims.index_unindex (d : GridDims) (i : ℕ) :
    d.index (i % d.nx) ((i / d.nx) % d.ny) (i / (d.nx * d.ny)) = i := by
  unfold GridDims.index
  have e1 : i % d.nx + (i / d.nx) * d.nx = i := by
    rw [Nat.mul_comm]
    exact Nat.mod_add_div i d.nx
  have e2 : (i / d.nx) % d.ny * d.nx + ((i / d.nx) / d.ny * d.nx) * d.ny =
      (i / d.nx) * d.nx := by
    have h := Nat.mod_add_div (i / d.nx) d.ny
    rw [Nat.mul_comm d.ny ((i / d.nx) / d.ny)] at h
    calc (i / d.nx) % d.ny * d.nx + ((i / d.nx) / d.ny * d.nx) * d.ny
        = ((i / d.nx) % d.ny + (i / d.nx) / d.ny * d.ny) * d.nx := by ring
      _ = (i / d.nx) * d.nx := by rw [h]
  have h3 : (i / d.nx) / d.ny = i / (d.nx * d.ny) := Nat.div_div_eq_div_mul i d.nx d.ny
  rw [h3] at e2
  nlinarith [e1, e2, Nat.mul_comm d.ny d.nx]

theorem GridDims.unindex_index (d : GridDims) {x y z : ℕ} (hx : x < d.nx) (hy : y < d.ny)
    (_hz : z < d.nz) : d.unindex (d.index x y z) = (x, y, z) := by
  unfold GridDims.unindex GridDims.index
  have hnx : 0 < d.nx := by omega
  have hny : 0 < d.ny := by omega
  have hfac : x + y * d.nx + z * (d.nx * d.ny) = x + d.nx * (y + z * d.ny) := by ring
  have h1 : (x + y * d.nx + z * (d.nx * d.ny)) % d.nx = x := by
    rw [hfac, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  have h2 : (x + y * d.nx + z * (d.nx * d.ny)) / d.nx = y + z * d.ny := by
    rw [hfac, Nat.add_mul_div_left x (y + z * d.ny) hnx, Nat.div_eq_of_lt hx, Nat.zero_add]
  have h3 : ((x + y * d.nx + z * (d.nx * d.ny)) / d.nx) % d.ny = y := by
    rw [h2, Nat.mul_comm z d.ny, Nat.add_mul_mod_self_left y d.ny z, Nat.mod_eq_of_lt hy]
  have h4 : (x + y * d.nx + z * (d.nx * d.ny)) / (d.nx * d.ny) = z := by
    have hfact : x + y * d.nx + d.nx * d.ny * z = x + y * d.nx + z * (d.nx * d.ny) := by ring
    rw [← hfact, Nat.add_mul_div_left (x + y * d.nx) z (Nat.mul_pos hnx hny)]
    have hlt : x + y * d.nx < d.nx * d.ny := by
      have hx1 : x ≤ d.nx - 1 := Nat.le_pred_of_lt hx
      have hy1 : y ≤ d.ny - 1 := Nat.le_pred_of_lt hy
      nlinarith [hx1, hy1, Nat.zero_le d.nx, Nat.zero_le d.ny]
    rw [Nat.div_eq_of_lt hlt, Nat.zero_add]
  rw [h1, h3, h4]

/-- Cell-centred world position of voxel `i` (`o + (i + 0.5)·h`). -/
def cellCenter (o h : ℚ) (i : ℕ) : ℚ := o + (i : ℚ) * h + h / 2

/-- The `tvdb_at`-style edge-clamped accessor: out-of-range coordinates
    clamp to the border, in-range coordinates are passed through. -/
def clampIdx (i : ℤ) (n : ℕ) : ℕ :=
  if i ≤ 0 then 0 else if i ≥ (n : ℤ) then n - 1 else i.toNat

theorem clampIdx_le_pred (i : ℤ) (n : ℕ) (hn : 1 ≤ n) : clampIdx i n ≤ n - 1 := by
  unfold clampIdx
  split_ifs
  · omega
  · omega
  · have h1 : i ≤ (n : ℤ) - 1 := by omega
    have h3 : i.toNat ≤ n - 1 := by
      rw [Int.toNat_le, Nat.cast_sub (show 1 ≤ n by omega)]
      push_cast
      omega
    exact h3

theorem clampIdx_eq_self (i : ℤ) (n : ℕ) (h0 : 0 ≤ i) (hi : i < (n : ℤ)) :
    clampIdx i n = i.toNat := by
  unfold clampIdx
  split_ifs with h1 h2
  · omega
  · omega
  · rfl

/-- The edge-clamped grid accessor. -/
noncomputable def atClamped {α : Type*} [Inhabited α] (g : ℕ → ℕ → ℕ → α)
    (nx ny nz : ℕ) (x y z : ℤ) : α :=
  g (clampIdx x nx) (clampIdx y ny) (clampIdx z nz)

theorem atClamped_eq {α : Type*} [Inhabited α] (g : ℕ → ℕ → ℕ → α) (nx ny nz : ℕ)
    {x y z : ℤ} (hx0 : 0 ≤ x) (hx1 : x < (nx : ℤ)) (hy0 : 0 ≤ y) (hy1 : y < (ny : ℤ))
    (hz0 : 0 ≤ z) (hz1 : z < (nz : ℤ)) :
    atClamped g nx ny nz x y z = g x.toNat y.toNat z.toNat := by
  unfold atClamped
  rw [clampIdx_eq_self x nx hx0 hx1, clampIdx_eq_self y ny hy0 hy1,
    clampIdx_eq_self z nz hz0 hz1]

/-! ## Trilinear sampling over one cell -/

/-- Trilinear interpolation of the eight corner values `g` over the unit
    cell, at fractional position `(x, y, z)`. `g i j k` is the corner
    selected by `i, j, k : Fin 2` along the x, y, z axes. -/
def trilinear (g : Fin 2 → Fin 2 → Fin 2 → ℚ) (x y z : ℚ) : ℚ :=
  (1 - x) * (1 - y) * (1 - z) * g 0 0 0 +
  x * (1 - y) * (1 - z) * g 1 0 0 +
  (1 - x) * y * (1 - z) * g 0 1 0 +
  x * y * (1 - z) * g 1 1 0 +
  (1 - x) * (1 - y) * z * g 0 0 1 +
  x * (1 - y) * z * g 1 0 1 +
  (1 - x) * y * z * g 0 1 1 +
  x * y * z * g 1 1 1

/-- The eight corner weights, as a function of the fractional position. -/
def weight (i j k : Fin 2) (x y z : ℚ) : ℚ :=
  (if i = 0 then (1 - x) else x) * (if j = 0 then (1 - y) else y) *
    (if k = 0 then (1 - z) else z)

/-- The trilinear form is the weighted sum of the eight corners. -/
theorem trilinear_eq_sum (g : Fin 2 → Fin 2 → Fin 2 → ℚ) (x y z : ℚ) :
    trilinear g x y z =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, weight i j k x y z * g i j k := by
  simp [trilinear, weight, Fin.sum_univ_two]; ring

/-- **Partition of unity**: the eight corner weights sum to 1. -/
theorem weight_sum_one (x y z : ℚ) :
    (∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, weight i j k x y z) = 1 := by
  simp [weight, Fin.sum_univ_two]; ring

/-- Every corner weight is non-negative on the unit cube. -/
theorem weight_nonneg (i j k : Fin 2) (hx : 0 ≤ x) (hx' : x ≤ 1)
    (hy : 0 ≤ y) (hy' : y ≤ 1) (hz : 0 ≤ z) (hz' : z ≤ 1) :
    0 ≤ weight i j k x y z := by
  have hx1 : (0 : ℚ) ≤ 1 - x := by linarith
  have hy1 : (0 : ℚ) ≤ 1 - y := by linarith
  have hz1 : (0 : ℚ) ≤ 1 - z := by linarith
  unfold weight
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp <;> positivity

/-- **Interpolates at voxel centres**: at integer fractional coordinates the
    interpolant is the corresponding corner value. -/
theorem trilinear_corner (g : Fin 2 → Fin 2 → Fin 2 → ℚ) (i j k : Fin 2) :
    trilinear g (if i = 0 then 0 else 1) (if j = 0 then 0 else 1)
      (if k = 0 then 0 else 1) = g i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [trilinear]

/-- The interpolant of a constant field is that constant. -/
theorem trilinear_const (v : ℚ) (x y z : ℚ) :
    trilinear (fun _ _ _ => v) x y z = v := by
  simp [trilinear]; ring

/-- **Convex combination**: on the unit cube the interpolant lies between the
    minimum and the maximum of the eight corners. -/
theorem trilinear_mem_Icc (g : Fin 2 → Fin 2 → Fin 2 → ℚ) {a b x y z : ℚ}
    (ha : ∀ i j k, a ≤ g i j k) (hb : ∀ i j k, g i j k ≤ b)
    (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ 1) (hz : 0 ≤ z) (hz' : z ≤ 1) :
    a ≤ trilinear g x y z ∧ trilinear g x y z ≤ b := by
  have hnonneg : ∀ i j k : Fin 2, 0 ≤ weight i j k x y z :=
    fun i j k => weight_nonneg i j k hx hx' hy hy' hz hz'
  have hsum : (∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, weight i j k x y z) = 1 :=
    weight_sum_one x y z
  have hlo_eq : trilinear g x y z =
      a * (∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, weight i j k x y z) +
        ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, weight i j k x y z * (g i j k - a) := by
    simp [trilinear, weight, Fin.sum_univ_two]; ring
  have hhi_eq : b * (∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, weight i j k x y z) =
      trilinear g x y z +
        ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, weight i j k x y z * (b - g i j k) := by
    simp [trilinear, weight, Fin.sum_univ_two]; ring
  have hnnlo : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
      weight i j k x y z * (g i j k - a) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (hnonneg i j k) (sub_nonneg.mpr (ha i j k))
  have hnnhi : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
      weight i j k x y z * (b - g i j k) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (hnonneg i j k) (sub_nonneg.mpr (hb i j k))
  constructor
  · rw [hlo_eq, hsum] at *
    linarith
  · rw [hsum] at hhi_eq
    linarith

/-! ## The sample/splat adjoint identity -/

/-- The inner product on the corner space of a cell. -/
def cornerInner (f h : Fin 2 → Fin 2 → Fin 2 → ℚ) : ℚ :=
  f 0 0 0 * h 0 0 0 + f 1 0 0 * h 1 0 0 + f 0 1 0 * h 0 1 0 + f 1 1 0 * h 1 1 0 +
  f 0 0 1 * h 0 0 1 + f 1 0 1 * h 1 0 1 + f 0 1 1 * h 0 1 1 + f 1 1 1 * h 1 1 1

/-- **Splat**: the scatter of a value `s` into the eight corners with the
    same weights the sample uses. The adjoint of trilinear sampling. -/
def splat (x y z : ℚ) (s : ℚ) : Fin 2 → Fin 2 → Fin 2 → ℚ :=
  fun i j k => weight i j k x y z * s

/-- **The sample/splat adjoint identity** — `s * trilinear g x y z` equals
    the corner inner product of `g` with the splat of `s`. This is exactly
    the identity a mesh→grid scatter/gather pair needs (and what the C
    autograd code relies on): `<s, sample(g)> = <splat(s), g>`. -/
theorem sample_splat_adjoint (g : Fin 2 → Fin 2 → Fin 2 → ℚ) (x y z s : ℚ) :
    s * trilinear g x y z = cornerInner g (splat x y z s) := by
  simp [cornerInner, splat, trilinear, weight]; ring

/-- The transpose of sampling: a splat of `1` followed by a constant `1`
    reconstruction is the identity. -/
theorem splat_one_sum (x y z s : ℚ) :
    cornerInner (fun _ _ _ => (1 : ℚ)) (splat x y z s) = s := by
  simp [cornerInner, splat, weight]; ring

end Vdb
