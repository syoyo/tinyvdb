/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Grid sizing (`lvl_make_grid` in `src/tinyvdb_levelset.c`): before filling a
  dense lattice the C code computes the per-axis cell count

      n = ceil(span / voxel_size) + 1        (n − 1)·vs ≥ span

  and places the origin at `lo − vs/2` (cell-centred, voxel-0 centre == `lo`).
  A non-finite or non-positive voxel size, a negative span, or a cell count
  past the int32 bound makes the call fail **without touching `out`**.

  This module models the sizing mathematics and the verdict:

  * `cells`/`cells_pos`/`cells_cover` and `centerAt` — the axis-wise sizing
    equations and the cover inequality;
  * **`axis_cover`** — every point of `[lo, hi]` is within half a voxel of a
    voxel centre (this is the coverage the generators get for free once they
    widen the bounds by the band);
  * **`grid_sizing`** — the C `lvl_make_grid` verdict as a sum type: `ok`
    with the three dimensions and the origin, or `rejected` with **no
    payload** (mirroring the `out`-untouched-on-failure contract);
  * **`grid_sizing_ok_cover`** — when the verdict is `ok`, every point of
    `[lo, hi]` is within half a voxel of a voxel centre in all three axes;
  * **`grid_sizing_rejected_iff`** — the verdict is `rejected` iff some
    guard fired (the C contract: no grid is produced, `out` untouched).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

namespace Vdb

/-! ### One axis -/

/-- The per-axis cell count of `lvl_make_grid`: `ceil(span / vs) + 1`. -/
noncomputable def cells (span vs : ℝ) : ℕ :=
  ⌈span / vs⌉₊ + 1

/-- The count is always at least one. -/
theorem cells_pos (span vs : ℝ) : 1 ≤ cells span vs :=
  Nat.le_add_left _ _

/-- The defining inequality: `(cells − 1) · vs ≥ span`. -/
theorem cells_cover (span vs : ℝ) (hvs : 0 < vs) : span ≤ (cells span vs - 1 : ℝ) * vs := by
  have h1 : span / vs ≤ (⌈span / vs⌉₊ : ℝ) := Nat.le_ceil _
  calc span = span / vs * vs := by field_simp
    _ ≤ (⌈span / vs⌉₊ : ℝ) * vs := mul_le_mul_of_nonneg_right h1 (le_of_lt hvs)
    _ = (cells span vs - 1 : ℝ) * vs := by
        unfold cells
        simp [Nat.cast_add]

/-- The centre of the `k`-th voxel is `lo + k·vs` (cell-centred lattice). -/
def centerAt (lo vs : ℝ) (k : ℕ) : ℝ :=
  lo + k * vs

/-- Voxel 0's centre is exactly `lo` (`origin + vs/2 = lo`). -/
theorem centerAt_zero (lo vs : ℝ) : centerAt lo vs 0 = lo := by
  simp [centerAt]

/-- **Axis coverage**: every point of `[lo, hi]` is within half a voxel of a
    voxel centre. The witness is the nearest cell to `p`. -/
theorem axis_cover (lo hi p vs : ℝ) (hvs : 0 < vs)
    (hplo : lo ≤ p) (hphi : p ≤ hi) :
    ∃ k : ℕ, k < cells (hi - lo) vs ∧ |centerAt lo vs k - p| ≤ vs / 2 := by
  have hp0 : 0 ≤ p - lo := sub_nonneg.mpr hplo
  rcases eq_or_lt_of_le hp0 with hsub | hsub
  · -- p = lo: voxel 0 is exactly p
    refine ⟨0, Nat.lt_of_lt_of_le (by norm_num) (cells_pos _ _), ?_⟩
    rw [centerAt_zero, abs_sub_comm, abs_of_nonneg hp0, ← hsub]
    linarith [hvs]
  · have ht0 : 0 ≤ (p - lo) / vs + 1 / 2 := by
      have : 0 ≤ (p - lo) / vs := div_nonneg hp0 (le_of_lt hvs)
      linarith
    set t := (p - lo) / vs + 1 / 2 with ht
    have hfl : 0 ≤ ⌊t⌋ := Int.floor_nonneg.mpr ht0
    set k := (⌊t⌋).toNat with hk
    have hk_toNat : (k : ℝ) = (⌊t⌋ : ℝ) := by
      rw [hk]
      exact_mod_cast Int.toNat_of_nonneg hfl
    have hkle : (k : ℝ) ≤ t := by
      rw [hk_toNat]
      exact_mod_cast Int.floor_le t
    have hkx : t < (k : ℝ) + 1 := by
      rw [hk_toNat]
      exact_mod_cast Int.lt_floor_add_one t
    have hlow : t - 1 ≤ (k : ℝ) := by linarith
    -- the k-th centre is within vs/2 of p
    have hc_le : centerAt lo vs k ≤ p + vs / 2 := by
      unfold centerAt
      have htv : (k : ℝ) * vs ≤ p - lo + vs / 2 := by
        calc (k : ℝ) * vs ≤ t * vs := mul_le_mul_of_nonneg_right hkle (le_of_lt hvs)
          _ = (p - lo) / vs * vs + vs / 2 := by rw [ht]; ring
          _ = p - lo + vs / 2 := by field_simp
      linarith
    have hc_ge : p - vs / 2 ≤ centerAt lo vs k := by
      unfold centerAt
      have htv : p - lo - vs / 2 ≤ (k : ℝ) * vs := by
        have h1 : p - lo - vs / 2 = (t - 1) * vs := by rw [ht]; field_simp; ring
        calc p - lo - vs / 2 = (t - 1) * vs := h1
          _ ≤ (k : ℝ) * vs := mul_le_mul_of_nonneg_right hlow (le_of_lt hvs)
      linarith
    -- k < cells
    have hspan : 0 ≤ hi - lo := by linarith [hp0, hphi]
    have hk_cells : k < cells (hi - lo) vs := by
      have h1 : (k : ℝ) ≤ (hi - lo) / vs + 1 / 2 := by
        refine le_trans hkle ?_
        have hdiv : (p - lo) / vs ≤ (hi - lo) / vs := by gcongr
        linarith [hdiv]
      have h2 : (k : ℝ) < (⌈(hi - lo) / vs⌉₊ : ℝ) + 1 := by
        have h3 : ((hi - lo) / vs : ℝ) ≤ (⌈(hi - lo) / vs⌉₊ : ℝ) := Nat.le_ceil _
        linarith
      have hk_lt : k < ⌈(hi - lo) / vs⌉₊ + 1 := by exact_mod_cast h2
      unfold cells
      exact hk_lt
    refine ⟨k, hk_cells, ?_⟩
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩

/-- **Lattice coverage**: every point of `[lo, hi]^3` is within half a voxel
    of a voxel centre. Follows axis by axis from `axis_cover`. -/
theorem grid_cover (lo hi : Fin 3 → ℝ) (vs : ℝ) (hvs : 0 < vs)
    (p : Fin 3 → ℝ) (hp : ∀ i, lo i ≤ p i ∧ p i ≤ hi i) (i : Fin 3) :
    ∃ k : ℕ, k < cells (hi i - lo i) vs ∧
      |centerAt (lo i) vs k - p i| ≤ vs / 2 :=
  axis_cover (lo i) (hi i) (p i) vs hvs (hp i).1 (hp i).2

/-! ### The C `lvl_make_grid` verdict -/

/-- The result of the C `lvl_make_grid` call: either `ok` with the three
    dimensions and the origin, or `rejected` with **no payload** (mirroring
    the contract that `out` is unmodified on the failure path). -/
inductive GridSizing where
  | ok (nx ny nz : ℕ) (origin : Fin 3 → ℝ)
  | rejected

/-- The int32 bound the C code uses (`cells > (double)INT_MAX` rejects). -/
def int32Max : ℕ := 2147483647

/-- The `lvl_make_grid` verdict. -/
noncomputable def grid_sizing (lo hi : Fin 3 → ℝ) (vs : ℝ) : GridSizing :=
  let c := fun i => cells (hi i - lo i) vs
  if vs ≤ 0 ∨ (∃ i, hi i < lo i) ∨ (∃ i, int32Max < c i) then
    .rejected
  else
    .ok (c 0) (c 1) (c 2) (fun i => lo i - vs / 2)

/-- When the verdict is `ok`, the dimensions are the `cells` values. -/
theorem grid_sizing_ok_dims {lo hi : Fin 3 → ℝ} {vs : ℝ} {nx ny nz : ℕ} {o : Fin 3 → ℝ}
    (h : grid_sizing lo hi vs = .ok nx ny nz o) :
    nx = cells (hi 0 - lo 0) vs ∧ ny = cells (hi 1 - lo 1) vs ∧ nz = cells (hi 2 - lo 2) vs ∧
      o = fun i => lo i - vs / 2 := by
  unfold grid_sizing at h
  by_cases hv : vs ≤ 0
  · rw [ite_eq_left (Or.inl hv)] at h
    simp at h
  · by_cases hneg : ∃ i, hi i < lo i
    · rw [ite_eq_left (Or.inr (Or.inl hneg))] at h
      simp at h
    · by_cases hover : ∃ i, int32Max < cells (hi i - lo i) vs
      · rw [ite_eq_left (Or.inr (Or.inr hover))] at h
        simp at h
      · have hne : ¬ (vs ≤ 0 ∨ (∃ i, hi i < lo i) ∨ ∃ i, int32Max < cells (hi i - lo i) vs) :=
          fun hdis => hdis.elim (fun h0 => hv h0)
            (fun h0 => h0.elim (fun hs => hneg hs) fun hs => hover hs)
        rw [ite_eq_right hne] at h
        injection h with h1 h2 h3 h4
        exact ⟨h1.symm, h2.symm, h3.symm, h4.symm⟩

/-- The verdict is `rejected` iff some guard fired. -/
theorem grid_sizing_rejected_iff {lo hi : Fin 3 → ℝ} {vs : ℝ} :
    grid_sizing lo hi vs = .rejected ↔
      vs ≤ 0 ∨ (∃ i, hi i < lo i) ∨ (∃ i, int32Max < cells (hi i - lo i) vs) := by
  unfold grid_sizing
  by_cases hv : vs ≤ 0
  · simp [hv]
  · by_cases hneg : ∃ i, hi i < lo i
    · simp [hv, hneg]
    · by_cases hover : ∃ i, int32Max < cells (hi i - lo i) vs
      · simp [hv, hneg, hover]
      · simp [hv, hneg, hover]

/-- **Coverage**: when the verdict is `ok`, every point of `[lo, hi]` is
    within half a voxel of a voxel centre on every axis. (The callers widen
    the bounds by the band, so this is the `bbox ⊕ band` coverage.) -/
theorem grid_sizing_ok_cover {lo hi p : Fin 3 → ℝ} {vs : ℝ} {nx ny nz : ℕ} {o : Fin 3 → ℝ}
    (h : grid_sizing lo hi vs = .ok nx ny nz o)
    (hp : ∀ i, lo i ≤ p i ∧ p i ≤ hi i) (i : Fin 3) :
    ∃ k : ℕ, k < cells (hi i - lo i) vs ∧
      |centerAt (lo i) vs k - p i| ≤ vs / 2 := by
  have hvs : (0:ℝ) < vs := by
    by_contra hv
    have hv' : vs ≤ 0 := not_lt.mp hv
    have hrej : grid_sizing lo hi vs = .rejected := grid_sizing_rejected_iff.mpr (Or.inl hv')
    rw [hrej] at h
    simp at h
  exact grid_cover lo hi vs hvs p hp i

/-- When the verdict is `rejected`, the int32 cell-count bound (or another
    guard) fired: no grid is produced, mirroring the C contract that `out`
    is unmodified on the failure path. -/
theorem grid_sizing_rejects_overflow {lo hi : Fin 3 → ℝ} {vs : ℝ}
    (hover : ∃ i, int32Max < cells (hi i - lo i) vs) :
    grid_sizing lo hi vs = .rejected := by
  rw [grid_sizing_rejected_iff]
  exact Or.inr (Or.inr hover)
