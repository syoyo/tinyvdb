/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  The Godunov local solver used by the Eikonal / fast-sweeping level-set
  renormalization: given the upwind grid-edge values `a ≤ b ≤ c` (non-negative)
  and the voxel size `h`, solve for the new value `x` of a voxel such that

    `(x - a)₊² + (x - b)₊² + (x - c)₊² = h²`  with  `x ≥ a`

  (`(·)₊ = max · 0`). The solver returns the smallest root consistent with
  the upwind direction, trying the 1-D, then 2-D, then 3-D candidate.

  Two algebraically different discriminant formulas appear in the C sources
  (`tvdb__godunov_solve` in `src/tinyvdb_ops.c` and `sdf_eikonal` in
  `src/tinyvdb_sdf_tree.c`); they are proven equal here.

  Theorems (`T-GOD-*`), over ℝ:
  * `godunov_spec` — the returned value satisfies the discrete Eikonal
    equation exactly;
  * `disc2_nonneg` / `disc3_nonneg` — the discriminants are non-negative
    whenever their branch is reached (the C `disc < 0` fallbacks are
    unreachable);
  * `disc3_eq` — the two source formulas for the 3-D discriminant are equal.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

noncomputable section

namespace Vdb

/-- Larger root of `(x-a)² + (x-b)² = h²` in the 2-D case. -/
def godunov2D (a b h : ℝ) : ℝ :=
  (a + b + Real.sqrt (2 * h ^ 2 - (a - b) ^ 2)) / 2

/-- The 3-D discriminant of `(x-a)² + (x-b)² + (x-c)² = h²`, in the `sdf_eikonal` form. -/
def disc3 (a b c h : ℝ) : ℝ :=
  3 * h ^ 2 - (a - b) ^ 2 - (a - c) ^ 2 - (b - c) ^ 2

/-- The 3-D discriminant in the `tvdb__godunov_solve` form. -/
def disc3Ops (a b c h : ℝ) : ℝ :=
  (a + b + c) ^ 2 - 3 * (a ^ 2 + b ^ 2 + c ^ 2 - h ^ 2)

theorem disc3_eq (a b c h : ℝ) : disc3Ops a b c h = disc3 a b c h := by
  unfold disc3Ops disc3
  ring

/-- The local Godunov solve, matching the C `tvdb__godunov_solve`. -/
def godunov (a b c h : ℝ) : ℝ :=
  if a + h ≤ b then a + h
  else if godunov2D a b h ≤ c then godunov2D a b h
  else (a + b + c + Real.sqrt (disc3 a b c h)) / 3

theorem godunov_oneD {a b c h : ℝ} (h1 : a + h ≤ b) :
    godunov a b c h = a + h := by
  unfold godunov
  simp only [h1, ite_true]

theorem godunov_twoD {a b c h : ℝ} (h1 : ¬ a + h ≤ b) (h2 : godunov2D a b h ≤ c) :
    godunov a b c h = godunov2D a b h := by
  unfold godunov
  simp only [h1, h2, ite_false, ite_true]

theorem godunov_threeD {a b c h : ℝ} (h1 : ¬ a + h ≤ b) (h2 : ¬ godunov2D a b h ≤ c) :
    godunov a b c h = (a + b + c + Real.sqrt (disc3 a b c h)) / 3 := by
  unfold godunov
  simp only [h1, h2, ite_false]

/-- The 2-D discriminant is non-negative whenever the 2-D branch is reached
    (`x1 = a + h > b`). -/
theorem disc2_nonneg {a b h : ℝ} (hh : b < a + h) (hab : a ≤ b) :
    0 ≤ 2 * h ^ 2 - (a - b) ^ 2 := by
  have h1 : -h < a - b := by linarith
  have h2 : (a - b) ^ 2 < h ^ 2 := by
    nlinarith [h1, hab, sq_nonneg (a - b + h)]
  nlinarith [h2]

/-- The 3-D discriminant is non-negative whenever the 3-D branch is reached,
    and strictly exceeds `(b − a + 2(c − b))²`. -/
theorem disc3_strong {a b c h : ℝ} (h1 : ¬ a + h ≤ b)
    (h2 : ¬ godunov2D a b h ≤ c) (hab : a ≤ b) (hbc : b ≤ c) :
    0 ≤ disc3 a b c h ∧ Real.sqrt (disc3 a b c h) > (b - a) + 2 * (c - b) := by
  set u := b - a with hu
  set v := c - b with hv
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  have hv0 : 0 ≤ v := by rw [hv]; linarith
  -- x2 > c implies h² > u² + 2v² + 2uv.
  have hx1 : b < a + h := not_le.mp h1
  have hd2 : 0 ≤ 2 * h ^ 2 - (a - b) ^ 2 := disc2_nonneg hx1 hab
  have hx2 : (a + b + Real.sqrt (2 * h ^ 2 - (a - b) ^ 2)) / 2 > c :=
    not_le.mp h2
  -- √d2 > 2c − a − b = u + 2v
  have hsqrt : Real.sqrt (2 * h ^ 2 - (a - b) ^ 2) > u + 2 * v := by
    have e : u + 2 * v = 2 * c - a - b := by
      subst u; subst v; ring
    have hbig : 2 * c - a - b < Real.sqrt (2 * h ^ 2 - (a - b) ^ 2) := by
      nlinarith [hx2]
    rwa [e]
  have habs : 2 * h ^ 2 - (a - b) ^ 2 > (u + 2 * v) ^ 2 := by
    have hsq := Real.sq_sqrt hd2
    nlinarith [hsq, hsqrt]
  -- h² > u² + 2v² + 2uv
  have hkey : h ^ 2 > u ^ 2 + 2 * v ^ 2 + 2 * u * v := by
    have : u + 2 * v = 2 * c - a - b := by subst u; subst v; ring
    have hab : (a - b) ^ 2 = u ^ 2 := by rw [hu]; ring
    nlinarith [habs, hab]
  -- d3 − (u + 2v)² = 3h² − 3u² − 6uv − 5v² > v² ≥ 0
  have hd3 : 0 ≤ disc3 a b c h := by
    unfold disc3
    have e1 : (a - b) ^ 2 = u ^ 2 := by rw [hu]; ring
    have e2 : (a - c) ^ 2 = (u + v) ^ 2 := by rw [hu, hv]; ring
    have e3 : (b - c) ^ 2 = v ^ 2 := by rw [hv]; ring
    rw [e1, e2, e3]
    nlinarith [hkey]
  have hsqrt3 : Real.sqrt (disc3 a b c h) > u + 2 * v := by
    have habs2 : disc3 a b c h > (u + 2 * v) ^ 2 := by
      unfold disc3
      have e1 : (a - b) ^ 2 = u ^ 2 := by rw [hu]; ring
      have e2 : (a - c) ^ 2 = (u + v) ^ 2 := by rw [hu, hv]; ring
      have e3 : (b - c) ^ 2 = v ^ 2 := by rw [hv]; ring
      rw [e1, e2, e3]
      nlinarith [hkey]
    have huv : 0 ≤ u + 2 * v := by linarith
    have hlt : Real.sqrt (disc3 a b c h) > Real.sqrt ((u + 2 * v) ^ 2) :=
      Real.sqrt_lt_sqrt (sq_nonneg _) habs2
    rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg huv] at hlt
  exact ⟨hd3, hsqrt3⟩

/-- The 2-D candidate satisfies the 2-D Eikonal equation. -/
theorem godunov2D_spec {a b h : ℝ} (h1 : ¬ a + h ≤ b) (hab : a ≤ b) :
    (godunov2D a b h - a) ^ 2 + (godunov2D a b h - b) ^ 2 = h ^ 2 := by
  unfold godunov2D
  set d := 2 * h ^ 2 - (a - b) ^ 2 with hd
  have hx1 : b < a + h := not_le.mp h1
  have hd2 : 0 ≤ d := disc2_nonneg hx1 hab
  have hsqrt : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd2
  nlinarith [hsqrt]

/-- Main solver specification: the returned value solves the discrete Eikonal
    equation `(x-a)₊² + (x-b)₊² + (x-c)₊² = h²`. -/
theorem godunov_spec {a b c h : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hh : 0 ≤ h) :
    max (godunov a b c h - a) 0 ^ 2 + max (godunov a b c h - b) 0 ^ 2
    + max (godunov a b c h - c) 0 ^ 2 = h ^ 2 := by
  unfold godunov
  split_ifs with h1 h2
  · -- 1-D case: x = a + h ≤ b ≤ c.
    show max (a + h - a) 0 ^ 2 + max (a + h - b) 0 ^ 2 + max (a + h - c) 0 ^ 2 = h ^ 2
    have ha' : a + h - a = h := by ring
    have hb' : max (a + h - b) 0 = 0 := max_eq_right (by linarith [h1])
    have hc' : max (a + h - c) 0 = 0 := max_eq_right (by linarith [h1])
    rw [ha', max_eq_left hh, hb', hc']
    simp
  · -- 2-D case: b < x2 ≤ c.
    have hx1 : b < a + h := not_le.mp h1
    have hge : b ≤ godunov2D a b h := by
      unfold godunov2D
      set d := 2 * h ^ 2 - (a - b) ^ 2 with hd
      have hd2 : 0 ≤ d := disc2_nonneg hx1 hab
      have hst : Real.sqrt d ≥ b - a := by
        have h2' : (a - b) ^ 2 ≤ d := by
          nlinarith [hx1, hab, sq_nonneg (a - b + h)]
        have hsqrt' := Real.sqrt_le_sqrt h2'
        rw [Real.sqrt_sq_eq_abs, abs_of_nonpos (by linarith), neg_sub] at hsqrt'
        exact hsqrt'
      nlinarith [hst]
    have ha' : a ≤ godunov2D a b h := le_trans hab hge
    have hc' : godunov2D a b h ≤ c := h2
    have heq := godunov2D_spec h1 hab
    show max (godunov2D a b h - a) 0 ^ 2 + max (godunov2D a b h - b) 0 ^ 2
        + max (godunov2D a b h - c) 0 ^ 2 = h ^ 2
    rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]
    simp [zero_pow (show (2:ℕ) ≠ 0 by norm_num)]
    exact heq
  · -- 3-D case: x3 > c ≥ b ≥ a.
    have hx1 : b < a + h := not_le.mp h1
    obtain ⟨hd3, hsqrt3⟩ := disc3_strong h1 h2 hab hbc
    have hge : c < (a + b + c + Real.sqrt (disc3 a b c h)) / 3 := by
      linarith [hsqrt3]
    have ha' : a ≤ (a + b + c + Real.sqrt (disc3 a b c h)) / 3 :=
      le_trans hab (le_trans hbc hge.le)
    have hb' : b ≤ (a + b + c + Real.sqrt (disc3 a b c h)) / 3 :=
      le_trans hbc hge.le
    have hc' : c ≤ (a + b + c + Real.sqrt (disc3 a b c h)) / 3 := le_of_lt hge
    show max ((a + b + c + Real.sqrt (disc3 a b c h)) / 3 - a) 0 ^ 2
        + max ((a + b + c + Real.sqrt (disc3 a b c h)) / 3 - b) 0 ^ 2
        + max ((a + b + c + Real.sqrt (disc3 a b c h)) / 3 - c) 0 ^ 2 = h ^ 2
    rw [max_eq_left (by linarith [ha']), max_eq_left (by linarith [hb']), max_eq_left (by linarith [hc'])]
    have hsqrt : (Real.sqrt (disc3 a b c h)) ^ 2 = disc3 a b c h := Real.sq_sqrt hd3
    unfold disc3 at hsqrt ⊢
    nlinarith [hsqrt]

/-! ### The `a + h / √3` lower bound and the `a + h` upper bound -/

theorem poly_bound {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    3 * (2 * u ^ 2 + 2 * u * v + v ^ 2) ^ 2 ≤
      4 * (2 * u + v) ^ 2 * (u ^ 2 + 2 * u * v + 2 * v ^ 2) := by
  have e : 4 * (2 * u + v) ^ 2 * (u ^ 2 + 2 * u * v + 2 * v ^ 2)
      - 3 * (2 * u ^ 2 + 2 * u * v + v ^ 2) ^ 2
      = 4 * u ^ 4 + 24 * u ^ 3 * v + 44 * u ^ 2 * v ^ 2 + 28 * u * v ^ 3 + 5 * v ^ 4 := by
    ring
  have h1 : (0:ℝ) ≤ u ^ 2 := sq_nonneg u
  have h2 : (0:ℝ) ≤ v ^ 2 := sq_nonneg v
  have h3 : (0:ℝ) ≤ u * v := mul_nonneg hu hv
  have h4 : (0:ℝ) ≤ u ^ 2 * v ^ 2 := by nlinarith [sq_nonneg (u * v)]
  have h5 : (0:ℝ) ≤ u ^ 3 * v := by nlinarith [h1, h3]
  have h6 : (0:ℝ) ≤ u * v ^ 3 := by nlinarith [h2, h3]
  have h7 : (0:ℝ) ≤ u ^ 4 := by nlinarith [h1]
  have h8 : (0:ℝ) ≤ v ^ 4 := by nlinarith [h2]
  have : (0:ℝ) ≤ 4 * u ^ 4 + 24 * u ^ 3 * v + 44 * u ^ 2 * v ^ 2 + 28 * u * v ^ 3 + 5 * v ^ 4 := by
    nlinarith [h4, h5, h6, h7, h8]
  linarith [this]

theorem threeD_sq_constraint {a b c h : ℝ} (h1 : ¬ a + h ≤ b)
    (h2 : ¬ (a + b + Real.sqrt (2 * h ^ 2 - (a - b) ^ 2)) / 2 ≤ c)
    (hab : a ≤ b) (hbc : b ≤ c) :
    (b - a) ^ 2 + 2 * (b - a) * (c - b) + 2 * (c - b) ^ 2 < h ^ 2 := by
  have hx1 : b < a + h := not_le.mp h1
  have hd2 : 0 ≤ 2 * h ^ 2 - (a - b) ^ 2 := disc2_nonneg hx1 hab
  have hx2 : (a + b + Real.sqrt (2 * h ^ 2 - (a - b) ^ 2)) / 2 > c :=
    not_le.mp h2
  have hab2 : (a - b) ^ 2 = (b - a) ^ 2 := by ring
  have hlt : Real.sqrt (2 * h ^ 2 - (a - b) ^ 2) > (b - a) + 2 * (c - b) := by
    have e : (b - a) + 2 * (c - b) = 2 * c - a - b := by ring
    have hbig : 2 * c - a - b < Real.sqrt (2 * h ^ 2 - (a - b) ^ 2) := by
      nlinarith [hx2]
    rwa [e]
  have habs : 2 * h ^ 2 - (a - b) ^ 2 > ((b - a) + 2 * (c - b)) ^ 2 := by
    have hsq := Real.sq_sqrt hd2
    nlinarith [hsq, hlt]
  nlinarith [habs, hab2]

theorem threeD_r2 {a b c h : ℝ} (h1 : ¬ a + h ≤ b)
    (h2 : ¬ (a + b + Real.sqrt (2 * h ^ 2 - (a - b) ^ 2)) / 2 ≤ c)
    (hab : a ≤ b) (hbc : b ≤ c) (hpos : 0 ≤ h) :
    (Real.sqrt 3 * h - 2 * (b - a) - (c - b)) ^ 2 ≤ disc3 a b c h := by
  have hsq : (b - a) ^ 2 + 2 * (b - a) * (c - b) + 2 * (c - b) ^ 2 < h ^ 2 :=
    threeD_sq_constraint h1 h2 hab hbc
  have hE : 4 * h ^ 2 * (2 * (b - a) + (c - b)) ^ 2 ≥
      3 * (2 * (b - a) ^ 2 + 2 * (b - a) * (c - b) + (c - b) ^ 2) ^ 2 := by
    have hpoly := poly_bound (sub_nonneg.mpr hab) (sub_nonneg.mpr hbc)
    nlinarith [hpoly, hsq]
  have hA : (0:ℝ) ≤ 2 * Real.sqrt 3 * h * (2 * (b - a) + (c - b)) := by positivity
  have hB : (0:ℝ) ≤ 3 * (2 * (b - a) ^ 2 + 2 * (b - a) * (c - b) + (c - b) ^ 2) := by
    have : 2 * (b - a) ^ 2 + 2 * (b - a) * (c - b) + (c - b) ^ 2 =
        (b - a) ^ 2 + ((b - a) + (c - b)) ^ 2 := by ring
    positivity
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hu0 : (0:ℝ) ≤ b - a := by linarith
  have hv0 : (0:ℝ) ≤ c - b := by linarith
  have hAB : 2 * Real.sqrt 3 * h * (2 * (b - a) + (c - b)) ≥
      3 * (2 * (b - a) ^ 2 + 2 * (b - a) * (c - b) + (c - b) ^ 2) := by
    have A2 : (2 * Real.sqrt 3 * h * (2 * (b - a) + (c - b))) ^ 2 ≥
        (3 * (2 * (b - a) ^ 2 + 2 * (b - a) * (c - b) + (c - b) ^ 2)) ^ 2 := by
      nlinarith [hE, hs3, hu0, hv0, sq_nonneg (2 * (b - a) + (c - b))]
    nlinarith [A2, hA, hB, sq_nonneg (2 * Real.sqrt 3 * h * (2 * (b - a) + (c - b)) -
      3 * (2 * (b - a) ^ 2 + 2 * (b - a) * (c - b) + (c - b) ^ 2))]
  unfold disc3
  have hsub : (a - b) ^ 2 = (b - a) ^ 2 := by ring
  have hsub2 : (a - c) ^ 2 = ((b - a) + (c - b)) ^ 2 := by ring
  have hsub3 : (b - c) ^ 2 = (c - b) ^ 2 := by ring
  rw [hsub, hsub2, hsub3]
  have hs3b : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have key : (Real.sqrt 3 * h - 2 * (b - a) - (c - b)) ^ 2 =
      3 * h ^ 2 - 2 * (2 * (b - a) + (c - b)) * (Real.sqrt 3 * h) + (2 * (b - a) + (c - b)) ^ 2 := by
    ring_nf
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  rw [key]
  nlinarith [hAB, hs3b]

theorem threeD_sqrt_ge {a b c h : ℝ} (h1 : ¬ a + h ≤ b)
    (h2 : ¬ (a + b + Real.sqrt (2 * h ^ 2 - (a - b) ^ 2)) / 2 ≤ c)
    (hab : a ≤ b) (hbc : b ≤ c) (hpos : 0 ≤ h) :
    Real.sqrt 3 * h - 2 * (b - a) - (c - b) ≤ Real.sqrt (disc3 a b c h) := by
  by_cases hle : Real.sqrt 3 * h - 2 * (b - a) - (c - b) ≤ 0
  · have := Real.sqrt_nonneg (disc3 a b c h)
    linarith
  · have hpos' : 0 < Real.sqrt 3 * h - 2 * (b - a) - (c - b) := not_le.mp hle
    have hr' : (Real.sqrt 3 * h - 2 * (b - a) - (c - b)) ^ 2 ≤ disc3 a b c h :=
      threeD_r2 h1 h2 hab hbc hpos
    rw [Real.le_sqrt' hpos']
    exact hr'

theorem godunov2D_ge {a b h : ℝ} (h1 : ¬ a + h ≤ b) (hab : a ≤ b) (_hpos : 0 ≤ h) :
    a + h / Real.sqrt 2 ≤ godunov2D a b h := by
  unfold godunov2D
  have hx1 : b < a + h := not_le.mp h1
  have hd2 : 0 ≤ 2 * h ^ 2 - (a - b) ^ 2 := disc2_nonneg hx1 hab
  have hδ : b - a < h := by linarith
  have hu : 0 ≤ b - a := by linarith
  have h2 : 2 * h ^ 2 - (a - b) ^ 2 ≥ (Real.sqrt 2 * h - (b - a)) ^ 2 := by
    have habs : (a - b) ^ 2 = (b - a) ^ 2 := by ring
    have hs22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs2h : Real.sqrt 2 * h ≥ h := by
      have h1 : (1:ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
      nlinarith [h1, _hpos]
    nlinarith [hs22, habs, hs2h, hu, hδ, _hpos, sq_nonneg (b - a)]
  have hne : (0:ℝ) ≤ Real.sqrt 2 * h - (b - a) := by
    have h1 : (1:ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
    have hs2h : Real.sqrt 2 * h ≥ h := by nlinarith [h1, _hpos]
    linarith [hs2h, hδ]
  have h3 : Real.sqrt (2 * h ^ 2 - (a - b) ^ 2) ≥ Real.sqrt 2 * h - (b - a) := by
    calc Real.sqrt (2 * h ^ 2 - (a - b) ^ 2) ≥ Real.sqrt ((Real.sqrt 2 * h - (b - a)) ^ 2) :=
          Real.sqrt_le_sqrt h2
      _ = Real.sqrt 2 * h - (b - a) := by
          simp [Real.sqrt_sq_eq_abs, abs_of_nonneg hne]
  have h4 : h / Real.sqrt 2 = Real.sqrt 2 * h / 2 := by
    have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
    have hs22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp [hs2]
    nlinarith [hs22]
  rw [h4]
  nlinarith [h3]

theorem godunov_lo_threeD {a b c h : ℝ} (h1 : ¬ a + h ≤ b)
    (h2 : ¬ (a + b + Real.sqrt (2 * h ^ 2 - (a - b) ^ 2)) / 2 ≤ c)
    (hab : a ≤ b) (hbc : b ≤ c) (hpos : 0 ≤ h) :
    a + h / Real.sqrt 3 ≤ (a + b + c + Real.sqrt (disc3 a b c h)) / 3 := by
  have hbase := threeD_sqrt_ge h1 h2 hab hbc hpos
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs3' : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have h1' : b + c + Real.sqrt (disc3 a b c h) ≥ 2 * a + Real.sqrt 3 * h := by
    nlinarith [hbase]
  have h2' : a + b + c + Real.sqrt (disc3 a b c h) ≥ 3 * a + Real.sqrt 3 * h := by
    nlinarith [h1']
  have h3 : h / Real.sqrt 3 = Real.sqrt 3 * h / 3 := by
    have hs3' : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)
    have hne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3))
    field_simp [hne]
    nlinarith [hs3']
  rw [h3]
  nlinarith [h2', hs3']

theorem godunov_lo {a b c h : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hh : 0 ≤ h) :
    a + h / Real.sqrt 3 ≤ godunov a b c h := by
  unfold godunov
  split_ifs with h1 h2
  · -- 1-D case: x = a + h
    have hs3' : Real.sqrt 3 ≥ 1 := by
      calc Real.sqrt 3 ≥ Real.sqrt 1 := Real.sqrt_le_sqrt (by norm_num)
        _ = 1 := Real.sqrt_one
    have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hle : h / Real.sqrt 3 ≤ h := by
      rw [div_le_iff₀ hs3]
      nlinarith [hh]
    linarith
  · -- 2-D case
    show a + h / Real.sqrt 3 ≤ godunov2D a b h
    have hs3' : Real.sqrt 3 ≥ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
    have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hle : h / Real.sqrt 3 ≤ h / Real.sqrt 2 := by
      rw [div_le_div_iff₀ hs3 hs2]
      nlinarith [hs3', hh]
    linarith [godunov2D_ge h1 hab hh, hle]
  · show a + h / Real.sqrt 3 ≤ (a + b + c + Real.sqrt (disc3 a b c h)) / 3
    exact godunov_lo_threeD h1 h2 hab hbc hh

theorem godunov_hi {a b c h : ℝ} (hab : a ≤ b) (_hbc : b ≤ c) (_hh : 0 ≤ h) :
    godunov a b c h ≤ a + h := by
  unfold godunov
  split_ifs with h1 h2
  · show a + h ≤ a + h; exact le_refl _
  · show godunov2D a b h ≤ a + h
    unfold godunov2D
    have hbh : b ≤ a + h := le_of_lt (not_le.mp h1)
    have hd2 : 0 ≤ 2 * h ^ 2 - (a - b) ^ 2 := disc2_nonneg (not_le.mp h1) hab
    have hside : (2 * h - (b - a)) ^ 2 ≥ 2 * h ^ 2 - (a - b) ^ 2 := by
      have : (a - b) ^ 2 = (b - a) ^ 2 := by ring
      nlinarith [this, hbh, _hh, sq_nonneg (h - (b - a))]
    calc (a + b + Real.sqrt (2 * h ^ 2 - (a - b) ^ 2)) / 2
        ≤ (a + b + (2 * h - (b - a))) / 2 := by
          have hs : Real.sqrt (2 * h ^ 2 - (a - b) ^ 2) ≤ 2 * h - (b - a) := by
            calc Real.sqrt (2 * h ^ 2 - (a - b) ^ 2) ≤ Real.sqrt ((2 * h - (b - a)) ^ 2) :=
                  Real.sqrt_le_sqrt hside
              _ = 2 * h - (b - a) := by
                  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith [hbh, _hh])]
          linarith [hs]
      _ = a + h := by ring
  · show (a + b + c + Real.sqrt (disc3 a b c h)) / 3 ≤ a + h
    have hbh : b ≤ a + h := le_of_lt (not_le.mp h1)
    have hx2 : (a + b + Real.sqrt (2 * h ^ 2 - (a - b) ^ 2)) / 2 ≤ a + h := by
      have hside : (2 * h - (b - a)) ^ 2 ≥ 2 * h ^ 2 - (a - b) ^ 2 := by
        have : (a - b) ^ 2 = (b - a) ^ 2 := by ring
        nlinarith [this, hbh, _hh]
      calc (a + b + Real.sqrt (2 * h ^ 2 - (a - b) ^ 2)) / 2
          ≤ (a + b + (2 * h - (b - a))) / 2 := by
            have hs : Real.sqrt (2 * h ^ 2 - (a - b) ^ 2) ≤ 2 * h - (b - a) := by
              calc Real.sqrt (2 * h ^ 2 - (a - b) ^ 2) ≤ Real.sqrt ((2 * h - (b - a)) ^ 2) :=
                    Real.sqrt_le_sqrt hside
                _ = 2 * h - (b - a) := by
                    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith [hbh, _hh])]
            linarith [hs]
        _ = a + h := by ring
    have hch : c ≤ a + h := by
      have hcx : c < (a + b + Real.sqrt (2 * h ^ 2 - (a - b) ^ 2)) / 2 := not_le.mp h2
      linarith
    have hp : 0 ≤ 2 * a + 3 * h - b - c := by linarith
    have hkey : 0 ≤ 2 * (a + h) ^ 2 - 2 * (a + h) * (b + c) + b ^ 2 + c ^ 2 := by
      nlinarith [sq_nonneg ((a + h) - (b + c) / 2), sq_nonneg (b - c)]
    have hdiff : (2 * a + 3 * h - b - c) ^ 2 - disc3 a b c h =
        3 * (2 * (a + h) ^ 2 - 2 * (a + h) * (b + c) + b ^ 2 + c ^ 2) := by
      unfold disc3; ring
    have hsq : (2 * a + 3 * h - b - c) ^ 2 ≥ disc3 a b c h := by
      linarith [hdiff, hkey]
    have hle : Real.sqrt (disc3 a b c h) ≤ 2 * a + 3 * h - b - c := by
      calc Real.sqrt (disc3 a b c h) ≤ Real.sqrt ((2 * a + 3 * h - b - c) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = 2 * a + 3 * h - b - c := by
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hp]
    linarith

/-- The 2-D candidate is at least `b` (always). -/
theorem godunov2D_ge_b {a b h : ℝ} (h1 : ¬ a + h ≤ b) (hab : a ≤ b) (_hpos : 0 ≤ h) :
    b ≤ godunov2D a b h := by
  unfold godunov2D
  have hx1 : b < a + h := not_le.mp h1
  have hd2 : 0 ≤ 2 * h ^ 2 - (a - b) ^ 2 := disc2_nonneg hx1 hab
  have hδ : (a - b) ^ 2 ≤ 2 * h ^ 2 - (a - b) ^ 2 := by
    have : a - b < h := by linarith
    nlinarith [this, hab]
  have hs := Real.sqrt_le_sqrt hδ
  rw [Real.sqrt_sq_eq_abs, abs_of_nonpos (by linarith)] at hs
  linarith [hs, hab]

/-- The 2-D candidate is monotone in `h`. -/
theorem godunov2D_mono {a b h h' : ℝ} (hhh : 0 ≤ h) (hh : h ≤ h') :
    godunov2D a b h ≤ godunov2D a b h' := by
  unfold godunov2D
  have hd : 2 * h ^ 2 - (a - b) ^ 2 ≤ 2 * h' ^ 2 - (a - b) ^ 2 := by
    nlinarith [hh, hhh, sq_nonneg h']
  have hsqrt := Real.sqrt_le_sqrt hd
  linarith [hsqrt]

/-- The 3-D discriminant is monotone in `h`. -/
theorem disc3_mono {a b c h h' : ℝ} (hhh : 0 ≤ h) (hh : h ≤ h') :
    disc3 a b c h ≤ disc3 a b c h' := by
  unfold disc3
  nlinarith [hh, hhh, sq_nonneg h']

/-- **Monotonicity in the grid size**: for fixed sorted upwind values
    `a ≤ b ≤ c`, the solver output is non-decreasing in `h`. -/
theorem godunov_mono_h {a b c h h' : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hhh : 0 ≤ h) (hh : h ≤ h') :
    godunov a b c h ≤ godunov a b c h' := by
  have hhh' : 0 ≤ h' := le_trans hhh hh
  by_cases h1 : a + h ≤ b
  · rw [godunov_oneD h1]
    by_cases h1' : a + h' ≤ b
    · rw [godunov_oneD h1']; linarith
    · by_cases h2' : godunov2D a b h' ≤ c
      · rw [godunov_twoD h1' h2']
        have h2b := godunov2D_ge_b h1' hab hhh'
        linarith
      · rw [godunov_threeD h1' h2']
        obtain ⟨hd3', hsqrt3'⟩ := disc3_strong h1' h2' hab hbc
        have h2b := godunov2D_ge_b h1' hab hhh'
        have hc3 : b ≤ (a + b + c + Real.sqrt (disc3 a b c h')) / 3 := by
          nlinarith [hsqrt3', hbc]
        linarith
  · by_cases h2 : godunov2D a b h ≤ c
    · rw [godunov_twoD h1 h2]
      by_cases h1' : a + h' ≤ b
      · exfalso
        have : a + h ≤ a + h' := by linarith
        linarith [h1', h1, this]
      · by_cases h2' : godunov2D a b h' ≤ c
        · rw [godunov_twoD h1' h2']; exact godunov2D_mono hhh hh
        · rw [godunov_threeD h1' h2']
          obtain ⟨hd3', hsqrt3'⟩ := disc3_strong h1' h2' hab hbc
          have hcx : c ≤ (a + b + c + Real.sqrt (disc3 a b c h')) / 3 := by
            nlinarith [hsqrt3', hhh']
          exact le_trans h2 hcx
    · rw [godunov_threeD h1 h2]
      by_cases h1' : a + h' ≤ b
      · exfalso
        have : a + h ≤ a + h' := by linarith
        linarith [h1', h1, this]
      · by_cases h2' : godunov2D a b h' ≤ c
        · exfalso
          have hle : godunov2D a b h ≤ godunov2D a b h' := godunov2D_mono hhh hh
          linarith [h2, h2', hle]
        · rw [godunov_threeD h1' h2']
          have hge : Real.sqrt (disc3 a b c h) ≤ Real.sqrt (disc3 a b c h') :=
            Real.sqrt_le_sqrt (disc3_mono hhh hh)
          linarith [hge]



end Vdb
