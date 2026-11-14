/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  The tree fast-sweeping relaxation (`sdf_eikonal` in
  `src/tinyvdb_sdf_tree.c`), modelled with `⊤ = inactive`.

  `tvdb_sdf_tree_fast_sweep` initialises every active voxel to `INFINITY`
  except the frozen band (the `av <= band` branch: frozen voxels take the
  exact value, everything else becomes `∞`), and relaxes with `sdf_eikonal`,
  a `tvdb__godunov_solve` variant that returns `INFINITY` when its smallest
  upwind value is `∞` (i.e. when no axis has a finite neighbor) and keeps
  the same branch structure otherwise — with the differences that
  (i) it does its own internal three-way sort instead of expecting
      pre-sorted input, and
  (ii) its discriminant fallbacks clamp `disc < 0` to `0` (the same clamp
      as in `tvdb__godunov_solve`; on sorted triples the discriminants are
      non-negative on every branch that reaches them — see
      `disc2_nonneg` / `disc3_strong` in `Vdb.Godunov`).

  This module models the tree operator directly:

  * `eikonalLo` / `eikonalMid` / `eikonalHi` — the three-way sort as a lattice computation
    irrelevant to proofs; no if-then-else);
  * `eikonalRelax a b c h` — the `WithTop ℝ` relaxation: sorted
    quadruple dispatch `(⊤,⊤,⊤) / (finite,⊤,⊤) / (finite,finite,⊤) /
    (finite,finite,finite)`, mirroring the C's branches exactly;
  * `eikonalRelax_eq_godunov` — on sorted finite triples it is exactly
    the `godunov` of `Vdb.Godunov` (the `max 0` clamps are identities,
    and `Real.sqrt` of a non-positive number is `0` anyway — matching
    the C's `disc < 0` clamp);
  * `eikonalRelax_nonneg` — non-negative boundary data gives a
    non-negative result (`⊤` allowed), which is what the frozen-band
    initialization of the tree sweep provides.

  What is *not* claimed here: convergence of the 8-direction sweep
  (Zhao 2005), and uniqueness of the fixed point. What is claimed about
  the operator follows from `Vdb.FastSweep` (monotonicity, frozen
  invariance, lower bound) and `Vdb.Godunov` (the solve and its spec)
  on top of the model.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Godunov
import Vdb.FastSweep
import Mathlib.Basic.Real.Basic
import Mathlib.Order.WithBot
import Mathlib.Tactic


set_option linter.unusedSimpArgs false

namespace Vdb

/-! ### Sorting helpers on `WithTop ℝ` -/

/-- A helper for the non-negativity proof: a coercion of a non-negative
    real is non-negative. -/
theorem withTop_nonneg {x : ℝ} (hx : 0 ≤ x) : (0 : WithTop ℝ) ≤ (x : WithTop ℝ) :=
  WithTop.coe_le_coe.mpr hx

/-- A helper: the default bound used by `untopD` at `⊤` is `0`. -/
theorem untopD_nonneg' {a : WithTop ℝ} (ha : 0 ≤ a) : 0 ≤ WithTop.untopD 0 a := by
  cases a with
  | top => exact le_rfl
  | coe a₀ => exact WithTop.coe_le_coe.mp ha

theorem godunov2D_nonneg {a b h : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ godunov2D a b h := by
  unfold godunov2D
  have hs := Real.sqrt_nonneg (2 * h ^ 2 - (a - b) ^ 2)
  linarith

/-- The 2-D candidate used by the solver is non-negative at
    non-negative arguments. -/
theorem godunov2D_nonneg_of_nonneg (x y h : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ (x + y + Real.sqrt (max 0 (2 * h ^ 2 - (x - y) ^ 2))) / 2 := by
  have hs := Real.sqrt_nonneg (max 0 (2 * h ^ 2 - (x - y) ^ 2))
  linarith

/-- The 3-D candidate used by the solver is non-negative at
    non-negative arguments. -/
theorem threeD_nonneg_of_nonneg (x y z h : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ (x + y + z +
        Real.sqrt (max 0 (3 * h ^ 2 - (x - y) ^ 2 - (x - z) ^ 2 - (y - z) ^ 2))) / 3 := by
  have hs := Real.sqrt_nonneg (max 0 (3 * h ^ 2 - (x - y) ^ 2 - (x - z) ^ 2 - (y - z) ^ 2))
  linarith

/-! ### The relaxation -/

/-- The smallest of the triple. -/
def eikonalLo (a b c : WithTop ℝ) : WithTop ℝ := min (min a b) c

/-- The middle of the triple. -/
def eikonalMid (a b c : WithTop ℝ) : WithTop ℝ :=
  max (max (min a b) (min a c)) (min b c)

/-- The largest of the triple. -/
def eikonalHi (a b c : WithTop ℝ) : WithTop ℝ := max (max a b) c

/-- The tree fast-sweeping relaxation (`sdf_eikonal`), with `⊤ = ∞`
    (inactive). The triple is sorted internally by `eikonalLo/Mid/Hi`;
    the branch structure mirrors the C exactly:

    * smallest = `⊤` → `⊤` (all-inactive neighborhood);
    * exactly one finite (middle = `⊤`) → `a + h`;
    * exactly two finite (largest = `⊤`) →
      `a + h` if `a + h ≤ b`, else the 2-D solve;
    * three finite → `a + h` if `a + h ≤ b`, the 2-D solve
      if `godunov2D a b h ≤ c`, else the 3-D solve.

    The `max 0` clamps on the discriminants match the C's `disc < 0`
    fallback. -/
noncomputable def eikonalRelax (a b c : WithTop ℝ) (h : ℝ) : WithTop ℝ :=
  if eikonalLo a b c = ⊤ then ⊤
  else if eikonalMid a b c = ⊤ then ↑(WithTop.untopD 0 (eikonalLo a b c) + h)
  else if eikonalHi a b c = ⊤ then
    if ↑(WithTop.untopD 0 (eikonalLo a b c) + h) ≤
        (↑(WithTop.untopD 0 (eikonalMid a b c)) : WithTop ℝ) then
      ↑(WithTop.untopD 0 (eikonalLo a b c) + h)
    else ↑(godunov2D (WithTop.untopD 0 (eikonalLo a b c)) (WithTop.untopD 0 (eikonalMid a b c)) h)
  else
    if ↑(WithTop.untopD 0 (eikonalLo a b c) + h) ≤
        (↑(WithTop.untopD 0 (eikonalMid a b c)) : WithTop ℝ) then
      ↑(WithTop.untopD 0 (eikonalLo a b c) + h)
    else if (godunov2D (WithTop.untopD 0 (eikonalLo a b c)) (WithTop.untopD 0 (eikonalMid a b c)) h : WithTop ℝ) ≤
        (↑(WithTop.untopD 0 (eikonalHi a b c)) : WithTop ℝ) then
      ↑(godunov2D (WithTop.untopD 0 (eikonalLo a b c)) (WithTop.untopD 0 (eikonalMid a b c)) h)
    else ↑((WithTop.untopD 0 (eikonalLo a b c) + WithTop.untopD 0 (eikonalMid a b c) +
        WithTop.untopD 0 (eikonalHi a b c) +
        Real.sqrt (max 0 (disc3 (WithTop.untopD 0 (eikonalLo a b c)) (WithTop.untopD 0 (eikonalMid a b c))
          (WithTop.untopD 0 (eikonalHi a b c)) h))) / 3)

theorem eikonalRelax_top_top_top (h : ℝ) :
    eikonalRelax ⊤ ⊤ ⊤ h = ⊤ := by
  unfold eikonalRelax eikonalLo eikonalMid eikonalHi
  simp

/-- A helper for coercion normalization. -/
theorem coe_add_le_iff {a h b : ℝ} : (↑a : WithTop ℝ) + ↑h ≤ (↑b : WithTop ℝ) ↔ a + h ≤ b := by
  rw [← WithTop.coe_add, WithTop.coe_le_coe]

/-- A helper for coercion normalization. -/
theorem coe_lt_iff {a h b : ℝ} : (↑a : WithTop ℝ) + ↑h < (↑b : WithTop ℝ) ↔ a + h < b := by
  rw [← WithTop.coe_add, WithTop.coe_lt_coe]

/-- For a sorted finite triple the relaxation is exactly `godunov` —
    the `max 0` clamps are identities here (or `Real.sqrt` of a
    non-positive number is `0`, matching the C's `disc < 0` clamp). -/
theorem eikonalRelax_eq_godunov {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (h : ℝ) :
    eikonalRelax (a : WithTop ℝ) (b : WithTop ℝ) (c : WithTop ℝ) h =
      (godunov a b c h : WithTop ℝ) := by
  have habw : (a : WithTop ℝ) ≤ (b : WithTop ℝ) := by simpa [WithTop.coe_le_coe] using hab
  have hbcw : (b : WithTop ℝ) ≤ (c : WithTop ℝ) := by simpa [WithTop.coe_le_coe] using hbc
  have hacw : (a : WithTop ℝ) ≤ (c : WithTop ℝ) := le_trans habw hbcw
  unfold eikonalRelax eikonalLo eikonalMid eikonalHi
  rw [min_eq_left habw, max_eq_right habw, min_eq_left hacw, min_eq_left hbcw,
      max_self, max_eq_right habw, max_eq_right hbcw]
  simp only [WithTop.untopD_coe, WithTop.coe_ne_top]
  by_cases hxb : a + h ≤ b
  · simp only [WithTop.untopD_coe, WithTop.coe_ne_top, WithTop.coe_le_coe, godunov, godunov2D, disc3]
    simp [hxb, ite_true, godunov, godunov2D, disc3]
  · simp only [WithTop.untopD_coe, WithTop.coe_ne_top, WithTop.coe_le_coe, godunov, godunov2D, disc3]
    by_cases hx2c : godunov2D a b h ≤ c
    · by_cases h2 : (a + b + √(2 * h ^ 2 - (a - b) ^ 2)) / 2 ≤ c
      · rw [ite_eq_left h2]
        simp [hxb, h2]
      · rw [ite_eq_right h2]
        have hd3 : 0 ≤ 3 * h ^ 2 - (a - b) ^ 2 - (a - c) ^ 2 - (b - c) ^ 2 := (disc3_strong hxb h2 hab hbc).1
        rw [max_eq_right hd3]
        simp [hxb, h2]
    · by_cases h2 : (a + b + √(2 * h ^ 2 - (a - b) ^ 2)) / 2 ≤ c
      · rw [ite_eq_left h2]
        simp [hxb, h2]
      · rw [ite_eq_right h2]
        have hd3 : 0 ≤ 3 * h ^ 2 - (a - b) ^ 2 - (a - c) ^ 2 - (b - c) ^ 2 := (disc3_strong hxb h2 hab hbc).1
        rw [max_eq_right hd3]
        simp [hxb, h2]

/-- Non-negative boundary data (with `⊤` allowed) and non-negative `h`
    give a non-negative result; every reachable leaf is `⊤` or a
    coercion of an explicit non-negative real. -/
theorem eikonalRelax_nonneg {a b c : WithTop ℝ} {h : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hh : 0 ≤ h) :
    0 ≤ eikonalRelax a b c h := by
  have hlo : 0 ≤ eikonalLo a b c := le_min (le_min ha hb) hc
  have hmid : 0 ≤ eikonalMid a b c :=
    le_trans (le_trans (le_min ha hb) (le_max_left (min a b) (min a c)))
      (le_max_left _ (min b c))
  have hhi : 0 ≤ eikonalHi a b c :=
    le_trans (le_trans ha (le_max_left a b)) (le_max_left _ c)
  have key0 : 0 ≤ WithTop.untopD 0 (eikonalLo a b c) := untopD_nonneg' hlo
  have key1 : 0 ≤ WithTop.untopD 0 (eikonalMid a b c) := untopD_nonneg' hmid
  have key2 : 0 ≤ WithTop.untopD 0 (eikonalHi a b c) := untopD_nonneg' hhi
  unfold eikonalRelax
  split_ifs
  all_goals (first
    | exact le_top
    | exact withTop_nonneg (by linarith [key0, key1, hh])
    | exact withTop_nonneg (godunov2D_nonneg key0 key1)
    | exact withTop_nonneg (threeD_nonneg_of_nonneg _ _ _ _ key0 key1 key2))

end Vdb
