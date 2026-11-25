/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  3D extension of the staircase inconsistency: a *non-axis-aligned plane* cut.

  The 2D result (`Vdb/StaircaseDiagonal.lean`) shows that the digital line
  `y = x` has `2n − 2` exposed directed faces against a true length of `n√2`,
  so the ratio tends to `√2 ≠ 1`. The L¹-ball family (`Vdb/StaircaseRatio.lean`,
  `Vdb/StaircaseClosed.lean`) gives `√3` in a different way. This module treats
  a third family: the oblique plane `x + y + z = c` on the `(c+1)³` box with
  the interior halfspace `x + y + z ≤ c`.

  Model. Cells are `(x, y, z) ∈ [0, c+1)³`. A directed boundary face is an
  in-window step from an inside cell to an outside cell; out-of-window
  neighbours are not counted, so the box perimeter does not pollute the cut.
  For the lower halfspace the only crossing steps are the `+x`, `+y`, `+z`
  steps from a cell of the slice `x + y + z = c` whose target stays in the box.
  A cell of the slice with `x < c` exposes exactly one `+x` face (its `+x`
  neighbour has sum `c+1`, hence is outside), and similarly for `y` and `z`.

  Closed form. The slice `x + y + z = c` (in the box) is the triangular set
  of lattice points with non-negative coordinates summing to `c`; it has
  `(c+1)(c+2)/2` points. Exactly one of them (`(c,0,0)`) has `x = c`, so the
  `+x` count is `(c+1)(c+2)/2 − 1 = c(c+3)/2`; by symmetry the same holds for
  `+y` and `+z`. Hence

      faces = 3 · c(c+3)/2 = (3/2)c² + O(c).

  The true area of the cut is the equilateral triangle with vertices
  `(c+1,0,0)`, `(0,c+1,0)`, `(0,0,c+1)` (side `(c+1)√2`, area
  `(√3/2)(c+1)²`). Therefore

      faces / trueArea → (3/2) / (√3/2) = √3 ≈ 1.732 ≠ 1.

  We prove the closed form in the `2·faces = 3·c·(c+3)` form (which avoids
  natural-number division), the exact real identity for the ratio, the limit
  `√3`, and non-consistency (`ratio` does not tend to `1`). Pure kernel
  proofs throughout; no placeholders and no `native_decide`.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Vdb

namespace StaircasePlane3D

/-- The interior halfspace cell predicate: `x + y + z ≤ c` on `[0,c+1)³`. -/
def planeInside (c x y z : ℕ) : Prop := x + y + z ≤ c

/-- The staircase (surface-area) estimator for the oblique plane cut: the
     number of directed in-window faces from an inside cell to an outside
     cell. For the lower halfspace only `+x`, `+y`, `+z` steps cross the cut,
     and a crossing occurs exactly at a slice cell with the moving coordinate
     strictly below `c` (so that the target remains in the box). -/
def planeFaces (c : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (c + 1), ∑ y ∈ Finset.range (c + 1), ∑ z ∈ Finset.range (c + 1),
    ((if x + y + z = c ∧ x < c then 1 else 0) +
     (if x + y + z = c ∧ y < c then 1 else 0) +
     (if x + y + z = c ∧ z < c then 1 else 0))

/-- Justification of the definition: a `+x` step at a cell of the box crosses
     from inside to outside iff `x + y + z = c` and `x < c`. -/
theorem planeFaces_step_x (c x y z : ℕ) (hx : x < c + 1) (hy : y < c + 1) (hz : z < c + 1) :
    (planeInside c x y z ∧ x + 1 < c + 1 ∧ ¬ planeInside c (x + 1) y z) ↔
      (x + y + z = c ∧ x < c) := by
  unfold planeInside
  omega

/-- Justification for `+y` and `+z` steps (same computation). -/
theorem planeFaces_step_y (c x y z : ℕ) (hx : x < c + 1) (hy : y < c + 1) (hz : z < c + 1) :
    (planeInside c x y z ∧ y + 1 < c + 1 ∧ ¬ planeInside c x (y + 1) z) ↔
      (x + y + z = c ∧ y < c) := by
  unfold planeInside
  omega

theorem planeFaces_step_z (c x y z : ℕ) (hx : x < c + 1) (hy : y < c + 1) (hz : z < c + 1) :
    (planeInside c x y z ∧ z + 1 < c + 1 ∧ ¬ planeInside c x y (z + 1)) ↔
      (x + y + z = c ∧ z < c) := by
  unfold planeInside
  omega

/-- The true area of the cut: the equilateral triangle with vertices
     `(c+1,0,0)`, `(0,c+1,0)`, `(0,0,c+1)`, i.e. side `(c+1)√2` and area
     `(√3/2)(c+1)²`. -/
noncomputable def planeCutArea (c : ℕ) : ℝ := (Real.sqrt 3 / 2) * ((c : ℝ) + 1) ^ 2

/-! ### Counting the triangular slice -/

set_option maxHeartbeats 800000 in
/-- A slice of the triangle: for fixed first coordinate `t`, the number of
     pairs `(a,b)` in the box with `t + a + b = c` is `c - t + 1` (if `t ≤ c`),
     otherwise `0`. -/
lemma two_slice (c t : ℕ) :
    (∑ a ∈ Finset.range (c + 1), ∑ b ∈ Finset.range (c + 1),
        (if t + a + b = c then 1 else 0 : ℕ)) =
      if t ≤ c then c - t + 1 else 0 := by
  by_cases htc : t ≤ c
  · simp only [htc, ite_true]
    have hb : ∀ a ∈ Finset.range (c + 1),
        (∑ b ∈ Finset.range (c + 1), (if t + a + b = c then 1 else 0 : ℕ)) =
          if t + a ≤ c then 1 else 0 := by
      intro a ha
      by_cases hta : t + a ≤ c
      · rw [Finset.sum_eq_single (c - (t + a))]
        · have heq : t + a + (c - (t + a)) = c := by omega
          simp [heq, hta]
        · intro b hbmem hbne
          have hneq : ¬ (t + a + b = c) := by
            intro heq
            have : b = c - (t + a) := by omega
            exact hbne this
          rw [ite_eq_right hneq]
        · intro hnot
          have hmem : c - (t + a) ∈ Finset.range (c + 1) := by
            simp only [Finset.mem_range]
            omega
          exact (hnot hmem).elim
      · have hzero : ∀ b ∈ Finset.range (c + 1),
            (if t + a + b = c then 1 else 0 : ℕ) = 0 := by
          intro b hbmem
          have hneq : ¬ (t + a + b = c) := by omega
          rw [ite_eq_right hneq]
        rw [Finset.sum_eq_zero hzero]
        simp [hta]
    rw [Finset.sum_congr rfl hb]
    rw [Finset.sum_boole]
    have hf : (Finset.range (c + 1)).filter (fun a => t + a ≤ c) = Finset.range (c - t + 1) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor <;> intro h <;> omega
    rw [hf, Finset.card_range]
    norm_num
  · simp only [htc, ite_false]
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    have hneq : ¬ (t + a + b = c) := by omega
    rw [ite_eq_right hneq]

set_option maxHeartbeats 800000 in
/-- `2 · ∑_{x<N} (N − x) = N·(N+1)`. -/
lemma sum_range_sub_two (N : ℕ) : 2 * (∑ x ∈ Finset.range N, (N - x)) = N * (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hpoint : ∀ x ∈ Finset.range N, (N + 1 - x) = (N - x) + 1 := by
        intro x hx
        have hxN : x ≤ N := by have := Finset.mem_range.mp hx; omega
        omega
      rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib]
      simp
      calc
        2 * ((∑ x ∈ Finset.range N, (N - x)) + N + 1)
            = 2 * (∑ x ∈ Finset.range N, (N - x)) + 2 * N + 2 := by ring
        _ = N * (N + 1) + 2 * N + 2 := by rw [ih]
        _ = (N + 1) * (N + 2) := by ring

set_option maxHeartbeats 800000 in
/-- `2 · ∑_{x<c} (c + 1 − x) = c·(c+3)`. -/
lemma sum_csub_two (c : ℕ) : 2 * (∑ x ∈ Finset.range c, (c + 1 - x)) = c * (c + 3) := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [Finset.sum_range_succ]
      have hpoint : ∀ x ∈ Finset.range c, (c + 2 - x) = (c + 1 - x) + 1 := by
        intro x hx
        have hxc : x ≤ c := by have := Finset.mem_range.mp hx; omega
        omega
      rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib]
      simp
      rw [show c + 1 + 1 - c = 2 by omega]
      calc
        2 * ((∑ x ∈ Finset.range c, (c + 1 - x)) + c + 2)
            = 2 * (∑ x ∈ Finset.range c, (c + 1 - x)) + 2 * c + 4 := by ring
        _ = c * (c + 3) + 2 * c + 4 := by rw [ih]
        _ = (c + 1) * (c + 4) := by ring

set_option maxHeartbeats 800000 in
/-- The common tail of a restricted slice: the sum over `t < c` of the slice
     count at `t`. -/
lemma weighted_lt_sum (c : ℕ) :
    (∑ t ∈ Finset.range (c + 1), (if t < c then c - t + 1 else 0)) =
      ∑ t ∈ Finset.range c, (c + 1 - t) := by
  rw [← Finset.sum_filter]
  have hf : (Finset.range (c + 1)).filter (fun t => t < c) = Finset.range c := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hf]
  apply Finset.sum_congr rfl
  intro t ht
  have htc : t ≤ c := by have := Finset.mem_range.mp ht; omega
  omega

set_option maxHeartbeats 800000 in
/-- The `+x` face count satisfies `2 · count = c(c+3)`. -/
lemma slice_x_two (c : ℕ) :
    2 * (∑ x ∈ Finset.range (c + 1), ∑ y ∈ Finset.range (c + 1), ∑ z ∈ Finset.range (c + 1),
        (if x + y + z = c ∧ x < c then 1 else 0 : ℕ)) = c * (c + 3) := by
  have hterm : ∀ x ∈ Finset.range (c + 1),
      (∑ y ∈ Finset.range (c + 1), ∑ z ∈ Finset.range (c + 1),
        (if x + y + z = c ∧ x < c then 1 else 0 : ℕ)) =
        (if x < c then c - x + 1 else 0) := by
    intro x hx
    by_cases hxc : x < c
    · calc
        (∑ y ∈ Finset.range (c + 1), ∑ z ∈ Finset.range (c + 1),
          (if x + y + z = c ∧ x < c then 1 else 0 : ℕ))
            = ∑ y ∈ Finset.range (c + 1), ∑ z ∈ Finset.range (c + 1),
                (if x + y + z = c then 1 else 0 : ℕ) := by
              apply Finset.sum_congr rfl
              intro y hy
              apply Finset.sum_congr rfl
              intro z hz
              simp [hxc]
        _ = c - x + 1 := by
              rw [two_slice c x]
              simp [le_of_lt hxc]
        _ = (if x < c then c - x + 1 else 0) := by simp [hxc]
    · simp [hxc]
  rw [Finset.sum_congr rfl hterm]
  rw [weighted_lt_sum]
  exact sum_csub_two c

set_option maxHeartbeats 800000 in
/-- The `+y` face count satisfies `2 · count = c(c+3)`. -/
lemma slice_y_two (c : ℕ) :
    2 * (∑ x ∈ Finset.range (c + 1), ∑ y ∈ Finset.range (c + 1), ∑ z ∈ Finset.range (c + 1),
        (if x + y + z = c ∧ y < c then 1 else 0 : ℕ)) = c * (c + 3) := by
  rw [Finset.sum_comm]
  have hterm : ∀ y ∈ Finset.range (c + 1),
      (∑ x ∈ Finset.range (c + 1), ∑ z ∈ Finset.range (c + 1),
        (if x + y + z = c ∧ y < c then 1 else 0 : ℕ)) =
        (if y < c then c - y + 1 else 0) := by
    intro y hy
    by_cases hyc : y < c
    · calc
        (∑ x ∈ Finset.range (c + 1), ∑ z ∈ Finset.range (c + 1),
          (if x + y + z = c ∧ y < c then 1 else 0 : ℕ))
            = ∑ x ∈ Finset.range (c + 1), ∑ z ∈ Finset.range (c + 1),
                (if y + x + z = c then 1 else 0 : ℕ) := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro z hz
              by_cases h1 : x + y + z = c ∧ y < c
              · have h2 : y + x + z = c := by omega
                simp [h1, h2]
              · have h2 : ¬ (y + x + z = c) := by
                  intro hh
                  apply h1
                  constructor <;> omega
                simp [h1, h2]
        _ = c - y + 1 := by
              rw [two_slice c y]
              simp [le_of_lt hyc]
        _ = (if y < c then c - y + 1 else 0) := by simp [hyc]
    · simp [hyc]
  rw [Finset.sum_congr rfl hterm]
  rw [weighted_lt_sum]
  exact sum_csub_two c

set_option maxHeartbeats 800000 in
/-- The `+z` face count satisfies `2 · count = c(c+3)`. -/
lemma slice_z_two (c : ℕ) :
    2 * (∑ x ∈ Finset.range (c + 1), ∑ y ∈ Finset.range (c + 1), ∑ z ∈ Finset.range (c + 1),
        (if x + y + z = c ∧ z < c then 1 else 0 : ℕ)) = c * (c + 3) := by
  have hswap : ∀ x ∈ Finset.range (c + 1),
      (∑ y ∈ Finset.range (c + 1), ∑ z ∈ Finset.range (c + 1),
        (if x + y + z = c ∧ z < c then 1 else 0 : ℕ)) =
      (∑ z ∈ Finset.range (c + 1), ∑ y ∈ Finset.range (c + 1),
        (if x + z + y = c ∧ z < c then 1 else 0 : ℕ)) := by
    intro x hx
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z hz
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h1 : x + y + z = c ∧ z < c
    · have h2 : x + z + y = c ∧ z < c := by constructor <;> omega
      simp [h1, h2]
    · have h2 : ¬ (x + z + y = c ∧ z < c) := by
        intro hh
        apply h1
        constructor <;> omega
      simp [h1, h2]
  rw [Finset.sum_congr rfl hswap]
  rw [Finset.sum_comm]
  have hterm : ∀ z ∈ Finset.range (c + 1),
      (∑ x ∈ Finset.range (c + 1), ∑ y ∈ Finset.range (c + 1),
        (if x + z + y = c ∧ z < c then 1 else 0 : ℕ)) =
        (if z < c then c - z + 1 else 0) := by
    intro z hz
    by_cases hzc : z < c
    · calc
        (∑ x ∈ Finset.range (c + 1), ∑ y ∈ Finset.range (c + 1),
          (if x + z + y = c ∧ z < c then 1 else 0 : ℕ))
            = ∑ x ∈ Finset.range (c + 1), ∑ y ∈ Finset.range (c + 1),
                (if z + x + y = c then 1 else 0 : ℕ) := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro y hy
              by_cases h1 : x + z + y = c ∧ z < c
              · have h2 : z + x + y = c := by omega
                simp [h1, h2]
              · have h2 : ¬ (z + x + y = c) := by
                  intro hh
                  apply h1
                  constructor <;> omega
                simp [h1, h2]
        _ = c - z + 1 := by
              rw [two_slice c z]
              simp [le_of_lt hzc]
        _ = (if z < c then c - z + 1 else 0) := by simp [hzc]
    · simp [hzc]
  rw [Finset.sum_congr rfl hterm]
  rw [weighted_lt_sum]
  exact sum_csub_two c

set_option maxHeartbeats 800000 in
/-- **Closed form (doubled)**: the staircase count of the plane cut satisfies
     `2 · faces = 3 · c · (c + 3)` for every `c`. -/
theorem planeFaces_eq_two (c : ℕ) : 2 * planeFaces c = 3 * c * (c + 3) := by
  unfold planeFaces
  simp only [Finset.sum_add_distrib]
  calc
    2 * ((∑ x ∈ Finset.range (c + 1), ∑ y ∈ Finset.range (c + 1), ∑ z ∈ Finset.range (c + 1),
            (if x + y + z = c ∧ x < c then 1 else 0 : ℕ))
         + (∑ x ∈ Finset.range (c + 1), ∑ y ∈ Finset.range (c + 1), ∑ z ∈ Finset.range (c + 1),
            (if x + y + z = c ∧ y < c then 1 else 0 : ℕ))
         + (∑ x ∈ Finset.range (c + 1), ∑ y ∈ Finset.range (c + 1), ∑ z ∈ Finset.range (c + 1),
            (if x + y + z = c ∧ z < c then 1 else 0 : ℕ)))
        = 2 * (∑ x ∈ Finset.range (c + 1), ∑ y ∈ Finset.range (c + 1), ∑ z ∈ Finset.range (c + 1),
            (if x + y + z = c ∧ x < c then 1 else 0 : ℕ))
          + 2 * (∑ x ∈ Finset.range (c + 1), ∑ y ∈ Finset.range (c + 1), ∑ z ∈ Finset.range (c + 1),
            (if x + y + z = c ∧ y < c then 1 else 0 : ℕ))
          + 2 * (∑ x ∈ Finset.range (c + 1), ∑ y ∈ Finset.range (c + 1), ∑ z ∈ Finset.range (c + 1),
            (if x + y + z = c ∧ z < c then 1 else 0 : ℕ)) := by ring
    _ = c * (c + 3) + c * (c + 3) + c * (c + 3) := by
          rw [slice_x_two c, slice_y_two c, slice_z_two c]
    _ = 3 * c * (c + 3) := by ring

/-- The closed form over `ℝ`: `faces = (3/2)·c·(c+3)`. -/
lemma planeFaces_real (c : ℕ) : (planeFaces c : ℝ) = (3 / 2 : ℝ) * (c : ℝ) * ((c : ℝ) + 3) := by
  have h := planeFaces_eq_two c
  have hR : (2 : ℝ) * (planeFaces c : ℝ) = 3 * (c : ℝ) * ((c : ℝ) + 3) := by
    exact_mod_cast h
  nlinarith

/-! ### The ratio and its limit -/

set_option maxHeartbeats 800000 in
/-- Exact identity for the ratio: it equals `√3 · c(c+3)/(c+1)²`. -/
lemma planeCut_ratio_eq (c : ℕ) :
    (planeFaces c : ℝ) / planeCutArea c =
      Real.sqrt 3 * ((c : ℝ) * ((c : ℝ) + 3) / ((c : ℝ) + 1) ^ 2) := by
  have hSpos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hSsq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc1pos : 0 < (c : ℝ) + 1 := by positivity
  rw [planeFaces_real c]
  unfold planeCutArea
  field_simp [hSpos.ne', hc1pos.ne']
  nlinarith [hSsq]

set_option maxHeartbeats 800000 in
/-- **Limit of the ratio**: `faces / trueArea → √3`. The correction term
     `c(c+3)/(c+1)² = 1 + (c−1)/(c+1)²` tends to `1` because `(c−1)/(c+1)²`
     is squeezed between `0` and `1/(c+1)`. -/
theorem planeFaces_ratio_tendsto :
    Filter.Tendsto (fun c : ℕ => (planeFaces c : ℝ) / planeCutArea c)
      Filter.atTop (nhds (Real.sqrt 3)) := by
  have hden : Filter.Tendsto (fun c : ℕ => (c : ℝ) + 1) Filter.atTop Filter.atTop := by
    simpa using (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hsmall : Filter.Tendsto (fun c : ℕ => (1 : ℝ) / ((c : ℝ) + 1))
      Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop hden
  have hnonneg : ∀ᶠ c : ℕ in Filter.atTop,
      0 ≤ ((c : ℝ) - 1) / ((c : ℝ) + 1) ^ 2 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with c hc
    have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    positivity
  have hle : ∀ᶠ c : ℕ in Filter.atTop,
      ((c : ℝ) - 1) / ((c : ℝ) + 1) ^ 2 ≤ (1 : ℝ) / ((c : ℝ) + 1) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with c hc
    have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    have hc1pos : 0 < (c : ℝ) + 1 := by positivity
    have hsqpos : 0 < ((c : ℝ) + 1) ^ 2 := by positivity
    rw [div_le_div_iff₀ hsqpos hc1pos]
    nlinarith [sq_nonneg ((c : ℝ) + 1)]
  have herr : Filter.Tendsto (fun c : ℕ => ((c : ℝ) - 1) / ((c : ℝ) + 1) ^ 2)
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsmall hnonneg hle
  have hdecomp : ∀ c : ℕ,
      ((c : ℝ) * ((c : ℝ) + 3)) / ((c : ℝ) + 1) ^ 2 =
        1 + ((c : ℝ) - 1) / ((c : ℝ) + 1) ^ 2 := by
    intro c
    have hc1 : (c : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hc1]
    ring
  have hg : Filter.Tendsto (fun c : ℕ => ((c : ℝ) * ((c : ℝ) + 3)) / ((c : ℝ) + 1) ^ 2)
      Filter.atTop (nhds 1) := by
    simp_rw [hdecomp]
    simpa using (tendsto_const_nhds.add herr)
  have hmul : Filter.Tendsto
      (fun c : ℕ => Real.sqrt 3 * (((c : ℝ) * ((c : ℝ) + 3)) / ((c : ℝ) + 1) ^ 2))
      Filter.atTop (nhds (Real.sqrt 3 * 1)) := tendsto_const_nhds.mul hg
  simpa [planeCut_ratio_eq] using hmul

set_option maxHeartbeats 800000 in
/-- **Non-consistency of the 3D plane cut**: the ratio does not tend to `1`
     (its limit is `√3 > 1`). -/
theorem planeFaces_ratio_not_tendsto_one :
    ¬ Filter.Tendsto (fun c : ℕ => (planeFaces c : ℝ) / planeCutArea c)
        Filter.atTop (nhds 1) := by
  intro h
  have hlim := planeFaces_ratio_tendsto
  have heq : Real.sqrt 3 = (1 : ℝ) := tendsto_nhds_unique hlim h
  have hgt : (1 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
  linarith

end StaircasePlane3D

end Vdb
