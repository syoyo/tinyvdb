/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  A-section: staircase estimator consistency for general sets.

  The staircase surface-area estimator is known NOT to be consistent: the
  octahedron family (`Vdb/StaircaseRatio.lean`, `Vdb/StaircaseClosed.lean`)
  overshoots the true area by a factor tending to `√3`. This module extends
  the negative result to a *non-axis-aligned planar cut*, in two dimensions,
  with an explicit constant: the digitisation of the line `y = x` on an
  `n × n` window has exactly `2n − 2` exposed directed faces, whereas the
  true length of the cut is `n·√2`. Hence

      faces / trueLength = (2n − 2) / (n·√2)  →  √2  ≈ 1.414  ≠  1.

  Concretely we prove (for `n ≥ 20`) `faces ≥ (4/3) · trueLength`, and the
  sharp version (for `n ≥ 110`) `faces ≥ (7/5) · trueLength`, and therefore
  that the ratio does not tend to `1`. This is the 2D analogue of the 3D
  octahedron overshoot, for a *different* geometric family (a sloped plane),
  and with a *different* limiting constant (`√2`).

  Model. Cells are `(x, y) ∈ [0,n)²`. The inside set is the lower triangle
  `y ≤ x`. A directed boundary face is an in-window step from an inside cell
  to an outside cell; out-of-window neighbours are not counted, so the box
  perimeter does not pollute the cut. For the lower triangle the only such
  steps are, at a diagonal cell `(x, x)`, the `-x` step to `(x−1, x)` (when
  `x > 0`) and the `+y` step to `(x, x+1)` (when `x+1 < n`); every other
  inside cell has all four in-window neighbours inside. This is proved below
  by `omega` (`diagFaces_eq`).

  Pure kernel proofs throughout; no placeholders and no `native_decide`.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Vdb

namespace StaircaseDiagonal

/-- The lower triangle `y ≤ x` inside the `n × n` window (a 2D digital set). -/
def insideDiag (x y : ℕ) : Prop := y ≤ x

/-- The staircase (surface-area) estimator for the diagonal cut: the number
    of directed in-window faces from an inside cell to an outside cell.

    For a cell `(x,y)` with `y ≤ x`, the `-x` neighbour `(x−1,y)` exists
    iff `0 < x` and is outside iff `x−1 < y`; the `+y` neighbour `(x,y+1)`
    exists iff `y+1 < n` and is outside iff `x < y+1`. Both conditions are
    equivalent (under `y ≤ x`) to `y = x`, which `diagFaces_eq` establishes.
    The `+x` and `-y` neighbours of an inside cell are always inside. -/
def diagFaces (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n,
    ((if y ≤ x ∧ 0 < x ∧ x - 1 < y then 1 else 0) +
     (if y ≤ x ∧ y + 1 < n ∧ x < y + 1 then 1 else 0))

set_option maxHeartbeats 800000 in
/-- **Closed form**: the diagonal cut of an `n × n` window has exactly
    `2n − 2` exposed directed faces (for `n = 0` this is `0`). -/
theorem diagFaces_eq (n : ℕ) : diagFaces n = 2 * n - 2 := by
  unfold diagFaces
  have hleft : ∀ x ∈ Finset.range n,
      (∑ y ∈ Finset.range n,
        (if y ≤ x ∧ 0 < x ∧ x - 1 < y then 1 else 0 : ℕ)) =
      (if 0 < x then 1 else 0) := by
    intro x hx
    have hxn : x < n := Finset.mem_range.mp hx
    by_cases hxp : 0 < x
    · simp only [hxp, true_and]
      rw [Finset.sum_eq_single x]
      · have hsub : x - 1 < x := by omega
        simp [hsub]
      · intro b hb hbne
        have hnot : ¬ (b ≤ x ∧ x - 1 < b) := by omega
        rw [ite_eq_right hnot]
      · intro hnot
        exact (hnot hx).elim
    · simp [hxp]
  have hright : ∀ x ∈ Finset.range n,
      (∑ y ∈ Finset.range n,
        (if y ≤ x ∧ y + 1 < n ∧ x < y + 1 then 1 else 0 : ℕ)) =
      (if x + 1 < n then 1 else 0) := by
    intro x hx
    have hxn : x < n := Finset.mem_range.mp hx
    by_cases hlast : x + 1 < n
    · rw [Finset.sum_eq_single x]
      · have hstep : x < x + 1 := by omega
        simp [hlast, hstep]
      · intro b hb hbne
        have hnot : ¬ (b ≤ x ∧ b + 1 < n ∧ x < b + 1) := by omega
        rw [ite_eq_right hnot]
      · intro hnot
        exact (hnot hx).elim
    · have hzero : ∀ y ∈ Finset.range n,
          (if y ≤ x ∧ y + 1 < n ∧ x < y + 1 then 1 else 0 : ℕ) = 0 := by
        intro y hy
        have hfalse : ¬ (y ≤ x ∧ y + 1 < n ∧ x < y + 1) := by
          intro hc
          have : y = x := by omega
          omega
        rw [ite_eq_right hfalse]
      rw [Finset.sum_eq_zero hzero]
      simp [hlast]
  rw [Finset.sum_congr rfl (fun x hx => by
    rw [Finset.sum_add_distrib, hleft x hx, hright x hx])]
  rw [Finset.sum_add_distrib]
  have c1 : (∑ x ∈ Finset.range n, (if 0 < x then 1 else 0 : ℕ)) = n - 1 := by
    rw [Finset.sum_boole]
    have hf : (Finset.range n).filter (fun x => 0 < x) = Finset.Ico 1 n := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hf, Nat.card_Ico]
    simp
  have c2 : (∑ x ∈ Finset.range n, (if x + 1 < n then 1 else 0 : ℕ)) = n - 1 := by
    rw [Finset.sum_boole]
    have hf : (Finset.range n).filter (fun x => x + 1 < n) = Finset.Ico 0 (n - 1) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hf, Nat.card_Ico]
    simp
  rw [c1, c2]
  omega

/-- The true length of the cut: the segment `y = x` across the `n × n`
    window has length `n·√2`. -/
noncomputable def diagLength (n : ℕ) : ℝ := (n : ℝ) * Real.sqrt 2

set_option maxHeartbeats 800000 in
/-- **Non-consistency (quantitative)**: for every `n ≥ 20` the estimator
    overcounts the true diagonal length by at least a factor `4/3`. -/
theorem diagFaces_lower_bound (n : ℕ) (hn : 20 ≤ n) :
    (4 / 3 : ℝ) * diagLength n ≤ (diagFaces n : ℝ) := by
  have hdn : (diagFaces n : ℝ) = 2 * (n : ℝ) - 2 := by
    rw [diagFaces_eq]
    have hle : 2 ≤ 2 * n := by omega
    rw [Nat.cast_sub hle]
    push_cast
    ring
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := by
    rw [Real.sq_sqrt]
    norm_num
  have hsnonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsle : Real.sqrt 2 ≤ 99 / 70 := by
    nlinarith [sq_nonneg (Real.sqrt 2 - 99 / 70)]
  have hnR : (20 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  unfold diagLength
  rw [hdn]
  nlinarith

set_option maxHeartbeats 800000 in
/-- The sharper constant `7/5` (which is `< √2`) holds for `n ≥ 110`. -/
theorem diagFaces_lower_bound_sharp (n : ℕ) (hn : 110 ≤ n) :
    (7 / 5 : ℝ) * diagLength n ≤ (diagFaces n : ℝ) := by
  have hdn : (diagFaces n : ℝ) = 2 * (n : ℝ) - 2 := by
    rw [diagFaces_eq]
    have hle : 2 ≤ 2 * n := by omega
    rw [Nat.cast_sub hle]
    push_cast
    ring
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := by
    rw [Real.sq_sqrt]
    norm_num
  have hsnonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsle : Real.sqrt 2 ≤ 283 / 200 := by
    nlinarith [sq_nonneg (Real.sqrt 2 - 283 / 200)]
  have hnR : (110 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  unfold diagLength
  rw [hdn]
  nlinarith

set_option maxHeartbeats 800000 in
/-- **The estimator is not consistent**: the ratio
    `faces / trueLength` does not tend to `1` (it is eventually ≥ `4/3`,
    while convergence to `1` would force it eventually `< 5/4`). -/
theorem diagFaces_ratio_not_tendsto_one :
    ¬ Filter.Tendsto
        (fun n : ℕ => (diagFaces n : ℝ) / diagLength n)
        Filter.atTop (nhds 1) := by
  intro h
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      (diagFaces n : ℝ) / diagLength n < 5 / 4 := by
    exact h.eventually (isOpen_Iio.mem_nhds (show (1 : ℝ) ∈ Set.Iio (5 / 4) from by norm_num))
  have hbig : ∀ᶠ n : ℕ in Filter.atTop, 20 ≤ n := Filter.eventually_ge_atTop 20
  have hfalse : ∀ᶠ n : ℕ in Filter.atTop, False := by
    filter_upwards [hsmall, hbig] with n hnsmall hn
    have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hdenpos : 0 < diagLength n := by
      unfold diagLength
      positivity
    have hlow := diagFaces_lower_bound n hn
    have hratio : (4 / 3 : ℝ) ≤ (diagFaces n : ℝ) / diagLength n := by
      rw [le_div_iff₀ hdenpos]
      exact hlow
    linarith
  rcases hfalse.exists with ⟨n, hn⟩
  exact hn.elim

/-
  General integer slope: the digital line `y = a·x` (the `b = 1` member of the
  rational family `y = (a/b)·x`), for an arbitrary positive integer `a`.

  This is the preferred closed-form instance of the general slope family: the
  staircase count is exactly `n + (n−2)/a` (`lineFaces_eq`), the true length of
  the cut across the window is `n·√(a²+1)/a` (`lineLength`), and the ratio
  `faces / length` tends to `(a+1)/√(a²+1) > 1`
  (`lineFaces_ratio_tendsto`, `lineFaces_ratio_not_tendsto_one`). The case
  `a = 1` specialises to `2n − 2` and `n√2`, i.e. the 45° result above.

  The rational slope `a/b` with `b > 1` is now proved below
  (`ratLineFaces_eq`, `ratLineFaces_ratio_tendsto`): for `a, b > 0`, `n ≥ 2`
  the count is
      min (a·(n−1)/b) (n−1) + min n (((n−1)·b − 1)/a + 1),
  with ratio limit `(a+b)/√(a²+b²)` against length `n·√(a²+b²)/b` when
  `a ≤ b` (and `n·√(a²+b²)/a` when `a > b`). Coprimality is not needed.
-/

/-- The inside set for the digital line `y = a·x`: the lower cells `y ≤ a·x`. -/
def insideLine (a x y : ℕ) : Prop := y ≤ a * x

/-- The staircase estimator for the digital line `y = a·x` on `[0,n)²`: the
    directed in-window faces from an inside cell to an outside cell. Exactly as
    for the diagonal, the `-x` and `+y` steps are the only boundary steps. -/
def lineFaces (a n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n,
    ((if y ≤ a*x ∧ 0 < x ∧ a*(x-1) < y then 1 else 0) +
     (if y ≤ a*x ∧ y+1 < n ∧ a*x < y+1 then 1 else 0))

set_option maxHeartbeats 800000 in
/-- Telescoping for `∑_{x<n} (m x − m (x−1))` when `m` is monotone (the `x=0`
    term is zero). All arithmetic is in `ℕ`, so the terms are truncated. -/
lemma sum_range_pred_sub (m : ℕ → ℕ) (N : ℕ) (hmono : ∀ k, m k ≤ m (k+1)) :
    (∑ x ∈ Finset.range N, (if 0 < x then m x - m (x-1) else 0)) = m (N-1) - m 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases hN : N = 0
      · subst N
        simp
      · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
        have hmono' : Monotone m := monotone_nat_of_le_succ hmono
        have hle0 : m 0 ≤ m (N-1) := hmono' (Nat.zero_le (N-1))
        have hle1 : m (N-1) ≤ m N := hmono' (by omega)
        simp [hNpos]
        omega

set_option maxHeartbeats 800000 in
/-- **Closed form for an arbitrary integer slope**: for `a > 0` and `n ≥ 2`,
    the digital line `y = a·x` on the `n × n` window exposes exactly
    `n + (n−2)/a` directed faces. (The `-x` steps telescope to `n−1`, the `+y`
    steps are one per column `x` with `a·x ≤ n−2`.) -/
theorem lineFaces_eq (a n : ℕ) (ha : 0 < a) (hn : 2 ≤ n) :
    lineFaces a n = n + (n-2)/a := by
  have hleft : ∀ x ∈ Finset.range n,
      (∑ y ∈ Finset.range n,
        (if y ≤ a*x ∧ 0 < x ∧ a*(x-1) < y then 1 else 0 : ℕ)) =
      (if 0 < x then min (a*x) (n-1) - a*(x-1) else 0) := by
    intro x hx
    by_cases hxp : 0 < x
    · simp only [hxp, true_and]
      rw [Finset.sum_boole]
      have hset : (Finset.range n).filter (fun y => y ≤ a*x ∧ a*(x-1) < y) =
          Finset.Ioc (a*(x-1)) (min (a*x) (n-1)) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
        constructor <;> intro h <;> omega
      rw [hset, Nat.card_Ioc]
      simp [hxp]
    · simp [hxp]
  have hright : ∀ x ∈ Finset.range n,
      (∑ y ∈ Finset.range n,
        (if y ≤ a*x ∧ y+1 < n ∧ a*x < y+1 then 1 else 0 : ℕ)) =
      (if a*x + 1 < n then 1 else 0) := by
    intro x hx
    have hxn : x < n := Finset.mem_range.mp hx
    by_cases hax : a*x < n
    · rw [Finset.sum_eq_single (a*x)]
      · have hstep : a*x < a*x + 1 := by omega
        simp [hstep]
      · intro b hb hbne
        have hnot : ¬ (b ≤ a*x ∧ b+1 < n ∧ a*x < b+1) := by
          intro hc
          have : b = a*x := by omega
          exact hbne this
        rw [ite_eq_right hnot]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr hax)).elim
    · have hzero : ∀ y ∈ Finset.range n,
          (if y ≤ a*x ∧ y+1 < n ∧ a*x < y+1 then 1 else 0 : ℕ) = 0 := by
        intro y hy
        have hfalse : ¬ (y ≤ a*x ∧ y+1 < n ∧ a*x < y+1) := by
          intro hc
          have : y = a*x := by omega
          have hyn : y < n := Finset.mem_range.mp hy
          omega
        rw [ite_eq_right hfalse]
      rw [Finset.sum_eq_zero hzero]
      have hnot : ¬ (a*x + 1 < n) := by omega
      simp [hnot]
  have hm_mono : ∀ k, min (a*k) (n-1) ≤ min (a*(k+1)) (n-1) := by
    intro k
    have hmul : a*k ≤ a*(k+1) := Nat.mul_le_mul_left a (by omega)
    omega
  have hleft_term : ∀ x ∈ Finset.range n,
      (if 0 < x then min (a*x) (n-1) - a*(x-1) else 0) =
      (if 0 < x then min (a*x) (n-1) - min (a*(x-1)) (n-1) else 0) := by
    intro x hx
    by_cases hxp : 0 < x
    · simp only [hxp, ite_true]
      have hmul : a*(x-1) ≤ a*x := Nat.mul_le_mul_left a (Nat.sub_le x 1)
      by_cases hlt : a*(x-1) < n - 1
      · have hm : min (a*(x-1)) (n-1) = a*(x-1) := by omega
        rw [hm]
      · have hge : n - 1 ≤ a*(x-1) := by omega
        have hm1 : min (a*(x-1)) (n-1) = n-1 := by omega
        have hm2 : min (a*x) (n-1) = n-1 := by omega
        rw [hm1, hm2]
        omega
    · simp [hxp]
  have hleft_sum : (∑ x ∈ Finset.range n,
      (if 0 < x then min (a*x) (n-1) - a*(x-1) else 0)) = n - 1 := by
    rw [Finset.sum_congr rfl hleft_term]
    rw [sum_range_pred_sub (fun k => min (a*k) (n-1)) n hm_mono]
    have hm0 : min (a*0) (n-1) = 0 := by simp
    have hmN : min (a*(n-1)) (n-1) = n-1 := by
      have hge : n-1 ≤ a*(n-1) := by
        have : 1 ≤ a := ha
        nlinarith
      omega
    rw [hm0, hmN]
    omega
  have hright_sum : (∑ x ∈ Finset.range n, (if a*x + 1 < n then 1 else 0)) = (n-2)/a + 1 := by
    rw [Finset.sum_boole]
    have hset : (Finset.range n).filter (fun x => a*x + 1 < n) = Finset.range ((n-2)/a + 1) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · intro h
        have hxax : a*x ≤ n-2 := by omega
        have hxle : x ≤ (n-2)/a := (Nat.le_div_iff_mul_le ha).2 (by simpa [Nat.mul_comm] using hxax)
        have hdivle : (n-2)/a ≤ n-2 := Nat.div_le_self (n-2) a
        omega
      · intro h
        have hxle : x ≤ (n-2)/a := by omega
        have hxax : a*x ≤ n-2 := by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha).1 hxle
        have hdivle : (n-2)/a ≤ n-2 := Nat.div_le_self (n-2) a
        omega
    rw [hset, Finset.card_range]
    simp
  unfold lineFaces
  rw [Finset.sum_congr rfl (fun x hx => by
    rw [Finset.sum_add_distrib, hleft x hx, hright x hx])]
  rw [Finset.sum_add_distrib, hleft_sum, hright_sum]
  omega

/-- The true length of the cut of the line `y = a·x`: the segment from `(0,0)`
    to `(n/a, n)` has length `n·√(a²+1)/a` (for `a = 1` this is `n√2`). -/
noncomputable def lineLength (a n : ℕ) : ℝ := (n : ℝ) * Real.sqrt ((a:ℝ)^2 + 1) / (a : ℝ)

set_option maxHeartbeats 800000 in
/-- **Sharp constant**: for `a > 0`, the ratio `faces / trueLength` of the
    integer-slope digital line tends to `(a+1)/√(a²+1)`, which is `> 1`
    (for `a = 1` this recovers the limit `√2`). -/
theorem lineFaces_ratio_tendsto (a : ℕ) (ha : 0 < a) :
    Filter.Tendsto (fun n : ℕ => (lineFaces a n : ℝ) / lineLength a n)
      Filter.atTop (nhds (((a:ℝ) + 1) / Real.sqrt ((a:ℝ)^2 + 1))) := by
  let S : ℝ := Real.sqrt ((a:ℝ)^2 + 1)
  let T : ℝ := ((a:ℝ) + 1) / S
  have hSpos : 0 < S := by
    dsimp [S]
    positivity
  have han : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hden_tendsto : Filter.Tendsto (fun n : ℕ => (n:ℝ) * S) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hSpos
  have hg : Filter.Tendsto (fun n : ℕ => T - ((a:ℝ)+2) / ((n:ℝ) * S)) Filter.atTop (nhds T) := by
    have hzero : Filter.Tendsto (fun n : ℕ => ((a:ℝ)+2) / ((n:ℝ) * S)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hden_tendsto
    simpa using (tendsto_const_nhds.sub hzero)
  have hh : Filter.Tendsto (fun n : ℕ => T) Filter.atTop (nhds T) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hh
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hnpos : 0 < n := by omega
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
    have hden : 0 < (n:ℝ) * S := mul_pos hnR hSpos
    have hlen : 0 < lineLength a n := by
      unfold lineLength
      dsimp [S] at hSpos
      positivity
    have hqa_le : (a:ℝ) * (((n-2)/a : ℕ) : ℝ) ≤ (n:ℝ) := by
      have hnat : ((n-2)/a) * a ≤ n-2 := Nat.div_mul_le_self (n-2) a
      have hnat' : a * ((n-2)/a) ≤ n := by
        rw [Nat.mul_comm]
        omega
      exact_mod_cast hnat'
    have hnat_lt : n - 2 < ((n-2)/a + 1) * a :=
      (Nat.div_lt_iff_lt_mul ha).1 (by omega)
    have hnat_lt' : n - 2 < ((n-2)/a) * a + a := by
      simpa [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hnat_lt
    have hnat : n ≤ ((n-2)/a) * a + a + 2 := by omega
    have hgap : (n:ℝ) - (a:ℝ) * (((n-2)/a : ℕ) : ℝ) ≤ (a:ℝ) + 2 := by
      have hnatR : (n:ℝ) ≤ (((n-2)/a : ℕ) : ℝ) * (a:ℝ) + (a:ℝ) + 2 := by
        exact_mod_cast hnat
      nlinarith
    have hR : (lineFaces a n : ℝ) / lineLength a n =
        ((n:ℝ) + (((n-2)/a : ℕ) : ℝ)) * (a:ℝ) / ((n:ℝ) * S) := by
      rw [lineFaces_eq a n ha (by omega)]
      unfold lineLength
      push_cast
      field_simp [hden.ne', han.ne']
      ring
    rw [hR]
    have hdiff : T - ((n:ℝ) + (((n-2)/a : ℕ) : ℝ)) * (a:ℝ) / ((n:ℝ) * S) =
        ((n:ℝ) - (a:ℝ) * (((n-2)/a : ℕ) : ℝ)) / ((n:ℝ) * S) := by
      dsimp [T]
      field_simp [hSpos.ne', hden.ne']
      ring
    have hdivle : ((n:ℝ) - (a:ℝ) * (((n-2)/a : ℕ) : ℝ)) / ((n:ℝ) * S) ≤
        ((a:ℝ)+2) / ((n:ℝ) * S) := (div_le_div_iff_of_pos_right hden).2 hgap
    linarith
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hnpos : 0 < n := by omega
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
    have hden : 0 < (n:ℝ) * S := mul_pos hnR hSpos
    have hqa_le : (a:ℝ) * (((n-2)/a : ℕ) : ℝ) ≤ (n:ℝ) := by
      have hnat : ((n-2)/a) * a ≤ n-2 := Nat.div_mul_le_self (n-2) a
      have hnat' : a * ((n-2)/a) ≤ n := by
        rw [Nat.mul_comm]
        omega
      exact_mod_cast hnat'
    have hR : (lineFaces a n : ℝ) / lineLength a n =
        ((n:ℝ) + (((n-2)/a : ℕ) : ℝ)) * (a:ℝ) / ((n:ℝ) * S) := by
      rw [lineFaces_eq a n ha (by omega)]
      unfold lineLength
      push_cast
      field_simp [hden.ne', han.ne']
      ring
    rw [hR]
    dsimp [T]
    rw [div_le_div_iff₀ hden hSpos]
    nlinarith [hqa_le, mul_pos hnR hSpos]

set_option maxHeartbeats 800000 in
/-- **Non-consistency for every integer slope**: the ratio of the staircase
    count to the true cut length does not tend to `1` (its limit is
    `(a+1)/√(a²+1) > 1`). -/
theorem lineFaces_ratio_not_tendsto_one (a : ℕ) (ha : 0 < a) :
    ¬ Filter.Tendsto (fun n : ℕ => (lineFaces a n : ℝ) / lineLength a n)
        Filter.atTop (nhds 1) := by
  intro h
  have hlim := lineFaces_ratio_tendsto a ha
  have heq : (((a:ℝ) + 1) / Real.sqrt ((a:ℝ)^2 + 1)) = 1 :=
    tendsto_nhds_unique hlim h
  have hSpos : 0 < Real.sqrt ((a:ℝ)^2 + 1) := by positivity
  have han : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hSlt : Real.sqrt ((a:ℝ)^2 + 1) < (a:ℝ) + 1 := by
    rw [Real.sqrt_lt (by positivity) (by positivity)]
    nlinarith
  have hTgt : 1 < (((a:ℝ) + 1) / Real.sqrt ((a:ℝ)^2 + 1)) := by
    rw [one_lt_div hSpos]
    exact hSlt
  linarith

/-
  Rational slope `a/b`. This closes the "remaining wall" recorded above: for
  arbitrary `a, b > 0` (coprimality is not needed) the digital line
  `y = (a/b)·x` on `[0,n)²` has exactly

      min (a·(n−1)/b) (n−1) + min n (((n−1)·b − 1)/a + 1)

  exposed directed faces (`ratLineFaces_eq`). Its true length is
  `n·√(a²+b²)/max a b` (`ratLineLength`), and the ratio tends to
  `(a+b)/√(a²+b²) > 1` (`ratLineFaces_ratio_tendsto`), so it does not tend to
  `1` (`ratLineFaces_ratio_not_tendsto_one`). The case `b = 1` specialises to
  `lineFaces_eq` / `lineLength`; `a = b = 1` specialises to `diagFaces_eq`.
-/

/-- The inside set for the digital line `y = (a/b)·x`: the cells with
    `b·y ≤ a·x`. -/
def ratLineInside (a b x y : ℕ) : Prop := b * y ≤ a * x

/-- The staircase estimator for the digital line `y = (a/b)·x` on `[0,n)²`:
    directed in-window faces from an inside cell to an outside cell. As before
    only the `-x` and `+y` steps can cross the (positively sloped) cut. -/
def ratLineFaces (a b n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n,
    ((if b*y ≤ a*x ∧ 0 < x ∧ a*(x-1) < b*y then 1 else 0) +
     (if b*y ≤ a*x ∧ y+1 < n ∧ a*x < b*(y+1) then 1 else 0))

set_option maxHeartbeats 800000 in
/-- **Closed form for a rational slope**: for `a, b > 0` and `n ≥ 2`,
    `ratLineFaces a b n = min (a·(n−1)/b) (n−1) + min n (((n−1)·b − 1)/a + 1)`
    (all divisions are natural-number floors). The `-x` steps telescope to
    `min (a·(n−1)/b) (n−1)`; the `+y` steps occur once in column `x` iff
    `a·x < (n−1)·b`. -/
theorem ratLineFaces_eq (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) (hn : 2 ≤ n) :
    ratLineFaces a b n =
      min (a*(n-1)/b) (n-1) + min n (((n-1)*b - 1)/a + 1) := by
  have hleft : ∀ x ∈ Finset.range n,
      (∑ y ∈ Finset.range n,
        (if b*y ≤ a*x ∧ 0 < x ∧ a*(x-1) < b*y then 1 else 0 : ℕ)) =
      (if 0 < x then min (a*x/b) (n-1) - a*(x-1)/b else 0) := by
    intro x hx
    by_cases hxp : 0 < x
    · simp only [hxp, true_and]
      rw [Finset.sum_boole]
      have hset : (Finset.range n).filter (fun y => b*y ≤ a*x ∧ a*(x-1) < b*y) =
          Finset.Ioc (a*(x-1)/b) (min (a*x/b) (n-1)) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
        constructor
        · intro h
          have hy_le : y ≤ a*x/b :=
            (Nat.le_div_iff_mul_le hb).2 (by simpa [Nat.mul_comm] using h.2.1)
          have hlt : a*(x-1)/b < y :=
            (Nat.div_lt_iff_lt_mul hb).2 (by simpa [Nat.mul_comm] using h.2.2)
          have hyn1 : y ≤ n-1 := by omega
          exact ⟨hlt, le_min hy_le hyn1⟩
        · intro h
          have hlt0 : a*(x-1) < y*b := (Nat.div_lt_iff_lt_mul hb).1 h.1
          rw [Nat.mul_comm y b] at hlt0
          have hlt : a*(x-1) < b*y := hlt0
          have hy_le_ax : b*y ≤ a*x := by
            have hy_le_div : y ≤ a*x/b := le_trans h.2 (min_le_left _ _)
            have hy_le_ax0 : y*b ≤ a*x := (Nat.le_div_iff_mul_le hb).1 hy_le_div
            rwa [Nat.mul_comm y b] at hy_le_ax0
          have hyn : y < n := by
            have : y ≤ n-1 := le_trans h.2 (min_le_right _ _)
            omega
          exact ⟨hyn, ⟨hy_le_ax, hlt⟩⟩
      rw [hset, Nat.card_Ioc]
      simp
    · simp [hxp]
  have hright : ∀ x ∈ Finset.range n,
      (∑ y ∈ Finset.range n,
        (if b*y ≤ a*x ∧ y+1 < n ∧ a*x < b*(y+1) then 1 else 0 : ℕ)) =
      (if a*x/b + 1 < n then 1 else 0) := by
    intro x hx
    by_cases hq : a*x/b + 1 < n
    · rw [Finset.sum_eq_single (a*x/b)]
      · have hqle : b*(a*x/b) ≤ a*x := by
          simpa [Nat.mul_comm] using (Nat.div_mul_le_self (a*x) b)
        have hxlt0 : a*x < (a*x/b + 1)*b :=
          (Nat.div_lt_iff_lt_mul hb).1 (by omega)
        have hxlt : a*x < b*(a*x/b + 1) := by simpa [Nat.mul_comm] using hxlt0
        simp [hqle, hq, hxlt]
      · intro y hy hyne
        have hnot : ¬ (b*y ≤ a*x ∧ y+1 < n ∧ a*x < b*(y+1)) := by
          intro hc
          have hyle : y ≤ a*x/b :=
            (Nat.le_div_iff_mul_le hb).2 (by simpa [Nat.mul_comm] using hc.1)
          have hyge : a*x/b ≤ y := by
            have : a*x/b < y+1 :=
              (Nat.div_lt_iff_lt_mul hb).2 (by simpa [Nat.mul_comm] using hc.2.2)
            omega
          have : y = a*x/b := by omega
          exact hyne this
        rw [ite_eq_right hnot]
      · intro hnot
        have hmem : a*x/b ∈ Finset.range n := by
          have : a*x/b < n := by omega
          exact Finset.mem_range.mpr this
        exact (hnot hmem).elim
    · have hzero : ∀ y ∈ Finset.range n,
          (if b*y ≤ a*x ∧ y+1 < n ∧ a*x < b*(y+1) then 1 else 0 : ℕ) = 0 := by
        intro y hy
        have hfalse : ¬ (b*y ≤ a*x ∧ y+1 < n ∧ a*x < b*(y+1)) := by
          intro hc
          have hyle : y ≤ a*x/b :=
            (Nat.le_div_iff_mul_le hb).2 (by simpa [Nat.mul_comm] using hc.1)
          have hyge : a*x/b ≤ y := by
            have : a*x/b < y+1 :=
              (Nat.div_lt_iff_lt_mul hb).2 (by simpa [Nat.mul_comm] using hc.2.2)
            omega
          have hyeq : y = a*x/b := by omega
          rw [hyeq] at hc
          exact hq hc.2.1
        rw [ite_eq_right hfalse]
      rw [Finset.sum_eq_zero hzero]
      simp [hq]
  have hm_mono : ∀ k, min (a*k/b) (n-1) ≤ min (a*(k+1)/b) (n-1) := by
    intro k
    have hmul : a*k ≤ a*(k+1) := Nat.mul_le_mul_left a (by omega)
    have hdiv : a*k/b ≤ a*(k+1)/b := Nat.div_le_div_right hmul
    exact min_le_min hdiv (le_refl _)
  have hleft_term : ∀ x ∈ Finset.range n,
      (if 0 < x then min (a*x/b) (n-1) - a*(x-1)/b else 0) =
      (if 0 < x then min (a*x/b) (n-1) - min (a*(x-1)/b) (n-1) else 0) := by
    intro x hx
    by_cases hxp : 0 < x
    · simp only [hxp, ite_true]
      have hdiv_le : a*(x-1)/b ≤ a*x/b :=
        Nat.div_le_div_right (Nat.mul_le_mul_left a (Nat.sub_le x 1))
      by_cases hlt : a*(x-1)/b < n - 1
      · have hm : min (a*(x-1)/b) (n-1) = a*(x-1)/b := by omega
        rw [hm]
      · have hge : n - 1 ≤ a*(x-1)/b := by omega
        have hm1 : min (a*(x-1)/b) (n-1) = n-1 := by omega
        have hm2 : min (a*x/b) (n-1) = n-1 := by omega
        rw [hm1, hm2]
        omega
    · simp [hxp]
  have hleft_sum : (∑ x ∈ Finset.range n,
      (if 0 < x then min (a*x/b) (n-1) - a*(x-1)/b else 0)) =
      min (a*(n-1)/b) (n-1) := by
    rw [Finset.sum_congr rfl hleft_term]
    rw [sum_range_pred_sub (fun k => min (a*k/b) (n-1)) n hm_mono]
    have hm0 : min (a*0/b) (n-1) = 0 := by simp
    rw [hm0]
    simp
  have hright_sum : (∑ x ∈ Finset.range n, (if a*x/b + 1 < n then 1 else 0)) =
      min n (((n-1)*b - 1)/a + 1) := by
    rw [Finset.sum_boole]
    have hset : (Finset.range n).filter (fun x => a*x/b + 1 < n) =
        Finset.range (min n (((n-1)*b - 1)/a + 1)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · intro h
        have hxltN : x < n := h.1
        have hdivlt : a*x/b < n-1 := by omega
        have haxlt : a*x < (n-1)*b := (Nat.div_lt_iff_lt_mul hb).1 hdivlt
        have hCpos : 1 ≤ (n-1)*b := by omega
        have haxle : a*x ≤ (n-1)*b - 1 := by omega
        have hxle : x ≤ ((n-1)*b - 1)/a :=
          (Nat.le_div_iff_mul_le ha).2 (by simpa [Nat.mul_comm] using haxle)
        have hxltQ : x < ((n-1)*b - 1)/a + 1 := by omega
        exact lt_min hxltN hxltQ
      · intro h
        have hxltN : x < n := lt_of_lt_of_le h (min_le_left _ _)
        have hxltQ : x < ((n-1)*b - 1)/a + 1 := lt_of_lt_of_le h (min_le_right _ _)
        have hxle : x ≤ ((n-1)*b - 1)/a := by omega
        have haxle' : x*a ≤ (n-1)*b - 1 := (Nat.le_div_iff_mul_le ha).1 hxle
        have haxle : a*x ≤ (n-1)*b - 1 := by simpa [Nat.mul_comm] using haxle'
        have hposC : 0 < (n-1)*b := Nat.mul_pos (by omega : 0 < n-1) hb
        have haxlt : a*x < (n-1)*b :=
          lt_of_le_of_lt haxle (Nat.sub_lt hposC (by norm_num))
        have hdivlt : a*x/b < n-1 :=
          (Nat.div_lt_iff_lt_mul hb).2 (by simpa [Nat.mul_comm] using haxlt)
        omega
    rw [hset, Finset.card_range]
    simp
  unfold ratLineFaces
  rw [Finset.sum_congr rfl (fun x hx => by
    rw [Finset.sum_add_distrib, hleft x hx, hright x hx])]
  rw [Finset.sum_add_distrib, hleft_sum, hright_sum]

/-- The true length of the line `y = (a/b)·x` across `[0,n)²`: it leaves the
    window at `(n, a·n/b)` if `a ≤ b` and at `(b·n/a, n)` if `a > b`, giving
    `n·√(a²+b²)/max a b`. -/
noncomputable def ratLineLength (a b n : ℕ) : ℝ :=
  (n : ℝ) * Real.sqrt ((a:ℝ)^2 + (b:ℝ)^2) / (max a b : ℝ)

set_option maxHeartbeats 800000 in
/-- **Limit of the ratio**: for `a, b > 0` the staircase count divided by the
    true cut length tends to `(a+b)/√(a²+b²)`, which is `> 1`. -/
theorem ratLineFaces_ratio_tendsto (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Filter.Tendsto (fun n : ℕ => (ratLineFaces a b n : ℝ) / ratLineLength a b n)
      Filter.atTop (nhds (((a:ℝ) + (b:ℝ)) / Real.sqrt ((a:ℝ)^2 + (b:ℝ)^2))) := by
  let S : ℝ := Real.sqrt ((a:ℝ)^2 + (b:ℝ)^2)
  let M : ℝ := (max a b : ℝ)
  let T : ℝ := ((a:ℝ) + (b:ℝ)) / S
  have haposR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hbposR : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hMposNat : 0 < max a b := lt_of_lt_of_le ha (Nat.le_max_left a b)
  have hMposR : (0:ℝ) < M := by
    dsimp [M]
    exact_mod_cast hMposNat
  have hSpos : 0 < S := by
    dsimp [S]
    positivity
  have hden_tendsto : Filter.Tendsto (fun n : ℕ => (n:ℝ) * S) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hSpos
  have hlow_tendsto :
      Filter.Tendsto (fun n : ℕ => T - (3*M) / ((n:ℝ)*S)) Filter.atTop (nhds T) := by
    have hz : Filter.Tendsto (fun n : ℕ => (3*M) / ((n:ℝ)*S)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hden_tendsto
    simpa using (tendsto_const_nhds.sub hz)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_tendsto
    (show Filter.Tendsto (fun _ : ℕ => T) Filter.atTop (nhds T) from tendsto_const_nhds)
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hnpos : 0 < n := by omega
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
    have hdenpos : 0 < (n:ℝ)*S := mul_pos hnR hSpos
    have hnm1 : ((n-1:ℕ) : ℝ) = (n:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    have hlenpos : 0 < ratLineLength a b n := by
      unfold ratLineLength
      exact div_pos hdenpos hMposR
    let Pnat : ℕ := min (a*(n-1)/b) (n-1)
    let Qnat : ℕ := min n (((n-1)*b - 1)/a + 1)
    have hsum : (ratLineFaces a b n : ℝ) = (Pnat:ℝ) + (Qnat:ℝ) := by
      rw [ratLineFaces_eq a b n ha hb hn]
      simp [Pnat, Qnat]
    have hP_mul_le : Pnat*b ≤ a*(n-1) := by
      have hle : Pnat ≤ a*(n-1)/b := by
        dsimp [Pnat]
        exact Nat.min_le_left _ _
      exact le_trans (Nat.mul_le_mul_right b hle) (Nat.div_mul_le_self _ _)
    have hP_upper : (Pnat:ℝ) ≤ (a:ℝ)*(n:ℝ)/(b:ℝ) := by
      have hc : (Pnat:ℝ)*(b:ℝ) ≤ (a:ℝ)*((n-1:ℕ):ℝ) := by
        exact_mod_cast hP_mul_le
      rw [hnm1] at hc
      have hle_div : (Pnat:ℝ) ≤ (a:ℝ)*((n:ℝ)-1)/(b:ℝ) := (le_div_iff₀ hbposR).2 hc
      calc
        (Pnat:ℝ) ≤ (a:ℝ)*((n:ℝ)-1)/(b:ℝ) := hle_div
        _ ≤ (a:ℝ)*(n:ℝ)/(b:ℝ) := by
          rw [show (a:ℝ)*((n:ℝ)-1)/(b:ℝ) = ((a:ℝ)/(b:ℝ))*((n:ℝ)-1) by ring,
              show (a:ℝ)*(n:ℝ)/(b:ℝ) = ((a:ℝ)/(b:ℝ))*(n:ℝ) by ring]
          exact mul_le_mul_of_nonneg_left (by linarith)
            (div_nonneg (le_of_lt haposR) (le_of_lt hbposR))
    have hQ_upper_n : (Qnat:ℝ) ≤ (n:ℝ) := by
      have : Qnat ≤ n := by
        dsimp [Qnat]
        exact Nat.min_le_left _ _
      exact_mod_cast this
    by_cases hle : a ≤ b
    · have hdiv_lower_nat : a*(n-1) < (a*(n-1)/b + 1)*b :=
        (Nat.div_lt_iff_lt_mul hb).1 (by omega)
      have hdiv_lower_cast : (a:ℝ)*((n:ℝ)-1)/(b:ℝ) - 1 ≤ ((a*(n-1)/b : ℕ) : ℝ) := by
        have hc : ((a*(n-1):ℕ) : ℝ) < (((a*(n-1)/b + 1)*b : ℕ) : ℝ) := by
          exact_mod_cast hdiv_lower_nat
        push_cast at hc
        rw [hnm1] at hc
        have hlt : (a:ℝ)*((n:ℝ)-1)/(b:ℝ) < ((a*(n-1)/b : ℕ) : ℝ) + 1 :=
          (div_lt_iff₀ hbposR).2 (by simpa [Nat.mul_comm] using hc)
        linarith
      have hcoef : (a:ℝ)/(b:ℝ) ≤ 1 := (div_le_one hbposR).2 (by exact_mod_cast hle)
      have hnminus_nonneg : 0 ≤ (n:ℝ) - 1 := by
        have hn1R : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
        linarith
      have hnminus_lower : (a:ℝ)*((n:ℝ)-1)/(b:ℝ) - 1 ≤ (n:ℝ) - 1 := by
        have htmp : (a:ℝ)*((n:ℝ)-1)/(b:ℝ) ≤ (n:ℝ)-1 := by
          calc
            (a:ℝ)*((n:ℝ)-1)/(b:ℝ) = ((a:ℝ)/(b:ℝ))*((n:ℝ)-1) := by ring
            _ ≤ 1*((n:ℝ)-1) := mul_le_mul_of_nonneg_right hcoef hnminus_nonneg
            _ = (n:ℝ)-1 := by ring
        linarith
      have hP_lower0 : (a:ℝ)*((n:ℝ)-1)/(b:ℝ) - 1 ≤ (Pnat:ℝ) := by
        rw [show (Pnat:ℝ) = min ((a*(n-1)/b : ℕ) : ℝ) ((n-1:ℕ) : ℝ) by simp [Pnat]]
        rw [hnm1]
        exact le_min hdiv_lower_cast hnminus_lower
      have hP_lower : (a:ℝ)*(n:ℝ)/(b:ℝ) - 2 ≤ (Pnat:ℝ) := by
        have hdecomp : (a:ℝ)*(n:ℝ)/(b:ℝ) =
            (a:ℝ)*((n:ℝ)-1)/(b:ℝ) + (a:ℝ)/(b:ℝ) := by ring
        rw [hdecomp]
        linarith [hcoef, hP_lower0]
      have hCge : a*(n-2) ≤ (n-1)*b - 1 := by
        have h1 : a*(n-2) ≤ b*(n-2) := Nat.mul_le_mul_right (n-2) hle
        have h2' : b*(n-2) + 1 ≤ b*(n-1) := by
          rw [show n-1 = (n-2)+1 by omega, Nat.mul_add]
          omega
        have h2 : b*(n-2) + 1 ≤ (n-1)*b := by simpa [Nat.mul_comm] using h2'
        omega
      have hQ_lower_nat : n-1 ≤ Qnat := by
        dsimp [Qnat]
        apply le_min
        · omega
        · have hdivge : n-2 ≤ ((n-1)*b - 1)/a :=
            (Nat.le_div_iff_mul_le ha).2 (by simpa [Nat.mul_comm] using hCge)
          omega
      have hQ_lower : (n:ℝ) - 1 ≤ (Qnat:ℝ) := by
        have : ((n-1:ℕ) : ℝ) ≤ (Qnat:ℝ) := by exact_mod_cast hQ_lower_nat
        rwa [hnm1] at this
      have hF_lower : (((a:ℝ)+(b:ℝ))*(n:ℝ) - 3*(b:ℝ))/(b:ℝ) ≤
          (ratLineFaces a b n : ℝ) := by
        rw [hsum]
        have htarget : (((a:ℝ)+(b:ℝ))*(n:ℝ) - 3*(b:ℝ))/(b:ℝ) =
            (a:ℝ)*(n:ℝ)/(b:ℝ) + (n:ℝ) - 3 := by
          field_simp [hbposR.ne'] <;> ring
        rw [htarget]
        linarith
      have hF_lower_mul : ((a:ℝ)+(b:ℝ))*(n:ℝ) - 3*(b:ℝ) ≤
          (ratLineFaces a b n : ℝ)*(b:ℝ) := (div_le_iff₀ hbposR).1 hF_lower
      have hratio : (ratLineFaces a b n : ℝ) / ratLineLength a b n =
          (ratLineFaces a b n : ℝ)*(b:ℝ) / ((n:ℝ)*S) := by
        unfold ratLineLength
        push_cast
        rw [max_eq_right (by exact_mod_cast hle)]
        dsimp [S]
        field_simp [hdenpos.ne', hbposR.ne'] <;> ring
      rw [hratio]
      dsimp [T, M]
      push_cast
      rw [max_eq_right (by exact_mod_cast hle)]
      rw [le_div_iff₀ hdenpos]
      have hcalc : (T - 3*(b:ℝ)/((n:ℝ)*S))*((n:ℝ)*S) =
          ((a:ℝ)+(b:ℝ))*(n:ℝ) - 3*(b:ℝ) := by
        dsimp [T]
        field_simp [hSpos.ne', hnR.ne'] <;> ring
      rw [hcalc]
      exact hF_lower_mul
    · have hlt : b < a := by omega
      have hmaxa : max a b = a := max_eq_left (le_of_lt hlt)
      have hP_nat : Pnat = n-1 := by
        dsimp [Pnat]
        apply min_eq_right
        have hmul : b*(n-1) ≤ a*(n-1) := Nat.mul_le_mul_right (n-1) (le_of_lt hlt)
        exact (Nat.le_div_iff_mul_le hb).2 (by simpa [Nat.mul_comm] using hmul)
      have hP_eq : (Pnat:ℝ) = (n:ℝ)-1 := by
        rw [hP_nat]
        exact hnm1
      have hcoefb : (b:ℝ)/(a:ℝ) ≤ 1 := (div_le_one haposR).2 (by exact_mod_cast (le_of_lt hlt))
      have haR1 : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
      have hainv : (1:ℝ)/(a:ℝ) ≤ 1 := (div_le_one haposR).2 haR1
      have hCcast : (((n-1)*b - 1 : ℕ) : ℝ) = (b:ℝ)*((n:ℝ)-1) - 1 := by
        have hposC : 1 ≤ (n-1)*b :=
          Nat.succ_le_of_lt (Nat.mul_pos (by omega : 0 < n-1) hb)
        rw [Nat.cast_sub hposC]
        push_cast
        rw [hnm1]
        ring
      have hC_lt : (n-1)*b - 1 < a*(n-1) := by
        have hble : b ≤ a-1 := by omega
        have hmul : (n-1)*b ≤ (n-1)*(a-1) := Nat.mul_le_mul_left (n-1) hble
        have hmul' : (n-1)*b ≤ (n-1)*a - (n-1) := by
          simpa [Nat.mul_sub_left_distrib] using hmul
        have hle1 : (n-1)*b ≤ (n-1)*a - 1 :=
          le_trans hmul' (Nat.sub_le_sub_left (by omega : 1 ≤ n-1) ((n-1)*a))
        have hlt0 : (n-1)*b < (n-1)*a :=
          lt_of_le_of_lt hle1
            (Nat.sub_lt (Nat.mul_pos (by omega : 0 < n-1) ha) (by norm_num))
        have hposleft : 0 < (n-1)*b := Nat.mul_pos (by omega : 0 < n-1) hb
        have hsub : (n-1)*b - 1 < (n-1)*b := Nat.sub_lt hposleft (by norm_num)
        rw [Nat.mul_comm a (n-1)]
        exact lt_trans hsub hlt0
      have hQ_nat : Qnat = ((n-1)*b - 1)/a + 1 := by
        dsimp [Qnat]
        apply min_eq_right
        have hdivlt : ((n-1)*b - 1)/a < n-1 :=
          (Nat.div_lt_iff_lt_mul ha).2 (by simpa [Nat.mul_comm] using hC_lt)
        omega
      have hC_lt_div : (n-1)*b - 1 < (((n-1)*b - 1)/a + 1)*a :=
        (Nat.div_lt_iff_lt_mul ha).1 (by omega)
      have hc0 : (((n-1)*b - 1 : ℕ) : ℝ) < (Qnat:ℝ)*(a:ℝ) := by
        have hc : (((n-1)*b - 1 : ℕ) : ℝ) <
            (((((n-1)*b - 1)/a + 1)*a : ℕ) : ℝ) := by exact_mod_cast hC_lt_div
        push_cast at hc
        have hQcast : (Qnat:ℝ) = ((((n-1)*b - 1)/a : ℕ) : ℝ) + 1 := by
          rw [hQ_nat]
          norm_num
        rw [hCcast] at hc ⊢
        rw [hQcast]
        exact hc
      have hQ_gt : (b:ℝ)*((n:ℝ)-1)/(a:ℝ) - 1/(a:ℝ) < (Qnat:ℝ) := by
        have hlt' : (b:ℝ)*((n:ℝ)-1) - 1 < (Qnat:ℝ)*(a:ℝ) := by
          simpa [hCcast] using hc0
        have hdivlt : ((b:ℝ)*((n:ℝ)-1) - 1)/(a:ℝ) < (Qnat:ℝ) :=
          (div_lt_iff₀ haposR).2 hlt'
        have heq : ((b:ℝ)*((n:ℝ)-1) - 1)/(a:ℝ) =
            (b:ℝ)*((n:ℝ)-1)/(a:ℝ) - 1/(a:ℝ) := by ring
        rwa [heq] at hdivlt
      have hsumc : (b:ℝ)/(a:ℝ) + 1/(a:ℝ) ≤ 2 := by linarith [hcoefb, hainv]
      have hdiff : (b:ℝ)*(n:ℝ)/(a:ℝ) - 2 ≤
          (b:ℝ)*((n:ℝ)-1)/(a:ℝ) - 1/(a:ℝ) := by
        have hdecomp : (b:ℝ)*(n:ℝ)/(a:ℝ) - 2 =
            (b:ℝ)*((n:ℝ)-1)/(a:ℝ) - 1/(a:ℝ) +
              ((b:ℝ)/(a:ℝ) + 1/(a:ℝ) - 2) := by ring
        rw [hdecomp]
        linarith
      have hQ_lower : (b:ℝ)*(n:ℝ)/(a:ℝ) - 2 ≤ (Qnat:ℝ) :=
        le_trans hdiff (le_of_lt hQ_gt)
      have hC_le : ((n-1)*b - 1)/a ≤ (n-1)*b - 1 := Nat.div_le_self _ _
      have hmulR : ((((n-1)*b - 1)/a : ℕ) : ℝ)*(a:ℝ) ≤ (b:ℝ)*((n:ℝ)-1) - 1 := by
        have hcNat : (((n-1)*b - 1)/a)*a ≤ (n-1)*b - 1 := Nat.div_mul_le_self _ _
        have hc : (((((n-1)*b - 1)/a)*a : ℕ) : ℝ) ≤ (((n-1)*b - 1 : ℕ) : ℝ) := by
          exact_mod_cast hcNat
        push_cast at hc
        rw [hCcast] at hc
        exact hc
      have hdivR : ((((n-1)*b - 1)/a : ℕ) : ℝ) ≤
          ((b:ℝ)*((n:ℝ)-1) - 1)/(a:ℝ) := (le_div_iff₀ haposR).2 hmulR
      have hQ_eq : (Qnat:ℝ) = ((((n-1)*b - 1)/a : ℕ) : ℝ) + 1 := by
        rw [hQ_nat]
        norm_num
      have hQ_upper : (Qnat:ℝ) ≤ (b:ℝ)*(n:ℝ)/(a:ℝ) + 1 := by
        rw [hQ_eq]
        have hle1 : ((b:ℝ)*((n:ℝ)-1) - 1)/(a:ℝ) ≤ (b:ℝ)*(n:ℝ)/(a:ℝ) := by
          rw [div_le_div_iff_of_pos_right haposR]
          nlinarith [le_of_lt hbposR]
        linarith
      have hF_lower : (((a:ℝ)+(b:ℝ))*(n:ℝ) - 3*(a:ℝ))/(a:ℝ) ≤
          (ratLineFaces a b n : ℝ) := by
        rw [hsum]
        rw [hP_eq]
        have htarget : (((a:ℝ)+(b:ℝ))*(n:ℝ) - 3*(a:ℝ))/(a:ℝ) =
            (n:ℝ) - 1 + ((b:ℝ)*(n:ℝ)/(a:ℝ) - 2) := by
          field_simp [haposR.ne']
          ring
        rw [htarget]
        linarith
      have hF_lower_mul : ((a:ℝ)+(b:ℝ))*(n:ℝ) - 3*(a:ℝ) ≤
          (ratLineFaces a b n : ℝ)*(a:ℝ) := (div_le_iff₀ haposR).1 hF_lower
      have hratio : (ratLineFaces a b n : ℝ) / ratLineLength a b n =
          (ratLineFaces a b n : ℝ)*(a:ℝ) / ((n:ℝ)*S) := by
        unfold ratLineLength
        push_cast
        rw [max_eq_left (by exact_mod_cast (le_of_lt hlt))]
        dsimp [S]
        field_simp [hdenpos.ne', haposR.ne'] <;> ring
      rw [hratio]
      dsimp [T, M]
      push_cast
      rw [max_eq_left (by exact_mod_cast (le_of_lt hlt))]
      rw [le_div_iff₀ hdenpos]
      have hcalc : (T - 3*(a:ℝ)/((n:ℝ)*S))*((n:ℝ)*S) =
          ((a:ℝ)+(b:ℝ))*(n:ℝ) - 3*(a:ℝ) := by
        dsimp [T]
        field_simp [hSpos.ne', hnR.ne'] <;> ring
      rw [hcalc]
      exact hF_lower_mul
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hnpos : 0 < n := by omega
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
    have hdenpos : 0 < (n:ℝ)*S := mul_pos hnR hSpos
    have hnm1 : ((n-1:ℕ) : ℝ) = (n:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    let Pnat : ℕ := min (a*(n-1)/b) (n-1)
    let Qnat : ℕ := min n (((n-1)*b - 1)/a + 1)
    have hsum : (ratLineFaces a b n : ℝ) = (Pnat:ℝ) + (Qnat:ℝ) := by
      rw [ratLineFaces_eq a b n ha hb hn]
      simp [Pnat, Qnat]
    have hP_mul_le : Pnat*b ≤ a*(n-1) := by
      have hle : Pnat ≤ a*(n-1)/b := by
        dsimp [Pnat]
        exact Nat.min_le_left _ _
      exact le_trans (Nat.mul_le_mul_right b hle) (Nat.div_mul_le_self _ _)
    have hP_upper : (Pnat:ℝ) ≤ (a:ℝ)*(n:ℝ)/(b:ℝ) := by
      have hc : (Pnat:ℝ)*(b:ℝ) ≤ (a:ℝ)*((n-1:ℕ):ℝ) := by
        exact_mod_cast hP_mul_le
      rw [hnm1] at hc
      have hle_div : (Pnat:ℝ) ≤ (a:ℝ)*((n:ℝ)-1)/(b:ℝ) := (le_div_iff₀ hbposR).2 hc
      calc
        (Pnat:ℝ) ≤ (a:ℝ)*((n:ℝ)-1)/(b:ℝ) := hle_div
        _ ≤ (a:ℝ)*(n:ℝ)/(b:ℝ) := by
          rw [show (a:ℝ)*((n:ℝ)-1)/(b:ℝ) = ((a:ℝ)/(b:ℝ))*((n:ℝ)-1) by ring,
              show (a:ℝ)*(n:ℝ)/(b:ℝ) = ((a:ℝ)/(b:ℝ))*(n:ℝ) by ring]
          exact mul_le_mul_of_nonneg_left (by linarith)
            (div_nonneg (le_of_lt haposR) (le_of_lt hbposR))
    have hQ_upper_n : (Qnat:ℝ) ≤ (n:ℝ) := by
      have : Qnat ≤ n := by
        dsimp [Qnat]
        exact Nat.min_le_left _ _
      exact_mod_cast this
    by_cases hle : a ≤ b
    · have hF_upper : (ratLineFaces a b n : ℝ) ≤ ((a:ℝ)+(b:ℝ))*(n:ℝ)/(b:ℝ) := by
        rw [hsum]
        have htarget : (a:ℝ)*(n:ℝ)/(b:ℝ) + (n:ℝ) =
            ((a:ℝ)+(b:ℝ))*(n:ℝ)/(b:ℝ) := by
          field_simp [hbposR.ne'] <;> ring
        rw [← htarget]
        linarith [hP_upper, hQ_upper_n]
      have hmul : (ratLineFaces a b n : ℝ)*(b:ℝ) ≤ ((a:ℝ)+(b:ℝ))*(n:ℝ) :=
        (le_div_iff₀ hbposR).1 hF_upper
      have hratio : (ratLineFaces a b n : ℝ) / ratLineLength a b n =
          (ratLineFaces a b n : ℝ)*(b:ℝ) / ((n:ℝ)*S) := by
        unfold ratLineLength
        push_cast
        rw [max_eq_right (by exact_mod_cast hle)]
        dsimp [S]
        field_simp [hdenpos.ne', hbposR.ne'] <;> ring
      rw [hratio]
      dsimp [T]
      rw [div_le_div_iff₀ hdenpos hSpos]
      have hmulS : ((ratLineFaces a b n : ℝ)*(b:ℝ))*S ≤
          (((a:ℝ)+(b:ℝ))*(n:ℝ))*S :=
        mul_le_mul_of_nonneg_right hmul (le_of_lt hSpos)
      nlinarith
    · have hlt : b < a := by omega
      have hmaxa : max a b = a := max_eq_left (le_of_lt hlt)
      have hP_nat : Pnat = n-1 := by
        dsimp [Pnat]
        apply min_eq_right
        have hmul : b*(n-1) ≤ a*(n-1) := Nat.mul_le_mul_right (n-1) (le_of_lt hlt)
        exact (Nat.le_div_iff_mul_le hb).2 (by simpa [Nat.mul_comm] using hmul)
      have hP_eq : (Pnat:ℝ) = (n:ℝ)-1 := by
        rw [hP_nat]
        exact hnm1
      have hCcast : (((n-1)*b - 1 : ℕ) : ℝ) = (b:ℝ)*((n:ℝ)-1) - 1 := by
        have hposC : 1 ≤ (n-1)*b :=
          Nat.succ_le_of_lt (Nat.mul_pos (by omega : 0 < n-1) hb)
        rw [Nat.cast_sub hposC]
        push_cast
        rw [hnm1]
        ring
      have hC_lt : (n-1)*b - 1 < a*(n-1) := by
        have hble : b ≤ a-1 := by omega
        have hmul : (n-1)*b ≤ (n-1)*(a-1) := Nat.mul_le_mul_left (n-1) hble
        have hmul' : (n-1)*b ≤ (n-1)*a - (n-1) := by
          simpa [Nat.mul_sub_left_distrib] using hmul
        have hle1 : (n-1)*b ≤ (n-1)*a - 1 :=
          le_trans hmul' (Nat.sub_le_sub_left (by omega : 1 ≤ n-1) ((n-1)*a))
        have hlt0 : (n-1)*b < (n-1)*a :=
          lt_of_le_of_lt hle1
            (Nat.sub_lt (Nat.mul_pos (by omega : 0 < n-1) ha) (by norm_num))
        have hposleft : 0 < (n-1)*b := Nat.mul_pos (by omega : 0 < n-1) hb
        have hsub : (n-1)*b - 1 < (n-1)*b := Nat.sub_lt hposleft (by norm_num)
        rw [Nat.mul_comm a (n-1)]
        exact lt_trans hsub hlt0
      have hQ_nat : Qnat = ((n-1)*b - 1)/a + 1 := by
        dsimp [Qnat]
        apply min_eq_right
        have hdivlt : ((n-1)*b - 1)/a < n-1 :=
          (Nat.div_lt_iff_lt_mul ha).2 (by simpa [Nat.mul_comm] using hC_lt)
        omega
      have hC_le : ((n-1)*b - 1)/a ≤ (n-1)*b - 1 := Nat.div_le_self _ _
      have hmulR : ((((n-1)*b - 1)/a : ℕ) : ℝ)*(a:ℝ) ≤ (b:ℝ)*((n:ℝ)-1) - 1 := by
        have hcNat : (((n-1)*b - 1)/a)*a ≤ (n-1)*b - 1 := Nat.div_mul_le_self _ _
        have hc : (((((n-1)*b - 1)/a)*a : ℕ) : ℝ) ≤ (((n-1)*b - 1 : ℕ) : ℝ) := by
          exact_mod_cast hcNat
        push_cast at hc
        rw [hCcast] at hc
        exact hc
      have hdivR : ((((n-1)*b - 1)/a : ℕ) : ℝ) ≤
          ((b:ℝ)*((n:ℝ)-1) - 1)/(a:ℝ) := (le_div_iff₀ haposR).2 hmulR
      have hQ_eq : (Qnat:ℝ) = ((((n-1)*b - 1)/a : ℕ) : ℝ) + 1 := by
        rw [hQ_nat]
        norm_num
      have hQ_upper : (Qnat:ℝ) ≤ (b:ℝ)*(n:ℝ)/(a:ℝ) + 1 := by
        rw [hQ_eq]
        have hle1 : ((b:ℝ)*((n:ℝ)-1) - 1)/(a:ℝ) ≤ (b:ℝ)*(n:ℝ)/(a:ℝ) := by
          rw [div_le_div_iff_of_pos_right haposR]
          nlinarith [le_of_lt hbposR]
        linarith
      have hF_upper : (ratLineFaces a b n : ℝ) ≤ ((a:ℝ)+(b:ℝ))*(n:ℝ)/(a:ℝ) := by
        rw [hsum]
        rw [hP_eq]
        have htarget : (n:ℝ) - 1 + ((b:ℝ)*(n:ℝ)/(a:ℝ) + 1) =
            ((a:ℝ)+(b:ℝ))*(n:ℝ)/(a:ℝ) := by
          field_simp [haposR.ne']
          ring
        rw [← htarget]
        linarith [hQ_upper]
      have hmul : (ratLineFaces a b n : ℝ)*(a:ℝ) ≤ ((a:ℝ)+(b:ℝ))*(n:ℝ) :=
        (le_div_iff₀ haposR).1 hF_upper
      have hratio : (ratLineFaces a b n : ℝ) / ratLineLength a b n =
          (ratLineFaces a b n : ℝ)*(a:ℝ) / ((n:ℝ)*S) := by
        unfold ratLineLength
        push_cast
        rw [max_eq_left (by exact_mod_cast (le_of_lt hlt))]
        dsimp [S]
        field_simp [hdenpos.ne', haposR.ne'] <;> ring
      rw [hratio]
      dsimp [T]
      rw [div_le_div_iff₀ hdenpos hSpos]
      have hmulS : ((ratLineFaces a b n : ℝ)*(a:ℝ))*S ≤
          (((a:ℝ)+(b:ℝ))*(n:ℝ))*S :=
        mul_le_mul_of_nonneg_right hmul (le_of_lt hSpos)
      nlinarith

set_option maxHeartbeats 800000 in
/-- **Non-consistency for every rational slope**: the ratio of the staircase
    count to the true cut length does not tend to `1` (its limit is
    `(a+b)/√(a²+b²) > 1`). -/
theorem ratLineFaces_ratio_not_tendsto_one (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ Filter.Tendsto (fun n : ℕ => (ratLineFaces a b n : ℝ) / ratLineLength a b n)
        Filter.atTop (nhds 1) := by
  intro h
  have hlim := ratLineFaces_ratio_tendsto a b ha hb
  have heq : (((a:ℝ) + (b:ℝ)) / Real.sqrt ((a:ℝ)^2 + (b:ℝ)^2)) = 1 :=
    tendsto_nhds_unique hlim h
  have hSpos : 0 < Real.sqrt ((a:ℝ)^2 + (b:ℝ)^2) := by positivity
  have haposR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hbposR : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hSlt : Real.sqrt ((a:ℝ)^2 + (b:ℝ)^2) < (a:ℝ) + (b:ℝ) := by
    rw [Real.sqrt_lt (by positivity) (by positivity)]
    nlinarith [mul_pos haposR hbposR]
  have hTgt : 1 < ((a:ℝ) + (b:ℝ)) / Real.sqrt ((a:ℝ)^2 + (b:ℝ)^2) := by
    rw [one_lt_div hSpos]
    exact hSlt
  linarith

end StaircaseDiagonal

end Vdb
