/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  A two-parameter generalization of the oblique-plane staircase inconsistency.

  `Vdb/StaircasePlane3D.lean` treats the equilateral cut `x + y + z = c` and
  obtains the limit `√3`. This module treats the whole family of planes

      x + y + m·z = m·n        (m ≥ 2, n ≥ 1),

  i.e. one coefficient may differ from the other two. The inside halfspace is
  `x + y + m·z ≤ m·n` on the box `[0, m·n+1)³`; only in-window steps from an
  inside cell to an outside cell are counted. For the `+x` and `+y` steps the
  cut is crossed exactly on the slice `x + y + m·z = m·n`; for the `+z` step
  (which changes the sum by `m`) the cut is crossed on the *band*
  `m·n - m < x + y + m·z ≤ m·n`. Counting the band telescopes against the
  triangular pair count, so the face count is again a closed-form quadratic.

  Main results (`m ≥ 2`, `n ≥ 1`):

      2 · faces = m²n² + 2mn² + 5mn + 4n + 2          (genFaces_eq_two)
      faces / trueArea → (m+2) / √(m²+2) > 1         (genFaces_ratio_tendsto)

  For `m = 1` the definition specializes to the equilateral case already
  proved in `Vdb/StaircasePlane3D.lean`; here `m ≥ 2` avoids duplicating it and
  makes the `+z` target automatically lie in the box.

  Pure kernel proofs throughout; no placeholders and no `native_decide`.

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

namespace StaircasePlane3DGeneral

/-- The interior halfspace cell predicate for the plane `x + y + m·z ≤ m·n`. -/
def genInside (m n x y z : ℕ) : Prop := x + y + m * z ≤ m * n

/-- The staircase estimator: directed in-window faces from an inside cell to an
     outside cell. The `+x`/`+y` crossings occur on the exact slice, the `+z`
     crossing on the top `m`-band of sums. -/
def genFaces (m n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (m * n + 1), ∑ y ∈ Finset.range (m * n + 1),
    ∑ z ∈ Finset.range (m * n + 1),
      ((if x + y + m * z = m * n ∧ x < m * n then 1 else 0) +
       (if x + y + m * z = m * n ∧ y < m * n then 1 else 0) +
       (if x + y + m * z ≤ m * n ∧ m * n < x + y + m * z + m ∧ z < m * n
          then 1 else 0))

/-! ### Justification of the three crossing conditions -/

theorem genFaces_step_x (m n x y z : ℕ)
    (hx : x < m * n + 1) (hy : y < m * n + 1) (hz : z < m * n + 1) :
    (genInside m n x y z ∧ x + 1 < m * n + 1 ∧ ¬ genInside m n (x + 1) y z) ↔
      (x + y + m * z = m * n ∧ x < m * n) := by
  unfold genInside
  omega

theorem genFaces_step_y (m n x y z : ℕ)
    (hx : x < m * n + 1) (hy : y < m * n + 1) (hz : z < m * n + 1) :
    (genInside m n x y z ∧ y + 1 < m * n + 1 ∧ ¬ genInside m n x (y + 1) z) ↔
      (x + y + m * z = m * n ∧ y < m * n) := by
  unfold genInside
  omega

set_option maxHeartbeats 800000 in
theorem genFaces_step_z (m n x y z : ℕ)
    (hx : x < m * n + 1) (hy : y < m * n + 1) (hz : z < m * n + 1) :
    (genInside m n x y z ∧ z + 1 < m * n + 1 ∧ ¬ genInside m n x y (z + 1)) ↔
      (x + y + m * z ≤ m * n ∧ m * n < x + y + m * z + m ∧ z < m * n) := by
  unfold genInside
  have hmul : m * (z + 1) = m * z + m := by ring
  rw [hmul]
  omega

/-! ### Arithmetic helpers (all doubled, to avoid natural division) -/

set_option maxHeartbeats 800000 in
lemma two_sum_range_succ (n : ℕ) : 2 * (∑ i ∈ Finset.range (n + 1), i) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        2 * ((∑ x ∈ Finset.range (n + 1), x) + (n + 1))
            = 2 * (∑ x ∈ Finset.range (n + 1), x) + 2 * (n + 1) := by ring
        _ = n * (n + 1) + 2 * (n + 1) := by rw [ih]
        _ = (n + 1) * ((n + 1) + 1) := by ring

lemma two_sum_range (n : ℕ) : 2 * (∑ i ∈ Finset.range n, i) = (n - 1) * n := by
  cases n with
  | zero => simp
  | succ n => simpa using two_sum_range_succ n

set_option maxHeartbeats 800000 in
lemma two_sum_range_plus (n : ℕ) : 2 * (∑ i ∈ Finset.range n, i) + n = n * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        2 * ((∑ i ∈ Finset.range n, i) + n) + (n + 1)
            = (2 * (∑ i ∈ Finset.range n, i) + n) + 2 * n + 1 := by ring
        _ = n * n + 2 * n + 1 := by rw [ih]
        _ = (n + 1) * (n + 1) := by ring

set_option maxHeartbeats 800000 in
lemma sum_linear_two (m n : ℕ) (hn : 1 ≤ n) :
    2 * (∑ k ∈ Finset.range n, (m * k + 1)) + m * n = m * n * n + 2 * n := by
  have hsum : ∑ k ∈ Finset.range n, (m * k + 1) =
      m * (∑ k ∈ Finset.range n, k) + n := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    simp
  rw [hsum]
  calc
    2 * (m * (∑ k ∈ Finset.range n, k) + n) + m * n
        = m * (2 * (∑ k ∈ Finset.range n, k) + n) + 2 * n := by ring
    _ = m * (n * n) + 2 * n := by rw [two_sum_range_plus n]
    _ = m * n * n + 2 * n := by ring

set_option maxHeartbeats 800000 in
lemma band_sum_two (t : ℕ) :
    2 * (∑ x ∈ Finset.range (t + 1), (t - x + 1)) = (t + 1) * (t + 2) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ]
      have hpoint : ∀ x ∈ Finset.range (t + 1), (t + 1 - x + 1) = (t - x + 1) + 1 := by
        intro x hx
        have hxt : x ≤ t := by have := Finset.mem_range.mp hx; omega
        omega
      rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib]
      simp
      calc
        2 * ((∑ x ∈ Finset.range (t + 1), (t - x + 1)) + (t + 1) + 1)
            = 2 * (∑ x ∈ Finset.range (t + 1), (t - x + 1)) + 2 * (t + 1) + 2 := by ring
        _ = (t + 1) * (t + 2) + 2 * (t + 1) + 2 := by rw [ih]
        _ = (t + 2) * (t + 3) := by ring

set_option maxHeartbeats 800000 in
lemma pairLe_two (C t : ℕ) (ht : t ≤ C) :
    2 * (∑ x ∈ Finset.range (C + 1), ∑ y ∈ Finset.range (C + 1),
           (if x + y ≤ t then 1 else 0 : ℕ)) = (t + 1) * (t + 2) := by
  have hinner : ∀ x ∈ Finset.range (C + 1),
      (∑ y ∈ Finset.range (C + 1), (if x + y ≤ t then 1 else 0 : ℕ)) =
        if x ≤ t then t - x + 1 else 0 := by
    intro x hx
    by_cases hxt : x ≤ t
    · rw [Finset.sum_boole]
      have hf : (Finset.range (C + 1)).filter (fun y => x + y ≤ t) = Finset.range (t - x + 1) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor <;> intro h <;> omega
      rw [hf, Finset.card_range]
      simp [hxt]
    · have hz : ∀ y ∈ Finset.range (C + 1), (if x + y ≤ t then 1 else 0 : ℕ) = 0 := by
        intro y hy
        have hf : ¬ (x + y ≤ t) := by omega
        rw [ite_eq_right hf]
      rw [Finset.sum_eq_zero hz]
      simp [hxt]
  rw [Finset.sum_congr rfl hinner]
  rw [← Finset.sum_filter]
  have hf : (Finset.range (C + 1)).filter (fun x => x ≤ t) = Finset.range (t + 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor <;> intro h <;> omega
  rw [hf]
  exact band_sum_two t

/-- The triangular pair count: pairs in the box with `x + y ≤ t`. -/
def pairLe (C t : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (C + 1), ∑ y ∈ Finset.range (C + 1),
    (if x + y ≤ t then 1 else 0 : ℕ)

lemma pairLe_mono (C t1 t2 : ℕ) (h12 : t1 ≤ t2) : pairLe C t1 ≤ pairLe C t2 := by
  unfold pairLe
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.sum_le_sum
  intro y hy
  by_cases h : x + y ≤ t1
  · have h' : x + y ≤ t2 := le_trans h h12
    simp [h, h']
  · simp [h]

lemma sum_three_swap (C : ℕ) (f : ℕ → ℕ → ℕ → ℕ) :
    (∑ x ∈ Finset.range C, ∑ y ∈ Finset.range C, ∑ z ∈ Finset.range C, f x y z) =
    (∑ z ∈ Finset.range C, ∑ y ∈ Finset.range C, ∑ x ∈ Finset.range C, f x y z) := by
  calc
    (∑ x ∈ Finset.range C, ∑ y ∈ Finset.range C, ∑ z ∈ Finset.range C, f x y z)
        = ∑ x ∈ Finset.range C, ∑ z ∈ Finset.range C, ∑ y ∈ Finset.range C, f x y z := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.sum_comm]
    _ = ∑ z ∈ Finset.range C, ∑ x ∈ Finset.range C, ∑ y ∈ Finset.range C, f x y z := by
            rw [Finset.sum_comm]
    _ = ∑ z ∈ Finset.range C, ∑ y ∈ Finset.range C, ∑ x ∈ Finset.range C, f x y z := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [Finset.sum_comm]

/-! ### Counting the `+x` and `+y` faces -/

set_option maxHeartbeats 800000 in
lemma x_slice (m n z : ℕ) (hm : 0 < m) (hz : z ≤ n) :
    (∑ x ∈ Finset.range (m * n + 1), ∑ y ∈ Finset.range (m * n + 1),
      (if x + y + m * z = m * n ∧ x < m * n then 1 else 0 : ℕ)) =
      (if z = 0 then m * n else m * n - m * z + 1) := by
  have hmz : m * z ≤ m * n := Nat.mul_le_mul_left m hz
  have hinner : ∀ x ∈ Finset.range (m * n + 1),
      (∑ y ∈ Finset.range (m * n + 1),
        (if x + y + m * z = m * n ∧ x < m * n then 1 else 0 : ℕ)) =
        (if x < m * n ∧ x ≤ m * n - m * z then 1 else 0) := by
    intro x hx
    by_cases hcond : x < m * n ∧ x ≤ m * n - m * z
    · have heq : x + (m * n - m * z - x) + m * z = m * n := by omega
      have hback : m * n - m * z + m * z = m * n := Nat.sub_add_cancel hmz
      rw [Finset.sum_eq_single (m * n - m * z - x)]
      · simp [hcond, heq, hback]
      · intro y hy hne
        have hneq : ¬ (x + y + m * z = m * n ∧ x < m * n) := by
          intro h
          have : y = m * n - m * z - x := by omega
          exact hne this
        rw [ite_eq_right hneq]
      · intro hnot
        have hmem : m * n - m * z - x ∈ Finset.range (m * n + 1) := by
          simp only [Finset.mem_range]
          omega
        exact (hnot hmem).elim
    · have hzero : ∀ y ∈ Finset.range (m * n + 1),
          (if x + y + m * z = m * n ∧ x < m * n then 1 else 0 : ℕ) = 0 := by
        intro y hy
        have hf : ¬ (x + y + m * z = m * n ∧ x < m * n) := by
          intro h
          apply hcond
          constructor
          · exact h.2
          · omega
        rw [ite_eq_right hf]
      rw [Finset.sum_eq_zero hzero]
      simp [hcond]
  rw [Finset.sum_congr rfl hinner]
  rw [← Finset.sum_filter]
  by_cases hz0 : z = 0
  · subst z
    simp only [Nat.mul_zero, Nat.sub_zero]
    have hf : (Finset.range (m * n + 1)).filter (fun x => x < m * n ∧ x ≤ m * n) =
        Finset.range (m * n) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor <;> intro h <;> omega
    rw [hf]
    simp
  · have hmzpos : 0 < m * z := Nat.mul_pos hm (Nat.pos_of_ne_zero hz0)
    have hf : (Finset.range (m * n + 1)).filter (fun x => x < m * n ∧ x ≤ m * n - m * z) =
        Finset.range (m * n - m * z + 1) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor <;> intro h <;> omega
    rw [hf]
    simp [hz0]

set_option maxHeartbeats 800000 in
lemma y_slice (m n z : ℕ) (hm : 0 < m) (hz : z ≤ n) :
    (∑ x ∈ Finset.range (m * n + 1), ∑ y ∈ Finset.range (m * n + 1),
      (if x + y + m * z = m * n ∧ y < m * n then 1 else 0 : ℕ)) =
      (if z = 0 then m * n else m * n - m * z + 1) := by
  rw [Finset.sum_comm]
  have hswap : ∀ y ∈ Finset.range (m * n + 1),
      (∑ x ∈ Finset.range (m * n + 1),
        (if x + y + m * z = m * n ∧ y < m * n then 1 else 0 : ℕ)) =
      (∑ x ∈ Finset.range (m * n + 1),
        (if y + x + m * z = m * n ∧ y < m * n then 1 else 0 : ℕ)) := by
    intro y hy
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h1 : x + y + m * z = m * n ∧ y < m * n
    · have h2 : y + x + m * z = m * n ∧ y < m * n := by constructor <;> omega
      simp [h1, h2]
    · have h2 : ¬ (y + x + m * z = m * n ∧ y < m * n) := by
        intro hh
        apply h1
        constructor <;> omega
      simp [h1, h2]
  rw [Finset.sum_congr rfl hswap]
  exact x_slice m n z hm hz

set_option maxHeartbeats 800000 in
lemma x_total (m n : ℕ) (hm : 0 < m) (hn : 1 ≤ n) :
    (∑ x ∈ Finset.range (m * n + 1), ∑ y ∈ Finset.range (m * n + 1),
      ∑ z ∈ Finset.range (m * n + 1),
        (if x + y + m * z = m * n ∧ x < m * n then 1 else 0 : ℕ)) =
      m * n + ∑ k ∈ Finset.range n, (m * k + 1) := by
  rw [sum_three_swap]
  have hnC : n ≤ m * n := by nlinarith
  have hslice : ∀ z ∈ Finset.range (m * n + 1),
      (∑ y ∈ Finset.range (m * n + 1), ∑ x ∈ Finset.range (m * n + 1),
        (if x + y + m * z = m * n ∧ x < m * n then 1 else 0 : ℕ)) =
        (if z ≤ n then (if z = 0 then m * n else m * n - m * z + 1) else 0) := by
    intro z hz
    by_cases hzn : z ≤ n
    · have hs := x_slice m n z hm hzn
      rw [Finset.sum_comm] at hs
      rw [hs]
      simp [hzn]
    · have hnlt : n < z := Nat.lt_of_not_ge hzn
      have hmzn : m * n < m * z := Nat.mul_lt_mul_of_pos_left hnlt hm
      rw [Finset.sum_eq_zero]
      · simp [hzn]
      · intro y hy
        apply Finset.sum_eq_zero
        intro x hx
        have hf : ¬ (x + y + m * z = m * n ∧ x < m * n) := by
          intro h
          omega
        rw [ite_eq_right hf]
  rw [Finset.sum_congr rfl hslice]
  rw [← Finset.sum_filter]
  have hf : (Finset.range (m * n + 1)).filter (fun z => z ≤ n) = Finset.range (n + 1) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor <;> intro h <;> omega
  rw [hf, Finset.sum_range_succ']
  simp only [Nat.mul_zero, Nat.sub_zero, ite_true]
  have hterm : ∀ z ∈ Finset.range n,
      (if z + 1 = 0 then m * n else m * n - m * (z + 1) + 1) = m * (n - 1 - z) + 1 := by
    intro z hz
    have hzlt : z < n := Finset.mem_range.mp hz
    have hnz : z + 1 ≠ 0 := by omega
    simp only [hnz, ite_false]
    have hmul : m * (z + 1) = m * z + m := by ring
    rw [hmul]
    have hnk : n - 1 - z = n - (z + 1) := by omega
    have hright : m * (n - 1 - z) = m * n - (m * z + m) := by
      rw [hnk, Nat.mul_sub_left_distrib, hmul]
    rw [hright]
  rw [Finset.sum_congr rfl hterm]
  rw [show (∑ z ∈ Finset.range n, (m * (n - 1 - z) + 1)) =
      ∑ z ∈ Finset.range n, (m * z + 1) by
        simpa using (Finset.sum_range_reflect (fun k => m * k + 1) n)]
  omega

set_option maxHeartbeats 800000 in
lemma y_total (m n : ℕ) (hm : 0 < m) (hn : 1 ≤ n) :
    (∑ x ∈ Finset.range (m * n + 1), ∑ y ∈ Finset.range (m * n + 1),
      ∑ z ∈ Finset.range (m * n + 1),
        (if x + y + m * z = m * n ∧ y < m * n then 1 else 0 : ℕ)) =
      m * n + ∑ k ∈ Finset.range n, (m * k + 1) := by
  rw [sum_three_swap]
  have hnC : n ≤ m * n := by nlinarith
  have hslice : ∀ z ∈ Finset.range (m * n + 1),
      (∑ y ∈ Finset.range (m * n + 1), ∑ x ∈ Finset.range (m * n + 1),
        (if x + y + m * z = m * n ∧ y < m * n then 1 else 0 : ℕ)) =
        (if z ≤ n then (if z = 0 then m * n else m * n - m * z + 1) else 0) := by
    intro z hz
    by_cases hzn : z ≤ n
    · have hs := y_slice m n z hm hzn
      rw [Finset.sum_comm] at hs
      rw [hs]
      simp [hzn]
    · have hnlt : n < z := Nat.lt_of_not_ge hzn
      have hmzn : m * n < m * z := Nat.mul_lt_mul_of_pos_left hnlt hm
      rw [Finset.sum_eq_zero]
      · simp [hzn]
      · intro y hy
        apply Finset.sum_eq_zero
        intro x hx
        have hf : ¬ (x + y + m * z = m * n ∧ y < m * n) := by
          intro h
          omega
        rw [ite_eq_right hf]
  rw [Finset.sum_congr rfl hslice]
  rw [← Finset.sum_filter]
  have hf : (Finset.range (m * n + 1)).filter (fun z => z ≤ n) = Finset.range (n + 1) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor <;> intro h <;> omega
  rw [hf, Finset.sum_range_succ']
  simp only [Nat.mul_zero, Nat.sub_zero, ite_true]
  have hterm : ∀ z ∈ Finset.range n,
      (if z + 1 = 0 then m * n else m * n - m * (z + 1) + 1) = m * (n - 1 - z) + 1 := by
    intro z hz
    have hzlt : z < n := Finset.mem_range.mp hz
    have hnz : z + 1 ≠ 0 := by omega
    simp only [hnz, ite_false]
    have hmul : m * (z + 1) = m * z + m := by ring
    rw [hmul]
    have hnk : n - 1 - z = n - (z + 1) := by omega
    have hright : m * (n - 1 - z) = m * n - (m * z + m) := by
      rw [hnk, Nat.mul_sub_left_distrib, hmul]
    rw [hright]
  rw [Finset.sum_congr rfl hterm]
  rw [show (∑ z ∈ Finset.range n, (m * (n - 1 - z) + 1)) =
      ∑ z ∈ Finset.range n, (m * z + 1) by
        simpa using (Finset.sum_range_reflect (fun k => m * k + 1) n)]
  omega

/-! ### Counting the `+z` faces by telescoping -/

/-- The layer count at height `z`. -/
def zLayer (m n z : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (m * n + 1), ∑ y ∈ Finset.range (m * n + 1),
    (if (x + y + m * z ≤ m * n ∧ m * n < x + y + m * z + m ∧ z < m * n)
      then 1 else 0 : ℕ)

/-- The prefix triangular count, extended by `0` above the plane. -/
def zg (m n z : ℕ) : ℕ := if z ≤ n then pairLe (m * n) (m * n - m * z) else 0

set_option maxHeartbeats 800000 in
lemma z_slice (m n z : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) (hz : z ≤ m * n) :
    zLayer m n z = zg m n z - zg m n (z + 1) := by
  have hmpos : 0 < m := by omega
  have hnC : n < m * n := by nlinarith
  by_cases hzn : z ≤ n
  · have hzC : z < m * n := lt_of_le_of_lt hzn hnC
    by_cases hzeq : z = n
    · subst z
      have hl : zLayer m n n = pairLe (m * n) 0 := by
        unfold zLayer pairLe
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        have hiff : (x + y + m * n ≤ m * n ∧ m * n < x + y + m * n + m ∧ n < m * n) ↔
            x + y ≤ 0 := by
          constructor <;> intro h <;> omega
        by_cases hp0 : x + y ≤ 0
        · have hp0' : x + y + m * n ≤ m * n ∧ m * n < x + y + m * n + m ∧ n < m * n :=
            hiff.mpr hp0
          simp [hp0, hp0']
        · have hp0' : ¬ (x + y + m * n ≤ m * n ∧ m * n < x + y + m * n + m ∧ n < m * n) := by
            intro h
            exact hp0 (hiff.mp h)
          simp [hp0, hp0']
      have hp := pairLe_two (m * n) 0 (Nat.zero_le _)
      have hp' : 2 * pairLe (m * n) 0 = (0 + 1) * (0 + 2) := hp
      have hrhs : (0 + 1 : ℕ) * (0 + 2) = 2 * 1 := by norm_num
      rw [hrhs] at hp'
      have hp1 : pairLe (m * n) 0 = 1 := Nat.mul_left_cancel (by norm_num) hp'
      unfold zg
      simp [hn, hp1]
      simpa [hp1] using hl
    · have hzlt : z < n := lt_of_le_of_ne hzn hzeq
      have hz1n : z + 1 ≤ n := by omega
      let t1 := m * n - m * z
      let t2 := m * n - m * (z + 1)
      have hmz : m * z ≤ m * n := Nat.mul_le_mul_left m hzn
      have hmul : m * (z + 1) = m * z + m := by ring
      have hmz1' : m * z + m ≤ m * n := by simpa [hmul] using (Nat.mul_le_mul_left m hz1n)
      have ht2t1 : t2 ≤ t1 := by dsimp [t1, t2]; rw [hmul]; omega
      have ht1C : t1 ≤ m * n := by dsimp [t1]; omega
      have htadd : t2 + m = t1 := by
        dsimp [t1, t2]
        rw [hmul]
        omega
      have hpoint : ∀ x ∈ Finset.range (m * n + 1), ∀ y ∈ Finset.range (m * n + 1),
          ((if (x + y + m * z ≤ m * n ∧ m * n < x + y + m * z + m ∧ z < m * n)
              then 1 else 0 : ℕ) +
           (if x + y ≤ t2 then 1 else 0 : ℕ)) = (if x + y ≤ t1 then 1 else 0 : ℕ) := by
        intro x hx y hy
        have ht1eq : t1 + m * z = m * n := by dsimp [t1]; omega
        have hiff1 : (x + y + m * z ≤ m * n ∧ m * n < x + y + m * z + m ∧ z < m * n) ↔
            (x + y ≤ t1 ∧ t2 < x + y) := by
          constructor
          · intro h
            constructor <;> omega
          · intro h
            constructor <;> omega
        by_cases h1 : x + y ≤ t1
        · by_cases h2 : t2 < x + y
          · have hf : x + y + m * z ≤ m * n ∧ m * n < x + y + m * z + m ∧ z < m * n :=
              hiff1.mpr ⟨h1, h2⟩
            have hnot2 : ¬ x + y ≤ t2 := by omega
            simp [hf, h1, hnot2]
          · have hf : ¬ (x + y + m * z ≤ m * n ∧ m * n < x + y + m * z + m ∧ z < m * n) := by
              intro hh
              have := hiff1.mp hh
              omega
            have hle2 : x + y ≤ t2 := by omega
            simp [hf, h1, hle2]
        · have hf : ¬ (x + y + m * z ≤ m * n ∧ m * n < x + y + m * z + m ∧ z < m * n) := by
            intro hh
            have := hiff1.mp hh
            omega
          have hnot2 : ¬ x + y ≤ t2 := by omega
          simp [hf, h1, hnot2]
      have hEq : zLayer m n z + pairLe (m * n) t2 = pairLe (m * n) t1 := by
        unfold zLayer pairLe
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        rw [← Finset.sum_add_distrib]
        rw [Finset.sum_congr rfl (fun y hy => hpoint x hx y hy)]
      have hzlayer : zLayer m n z = pairLe (m * n) t1 - pairLe (m * n) t2 := by omega
      unfold zg
      simp [hzn, hz1n]
      simpa [t1, t2] using hzlayer
  · have hznlt : n < z := Nat.lt_of_not_ge hzn
    have hmzn : m * n < m * z := Nat.mul_lt_mul_of_pos_left hznlt hmpos
    have hlzero : zLayer m n z = 0 := by
      unfold zLayer
      apply Finset.sum_eq_zero
      intro x hx
      apply Finset.sum_eq_zero
      intro y hy
      have hf : ¬ (x + y + m * z ≤ m * n ∧ m * n < x + y + m * z + m ∧ z < m * n) := by
        intro h
        omega
      rw [ite_eq_right hf]
    unfold zg
    simp [hzn]
    have hzn1 : ¬ z + 1 ≤ n := by omega
    simp [hzn1, hlzero]

set_option maxHeartbeats 800000 in
lemma zg_decreasing (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) :
    ∀ k, zg m n (k + 1) ≤ zg m n k := by
  intro k
  unfold zg
  by_cases hk : k + 1 ≤ n
  · have hk0 : k ≤ n := by omega
    simp [hk, hk0]
    apply pairLe_mono
    have hmul : m * (k + 1) = m * k + m := by ring
    rw [hmul]
    omega
  · simp [hk]

lemma sum_telescope_dec (g : ℕ → ℕ) (N : ℕ) (hdec : ∀ k, g (k + 1) ≤ g k) :
    (∑ z ∈ Finset.range N, (g z - g (z + 1))) = g 0 - g N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hanti : Antitone g := antitone_nat_of_succ_le hdec
      have hle1 : g N ≤ g 0 := hanti (Nat.zero_le N)
      have hle2 : g (N + 1) ≤ g N := hdec N
      omega

set_option maxHeartbeats 800000 in
lemma z_total (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) :
    (∑ x ∈ Finset.range (m * n + 1), ∑ y ∈ Finset.range (m * n + 1),
      ∑ z ∈ Finset.range (m * n + 1),
        (if (x + y + m * z ≤ m * n ∧ m * n < x + y + m * z + m ∧ z < m * n)
          then 1 else 0 : ℕ)) = pairLe (m * n) (m * n) := by
  rw [sum_three_swap]
  have hswap : ∀ z ∈ Finset.range (m * n + 1),
      (∑ y ∈ Finset.range (m * n + 1), ∑ x ∈ Finset.range (m * n + 1),
        (if (x + y + m * z ≤ m * n ∧ m * n < x + y + m * z + m ∧ z < m * n)
          then 1 else 0 : ℕ)) = zLayer m n z := by
    intro z hz
    unfold zLayer
    rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl hswap]
  rw [Finset.sum_congr rfl (fun z hz => z_slice m n z hm hn
    (by have := Finset.mem_range.mp hz; omega))]
  rw [sum_telescope_dec (zg m n) (m * n + 1) (zg_decreasing m n hm hn)]
  unfold zg
  have hnle : ¬ m * n < n := by nlinarith
  simp [hn, hnle]

/-! ### The closed form -/

set_option maxHeartbeats 800000 in
/-- **Closed form (doubled)**: `2 · faces = m²n² + 2mn² + 5mn + 4n + 2`
     for `m ≥ 2, n ≥ 1`. -/
theorem genFaces_eq_two (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) :
    2 * genFaces m n = m * m * n * n + 2 * m * n * n + 5 * m * n + 4 * n + 2 := by
  unfold genFaces
  simp only [Finset.sum_add_distrib]
  have hx := x_total m n (by omega : 0 < m) hn
  have hy := y_total m n (by omega : 0 < m) hn
  have hz := z_total m n hm hn
  rw [hx, hy, hz]
  have hS := sum_linear_two m n hn
  have hP : 2 * pairLe (m * n) (m * n) = (m * n + 1) * (m * n + 2) :=
    pairLe_two (m * n) (m * n) le_rfl
  nlinarith

lemma genFaces_real (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) :
    (genFaces m n : ℝ) =
      ((m : ℝ) * (m : ℝ) * (n : ℝ) * (n : ℝ) +
       2 * (m : ℝ) * (n : ℝ) * (n : ℝ) + 5 * (m : ℝ) * (n : ℝ) +
       4 * (n : ℝ) + 2) / 2 := by
  have h := genFaces_eq_two m n hm hn
  have hR : (2 : ℝ) * (genFaces m n : ℝ) =
      (m : ℝ) * (m : ℝ) * (n : ℝ) * (n : ℝ) +
      2 * (m : ℝ) * (n : ℝ) * (n : ℝ) + 5 * (m : ℝ) * (n : ℝ) + 4 * (n : ℝ) + 2 := by
    exact_mod_cast h
  nlinarith

/-! ### The true area of the cut and the limiting ratio -/

/-- The true area: the triangle with intercepts `(mn+1,0,0)`, `(0,mn+1,0)`,
     `(0,0,(mn+1)/m)`, i.e. `(√(m²+2)/(2m))·(mn+1)²`. -/
noncomputable def genCutArea (m n : ℕ) : ℝ :=
  (Real.sqrt ((m : ℝ) ^ 2 + 2) / (2 * (m : ℝ))) * ((m : ℝ) * (n : ℝ) + 1) ^ 2

set_option maxHeartbeats 800000 in
/-- Exact ratio identity used for the limit. -/
lemma genFaces_ratio_eq (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) :
    (genFaces m n : ℝ) / genCutArea m n =
      (m : ℝ) / Real.sqrt ((m : ℝ) ^ 2 + 2) *
        (((m : ℝ) * (m : ℝ) * (n : ℝ) * (n : ℝ) +
          2 * (m : ℝ) * (n : ℝ) * (n : ℝ) + 5 * (m : ℝ) * (n : ℝ) +
          4 * (n : ℝ) + 2) / ((m : ℝ) * (n : ℝ) + 1) ^ 2) := by
  have hmposR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hSpos : 0 < Real.sqrt ((m : ℝ) ^ 2 + 2) := by positivity
  have hden : (m : ℝ) * (n : ℝ) + 1 ≠ 0 := by positivity
  rw [genFaces_real m n hm hn]
  unfold genCutArea
  field_simp [hSpos.ne', hmposR.ne', hden]

set_option maxHeartbeats 800000 in
/-- **Limit of the ratio**: `faces / trueArea → (m+2)/√(m²+2)`. -/
theorem genFaces_ratio_tendsto (m : ℕ) (hm : 2 ≤ m) :
    Filter.Tendsto (fun n : ℕ => (genFaces m n : ℝ) / genCutArea m n)
      Filter.atTop (nhds (((m : ℝ) + 2) / Real.sqrt ((m : ℝ) ^ 2 + 2))) := by
  let S : ℝ := Real.sqrt ((m : ℝ) ^ 2 + 2)
  let T : ℝ := ((m : ℝ) + 2) / S
  have hmposR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hSpos : 0 < S := by dsimp [S]; positivity
  have hSne : S ≠ 0 := hSpos.ne'
  have hn_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hsmall : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.div_atTop hn_atTop :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) Filter.atTop (nhds 0))
  have hden_tendsto : Filter.Tendsto (fun n : ℕ => ((m : ℝ) + 1 / (n : ℝ)) ^ 2)
      Filter.atTop (nhds ((m : ℝ) ^ 2)) := by
    have hm1 : Filter.Tendsto (fun n : ℕ => (m : ℝ) + 1 / (n : ℝ)) Filter.atTop (nhds ((m : ℝ) + 0)) :=
      tendsto_const_nhds.add hsmall
    simpa using hm1.pow 2
  have hnum_tendsto : Filter.Tendsto
      (fun n : ℕ => ((m : ℝ) * (m : ℝ) * (n : ℝ) * (n : ℝ) +
        2 * (m : ℝ) * (n : ℝ) * (n : ℝ) + 5 * (m : ℝ) * (n : ℝ) +
        4 * (n : ℝ) + 2) / ((n : ℝ) ^ 2))
      Filter.atTop (nhds ((m : ℝ) * (m : ℝ) + 2 * (m : ℝ))) := by
    have h1 : Filter.Tendsto (fun n : ℕ => ((m : ℝ) * (m : ℝ) + 2 * (m : ℝ)) +
        (5 * (m : ℝ) + 4) / (n : ℝ) + 2 / ((n : ℝ) ^ 2)) Filter.atTop
        (nhds ((m : ℝ) * (m : ℝ) + 2 * (m : ℝ))) := by
      have hA : Filter.Tendsto (fun n : ℕ => (5 * (m : ℝ) + 4) / (n : ℝ)) Filter.atTop (nhds 0) := by
        simpa using (tendsto_const_nhds.div_atTop hn_atTop :
          Filter.Tendsto (fun n : ℕ => (5 * (m : ℝ) + 4) / (n : ℝ)) Filter.atTop (nhds 0))
      have hB : Filter.Tendsto (fun n : ℕ => (2 : ℝ) / ((n : ℝ) ^ 2)) Filter.atTop (nhds 0) := by
        have hsq : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) / (n : ℝ)) ^ 2) Filter.atTop (nhds 0) := by
          simpa using (hsmall.pow 2)
        have hB' : Filter.Tendsto (fun n : ℕ => (2 : ℝ) * ((1 : ℝ) / (n : ℝ)) ^ 2)
            Filter.atTop (nhds 0) := by
          simpa using (tendsto_const_nhds.mul hsq)
        apply hB'.congr'
        filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hnR : (n : ℝ) ≠ 0 := by positivity
        field_simp [hnR]
      simpa using ((tendsto_const_nhds.add hA).add hB)
    apply h1.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by positivity
    field_simp [hnR]
    ring
  have hmain : Filter.Tendsto
      (fun n : ℕ => (m : ℝ) / S *
        ((((m : ℝ) * (m : ℝ) * (n : ℝ) * (n : ℝ) +
          2 * (m : ℝ) * (n : ℝ) * (n : ℝ) + 5 * (m : ℝ) * (n : ℝ) +
          4 * (n : ℝ) + 2) / ((n : ℝ) ^ 2)) /
        ((m : ℝ) + 1 / (n : ℝ)) ^ 2))
      Filter.atTop (nhds ((m : ℝ) / S * (((m : ℝ) * (m : ℝ) + 2 * (m : ℝ)) / ((m : ℝ) ^ 2)))) := by
    have hdiv := hnum_tendsto.div hden_tendsto (by positivity : (m : ℝ) ^ 2 ≠ 0)
    have hconst : Filter.Tendsto (fun _ : ℕ => (m : ℝ) / S) Filter.atTop (nhds ((m : ℝ) / S)) :=
      tendsto_const_nhds
    exact hconst.mul hdiv
  have htarget : (m : ℝ) / S * (((m : ℝ) * (m : ℝ) + 2 * (m : ℝ)) / ((m : ℝ) ^ 2)) = T := by
    dsimp [T]
    field_simp [hSne, hmposR.ne']
  change Filter.Tendsto (fun n : ℕ => (genFaces m n : ℝ) / genCutArea m n)
    Filter.atTop (nhds T)
  rw [← htarget]
  apply hmain.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnR : (n : ℝ) ≠ 0 := by positivity
  rw [genFaces_ratio_eq m n hm (by omega)]
  field_simp [hSne, hnR]
  ring

set_option maxHeartbeats 800000 in
/-- **Non-consistency**: the ratio does not tend to `1` because its limit is
     `(m+2)/√(m²+2) > 1`. -/
theorem genFaces_ratio_not_tendsto_one (m : ℕ) (hm : 2 ≤ m) :
    ¬ Filter.Tendsto (fun n : ℕ => (genFaces m n : ℝ) / genCutArea m n)
        Filter.atTop (nhds 1) := by
  intro h
  have hlim := genFaces_ratio_tendsto m hm
  have heq : (((m : ℝ) + 2) / Real.sqrt ((m : ℝ) ^ 2 + 2)) = 1 :=
    tendsto_nhds_unique hlim h
  have hSpos : 0 < Real.sqrt ((m : ℝ) ^ 2 + 2) := by positivity
  have hSlt : Real.sqrt ((m : ℝ) ^ 2 + 2) < (m : ℝ) + 2 := by
    rw [Real.sqrt_lt (by positivity) (by positivity)]
    nlinarith [show (0 : ℝ) < (m : ℝ) by exact_mod_cast (by omega : 0 < m)]
  have hTgt : 1 < (((m : ℝ) + 2) / Real.sqrt ((m : ℝ) ^ 2 + 2)) := by
    rw [one_lt_div hSpos]
    exact hSlt
  linarith

end StaircasePlane3DGeneral

end Vdb
