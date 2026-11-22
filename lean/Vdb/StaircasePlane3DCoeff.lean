/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  Full three-term plane-coefficient generalization of the staircase
  inconsistency.

  `Vdb/StaircasePlane3D.lean` treats the equilateral cut `x + y + z = c`
  (limit `√3`) and `Vdb/StaircasePlane3DGeneral.lean` treats the one-parameter
  family `x + y + m·z = m·n` (limit `(m+2)/√(m²+2)`). This module goes beyond
  both: for arbitrary positive integers `p, q, m` with `m ≥ 2` it studies the
  plane

      p·x + q·y + m·z = m·n

  on the box `[0, m·n+1)³` with lower halfspace. A directed face crosses the
  cut when the moving coordinate stays in-window and the linear form passes
  from `≤ m·n` to `> m·n`; for the `+x` step this happens exactly on the band
  `m·n - p < p·x + (q·y + m·z) ≤ m·n`. Counting that band reduces to the
  lattice count `#{(y,z) : q·y + m·z ≤ T}` with `T = m·n`, up to one point.

  Main results (`p,q ≥ 1`, `m ≥ 2`, `n ≥ 1`, `T = m·n`):

    - `coefFaces_bounds`: a sharp two-sided asymptotic
        K·T² - 3 ≤ faces ≤ K·T² + C₁·T + C₀,
      where `K = (p+q+m)/(2·p·q·m)`. In particular
        faces = K·T² + O(T)  with  K = (p+q+m)/(2pqm).
    - `coefFaces_ratio_tendsto`:
        faces / trueArea → (p+q+m)/√(p²q² + q²m² + m²p²).
    - `coefFaces_ratio_not_tendsto_one`: non-consistency whenever this limit
      exceeds `1`.

  The true area is the area of the triangle with intercepts
  `((m·n)/p, 0, 0)`, `(0, (m·n)/q, 0)`, `(0, 0, (m·n)/m)`; its area is
  `√(p²q² + q²m² + m²p²)/(2pqm) · (m·n)²`. The leading coefficient ratio is
  exactly `(p+q+m)/√(p²q² + q²m² + m²p²)`, which is `> 1` by Cauchy--Schwarz
  unless `p = q = m` (and for `p = q = m` it equals `√3`, recovering the
  equilateral case). Pure kernel proofs throughout; no placeholders and no
  `native_decide`.

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
set_option linter.unnecessarySeqFocus false

namespace Vdb

namespace StaircasePlane3DCoeff


def latticeCount (a b T : ℕ) : ℕ :=
  ∑ y ∈ Finset.range (T + 1), ∑ z ∈ Finset.range (T + 1),
    (if a * y + b * z ≤ T then 1 else 0 : ℕ)

set_option maxHeartbeats 800000 in
lemma lattice_inner (a b T y : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∑ z ∈ Finset.range (T + 1), (if a * y + b * z ≤ T then 1 else 0 : ℕ)) =
      if a * y ≤ T then (T - a * y) / b + 1 else 0 := by
  by_cases hay : a * y ≤ T
  · rw [Finset.sum_boole]
    have hf : (Finset.range (T + 1)).filter (fun z => a * y + b * z ≤ T) =
        Finset.range ((T - a * y) / b + 1) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · intro h
        have hbz : b * z ≤ T - a * y := by omega
        have hzle : z ≤ (T - a * y) / b := (Nat.le_div_iff_mul_le hb).2 (by simpa [Nat.mul_comm] using hbz)
        simpa [Nat.succ_eq_add_one] using (Nat.lt_succ_of_le hzle)
      · intro hz
        have hzle : z ≤ (T - a * y) / b := by simpa [Nat.succ_eq_add_one] using (Nat.le_of_lt_succ hz)
        have hbz : b * z ≤ T - a * y := by
          simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hb).1 hzle
        have hzT : z ≤ T := le_trans hzle (le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _))
        exact ⟨Nat.lt_succ_of_le hzT, by omega⟩
    rw [hf, Finset.card_range]
    simp [hay]
  · have hz : ∀ z ∈ Finset.range (T + 1), (if a * y + b * z ≤ T then 1 else 0 : ℕ) = 0 := by
      intro z hzmem
      have hle : a * y ≤ a * y + b * z := Nat.le_add_right _ _
      have hf : ¬ (a * y + b * z ≤ T) := by omega
      rw [ite_eq_right hf]
    rw [Finset.sum_eq_zero hz]
    simp [hay]

set_option maxHeartbeats 800000 in
lemma latticeCount_eq_sum (a b T : ℕ) (ha : 0 < a) (hb : 0 < b) :
    latticeCount a b T = ∑ y ∈ Finset.range (T / a + 1), ((T - a * y) / b + 1) := by
  unfold latticeCount
  rw [Finset.sum_congr rfl (fun y hy => lattice_inner a b T y ha hb)]
  rw [← Finset.sum_filter]
  have hf : (Finset.range (T + 1)).filter (fun y => a * y ≤ T) = Finset.range (T / a + 1) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      have hyle : y ≤ T / a := (Nat.le_div_iff_mul_le ha).2 (by simpa [Nat.mul_comm] using h.2)
      simpa [Nat.succ_eq_add_one] using (Nat.lt_succ_of_le hyle)
    · intro h
      have hyle : y ≤ T / a := by simpa [Nat.succ_eq_add_one] using (Nat.le_of_lt_succ h)
      have hay : a * y ≤ T := by
        have hmul : a * y ≤ a * (T / a) := Nat.mul_le_mul_left a hyle
        exact le_trans hmul (Nat.mul_div_le T a)
      have hyT : y ≤ T := le_trans hyle (Nat.div_le_self T a)
      exact ⟨Nat.lt_succ_of_le hyT, hay⟩
  rw [hf]

set_option maxHeartbeats 800000 in
lemma two_sum_range_succ (q : ℕ) : 2 * (∑ i ∈ Finset.range (q + 1), i) = q * (q + 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ]
      calc
        2 * ((∑ x ∈ Finset.range (q + 1), x) + (q + 1))
            = 2 * (∑ x ∈ Finset.range (q + 1), x) + 2 * (q + 1) := by ring
        _ = q * (q + 1) + 2 * (q + 1) := by rw [ih]
        _ = (q + 1) * ((q + 1) + 1) := by ring

/- Exact closed forms obtained from `latticeCount_eq_sum`.

   `Nat.sub_mul_div` gives `(T - a*y)/a = T/a - y` pointwise on the range
   `y ≤ T/a`, so for `a = b` the floor-sum collapses to a triangular sum.
   These are exact equalities of naturals (no asymptotics, no hypotheses
   beyond positivity), and they can be used to replace the `a = b` instances
   of `latticeCount_bounds` by sharp formulas. -/

set_option maxHeartbeats 800000 in
lemma latticeCount_eq_diag_sum (a T : ℕ) (ha : 0 < a) :
    latticeCount a a T = ∑ y ∈ Finset.range (T / a + 1), (T / a + 1 - y) := by
  rw [latticeCount_eq_sum a a T ha ha]
  apply Finset.sum_congr rfl
  intro y hy
  have hyq : y ≤ T / a := Nat.le_of_lt_succ (Finset.mem_range.mp hy)
  rw [Nat.sub_mul_div]
  omega

set_option maxHeartbeats 800000 in
lemma sum_range_anti (q : ℕ) :
    (∑ y ∈ Finset.range (q + 1), (q + 1 - y)) = (q + 1) * (q + 2) / 2 := by
  let S : ℕ := ∑ i ∈ Finset.range (q + 1), i
  have htwoS : 2 * S = q * (q + 1) := by
    dsimp [S]
    exact two_sum_range_succ q
  have hreflect : (∑ y ∈ Finset.range (q + 1), (q + 1 - y)) =
      ∑ j ∈ Finset.range (q + 1), (j + 1) := by
    have h := Finset.sum_range_reflect (fun j : ℕ => j + 1) (q + 1)
    convert h using 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjle : j ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    omega
  have hsup : (∑ j ∈ Finset.range (q + 1), (j + 1)) = S + (q + 1) := by
    dsimp [S]
    rw [Finset.sum_add_distrib]
    simp
  have htwototal : 2 * (∑ y ∈ Finset.range (q + 1), (q + 1 - y)) =
      (q + 1) * (q + 2) := by
    rw [hreflect, hsup]
    nlinarith
  have hdvd : 2 ∣ (q + 1) * (q + 2) := by
    convert (Nat.even_mul_succ_self (q + 1)).two_dvd using 1 <;> omega
  symm
  rw [Nat.div_eq_iff_eq_mul_left (by norm_num : 0 < 2) hdvd]
  nlinarith

set_option maxHeartbeats 800000 in
lemma latticeCount_diag (a T : ℕ) (ha : 0 < a) :
    latticeCount a a T = (T / a + 1) * (T / a + 2) / 2 := by
  rw [latticeCount_eq_diag_sum a T ha]
  exact sum_range_anti (T / a)

/- More generally, if `b ∣ a` then `(T - a*y)/b = T/b - (a/b)*y` on the
   whole summation range, so the two-dimensional count reduces to one exact
   arithmetic-progression sum. -/
set_option maxHeartbeats 800000 in
lemma latticeCount_eq_divisible_sum (a b T : ℕ) (ha : 0 < a) (hb : 0 < b) (hdiv : b ∣ a) :
    latticeCount a b T = ∑ y ∈ Finset.range (T / a + 1), (T / b - (a / b) * y + 1) := by
  rw [latticeCount_eq_sum a b T ha hb]
  apply Finset.sum_congr rfl
  intro y hy
  have hmul : b * ((a / b) * y) = a * y := by
    rw [← Nat.mul_assoc, Nat.mul_comm b (a / b), Nat.div_mul_cancel hdiv]
  rw [← hmul, Nat.sub_mul_div]

/- Exact isolation of the only term that still needs number theory for the
   coprime asymptotic.  Writing `q = T/a`, every summand of `latticeCount_eq_sum`
   satisfies `((T - a*y)/b + 1 : ℕ) = ((T - a*y : ℕ) : ℝ)/b + 1
   - (((T - a*y) % b : ℕ) : ℝ)/b`.  Summing and using
   `∑ (T - a*y) = (q+1)*T - a*q*(q+1)/2` gives the identity below.  Writing
   `r = T%a` and `R = ∑_{y<q+1} ((T - a*y) % b)`, an exact rearrangement gives

     latticeCount a b T - (T²/(2ab) + T/(2a) + T/(2b) + T/(2ab))
       = ((q+1)*(b-1)/2 - R)/b + (a*b + a*r + a - b*r - r² - r)/(2*a*b).

   The second term is bounded by a constant depending only on `a,b` (since
   `0 ≤ r < a`).  Hence an exact main term with an `O(a+b)` periodic error for
   `a.Coprime b` reduces exactly to the still-unproved residue estimate

     |R - (q+1)*(b-1)/2| ≤ b²

   (equidistribution of `a*y mod b` over consecutive blocks of length `b`).
   For non-coprime `a,b` this residue estimate fails and the linear error
   genuinely persists, so the coprime hypothesis is essential. -/
set_option maxHeartbeats 800000 in
lemma latticeCount_eq_residue_sum (a b T : ℕ) (ha : 0 < a) (hb : 0 < b) :
    let q := T / a
    (latticeCount a b T : ℝ) =
      (((q + 1 : ℕ) : ℝ) * (T : ℝ) - (a : ℝ) * ((q : ℝ) * ((q + 1 : ℕ) : ℝ) / 2)) / (b : ℝ)
      + ((q + 1 : ℕ) : ℝ)
      - (((∑ y ∈ Finset.range (q + 1), ((T - a * y) % b)) : ℕ) : ℝ) / (b : ℝ) := by
  dsimp
  set q := T / a
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hy_le : ∀ y ∈ Finset.range (q + 1), a * y ≤ T := by
    intro y hy
    have hyq : y ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hy)
    have hmul : a * y ≤ a * q := Nat.mul_le_mul_left a hyq
    exact le_trans hmul (Nat.mul_div_le T a)
  have hsum_id : (∑ y ∈ Finset.range (q + 1), (((T - a * y : ℕ) : ℝ))) =
      ((q + 1 : ℕ) : ℝ) * (T : ℝ) - (a : ℝ) * ((q : ℝ) * ((q + 1 : ℕ) : ℝ) / 2) := by
    calc
      (∑ y ∈ Finset.range (q + 1), (((T - a * y : ℕ) : ℝ)))
          = ∑ y ∈ Finset.range (q + 1), ((T : ℝ) - (a : ℝ) * (y : ℝ)) := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [Nat.cast_sub (hy_le y hy)]
              push_cast
              ring
      _ = ((q + 1 : ℕ) : ℝ) * (T : ℝ) - (a : ℝ) * (∑ y ∈ Finset.range (q + 1), (y : ℝ)) := by
              rw [Finset.sum_sub_distrib]
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              rw [Finset.mul_sum]
      _ = ((q + 1 : ℕ) : ℝ) * (T : ℝ) - (a : ℝ) * ((q : ℝ) * ((q + 1 : ℕ) : ℝ) / 2) := by
              rw [show (∑ y ∈ Finset.range (q + 1), (y : ℝ)) =
                  (q : ℝ) * ((q + 1 : ℕ) : ℝ) / 2 by
                rw [← Nat.cast_sum]
                have ht := two_sum_range_succ q
                have htR : (2 : ℝ) * ((∑ y ∈ Finset.range (q + 1), y : ℕ) : ℝ) =
                    (q : ℝ) * ((q + 1 : ℕ) : ℝ) := by exact_mod_cast ht
                nlinarith]
  have hterm : ∀ y ∈ Finset.range (q + 1),
      (((T - a * y) / b + 1 : ℕ) : ℝ) =
        (((T - a * y : ℕ) : ℝ) - (((T - a * y) % b : ℕ) : ℝ)) / (b : ℝ) + 1 := by
    intro y hy
    have hmod := Nat.div_add_mod (T - a * y) b
    have hcast : ((b : ℝ) * (((T - a * y) / b : ℕ) : ℝ) + (((T - a * y) % b : ℕ) : ℝ)) =
        ((T - a * y : ℕ) : ℝ) := by exact_mod_cast hmod
    push_cast
    field_simp [hbR.ne']
    nlinarith
  rw [latticeCount_eq_sum a b T ha hb]
  rw [show T / a + 1 = q + 1 by rfl]
  rw [@Nat.cast_sum ℝ _ _ _]
  rw [Finset.sum_congr rfl hterm]
  calc
    (∑ y ∈ Finset.range (q + 1),
        ((((T - a * y : ℕ) : ℝ) - (((T - a * y) % b : ℕ) : ℝ)) / (b : ℝ) + 1))
        = ((∑ y ∈ Finset.range (q + 1),
              (((T - a * y : ℕ) : ℝ) - (((T - a * y) % b : ℕ) : ℝ))) / (b : ℝ)) +
            ((q + 1 : ℕ) : ℝ) := by
              rw [Finset.sum_add_distrib, Finset.sum_div]
              simp
    _ = ((∑ y ∈ Finset.range (q + 1), (((T - a * y : ℕ) : ℝ))) -
            (∑ y ∈ Finset.range (q + 1), (((T - a * y) % b : ℕ) : ℝ))) / (b : ℝ) +
            ((q + 1 : ℕ) : ℝ) := by
              rw [Finset.sum_sub_distrib]
    _ = (((q + 1 : ℕ) : ℝ) * (T : ℝ) - (a : ℝ) * ((q : ℝ) * ((q + 1 : ℕ) : ℝ) / 2)) / (b : ℝ) +
            ((q + 1 : ℕ) : ℝ) -
            (((∑ y ∈ Finset.range (q + 1), ((T - a * y) % b)) : ℕ) : ℝ) / (b : ℝ) := by
              rw [hsum_id]
              rw [← Nat.cast_sum]
              ring

set_option maxHeartbeats 800000 in
lemma latticeCount_bounds (a b T : ℕ) (ha : 0 < a) (hb : 0 < b) (hT : 0 < T) :
    ((T : ℝ) ^ 2 / (2 * a * b) ≤ (latticeCount a b T : ℝ)) ∧
    ((latticeCount a b T : ℝ) ≤ (T : ℝ) ^ 2 / (2 * a * b) + (T : ℝ) / b + (T : ℝ) / a + (a : ℝ) / (2 * b) + 1) := by
  let q := T / a
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqle : (q : ℝ) ≤ (T : ℝ) / a := by
    apply (le_div_iff₀ haR).2
    dsimp [q]
    exact_mod_cast (by simpa [Nat.mul_comm] using Nat.mul_div_le T a)
  have hqgt : (T : ℝ) / a - 1 < (q : ℝ) := by
    have hnat := Nat.div_add_mod T a
    have hcast : (a : ℝ) * ((T / a : ℕ) : ℝ) + ((T % a : ℕ) : ℝ) = (T : ℝ) := by exact_mod_cast hnat
    have hmodNat := Nat.mod_lt T ha
    have hmod : ((T % a : ℕ) : ℝ) < (a : ℝ) := by exact_mod_cast hmodNat
    have htmp : (T : ℝ) / a < (q : ℝ) + 1 := by
      apply (div_lt_iff₀ haR).2
      dsimp [q]
      nlinarith
    linarith
  have hqle' : (a : ℝ) * (q : ℝ) ≤ (T : ℝ) := by
    have := (le_div_iff₀ haR).1 hqle
    nlinarith
  have hqgt' : (T : ℝ) < (a : ℝ) * ((q : ℝ) + 1) := by
    have htmp : (T : ℝ) / a < (q : ℝ) + 1 := by linarith
    have := (div_lt_iff₀ haR).1 htmp
    nlinarith
  have hy_le : ∀ y ∈ Finset.range (q + 1), a * y ≤ T := by
    intro y hy
    have hyq : y ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hy)
    have hmul : a * y ≤ a * q := Nat.mul_le_mul_left a hyq
    exact le_trans hmul (Nat.mul_div_le T a)
  have hsum_y : (∑ y ∈ Finset.range (q + 1), (y : ℝ)) = (q : ℝ) * (q + 1 : ℝ) / 2 := by
    rw [← Nat.cast_sum]
    have htwo := two_sum_range_succ q
    have htwoR : (2 : ℝ) * ((∑ y ∈ Finset.range (q + 1), y : ℕ) : ℝ) =
        (q : ℝ) * (q + 1 : ℝ) := by exact_mod_cast htwo
    nlinarith
  have hsum_id : (∑ y ∈ Finset.range (q + 1), (((T - a * y : ℕ) : ℝ))) =
      ((q + 1 : ℕ) : ℝ) * (T : ℝ) - (a : ℝ) * ((q : ℝ) * (q + 1 : ℝ) / 2) := by
    calc
      (∑ y ∈ Finset.range (q + 1), (((T - a * y : ℕ) : ℝ)))
          = ∑ y ∈ Finset.range (q + 1), ((T : ℝ) - (a : ℝ) * (y : ℝ)) := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [Nat.cast_sub (hy_le y hy)]
              push_cast
              ring
      _ = ((q + 1 : ℕ) : ℝ) * (T : ℝ) - (a : ℝ) * (∑ y ∈ Finset.range (q + 1), (y : ℝ)) := by
              rw [Finset.sum_sub_distrib]
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              rw [Finset.mul_sum]
      _ = ((q + 1 : ℕ) : ℝ) * (T : ℝ) - (a : ℝ) * ((q : ℝ) * (q + 1 : ℝ) / 2) := by
              rw [hsum_y]
  have hS_eq : (∑ y ∈ Finset.range (q + 1), (((T - a * y : ℕ) : ℝ))) =
      ((q : ℝ) + 1) * ((T : ℝ) - (a : ℝ) * (q : ℝ) / 2) := by
    rw [hsum_id]
    push_cast
    ring
  have hAlo : (T : ℝ) ≤ (a : ℝ) * ((q : ℝ) + 1) := by nlinarith
  have hBlo : (T : ℝ) ≤ 2 * (T : ℝ) - (a : ℝ) * (q : ℝ) := by nlinarith
  have hAhi : (a : ℝ) * ((q : ℝ) + 1) ≤ (T : ℝ) + (a : ℝ) := by nlinarith
  have hBhi : 2 * (T : ℝ) - (a : ℝ) * (q : ℝ) ≤ (T : ℝ) + (a : ℝ) := by nlinarith
  have hBnonneg : 0 ≤ 2 * (T : ℝ) - (a : ℝ) * (q : ℝ) := by nlinarith
  have hprodlo := mul_le_mul hAlo hBlo (by positivity : 0 ≤ (T : ℝ)) (by positivity : 0 ≤ (a : ℝ) * ((q : ℝ) + 1))
  have hprodhi := mul_le_mul hAhi hBhi hBnonneg (by positivity : 0 ≤ (T : ℝ) + (a : ℝ))
  have hSlo : (T : ℝ) ^ 2 / (2 * a) ≤ (∑ y ∈ Finset.range (q + 1), (((T - a * y : ℕ) : ℝ))) := by
    rw [hS_eq]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * a)]
    nlinarith
  have hShi : (∑ y ∈ Finset.range (q + 1), (((T - a * y : ℕ) : ℝ))) ≤
      (T : ℝ) ^ 2 / (2 * a) + (T : ℝ) + (a : ℝ) / 2 := by
    rw [hS_eq]
    have hrhs : (T : ℝ) ^ 2 / (2 * a) + (T : ℝ) + (a : ℝ) / 2 =
        ((T : ℝ) ^ 2 + 2 * a * T + a ^ 2) / (2 * a) := by
      field_simp [haR.ne']
    rw [hrhs, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * a)]
    nlinarith
  have hterm_l : ∀ y ∈ Finset.range (q + 1),
      (((T - a * y : ℕ) : ℝ)) / (b : ℝ) ≤ (((T - a * y) / b + 1 : ℕ) : ℝ) := by
    intro y hy
    have hd : T - a * y < b * ((T - a * y) / b + 1) := by
      have hmod := Nat.mod_lt (T - a * y) hb
      have hdiv := Nat.div_add_mod (T - a * y) b
      have hmul : b * ((T - a * y) / b + 1) = b * ((T - a * y) / b) + b := by ring
      rw [hmul]
      omega
    have hdR : ((T - a * y : ℕ) : ℝ) < (b : ℝ) * (((T - a * y) / b + 1 : ℕ) : ℝ) := by exact_mod_cast hd
    apply (div_le_iff₀ hbR).2
    nlinarith
  have hterm_u : ∀ y ∈ Finset.range (q + 1),
      (((T - a * y) / b + 1 : ℕ) : ℝ) ≤ (((T - a * y : ℕ) : ℝ)) / (b : ℝ) + 1 := by
    intro y hy
    have hby := Nat.mul_div_le (T - a * y) b
    have hbyR : (b : ℝ) * (((T - a * y) / b : ℕ) : ℝ) ≤ ((T - a * y : ℕ) : ℝ) := by
      exact_mod_cast hby
    have hdivle : (((T - a * y) / b : ℕ) : ℝ) ≤ ((T - a * y : ℕ) : ℝ) / (b : ℝ) := by
      apply (le_div_iff₀ hbR).2
      nlinarith
    push_cast
    linarith
  have hsumdiv : (∑ y ∈ Finset.range (q + 1), (((T - a * y : ℕ) : ℝ)) / (b : ℝ)) =
      (∑ y ∈ Finset.range (q + 1), (((T - a * y : ℕ) : ℝ))) / (b : ℝ) := by
    rw [Finset.sum_div]
  constructor
  · rw [latticeCount_eq_sum a b T ha hb]
    rw [show T / a + 1 = q + 1 by rfl]
    rw [@Nat.cast_sum ℝ _ _ _]
    have hlow := Finset.sum_le_sum (fun y hy => hterm_l y hy)
    rw [hsumdiv] at hlow
    have hSlo_div : (T : ℝ) ^ 2 / (2 * a * b) ≤
        (∑ y ∈ Finset.range (q + 1), (((T - a * y : ℕ) : ℝ))) / (b : ℝ) := by
      have hh := (div_le_div_iff_of_pos_right hbR).2 hSlo
      convert hh using 1 <;> field_simp [haR.ne', hbR.ne'] <;> ring
    exact le_trans hSlo_div hlow
  · rw [latticeCount_eq_sum a b T ha hb]
    rw [show T / a + 1 = q + 1 by rfl]
    rw [@Nat.cast_sum ℝ _ _ _]
    have hupp := Finset.sum_le_sum (fun y hy => hterm_u y hy)
    have hupp2 : (∑ y ∈ Finset.range (q + 1), ((((T - a * y : ℕ) : ℝ)) / (b : ℝ) + 1)) =
        (∑ y ∈ Finset.range (q + 1), (((T - a * y : ℕ) : ℝ))) / (b : ℝ) + (q + 1 : ℕ) := by
      rw [Finset.sum_add_distrib, hsumdiv]
      simp
    rw [hupp2] at hupp
    have hq1 : ((q + 1 : ℕ) : ℝ) ≤ (T : ℝ) / a + 1 := by
      norm_num
      linarith
    have hShi_div : (∑ y ∈ Finset.range (q + 1), (((T - a * y : ℕ) : ℝ))) / (b : ℝ) ≤
        (T : ℝ) ^ 2 / (2 * a * b) + (T : ℝ) / b + (a : ℝ) / (2 * b) := by
      have hh := (div_le_div_iff_of_pos_right hbR).2 hShi
      convert hh using 1 <;> field_simp [haR.ne', hbR.ne'] <;> ring
    nlinarith

set_option maxHeartbeats 800000 in
lemma band_count (p s T : ℕ) (hp : 0 < p) (hT : 0 < T) :
    (∑ x ∈ Finset.range (T + 1),
        (if x < T ∧ T < p * x + s + p ∧ p * x + s ≤ T then 1 else 0 : ℕ)) =
      if s ≤ T ∧ (2 ≤ p ∨ 0 < s) then 1 else 0 := by
  let d := T - s
  by_cases hs : s ≤ T
  · have hTd : d + s = T := by dsimp [d]; omega
    by_cases hv : 2 ≤ p ∨ 0 < s
    · have hxT : d / p < T := by
        by_cases hd0 : d = 0
        · simp [hd0, hT]
        · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
          by_cases hp1 : p = 1
          · have : d / p = d := by simp [hp1]
            rw [this]
            have hs0 : s ≠ 0 := by omega
            omega
          · have hp2 : 1 < p := by omega
            exact lt_of_lt_of_le (Nat.div_lt_self hdpos hp2) (by dsimp [d]; omega)
      rw [Finset.sum_eq_single (d / p)]
      · have hpm : p * (d / p) = d - d % p := by
          have hdiv : p * (d / p) + d % p = d := Nat.div_add_mod d p
          have hmodle : d % p ≤ d := Nat.mod_le d p
          omega
        have hle : p * (d / p) + s ≤ T := by omega
        have hgt : T < p * (d / p) + s + p := by
          have hmodlt : d % p < p := Nat.mod_lt d hp
          have hmodle : d % p ≤ d := Nat.mod_le d p
          omega
        have hcond : d / p < T ∧ T < p * (d / p) + s + p ∧ p * (d / p) + s ≤ T :=
          ⟨hxT, hgt, hle⟩
        have hres : s ≤ T ∧ (2 ≤ p ∨ 0 < s) := ⟨hs, hv⟩
        rw [ite_eq_left hcond, ite_eq_left hres]
      · intro x hx hne
        by_cases hcond : x < T ∧ T < p * x + s + p ∧ p * x + s ≤ T
        · have hpx : p * x ≤ d := Nat.le_sub_of_add_le hcond.2.2
          have hlt : d < p * (x + 1) := by
            apply (Nat.sub_lt_iff_lt_add hs).2
            rw [Nat.mul_add]
            omega
          have hx_le : x ≤ d / p := by
            apply (Nat.le_div_iff_mul_le hp).2
            simpa [Nat.mul_comm] using hpx
          have hx_ge : d / p ≤ x := by
            have : d / p < x + 1 := (Nat.div_lt_iff_lt_mul hp).2 (by simpa [Nat.mul_comm] using hlt)
            omega
          exact (hne (by omega : x = d / p)).elim
        · rw [ite_eq_right hcond]
      · intro hnot
        have hmem : d / p ∈ Finset.range (T + 1) := by
          simp only [Finset.mem_range]
          exact Nat.lt_succ_of_le (Nat.le_of_lt hxT)
        exact (hnot hmem).elim
    · have hp1 : p = 1 := by omega
      have hs0 : s = 0 := by omega
      rw [Finset.sum_eq_zero]
      · have hnres : ¬ (s ≤ T ∧ (2 ≤ p ∨ 0 < s)) := by omega
        rw [ite_eq_right hnres]
      · intro x hx
        by_cases hc : x < T ∧ T < p * x + s + p ∧ p * x + s ≤ T
        · simp [hp1, hs0] at hc
          omega
        · rw [ite_eq_right hc]
  · have hsT : T < s := Nat.lt_of_not_ge hs
    rw [Finset.sum_eq_zero]
    · have hnres : ¬ (s ≤ T ∧ (2 ≤ p ∨ 0 < s)) := by omega
      rw [ite_eq_right hnres]
    · intro x hx
      rw [ite_eq_right (by omega : ¬ (x < T ∧ T < p * x + s + p ∧ p * x + s ≤ T))]

def bandFaces (d u w T : ℕ) : ℕ :=
  ∑ a ∈ Finset.range (T + 1), ∑ b ∈ Finset.range (T + 1), ∑ c ∈ Finset.range (T + 1),
    (if a < T ∧ T < (d * a + (u * b + w * c)) + d ∧ d * a + (u * b + w * c) ≤ T
      then 1 else 0 : ℕ)

set_option maxHeartbeats 800000 in
lemma bandFaces_eq_band (d u w T : ℕ) (hd : 0 < d) (hT : 0 < T) :
    bandFaces d u w T =
      ∑ b ∈ Finset.range (T + 1), ∑ c ∈ Finset.range (T + 1),
        (if u * b + w * c ≤ T ∧ (2 ≤ d ∨ 0 < u * b + w * c) then 1 else 0 : ℕ) := by
  unfold bandFaces
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  exact band_count d (u * b + w * c) T hd hT

set_option maxHeartbeats 800000 in
lemma bandFaces_bounds (d u w T : ℕ) (hd : 0 < d) (hu : 0 < u) (hw : 0 < w) (hT : 0 < T) :
    latticeCount u w T - 1 ≤ bandFaces d u w T ∧ bandFaces d u w T ≤ latticeCount u w T := by
  rw [bandFaces_eq_band d u w T hd hT]
  constructor
  · have hpoint : ∀ b ∈ Finset.range (T + 1), ∀ c ∈ Finset.range (T + 1),
        (if u * b + w * c ≤ T then 1 else 0 : ℕ) ≤
        (if u * b + w * c ≤ T ∧ (2 ≤ d ∨ 0 < u * b + w * c) then 1 else 0 : ℕ) +
        (if b = 0 ∧ c = 0 then 1 else 0 : ℕ) := by
      intro b hb c hc
      by_cases hs : u * b + w * c ≤ T
      · by_cases hd2 : 2 ≤ d ∨ 0 < u * b + w * c
        · have hconj : u * b + w * c ≤ T ∧ (2 ≤ d ∨ 0 < u * b + w * c) := ⟨hs, hd2⟩
          rw [ite_eq_left hconj, ite_eq_left hs]
          omega
        · have hd1 : d = 1 := by omega
          have hs0 : u * b + w * c = 0 := by omega
          have hb0 : b = 0 := by nlinarith
          have hc0 : c = 0 := by nlinarith
          have hnand : ¬ (u * b + w * c ≤ T ∧ (2 ≤ d ∨ 0 < u * b + w * c)) := by
            intro h
            exact hd2 h.2
          rw [ite_eq_right hnand, ite_eq_left hs]
          simp [hb0, hc0]
      · have hnand : ¬ (u * b + w * c ≤ T ∧ (2 ≤ d ∨ 0 < u * b + w * c)) := by
          intro h
          exact hs h.1
        rw [ite_eq_right hnand, ite_eq_right hs]
        norm_num
    have hsum := Finset.sum_le_sum (fun b hb => Finset.sum_le_sum (fun c hc => hpoint b hb c hc))
    unfold latticeCount
    have hsum2 : (∑ b ∈ Finset.range (T + 1), ∑ c ∈ Finset.range (T + 1),
        ((if u * b + w * c ≤ T ∧ (2 ≤ d ∨ 0 < u * b + w * c) then 1 else 0 : ℕ) +
         (if b = 0 ∧ c = 0 then 1 else 0 : ℕ))) =
        (∑ b ∈ Finset.range (T + 1), ∑ c ∈ Finset.range (T + 1),
          (if u * b + w * c ≤ T ∧ (2 ≤ d ∨ 0 < u * b + w * c) then 1 else 0 : ℕ)) +
        (∑ b ∈ Finset.range (T + 1), ∑ c ∈ Finset.range (T + 1),
          (if b = 0 ∧ c = 0 then 1 else 0 : ℕ)) := by
      calc
        (∑ b ∈ Finset.range (T + 1), ∑ c ∈ Finset.range (T + 1),
          ((if u * b + w * c ≤ T ∧ (2 ≤ d ∨ 0 < u * b + w * c) then 1 else 0 : ℕ) +
           (if b = 0 ∧ c = 0 then 1 else 0 : ℕ)))
            = ∑ b ∈ Finset.range (T + 1),
                ((∑ c ∈ Finset.range (T + 1),
                   (if u * b + w * c ≤ T ∧ (2 ≤ d ∨ 0 < u * b + w * c) then 1 else 0 : ℕ)) +
                 (∑ c ∈ Finset.range (T + 1),
                   (if b = 0 ∧ c = 0 then 1 else 0 : ℕ))) := by
                  apply Finset.sum_congr rfl
                  intro b hb
                  rw [Finset.sum_add_distrib]
        _ = (∑ b ∈ Finset.range (T + 1), ∑ c ∈ Finset.range (T + 1),
              (if u * b + w * c ≤ T ∧ (2 ≤ d ∨ 0 < u * b + w * c) then 1 else 0 : ℕ)) +
            (∑ b ∈ Finset.range (T + 1), ∑ c ∈ Finset.range (T + 1),
              (if b = 0 ∧ c = 0 then 1 else 0 : ℕ)) := by
                  rw [Finset.sum_add_distrib]
    rw [hsum2] at hsum
    have hsingle : (∑ b ∈ Finset.range (T + 1), ∑ c ∈ Finset.range (T + 1),
        (if b = 0 ∧ c = 0 then 1 else 0 : ℕ)) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro b hb hne
        by_cases hb0 : b = 0
        · exact (hne hb0).elim
        · apply Finset.sum_eq_zero
          intro c hc
          rw [ite_eq_right]
          intro h
          exact hb0 h.1
      · simp
    rw [hsingle] at hsum
    omega
  · apply Finset.sum_le_sum
    intro b hb
    apply Finset.sum_le_sum
    intro c hc
    by_cases h1 : u * b + w * c ≤ T
    · by_cases h2 : 2 ≤ d ∨ 0 < u * b + w * c
      · have hconj : u * b + w * c ≤ T ∧ (2 ≤ d ∨ 0 < u * b + w * c) := ⟨h1, h2⟩
        rw [ite_eq_left hconj, ite_eq_left h1]
      · have hnconj : ¬ (u * b + w * c ≤ T ∧ (2 ≤ d ∨ 0 < u * b + w * c)) := by
          intro h
          exact h2 h.2
        rw [ite_eq_right hnconj, ite_eq_left h1]
        norm_num
    · have hnand : ¬ (u * b + w * c ≤ T ∧ (2 ≤ d ∨ 0 < u * b + w * c)) := by
        intro h
        exact h1 h.1
      rw [ite_eq_right hnand, ite_eq_right h1]


def coefInside (p q m n x y z : ℕ) : Prop := p * x + q * y + m * z ≤ m * n

def coefFaces (p q m n : ℕ) : ℕ :=
  bandFaces p q m (m * n) + bandFaces q p m (m * n) + bandFaces m p q (m * n)

set_option maxHeartbeats 800000 in
theorem coefFaces_step_x (p q m n x y z : ℕ)
    (hx : x < m * n + 1) (hy : y < m * n + 1) (hz : z < m * n + 1) :
    (coefInside p q m n x y z ∧ x + 1 < m * n + 1 ∧ ¬ coefInside p q m n (x + 1) y z) ↔
      (x < m * n ∧ m * n < p * x + (q * y + m * z) + p ∧ p * x + (q * y + m * z) ≤ m * n) := by
  unfold coefInside
  have hmul : p * (x + 1) = p * x + p := by ring
  rw [hmul]
  omega

set_option maxHeartbeats 800000 in
theorem coefFaces_step_y (p q m n x y z : ℕ)
    (hx : x < m * n + 1) (hy : y < m * n + 1) (hz : z < m * n + 1) :
    (coefInside p q m n x y z ∧ y + 1 < m * n + 1 ∧ ¬ coefInside p q m n x (y + 1) z) ↔
      (y < m * n ∧ m * n < q * y + (p * x + m * z) + q ∧ q * y + (p * x + m * z) ≤ m * n) := by
  unfold coefInside
  have hmul : q * (y + 1) = q * y + q := by ring
  rw [hmul]
  omega

set_option maxHeartbeats 800000 in
theorem coefFaces_step_z (p q m n x y z : ℕ)
    (hx : x < m * n + 1) (hy : y < m * n + 1) (hz : z < m * n + 1) :
    (coefInside p q m n x y z ∧ z + 1 < m * n + 1 ∧ ¬ coefInside p q m n x y (z + 1)) ↔
      (z < m * n ∧ m * n < m * z + (p * x + q * y) + m ∧ m * z + (p * x + q * y) ≤ m * n) := by
  unfold coefInside
  have hmul : m * (z + 1) = m * z + m := by ring
  rw [hmul]
  omega

set_option maxHeartbeats 800000 in
theorem coefFaces_bounds (p q m n : ℕ) (hp : 0 < p) (hq : 0 < q) (hm : 2 ≤ m) (hn : 1 ≤ n) :
    (((p : ℝ) + (q : ℝ) + (m : ℝ)) / (2 * (p : ℝ) * (q : ℝ) * (m : ℝ))) * ((m * n : ℕ) : ℝ) ^ 2 - 3
        ≤ (coefFaces p q m n : ℝ) ∧
    (coefFaces p q m n : ℝ) ≤
        (((p : ℝ) + (q : ℝ) + (m : ℝ)) / (2 * (p : ℝ) * (q : ℝ) * (m : ℝ))) * ((m * n : ℕ) : ℝ) ^ 2 +
        (2 / (p : ℝ) + 2 / (q : ℝ) + 2 / (m : ℝ)) * ((m * n : ℕ) : ℝ) +
        ((q : ℝ) / (2 * (m : ℝ)) + (p : ℝ) / (2 * (m : ℝ)) +
          (p : ℝ) / (2 * (q : ℝ)) + 3) := by
  let T := m * n
  have hT : 0 < T := by dsimp [T]; nlinarith
  have hP : (0 : ℝ) < p := by exact_mod_cast hp
  have hQ : (0 : ℝ) < q := by exact_mod_cast hq
  have hM : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h1 := latticeCount_bounds q m T hq (by omega : 0 < m) hT
  have h2 := latticeCount_bounds p m T hp (by omega : 0 < m) hT
  have h3 := latticeCount_bounds p q T hp hq hT
  have b1 := bandFaces_bounds p q m T hp hq (by omega : 0 < m) hT
  have b2 := bandFaces_bounds q p m T hq hp (by omega : 0 < m) hT
  have b3 := bandFaces_bounds m p q T (by omega : 0 < m) hp hq hT
  have b1loNat : latticeCount q m T ≤ bandFaces p q m T + 1 := by omega
  have b2loNat : latticeCount p m T ≤ bandFaces q p m T + 1 := by omega
  have b3loNat : latticeCount p q T ≤ bandFaces m p q T + 1 := by omega
  have b1lo : (latticeCount q m T : ℝ) ≤ (bandFaces p q m T : ℝ) + 1 := by exact_mod_cast b1loNat
  have b2lo : (latticeCount p m T : ℝ) ≤ (bandFaces q p m T : ℝ) + 1 := by exact_mod_cast b2loNat
  have b3lo : (latticeCount p q T : ℝ) ≤ (bandFaces m p q T : ℝ) + 1 := by exact_mod_cast b3loNat
  have b1hi : (bandFaces p q m T : ℝ) ≤ (latticeCount q m T : ℝ) := by exact_mod_cast b1.2
  have b2hi : (bandFaces q p m T : ℝ) ≤ (latticeCount p m T : ℝ) := by exact_mod_cast b2.2
  have b3hi : (bandFaces m p q T : ℝ) ≤ (latticeCount p q T : ℝ) := by exact_mod_cast b3.2
  have hK : (((p : ℝ) + (q : ℝ) + (m : ℝ)) / (2 * p * q * m)) * (T : ℝ) ^ 2 =
      (T : ℝ) ^ 2 / (2 * q * m) + (T : ℝ) ^ 2 / (2 * p * m) + (T : ℝ) ^ 2 / (2 * p * q) := by
    field_simp [hP.ne', hQ.ne', hM.ne']
  unfold coefFaces
  rw [Nat.cast_add, Nat.cast_add]
  rw [show ((m * n : ℕ) : ℝ) = (T : ℝ) by rfl]
  rw [hK]
  change (T : ℝ) ^ 2 / (2 * q * m) + (T : ℝ) ^ 2 / (2 * p * m) + (T : ℝ) ^ 2 / (2 * p * q) - 3 ≤
      (bandFaces p q m T : ℝ) + (bandFaces q p m T : ℝ) + (bandFaces m p q T : ℝ) ∧
    (bandFaces p q m T : ℝ) + (bandFaces q p m T : ℝ) + (bandFaces m p q T : ℝ) ≤
      (T : ℝ) ^ 2 / (2 * q * m) + (T : ℝ) ^ 2 / (2 * p * m) + (T : ℝ) ^ 2 / (2 * p * q) +
      (2 / (p : ℝ) + 2 / (q : ℝ) + 2 / (m : ℝ)) * (T : ℝ) +
      ((q : ℝ) / (2 * (m : ℝ)) + (p : ℝ) / (2 * (m : ℝ)) + (p : ℝ) / (2 * (q : ℝ)) + 3)
  have hC : (2 / (p : ℝ) + 2 / (q : ℝ) + 2 / (m : ℝ)) * (T : ℝ) =
      ((T : ℝ) / (m : ℝ) + (T : ℝ) / (m : ℝ)) +
      ((T : ℝ) / (q : ℝ) + (T : ℝ) / (q : ℝ)) +
      ((T : ℝ) / (p : ℝ) + (T : ℝ) / (p : ℝ)) := by
    field_simp [hP.ne', hQ.ne', hM.ne']
    ring
  rw [hC]
  constructor
  · have hsumlo : (T : ℝ) ^ 2 / (2 * q * m) + (T : ℝ) ^ 2 / (2 * p * m) + (T : ℝ) ^ 2 / (2 * p * q) ≤
        (latticeCount q m T : ℝ) + (latticeCount p m T : ℝ) + (latticeCount p q T : ℝ) := by
      linarith [h1.1, h2.1, h3.1]
    linarith
  · have hsumhi : (latticeCount q m T : ℝ) + (latticeCount p m T : ℝ) + (latticeCount p q T : ℝ) ≤
        (T : ℝ) ^ 2 / (2 * q * m) + (T : ℝ) ^ 2 / (2 * p * m) + (T : ℝ) ^ 2 / (2 * p * q) +
        ((T : ℝ) / (m : ℝ) + (T : ℝ) / (q : ℝ) + (q : ℝ) / (2 * (m : ℝ)) + 1) +
        ((T : ℝ) / (m : ℝ) + (T : ℝ) / (p : ℝ) + (p : ℝ) / (2 * (m : ℝ)) + 1) +
        ((T : ℝ) / (q : ℝ) + (T : ℝ) / (p : ℝ) + (p : ℝ) / (2 * (q : ℝ)) + 1) := by
      linarith [h1.2, h2.2, h3.2]
    linarith

noncomputable def cutArea (p q m n : ℕ) : ℝ :=
  (Real.sqrt ((p : ℝ)^2 * (q : ℝ)^2 + (q : ℝ)^2 * (m : ℝ)^2 + (m : ℝ)^2 * (p : ℝ)^2) /
    (2 * (p : ℝ) * (q : ℝ) * (m : ℝ))) * ((m : ℝ) * (n : ℝ)) ^ 2

set_option maxHeartbeats 800000 in
lemma coefFaces_ratio_tendsto (p q m : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hm : 2 ≤ m) :
    Filter.Tendsto (fun n : ℕ => (coefFaces p q m n : ℝ) / cutArea p q m n)
      Filter.atTop (nhds (((p : ℝ) + (q : ℝ) + (m : ℝ)) /
        Real.sqrt ((p : ℝ)^2 * (q : ℝ)^2 + (q : ℝ)^2 * (m : ℝ)^2 + (m : ℝ)^2 * (p : ℝ)^2))) := by
  let S : ℝ := Real.sqrt ((p : ℝ)^2 * (q : ℝ)^2 + (q : ℝ)^2 * (m : ℝ)^2 + (m : ℝ)^2 * (p : ℝ)^2)
  let K : ℝ := ((p : ℝ) + (q : ℝ) + (m : ℝ)) / (2 * (p : ℝ) * (q : ℝ) * (m : ℝ))
  have hP : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hQ : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hM : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hSp : 0 < S := by dsimp [S]; positivity
  have hT_atTop : Filter.Tendsto (fun n : ℕ => ((m * n : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    exact Filter.tendsto_atTop_mono' Filter.atTop
      (f₁ := fun n : ℕ => (n : ℝ)) (f₂ := fun n : ℕ => ((m * n : ℕ) : ℝ))
      (by filter_upwards with n; exact_mod_cast (by nlinarith : n ≤ m * n))
      tendsto_natCast_atTop_atTop
  have hTsq_atTop : Filter.Tendsto (fun n : ℕ => ((m * n : ℕ) : ℝ) ^ 2) Filter.atTop Filter.atTop := by
    have hnat : Filter.Tendsto (fun n : ℕ => (((m * n) ^ 2 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
      exact Filter.tendsto_atTop_mono' Filter.atTop
        (f₁ := fun n : ℕ => (n : ℝ)) (f₂ := fun n : ℕ => (((m * n) ^ 2 : ℕ) : ℝ))
        (by
          filter_upwards with n
          have hle : n ≤ (m * n) ^ 2 := by
            have hmn2 : 2 * n ≤ m * n := Nat.mul_le_mul_right n hm
            nlinarith [sq_nonneg (m * n - n)]
          exact_mod_cast hle)
        tendsto_natCast_atTop_atTop
    apply hnat.congr'
    filter_upwards with n
    norm_num
  have hlow_tend : Filter.Tendsto (fun n : ℕ => K - 3 / ((m * n : ℕ) : ℝ) ^ 2) Filter.atTop (nhds K) := by
    have h3 : Filter.Tendsto (fun n : ℕ => (3 : ℝ) / ((m * n : ℕ) : ℝ) ^ 2) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hTsq_atTop
    simpa using (tendsto_const_nhds.sub h3)
  let hC1 : ℝ := 2 / (p : ℝ) + 2 / (q : ℝ) + 2 / (m : ℝ)
  let hC0 : ℝ := (q : ℝ) / (2 * (m : ℝ)) + (p : ℝ) / (2 * (m : ℝ)) +
    (p : ℝ) / (2 * (q : ℝ)) + 3
  have hupp_tend : Filter.Tendsto (fun n : ℕ => K + hC1 / ((m * n : ℕ) : ℝ) + hC0 / ((m * n : ℕ) : ℝ) ^ 2)
      Filter.atTop (nhds K) := by
    have h1 : Filter.Tendsto (fun n : ℕ => hC1 / ((m * n : ℕ) : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hT_atTop
    have h2 : Filter.Tendsto (fun n : ℕ => hC0 / ((m * n : ℕ) : ℝ) ^ 2) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hTsq_atTop
    simpa using ((tendsto_const_nhds.add h1).add h2)
  have hmain : Filter.Tendsto (fun n : ℕ => (coefFaces p q m n : ℝ) / ((m * n : ℕ) : ℝ) ^ 2)
      Filter.atTop (nhds K) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_tend hupp_tend
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hb := coefFaces_bounds p q m n (by omega : 0 < p) (by omega : 0 < q) hm hn
      have hT : ((m * n : ℕ) : ℝ) ≠ 0 := by positivity
      have hT2 : 0 < ((m * n : ℕ) : ℝ) ^ 2 := by positivity
      have hdiv := (div_le_div_iff_of_pos_right hT2).2 hb.1
      have hrhs : (K * ((m * n : ℕ) : ℝ) ^ 2 - 3) / ((m * n : ℕ) : ℝ) ^ 2 =
          K - 3 / ((m * n : ℕ) : ℝ) ^ 2 := by
        field_simp [hT]
      have hrhs : K - 3 / ((m * n : ℕ) : ℝ) ^ 2 =
          (K * ((m * n : ℕ) : ℝ) ^ 2 - 3) / ((m * n : ℕ) : ℝ) ^ 2 := by
        field_simp [hT]
      rw [hrhs]
      simpa [K] using hdiv
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hb := coefFaces_bounds p q m n (by omega : 0 < p) (by omega : 0 < q) hm hn
      have hT : ((m * n : ℕ) : ℝ) ≠ 0 := by positivity
      have hT2 : 0 < ((m * n : ℕ) : ℝ) ^ 2 := by positivity
      have hdiv := (div_le_div_iff_of_pos_right hT2).2 hb.2
      have hrhs : K + hC1 / ((m * n : ℕ) : ℝ) + hC0 / ((m * n : ℕ) : ℝ) ^ 2 =
          (K * ((m * n : ℕ) : ℝ) ^ 2 + hC1 * ((m * n : ℕ) : ℝ) + hC0) / ((m * n : ℕ) : ℝ) ^ 2 := by
        field_simp [hT]
      rw [hrhs]
      simpa [K, hC1, hC0] using hdiv
  have hconst : Filter.Tendsto (fun _ : ℕ => (2 * (p : ℝ) * (q : ℝ) * (m : ℝ)) / S)
      Filter.atTop (nhds ((2 * (p : ℝ) * (q : ℝ) * (m : ℝ)) / S)) := tendsto_const_nhds
  have hmul := hmain.mul hconst
  have hratio : Filter.Tendsto (fun n : ℕ => (coefFaces p q m n : ℝ) / cutArea p q m n)
      Filter.atTop (nhds (K * ((2 * (p : ℝ) * (q : ℝ) * (m : ℝ)) / S))) := by
    apply hmul.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hT : ((m * n : ℕ) : ℝ) ≠ 0 := by positivity
    unfold cutArea
    field_simp [hT, hSp.ne', hP.ne', hQ.ne', hM.ne']
    rw [show Real.sqrt ((q : ℝ) ^ 2 * ((p : ℝ) ^ 2 + (m : ℝ) ^ 2) + (p : ℝ) ^ 2 * (m : ℝ) ^ 2) = S by
      dsimp [S]; congr 1; ring]
    norm_num [Nat.cast_mul]
    ring
  have htarget : K * ((2 * (p : ℝ) * (q : ℝ) * (m : ℝ)) / S) =
      ((p : ℝ) + (q : ℝ) + (m : ℝ)) / S := by
    dsimp [K]
    field_simp [hSp.ne', hP.ne', hQ.ne', hM.ne']
  rw [← htarget]
  exact hratio

set_option maxHeartbeats 800000 in
theorem coefFaces_ratio_not_tendsto_one (p q m : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hm : 2 ≤ m)
    (hgt : 1 < ((p : ℝ) + (q : ℝ) + (m : ℝ)) /
      Real.sqrt ((p : ℝ)^2 * (q : ℝ)^2 + (q : ℝ)^2 * (m : ℝ)^2 + (m : ℝ)^2 * (p : ℝ)^2)) :
    ¬ Filter.Tendsto (fun n : ℕ => (coefFaces p q m n : ℝ) / cutArea p q m n)
        Filter.atTop (nhds 1) := by
  intro h
  have hlim := coefFaces_ratio_tendsto p q m hp hq hm
  have heq : (((p : ℝ) + (q : ℝ) + (m : ℝ)) /
      Real.sqrt ((p : ℝ)^2 * (q : ℝ)^2 + (q : ℝ)^2 * (m : ℝ)^2 + (m : ℝ)^2 * (p : ℝ)^2)) = 1 :=
    tendsto_nhds_unique hlim h
  linarith

end StaircasePlane3DCoeff

end Vdb
