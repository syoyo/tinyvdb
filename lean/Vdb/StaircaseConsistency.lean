/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  General staircase-consistency wall group (§4.0). Defines consistency of a
  staircase face-count estimator against a surface-area family, and transfers
  the landed coefficient-plane limit theorem into an inconsistency theorem for
  every positive integer plane family whose limit factor exceeds one. A bounded
  exact-integer check shows no ratio-1 triples in a small range; the full
  classification of exceptional triples remains open.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.StaircasePlane3DCoeff

set_option linter.unusedSectionVars false

namespace Vdb

/-- A face-count estimator is consistent with an area family when their ratio
    tends to one as the refinement parameter grows. -/
def Consistent (faces : ℕ → ℕ) (area : ℕ → ℝ) : Prop :=
  Filter.Tendsto (fun n : ℕ => (faces n : ℝ) / area n) Filter.atTop (nhds 1)

theorem coef_estimator_inconsistent (p q m : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hm : 2 ≤ m)
    (hgt : 1 < ((p : ℝ) + (q : ℝ) + (m : ℝ)) /
      Real.sqrt ((p : ℝ)^2 * (q : ℝ)^2 + (q : ℝ)^2 * (m : ℝ)^2 + (m : ℝ)^2 * (p : ℝ)^2)) :
    ¬ Consistent (fun n => StaircasePlane3DCoeff.coefFaces p q m n) (fun n => StaircasePlane3DCoeff.cutArea p q m n) := by
  exact StaircasePlane3DCoeff.coefFaces_ratio_not_tendsto_one p q m hp hq hm hgt

/-- Exact integer test for a unit limiting ratio: (p+q+m)² = the squared
    denominator. Checked over the bounded range 1..12. -/
def ratioOneSquared (p q m : Nat) : Bool :=
  (p + q + m)^2 == p^2*q^2 + q^2*m^2 + m^2*p^2

def noSmallRatioOne : Bool :=
  (List.range 12).all fun pi =>
    (List.range 12).all fun qi =>
      (List.range 12).all fun mi =>
        let p := pi + 1
        let q := qi + 1
        let m := mi + 1
        !ratioOneSquared p q m

theorem noSmallRatioOne_true : noSmallRatioOne = true := by
  native_decide

theorem ratio_not_one_of_small {p q m : Nat} (hp : p ≤ 12) (hq : q ≤ 12) (hm : m ≤ 12)
    (hp0 : 0 < p) (hq0 : 0 < q) (hm0 : 0 < m) : ratioOneSquared p q m = false := by
  have hpbound : p - 1 < 12 := by
    have h := Nat.sub_le_sub_right hp 1
    omega
  have hqbound : q - 1 < 12 := by
    have h := Nat.sub_le_sub_right hq 1
    omega
  have hmbound : m - 1 < 12 := by
    have h := Nat.sub_le_sub_right hm 1
    omega
  have houter := List.all_eq_true.mp noSmallRatioOne_true (p - 1) (List.mem_range.mpr hpbound)
  have hsecond := List.all_eq_true.mp houter (q - 1) (List.mem_range.mpr hqbound)
  have hthird := List.all_eq_true.mp hsecond (m - 1) (List.mem_range.mpr hmbound)
  simpa [ratioOneSquared, Nat.sub_add_cancel hp0, Nat.sub_add_cancel hq0,
    Nat.sub_add_cancel hm0] using hthird

end Vdb
