/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Zhao-tier wall group (§4.0): the maximum-propagation lemma for the 1-D
  Eikonal relaxation. If `u` is a subsolution, `v` a supersolution, and
  `u − v` attains a positive maximum at an interior voxel, then at least one
  neighbour attains the same maximum. Combined with `DiscreteComparison`, this
  is the remaining structural step before 1-D convergence; the rank-decrease
  form needed by the generic theorem is still open.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.DiscreteComparison

set_option linter.unusedSectionVars false

namespace Vdb

theorem eikonal_max_step {n : ℕ} (u v : Fin (n + 2) → ℝ) (h : ℝ)
    (i : Fin (n + 2)) (hiN : i.val ≠ n + 1)
    (hsub : u i ≤ min (u ⟨i.val - 1, by omega⟩) (u ⟨i.val + 1, by omega⟩) + h)
    (hsup : min (v ⟨i.val - 1, by omega⟩) (v ⟨i.val + 1, by omega⟩) + h ≤ v i)
    (hmax : ∀ j, u j - v j ≤ u i - v i) :
    u ⟨i.val - 1, by omega⟩ - v ⟨i.val - 1, by omega⟩ = u i - v i ∨
      u ⟨i.val + 1, by omega⟩ - v ⟨i.val + 1, by omega⟩ = u i - v i := by
  let il : Fin (n + 2) := ⟨i.val - 1, by omega⟩
  let ir : Fin (n + 2) := ⟨i.val + 1, by omega⟩
  by_contra hnot
  push Not at hnot
  have hwl : u il - v il < u i - v i := lt_of_le_of_ne (hmax il) hnot.1
  have hwr : u ir - v ir < u i - v i := lt_of_le_of_ne (hmax ir) hnot.2
  have hminlt : min (u il) (u ir) < min (v il) (v ir) + (u i - v i) := by
    by_cases hv : v il ≤ v ir
    · have hmin : min (v il) (v ir) = v il := min_eq_left hv
      have hule : min (u il) (u ir) ≤ u il := min_le_left _ _
      linarith
    · have hv' : v ir ≤ v il := le_of_not_ge hv
      have hmin : min (v il) (v ir) = v ir := min_eq_right hv'
      have hule : min (u il) (u ir) ≤ u ir := min_le_right _ _
      linarith
  have : u i - v i < u i - v i := by
    have h1 := hsub
    have h2 := hsup
    linarith
  exact (lt_irrefl _ this)

end Vdb
