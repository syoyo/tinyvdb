/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Zhao-tier wall group (§4.0): the structural comparison principle behind
  fast-sweeping convergence. On a finite graph with a rank function decreasing
  toward the frozen boundary, if a strict positive maximum of `u − v` must have
  a neighbour at the same maximum with smaller rank, then no such maximum can
  exist and `u ≤ v` everywhere. The Eikonal-specific maximum propagation is
  left as an explicit premise; the graph/rank argument is proved here.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

namespace Vdb

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The structural comparison principle: a positive maximum of `u − v` cannot
    persist down a rank-decreasing chain ending at a frozen node. -/
theorem comparison_of_rank_step (u v : ι → ℝ) (rank : ι → ℕ)
    (adj : ι → ι → Prop) (F : ι → Prop)
    (hboundary : ∀ i, rank i = 0 → F i)
    (hstep : ∀ (M : ℝ) (i : ι), M = u i - v i → 0 < M → rank i ≠ 0 →
      ∃ j, adj i j ∧ M = u j - v j ∧ rank j < rank i)
    (hfrozen : ∀ i, F i → u i ≤ v i) :
    ∀ i, u i ≤ v i := by
  intro i
  by_contra hnot
  have hpos : 0 < u i - v i := sub_pos.mpr (lt_of_not_ge hnot)
  let S : Finset ℝ := Finset.univ.image (fun j => u j - v j)
  have hSne : S.Nonempty := ⟨u i - v i, by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  let M : ℝ := S.max' hSne
  have hM_ge : u i - v i ≤ M := by
    exact Finset.le_max' S (u i - v i)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hMpos : 0 < M := lt_of_lt_of_le hpos hM_ge
  have hex : ∃ j, M = u j - v j := by
    have hmem : M ∈ S := by dsimp [M]; exact Finset.max'_mem S hSne
    rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
    exact ⟨j, hj.symm⟩
  rcases hex with ⟨j0, hj0⟩
  -- Descend along rank from a maximum node.
  let P : Nat → Prop := fun n => ∀ j, M = u j - v j → rank j = n → False
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
        intro j hj hjn
        by_cases hz : rank j = 0
        · have hFj := hboundary j hz
          have hle := hfrozen j hFj
          have : 0 < u j - v j := by rw [← hj]; exact hMpos
          exact (not_lt_of_ge hle) (sub_pos.mp this)
        · rcases hstep M j hj hMpos hz with ⟨k, hadj, hk, hkrank⟩
          have hkrank' : rank k < n := by simpa [hjn] using hkrank
          exact ih (rank k) hkrank' k hk rfl
  exact hP (rank j0) j0 hj0 rfl

end Vdb
