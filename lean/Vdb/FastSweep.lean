/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Fast sweeping, abstractly: an Eikonal / fast-sweeping renormalisation is an
  iteration on a finite node set with a frozen boundary. Each step

    `d_{k+1} v = if frozen v then d_k v else min (d_k v) (relax d_k v)`

  lowers every non-frozen value toward the boundary (Godunov relaxation).
  This module proves the sweep-side invariants that hold for any relaxation
  operator satisfying the obvious local bounds:

  * `sweepStep_le` / `sweepIter_mono` — the iteration is pointwise
    non-increasing (T-FS-MONO);
  * `sweepIter_frozen` — frozen nodes never change (T-FS-FIX);
  * `sweepIter_lb` — a common lower bound is preserved (T-FS-SIGN: with the
    boundary non-negative and `relax` non-negative, the iterate is too);
  * `sweepIter_big_steps_card` — the number of iterations in which some node
    decreases by more than `tol > 0` is uniformly bounded by
    `(∑ v, (d₀ v - lb)) / tol`, so a `max_change ≤ tol` stopping rule fires
    after finitely many sweeps (T-FS-TERM).

  What is *not* proved here: convergence of the full 8-direction sweep order
  to the exact Godunov solution (that is the content of Zhao 2005 and needs
  the semi-discrete theory); and the settle-in-finitely-many-sweeps property
  with the Godunov Hamiltonian specifically. Those remain future work.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false

namespace Vdb

variable {ι : Type*} [Fintype ι]

/-- One sweep step with a frozen set: frozen nodes keep their value, others
    take the pointwise minimum with the relaxed update. -/
def sweepStep (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (d : ι → ℝ) : ι → ℝ :=
  fun v => if frozen v then d v else min (d v) (relax d v)

/-- The `k`-th iterate of the sweep. -/
def sweepIter (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (d : ι → ℝ) : ℕ → (ι → ℝ)
  | 0 => d
  | k + 1 => sweepStep frozen relax (sweepIter frozen relax d k)

theorem sweepIter_succ (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (d : ι → ℝ) (k : ℕ) :
    sweepIter frozen relax d (k + 1) = sweepStep frozen relax (sweepIter frozen relax d k) := rfl

/-- Non-frozen nodes take the pointwise min with the relaxation. -/
theorem sweepStep_le (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (d : ι → ℝ) (v : ι) :
    sweepStep frozen relax d v ≤ d v := by
  unfold sweepStep
  split_ifs with h
  · exact le_refl _
  · exact min_le_left _ _

/-- **T-FS-MONO**: the iteration is non-increasing in the step index. -/
theorem sweepIter_mono (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (d : ι → ℝ) :
    ∀ k v, sweepIter frozen relax d (k + 1) v ≤ sweepIter frozen relax d k v := by
  intro k v
  rw [sweepIter_succ]
  exact sweepStep_le frozen relax (sweepIter frozen relax d k) v

/-- Pointwise non-increasing along the iteration. -/
theorem sweepIter_mono' (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (d : ι → ℝ) :
    ∀ k j, k ≤ j → ∀ v, sweepIter frozen relax d j v ≤ sweepIter frozen relax d k v := by
  intro k j hkj
  induction j with
  | zero =>
    intro v
    rw [show k = 0 from Nat.le_zero.mp hkj]
  | succ j ih =>
    intro v
    by_cases hkj : k ≤ j
    · exact le_trans (sweepStep_le frozen relax _ v) (ih hkj v)
    · have hk : k = j + 1 := by omega
      rw [hk]

/-- **T-FS-FIX**: frozen nodes never change. -/
theorem sweepIter_frozen (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (d : ι → ℝ) :
    ∀ k v, frozen v = true → sweepIter frozen relax d k v = d v := by
  intro k
  induction k with
  | zero => intro v _; rfl
  | succ k ih =>
    intro v hv
    rw [sweepIter_succ, sweepStep]
    split_ifs
    · exact ih v hv

/-- **T-FS-SIGN**: a lower bound on the initial data is preserved, as long as
    the relaxation respects it. -/
theorem sweepIter_lb (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (lb : ℝ) (d : ι → ℝ)
    (hrelax : ∀ (e : ι → ℝ) v, (∀ w, lb ≤ e w) → lb ≤ relax e v)
    (hd : ∀ v, lb ≤ d v) :
    ∀ k v, lb ≤ sweepIter frozen relax d k v := by
  intro k
  induction k with
  | zero => intro v; exact hd v
  | succ k ih =>
    intro v
    unfold sweepIter sweepStep
    split_ifs with h
    · exact ih v
    · rw [le_min_iff]
      exact ⟨ih v, hrelax _ v ih⟩

/-- The "drop" of the iterate from the initial state, summed over all nodes. -/
def sweepDrop (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (d : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ v : ι, (d v - sweepIter frozen relax d k v)

/-- The drop measure is non-decreasing in the step index. -/
theorem sweepDrop_mono (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (d : ι → ℝ) :
    ∀ k j, k ≤ j → sweepDrop frozen relax d k ≤ sweepDrop frozen relax d j := by
  intro k j hkj
  unfold sweepDrop
  apply Finset.sum_le_sum
  intro v _
  have hmono := sweepIter_mono' frozen relax d k j hkj v
  linarith

/-- One node that decreases by more than `tol` contributes more than `tol`
    to the drop. -/
theorem sweepDrop_gap (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (d : ι → ℝ) (k : ℕ)
    (v : ι) (htol : sweepIter frozen relax d k v - sweepIter frozen relax d (k + 1) v > tol) :
    sweepDrop frozen relax d (k + 1) - sweepDrop frozen relax d k > tol := by
  unfold sweepDrop
  have hsum : ∑ v' : ι, (sweepIter frozen relax d k v' - sweepIter frozen relax d (k + 1) v') >
      tol := by
    -- isolate the v contribution; all terms are non-negative
    have hnn : ∀ v' ∈ Finset.univ, (0:ℝ) ≤ sweepIter frozen relax d k v' - sweepIter frozen relax d (k + 1) v' := by
      intro v' _
      exact sub_nonneg.mpr (sweepIter_mono frozen relax d k v')
    -- the sum is at least the single term at v
    have hle := Finset.single_le_sum hnn (Finset.mem_univ v)
    linarith [hle, htol]
  have hdist : ∑ v : ι, (d v - sweepIter frozen relax d (k + 1) v) -
      ∑ v : ι, (d v - sweepIter frozen relax d k v) =
      ∑ v : ι, (sweepIter frozen relax d k v - sweepIter frozen relax d (k + 1) v) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    ring
  linarith [hdist, hsum]

/-- **T-FS-TERM** (quantitative): at most `(∑ v, (d₀ v − lb)) / tol` sweeps
    can decrease some node by more than `tol > 0`. The iteration is
    non-increasing and bounded below by `lb`, so a `max_change ≤ tol`
    stopping rule fires after finitely many sweeps. -/
theorem sweepIter_big_steps_card (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ)
    (lb : ℝ) (d : ι → ℝ) (tol : ℝ) (ht : 0 < tol)
    (hlb : ∀ k v, lb ≤ sweepIter frozen relax d k v) (N : ℕ) :
    ((Finset.range N).filter fun k =>
      ∃ v, sweepIter frozen relax d k v - sweepIter frozen relax d (k + 1) v > tol).card ≤
      (∑ v : ι, (d v - lb)) / tol := by
  set B := (Finset.range N).filter fun k =>
    ∃ v, sweepIter frozen relax d k v - sweepIter frozen relax d (k + 1) v > tol with hB
  have hgap : ∀ k ∈ B, sweepDrop frozen relax d (k + 1) - sweepDrop frozen relax d k ≥ tol := by
    intro k hk
    rw [hB] at hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨_, v, hv⟩ := hk
    exact (sweepDrop_gap frozen relax d k v (by linarith [hv])).le
  have hsub : B ⊆ Finset.range N := Finset.filter_subset _ _
  have hle : ∑ k ∈ B, (sweepDrop frozen relax d (k + 1) - sweepDrop frozen relax d k) ≤
      ∑ k ∈ Finset.range N, (sweepDrop frozen relax d (k + 1) - sweepDrop frozen relax d k) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro k _ _
    exact sub_nonneg.mpr (sweepDrop_mono frozen relax d k (k + 1) (Nat.le_succ k))
  have hsum_range : ∀ n,
      ∑ k ∈ Finset.range n, (sweepDrop frozen relax d (k + 1) - sweepDrop frozen relax d k) =
        sweepDrop frozen relax d n := by
    intro n
    induction n with
    | zero => simp [sweepDrop, sweepIter]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have hdropN : sweepDrop frozen relax d N ≤ ∑ v : ι, (d v - lb) := by
    unfold sweepDrop
    apply Finset.sum_le_sum
    intro v _
    have := hlb N v
    linarith
  have hgapsum : B.card * tol ≤ ∑ k ∈ B,
      (sweepDrop frozen relax d (k + 1) - sweepDrop frozen relax d k) := by
    have h1 : ∑ k ∈ B, tol ≤ ∑ k ∈ B, (sweepDrop frozen relax d (k + 1) - sweepDrop frozen relax d k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hgap k hk
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    linarith [h1]
  rw [le_div_iff₀ ht]
  rw [hsum_range] at hle
  linarith [hle, hdropN, hgapsum]

end Vdb
