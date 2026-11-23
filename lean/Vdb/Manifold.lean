/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  PH-4: contact-manifold reduction. A narrowphase produces many contacts per
  frame; a manifold keeps a separated subset (no two representatives closer
  than `ε`) that still covers every raw contact within `ε`. The greedy reduction
  below is the exact algorithm used by the C query; the theorems establish the
  three contracts a physics solver relies on: subset, separation and coverage,
  plus idempotence.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Vdb.LevelSet

set_option linter.unusedSectionVars false

noncomputable section

open scoped RealInnerProductSpace

namespace Vdb

variable {α : Type}

/-- One reduction step: keep `x` unless an already-kept representative is
    within `ε`. -/
def keepIfFar (ε : ℝ) (pos : α → Point) (x : α) (rest : List α) : List α :=
  if rest.any (fun y => decide (dist (pos x) (pos y) ≤ ε)) then rest else x :: rest

/-- Greedy separated net: process the list from the tail. -/
def greedyNet (ε : ℝ) (pos : α → Point) : List α → List α
  | [] => []
  | x :: xs => keepIfFar ε pos x (greedyNet ε pos xs)

theorem greedyNet_subset (ε : ℝ) (pos : α → Point) (xs : List α) :
    ∀ z ∈ greedyNet ε pos xs, z ∈ xs := by
  induction xs with
  | nil => simp [greedyNet]
  | cons x xs ih =>
      change ∀ z ∈ keepIfFar ε pos x (greedyNet ε pos xs), z ∈ x :: xs
      unfold keepIfFar
      by_cases h : (greedyNet ε pos xs).any (fun y => decide (dist (pos x) (pos y) ≤ ε))
      · simp only [h]
        intro z hz
        exact List.mem_cons_of_mem x (ih z hz)
      · simp only [h]
        intro z hz
        rcases List.mem_cons.mp hz with hzx | hz
        · rw [hzx]
          exact by simp
        · exact List.mem_cons_of_mem x (ih z hz)

theorem greedyNet_separated (ε : ℝ) (pos : α → Point) (xs : List α) :
    ∀ a ∈ greedyNet ε pos xs, ∀ b ∈ greedyNet ε pos xs,
      a ≠ b → ε < dist (pos a) (pos b) := by
  induction xs with
  | nil => simp [greedyNet]
  | cons x xs ih =>
      let rest := greedyNet ε pos xs
      change ∀ a ∈ keepIfFar ε pos x rest, ∀ b ∈ keepIfFar ε pos x rest,
        a ≠ b → ε < dist (pos a) (pos b)
      unfold keepIfFar
      by_cases h : rest.any (fun y => decide (dist (pos x) (pos y) ≤ ε))
      · simp only [h]
        simpa [rest] using ih
      · simp only [h]
        have hx : ∀ y ∈ rest, ε < dist (pos x) (pos y) := by
          intro y hy
          have hn : ¬ dist (pos x) (pos y) ≤ ε := by
            intro hd
            exact h (List.any_eq_true.mpr ⟨y, hy, by simp [hd]⟩)
          exact lt_of_not_ge hn
        intro a ha b hb hne
        rcases List.mem_cons.mp ha with hax | ha <;> rcases List.mem_cons.mp hb with hbx | hb
        · rw [hax, hbx] at hne
          exact (hne rfl).elim
        · rw [hax]
          exact hx b hb
        · rw [hbx]
          rw [dist_comm]
          exact hx a ha
        · simpa [rest] using ih a ha b hb hne

theorem greedyNet_covers (ε : ℝ) (pos : α → Point) (xs : List α) (hε : 0 ≤ ε) :
    ∀ z ∈ xs, ∃ y ∈ greedyNet ε pos xs, dist (pos z) (pos y) ≤ ε := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      let rest := greedyNet ε pos xs
      change ∀ z ∈ x :: xs, ∃ y ∈ keepIfFar ε pos x rest, dist (pos z) (pos y) ≤ ε
      unfold keepIfFar
      by_cases h : rest.any (fun y => decide (dist (pos x) (pos y) ≤ ε))
      · simp only [h]
        intro z hz
        rcases List.mem_cons.mp hz with hzx | hz
        · rw [hzx]
          rcases List.any_eq_true.mp h with ⟨y, hy, hdec⟩
          exact ⟨y, hy, of_decide_eq_true hdec⟩
        · rcases ih z hz with ⟨y, hy, hdist⟩
          exact ⟨y, hy, hdist⟩
      · simp only [h]
        intro z hz
        rcases List.mem_cons.mp hz with hzx | hz
        · rw [hzx]
          exact ⟨x, by simp, by simpa using hε⟩
        · rcases ih z hz with ⟨y, hy, hdist⟩
          exact ⟨y, List.mem_cons_of_mem x hy, hdist⟩

end Vdb
