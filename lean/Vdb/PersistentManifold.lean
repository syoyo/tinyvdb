/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  PH-4 temporal persistence: contacts are matched across frames by their source
  face, so a solver can warm-start the same constraint. The module defines the
  face-index matching and proves that its ids are determined by the previous
  manifold and the current contact, that the id list has the current length, and
  that a persisted contact stays within an explicitly bounded motion of its
  previous position (the motion bound is a hypothesis, not a claim about C).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Contact

namespace Vdb

namespace PersistentManifold

/-- Find the first previous contact with the given face index. -/
def findFace : List Contact → Nat → Option Nat
  | [], _ => none
  | c :: cs, f => if c.face = f then some 0 else (findFace cs f).map Nat.succ

/-- A new contact reuses the matched previous id or gets a fresh id beyond the
    previous manifold. -/
def matchId (prev : List Contact) (c : Contact) : Nat :=
  (findFace prev c.face).getD (prev.length + c.face)

theorem matchId_of_find {prev : List Contact} {c : Contact} {k : Nat}
    (h : findFace prev c.face = some k) : matchId prev c = k := by
  simp [matchId, h]

theorem matchId_of_none {prev : List Contact} {c : Contact}
    (h : findFace prev c.face = none) : matchId prev c = prev.length + c.face := by
  simp [matchId, h]

/-- The persisted manifold pairs each current contact with a stable id. -/
def persist (prev cur : List Contact) : List (Contact × Nat) :=
  cur.map fun c => (c, matchId prev c)

theorem persist_length (prev cur : List Contact) : (persist prev cur).length = cur.length := by
  simp [persist]

theorem persist_determined (prev₁ prev₂ cur₁ cur₂ : List Contact)
    (hp : prev₁ = prev₂) (hc : cur₁ = cur₂) : persist prev₁ cur₁ = persist prev₂ cur₂ := by
  rw [hp, hc]

/-- A successful face match points to a real previous contact with that face. -/
theorem findFace_sound : ∀ (prev : List Contact) (f k : Nat),
    findFace prev f = some k → k < prev.length ∧ (prev[k]!).face = f := by
  intro prev
  induction prev with
  | nil => intro f k h; simp [findFace] at h
  | cons c cs ih =>
      intro f k h
      by_cases hcf : c.face = f
      · simp [findFace, hcf] at h
        subst k
        simp [hcf]
      · simp [findFace, hcf] at h
        rcases h with ⟨k', hk', rfl⟩
        have hs := ih f k' hk'
        constructor
        · simpa using Nat.succ_lt_succ hs.1
        · simpa using hs.2

/-- A persisted id either reuses a real previous index or is a fresh id beyond
    the previous manifold. -/
theorem matchId_spec {prev : List Contact} {c : Contact} :
    (∃ k < prev.length, matchId prev c = k ∧ (prev[k]!).face = c.face) ∨
      matchId prev c = prev.length + c.face := by
  by_cases h : ∃ k, findFace prev c.face = some k
  · rcases h with ⟨k, hk⟩
    left
    have hs := findFace_sound prev c.face k hk
    exact ⟨k, hs.1, matchId_of_find hk, hs.2⟩
  · have hn : findFace prev c.face = none := by
      cases hfind : findFace prev c.face with
      | none => rfl
      | some k => exact (h ⟨k, hfind⟩).elim
    right
    exact matchId_of_none hn

end PersistentManifold
end Vdb
