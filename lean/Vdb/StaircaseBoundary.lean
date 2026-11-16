/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  General-set statements about the `staircaseFaces` estimator
  (`Vdb/FloodFill.lean`): the count of distinct exterior voxels adjacent
  to the interior fill (the union over interior voxels of the exterior
  6-adjacent cells). The octahedron-family overshoot analysis
  (`Vdb/StaircaseRatio.lean`, `Vdb/StaircaseClosed.lean`) is a concrete
  family; this module proves what holds for **every** sign field / seed
  set:

  * **grid connectedness**: any two voxels of the `nx × ny × nz` box are
    connected by an `adj6` (von Neumann) path (`adj6_connected`);
  * **boundary exit**: a nonempty adjacency-closed subset of the box
    that is not everything has an edge from the subset to its
    complement (`adj6_path_exit`);
  * **`staircaseFaces_eq_zero_iff`**: the estimator vanishes exactly
    for the degenerate fills — empty or full box;
  * **`staircaseFaces_le_exterior`**: the estimator is bounded by the
    number of exterior voxels (and `staircaseFaces_le_min` with the
    `6 · #interior` bound);
  * **`staircaseFaces_six`**: the `6 · #interior` bound is attained
    (a single isolated far voxel with empty seeds has six exposed
    faces);
  * `mem_biUnion` (membership form) — a bookkeeping lemma.

  What is **not** proved: consistency of the estimator with any surface
  area (the octahedron evidence remains the standing counterexample),
  additivity over interior components (it fails: two interior components
  sharing an exterior cell are counted once), and monotonicity in the
  seed set (also false). The ledger tracks what remains open.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.FloodFill

set_option linter.unusedSimpArgs false

namespace Vdb

namespace StaircaseBoundary

/-! ### Grid paths: monotone steps along one axis, both directions -/

/-- An `x`-path from `⟨a, ha⟩` to `⟨b, hb⟩`, stepping toward `b`. -/
theorem adj6_step_x {nx ny nz : ℕ} (y : Fin ny) (z : Fin nz) {a b : ℕ}
    (ha : a < nx) (hb : b < nx) (h : a ≤ b) :
    Relation.ReflTransGen adj6 ((⟨a, ha⟩, y, z) : GPoint nx ny nz) (⟨b, hb⟩, y, z) := by
  suffices key : ∀ (d : ℕ) (a : ℕ) (ha : a < nx), b - a = d → a ≤ b →
      Relation.ReflTransGen adj6 ((⟨a, ha⟩, y, z) : GPoint nx ny nz) (⟨b, hb⟩, y, z) from
    key (b - a) a ha rfl h
  intro d
  induction d with
  | zero =>
    intro a ha heq _
    have h' : a = b := by omega
    subst h'
    exact Relation.ReflTransGen.refl
  | succ d ih =>
    intro a ha heq _
    have ha1 : a + 1 < nx := by omega
    have hadj : adj6 ((⟨a, ha⟩, y, z) : GPoint nx ny nz) (⟨a + 1, ha1⟩, y, z) := by
      refine Or.inl ⟨by simp, rfl, rfl⟩
    exact (Relation.ReflTransGen.single hadj).trans (ih (a + 1) (by omega) (by omega) (by omega))

/-- An `x`-path from `⟨a, ha⟩` down to `⟨b, hb⟩`, `b ≤ a`. -/
theorem adj6_step_x' {nx ny nz : ℕ} (y : Fin ny) (z : Fin nz) {a b : ℕ}
    (ha : a < nx) (hb : b < nx) (h : b ≤ a) :
    Relation.ReflTransGen adj6 ((⟨a, ha⟩, y, z) : GPoint nx ny nz) (⟨b, hb⟩, y, z) := by
  suffices key : ∀ (d : ℕ) (a : ℕ) (ha : a < nx), a - b = d → b ≤ a →
      Relation.ReflTransGen adj6 ((⟨a, ha⟩, y, z) : GPoint nx ny nz) (⟨b, hb⟩, y, z) from
    key (a - b) a ha rfl h
  intro d
  induction d with
  | zero =>
    intro a ha heq _
    have h' : a = b := by omega
    subst h'
    exact Relation.ReflTransGen.refl
  | succ d ih =>
    intro a ha heq _
    have ha1' : a - 1 < nx := by omega
    have hadj : adj6 ((⟨a, ha⟩, y, z) : GPoint nx ny nz) (⟨a - 1, ha1'⟩, y, z) := by
      refine Or.inr (Or.inl ⟨by simp; omega, rfl, rfl⟩)
    exact (Relation.ReflTransGen.single hadj).trans (ih (a - 1) (by omega) (by omega) (by omega))

/-- A `y`-path from `⟨a, ha⟩` to `⟨b, hb⟩`, `a ≤ b`. -/
theorem adj6_step_y {nx ny nz : ℕ} (x : Fin nx) (z : Fin nz) {a b : ℕ}
    (ha : a < ny) (hb : b < ny) (h : a ≤ b) :
    Relation.ReflTransGen adj6 ((x, (⟨a, ha⟩, z)) : GPoint nx ny nz) (x, (⟨b, hb⟩, z)) := by
  suffices key : ∀ (d : ℕ) (a : ℕ) (ha : a < ny), b - a = d → a ≤ b →
      Relation.ReflTransGen adj6 ((x, (⟨a, ha⟩, z)) : GPoint nx ny nz) (x, (⟨b, hb⟩, z)) from
    key (b - a) a ha rfl h
  intro d
  induction d with
  | zero =>
    intro a ha heq _
    have h' : a = b := by omega
    subst h'
    exact Relation.ReflTransGen.refl
  | succ d ih =>
    intro a ha heq _
    have ha1 : a + 1 < ny := by omega
    have hadj : adj6 ((x, (⟨a, ha⟩, z)) : GPoint nx ny nz) (x, (⟨a + 1, ha1⟩, z)) := by
      refine Or.inr (Or.inr (Or.inl ⟨rfl, by simp, rfl⟩))
    exact (Relation.ReflTransGen.single hadj).trans (ih (a + 1) (by omega) (by omega) (by omega))

/-- A `y`-path from `⟨a, ha⟩` down to `⟨b, hb⟩`, `b ≤ a`. -/
theorem adj6_step_y' {nx ny nz : ℕ} (x : Fin nx) (z : Fin nz) {a b : ℕ}
    (ha : a < ny) (hb : b < ny) (h : b ≤ a) :
    Relation.ReflTransGen adj6 ((x, (⟨a, ha⟩, z)) : GPoint nx ny nz) (x, (⟨b, hb⟩, z)) := by
  suffices key : ∀ (d : ℕ) (a : ℕ) (ha : a < ny), a - b = d → b ≤ a →
      Relation.ReflTransGen adj6 ((x, (⟨a, ha⟩, z)) : GPoint nx ny nz) (x, (⟨b, hb⟩, z)) from
    key (a - b) a ha rfl h
  intro d
  induction d with
  | zero =>
    intro a ha heq _
    have h' : a = b := by omega
    subst h'
    exact Relation.ReflTransGen.refl
  | succ d ih =>
    intro a ha heq _
    have ha1' : a - 1 < ny := by omega
    have hadj : adj6 ((x, (⟨a, ha⟩, z)) : GPoint nx ny nz) (x, (⟨a - 1, ha1'⟩, z)) := by
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by simp; omega, rfl⟩)))
    exact (Relation.ReflTransGen.single hadj).trans (ih (a - 1) (by omega) (by omega) (by omega))

/-- A `z`-path from `⟨a, ha⟩` to `⟨b, hb⟩`, `a ≤ b`. -/
theorem adj6_step_z {nx ny nz : ℕ} (x : Fin nx) (y : Fin ny) {a b : ℕ}
    (ha : a < nz) (hb : b < nz) (h : a ≤ b) :
    Relation.ReflTransGen adj6 ((x, (y, ⟨a, ha⟩)) : GPoint nx ny nz) (x, (y, ⟨b, hb⟩)) := by
  suffices key : ∀ (d : ℕ) (a : ℕ) (ha : a < nz), b - a = d → a ≤ b →
      Relation.ReflTransGen adj6 ((x, (y, ⟨a, ha⟩)) : GPoint nx ny nz) (x, (y, ⟨b, hb⟩)) from
    key (b - a) a ha rfl h
  intro d
  induction d with
  | zero =>
    intro a ha heq _
    have h' : a = b := by omega
    subst h'
    exact Relation.ReflTransGen.refl
  | succ d ih =>
    intro a ha heq _
    have ha1 : a + 1 < nz := by omega
    have hadj : adj6 ((x, (y, ⟨a, ha⟩)) : GPoint nx ny nz) (x, (y, ⟨a + 1, ha1⟩)) := by
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by simp⟩))))
    exact (Relation.ReflTransGen.single hadj).trans (ih (a + 1) (by omega) (by omega) (by omega))

/-- A `z`-path from `⟨a, ha⟩` down to `⟨b, hb⟩`, `b ≤ a`. -/
theorem adj6_step_z' {nx ny nz : ℕ} (x : Fin nx) (y : Fin ny) {a b : ℕ}
    (ha : a < nz) (hb : b < nz) (h : b ≤ a) :
    Relation.ReflTransGen adj6 ((x, (y, ⟨a, ha⟩)) : GPoint nx ny nz) (x, (y, ⟨b, hb⟩)) := by
  suffices key : ∀ (d : ℕ) (a : ℕ) (ha : a < nz), a - b = d → b ≤ a →
      Relation.ReflTransGen adj6 ((x, (y, ⟨a, ha⟩)) : GPoint nx ny nz) (x, (y, ⟨b, hb⟩)) from
    key (a - b) a ha rfl h
  intro d
  induction d with
  | zero =>
    intro a ha heq _
    have h' : a = b := by omega
    subst h'
    exact Relation.ReflTransGen.refl
  | succ d ih =>
    intro a ha heq _
    have ha1' : a - 1 < nz := by omega
    have hadj : adj6 ((x, (y, ⟨a, ha⟩)) : GPoint nx ny nz) (x, (y, ⟨a - 1, ha1'⟩)) := by
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, by simp; omega⟩))))
    exact (Relation.ReflTransGen.single hadj).trans (ih (a - 1) (by omega) (by omega) (by omega))

/-- **Grid connectedness**: any two voxels of the box are connected by an
    `adj6` path (x first, then y, then z). -/
theorem adj6_connected {nx ny nz : ℕ} (p q : GPoint nx ny nz) :
    Relation.ReflTransGen adj6 p q := by
  obtain ⟨px, py, pz⟩ := p
  obtain ⟨qx, qy, qz⟩ := q
  have hxy : Relation.ReflTransGen adj6 ((px, py, pz) : GPoint nx ny nz) ((qx, py, pz) : GPoint nx ny nz) := by
    rcases Nat.le_or_le px.val qx.val with h | h
    · exact adj6_step_x py pz px.isLt qx.isLt h
    · exact adj6_step_x' py pz px.isLt qx.isLt h
  have hyz : Relation.ReflTransGen adj6 ((qx, py, pz) : GPoint nx ny nz) ((qx, qy, pz) : GPoint nx ny nz) := by
    rcases Nat.le_or_le py.val qy.val with h | h
    · exact adj6_step_y qx pz py.isLt qy.isLt h
    · exact adj6_step_y' qx pz py.isLt qy.isLt h
  have hzq : Relation.ReflTransGen adj6 ((qx, qy, pz) : GPoint nx ny nz) ((qx, qy, qz) : GPoint nx ny nz) := by
    rcases Nat.le_or_le pz.val qz.val with h | h
    · exact adj6_step_z qx qy pz.isLt qz.isLt h
    · exact adj6_step_z' qx qy pz.isLt qz.isLt h
  exact hxy.trans (hyz.trans hzq)

/-! ### Boundary exit: adjacency-closed non-trivial sets have a boundary edge -/

/-- If `S` is closed under `adj6`, nonempty and not everything, then there is a
    point of `S` adjacent to a point outside `S`. -/
theorem adj6_path_exit {S : Finset (GPoint nx ny nz)}
    {a b : GPoint nx ny nz} (hpath : Relation.ReflTransGen adj6 a b) :
    a ∈ S → b ∉ S → ∃ p' ∈ S, ∃ q' ∉ S, adj6 p' q' := by
  induction hpath with
  | refl => intro ha hb; exact absurd ha hb
  | tail hab hbc ih =>
    intro ha hb
    rename_i m b'
    by_cases hx : m ∈ S
    · exact ⟨m, hx, b', hb, hbc⟩
    · exact ih ha hx

/-- The membership form of `staircaseFaces`'s bi-union: `q` is an exposed
    voxel iff `q` is outside the interior and has an interior neighbour. -/
theorem mem_biUnion {nx ny nz : ℕ} {far : GPoint nx ny nz → Bool}
    {seeds : Finset (GPoint nx ny nz)} {q : GPoint nx ny nz} :
    q ∈ (interior far seeds).biUnion (fun p =>
        (Finset.univ : Finset (GPoint nx ny nz)).filter fun q =>
          adj6 p q ∧ q ∉ interior far seeds)
      ↔ q ∉ interior far seeds ∧ ∃ p ∈ interior far seeds, adj6 p q := by
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, hadj, hq⟩
    exact ⟨hq, p, hp, hadj⟩
  · rintro ⟨hq, p, hp, hadj⟩
    exact ⟨p, hp, hadj, hq⟩

/-- The bi-union of exposed voxels is empty iff the interior is empty or is
    everything. -/
theorem biUnion_eq_empty_iff {nx ny nz : ℕ} {far : GPoint nx ny nz → Bool}
    {seeds : Finset (GPoint nx ny nz)} :
    (interior far seeds).biUnion (fun p =>
        (Finset.univ : Finset (GPoint nx ny nz)).filter fun q =>
          adj6 p q ∧ q ∉ interior far seeds) = ∅
      ↔ interior far seeds = ∅ ∨ interior far seeds = Finset.univ := by
  constructor
  · intro h
    by_cases hempty : interior far seeds = ∅
    · exact Or.inl hempty
    · refine Or.inr ?_
      rw [Finset.eq_univ_iff_forall]
      intro t
      have hSc : ∀ p ∈ interior far seeds, ∀ q, adj6 p q → q ∈ interior far seeds := by
        intro p hp q hadj
        by_contra hqnot
        have hq : q ∈ (interior far seeds).biUnion (fun p =>
            (Finset.univ : Finset (GPoint nx ny nz)).filter fun q =>
              adj6 p q ∧ q ∉ interior far seeds) :=
          Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hadj, hqnot⟩⟩
        rw [h] at hq
        simp at hq
      obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      by_contra ht
      obtain ⟨p', hp', q', hq', hadj'⟩ := adj6_path_exit (adj6_connected p₀ t) hp₀ ht
      exact hq' (hSc p' hp' q' hadj')
  · rintro (h | h)
    · rw [h]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      rw [Finset.mem_biUnion] at hq
      obtain ⟨p, hp, -⟩ := hq
      simp at hp
    · rw [h]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      rw [Finset.mem_biUnion] at hq
      obtain ⟨p, hp, hq'⟩ := hq
      rw [Finset.mem_filter] at hq'
      exact hq'.2.2 (Finset.mem_univ q)

/-- **The estimator vanishes exactly at the degenerate fills**: no exposed
    voxel iff the interior is empty or fills the box. -/
theorem staircaseFaces_eq_zero_iff {nx ny nz : ℕ} {far : GPoint nx ny nz → Bool}
    {seeds : Finset (GPoint nx ny nz)} :
    staircaseFaces far seeds = 0 ↔
      interior far seeds = ∅ ∨ interior far seeds = Finset.univ := by
  unfold staircaseFaces
  rw [Finset.card_eq_zero, biUnion_eq_empty_iff]

/-! ### Bounds -/

/-- The exposed-voxel union is a subset of the exterior. -/
theorem biUnion_subset_exterior {nx ny nz : ℕ} {far : GPoint nx ny nz → Bool}
    {seeds : Finset (GPoint nx ny nz)} :
    (interior far seeds).biUnion (fun p =>
        (Finset.univ : Finset (GPoint nx ny nz)).filter fun q =>
          adj6 p q ∧ q ∉ interior far seeds) ⊆ Finset.univ \ interior far seeds := by
  intro q hq
  rw [mem_biUnion] at hq
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, hq.1⟩

/-- **Exterior bound**: the estimator is at most the number of exterior voxels. -/
theorem staircaseFaces_le_exterior {nx ny nz : ℕ} {far : GPoint nx ny nz → Bool}
    {seeds : Finset (GPoint nx ny nz)} :
    staircaseFaces far seeds ≤ (Finset.univ \ interior far seeds).card := by
  unfold staircaseFaces
  exact Finset.card_le_card biUnion_subset_exterior

/-- The estimator is at most both the `6 · #interior` bound and the exterior
    count. -/
theorem staircaseFaces_le_min {nx ny nz : ℕ} {far : GPoint nx ny nz → Bool}
    {seeds : Finset (GPoint nx ny nz)} :
    staircaseFaces far seeds
      ≤ min (6 * (interior far seeds).card) (Finset.univ \ interior far seeds).card :=
  le_min (staircaseFaces_le far seeds) (staircaseFaces_le_exterior)

/-! ### Sharpness -/

/-- **The `6 · #interior` bound is attained**: the single isolated far voxel
    `(1,1,1)` of an otherwise-empty `3 × 3 × 3` box (no seeds) has six exposed
    faces — one per direction. -/
theorem staircaseFaces_six :
    staircaseFaces (fun p : GPoint 3 3 3 => decide (p = (1, 1, 1))) ∅ = 6 := by
  native_decide

end StaircaseBoundary

end Vdb
