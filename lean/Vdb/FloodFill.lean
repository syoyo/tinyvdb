/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Signed flood fill (the pass `tvdb_signed_flood_fill` in `src/tinyvdb_ops.c`):
  on a dense grid, the far voxels (`|v| ≥ band`) that are 6-connected to the
  grid boundary (through far voxels) are the exterior; the remaining far voxels
  are the interior. The filled field is `+band` on the exterior and `−band`
  on the interior.

  This module models the lattice mathematically:

  * `GPoint` — lattice points of an `nx × ny × nz` box;
  * `adj6` — the 6-neighbour (von Neumann) adjacency, decidable, symmetric;
  * `FarConn` — `far`-bounded, 6-connected reachability (a path);
  * `fillIter`/`fillStep` — the BFS closure as finite iteration;
  * `mem_fillIter` / `fillIter_stable` / `closure_eq` — the closure equals the
    seed-connected far set, at `nx * ny * nz + 1` iterations;
  * `interior_adj_closed` — the interior is closed under far adjacency
    (an interior point's far neighbours are interior);
  * `interior_farconn` — hence the filled sign is constant on each
    6-connected far component;
  * **volume**: `interiorVolume h interior := (interior.card : ℝ) * h^3` and
    `interiorVolume_add` — interior + exterior volumes = far volume;
  * **staircase area**: `staircaseFaces` (exposed boundary faces of the
    interior set); the standard staircase estimator. It is *not* a consistent
    surface-area estimator in general (a diagonal plane rasterised on a grid
    overestimates/underestimates it direction-dependently); the estimator is
    documented and its one elementary fact proved here:
    `staircaseFaces_le` — at most `6 · #interior` directed faces.

  What is *not* proved here: any theorem about re-meshing the filled level
  set; that is future work.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Order.RelClasses
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false

namespace Vdb

/-- A point of an `nx × ny × nz` lattice. -/
abbrev GPoint (nx ny nz : ℕ) := Fin nx × Fin ny × Fin nz

/-- The 6-neighbour (von Neumann) adjacency. -/
def adj6 {nx ny nz : ℕ} (p q : GPoint nx ny nz) : Prop :=
  ((p.1.val + 1 = q.1.val) ∧ p.2.1 = q.2.1 ∧ p.2.2 = q.2.2) ∨
  ((q.1.val + 1 = p.1.val) ∧ p.2.1 = q.2.1 ∧ p.2.2 = q.2.2) ∨
  (p.1 = q.1 ∧ p.2.1.val + 1 = q.2.1.val ∧ p.2.2 = q.2.2) ∨
  (p.1 = q.1 ∧ q.2.1.val + 1 = p.2.1.val ∧ p.2.2 = q.2.2) ∨
  (p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ p.2.2.val + 1 = q.2.2.val) ∨
  (p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ q.2.2.val + 1 = p.2.2.val)

instance {nx ny nz : ℕ} (p q : GPoint nx ny nz) : Decidable (adj6 p q) := by
  unfold adj6
  infer_instance

theorem adj6_symm {nx ny nz : ℕ} (p q : GPoint nx ny nz) : adj6 p q ↔ adj6 q p := by
  constructor <;> intro h <;>
  rcases h with (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;>
  refine ?_ <;> simp only [adj6]
  · exact Or.inr (Or.inl ⟨h1, h2.symm, h3.symm⟩)
  · exact Or.inl ⟨h1, h2.symm, h3.symm⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1.symm, h2, h3.symm⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨h1.symm, by omega, h3.symm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1.symm, h2.symm, by omega⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1.symm, h2.symm, by omega⟩))))
  · exact Or.inr (Or.inl ⟨h1, h2.symm, h3.symm⟩)
  · exact Or.inl ⟨h1, h2.symm, h3.symm⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1.symm, h2, h3.symm⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨h1.symm, by omega, h3.symm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1.symm, h2.symm, by omega⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1.symm, h2.symm, by omega⟩))))

/-- The flood-fill step relation: both endpoints far, 6-adjacent. -/
def FarStep {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool) (a b : GPoint nx ny nz) : Prop :=
  far a = true ∧ adj6 a b ∧ far b = true

/-- Far-bounded 6-connected reachability, as a `ReflTransGen` of `FarStep`. -/
abbrev FarConn {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool) (p q : GPoint nx ny nz) : Prop :=
  Relation.ReflTransGen (FarStep far) p q

/-- One flood-fill growth step: add every far neighbour of a visited point. -/
def fillStep {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (s : Finset (GPoint nx ny nz)) : Finset (GPoint nx ny nz) :=
  s ∪ (s.biUnion fun p =>
    (Finset.univ : Finset (GPoint nx ny nz)).filter fun q =>
      far p = true ∧ far q = true ∧ adj6 p q)

theorem mem_fillStep {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (s : Finset (GPoint nx ny nz)) (p : GPoint nx ny nz) :
    p ∈ fillStep far s ↔ p ∈ s ∨ ∃ q ∈ s, far q = true ∧ far p = true ∧ adj6 q p := by
  unfold fillStep
  rw [Finset.mem_union, Finset.mem_biUnion]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The flood-fill closure after `k` growth steps. -/
def fillIter {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) : ℕ → Finset (GPoint nx ny nz)
  | 0 => seeds
  | k + 1 => fillStep far (fillIter far seeds k)

theorem fillIter_mono {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) (k : ℕ) :
    fillIter far seeds k ⊆ fillIter far seeds (k + 1) := by
  intro p hp
  unfold fillIter
  rw [mem_fillStep]
  exact Or.inl hp

theorem fillIter_mono' {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) {i j : ℕ} (h : i ≤ j) :
    fillIter far seeds i ⊆ fillIter far seeds j := by
  induction j with
  | zero =>
    rw [show i = 0 from Nat.le_zero.mp h]
  | succ j ih =>
    by_cases hij : i ≤ j
    · exact fun p hp => fillIter_mono far seeds j (ih hij hp)
    · have : i = j + 1 := by omega
      rw [this]

theorem fillIter_card_le {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) (k : ℕ) :
    (fillIter far seeds k).card ≤ nx * (ny * nz) := by
  have h := Finset.card_le_univ (fillIter far seeds k)
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin] at h
  exact h

/-- Every point in the closure is connected to the seed set through far points. -/
theorem mem_fillIter {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) (seeds_far : ∀ q ∈ seeds, far q = true)
    (k : ℕ) : ∀ p ∈ fillIter far seeds k, ∃ q ∈ seeds, far q = true ∧ FarConn far q p := by
  induction k with
  | zero =>
    intro p hp
    exact ⟨p, hp, seeds_far p hp, Relation.ReflTransGen.refl⟩
  | succ k ih =>
    intro p hp
    rw [fillIter, mem_fillStep] at hp
    rcases hp with h' | ⟨q, hq, hqfar, hpfar, hadj⟩
    · exact ih _ h'
    · obtain ⟨s, hs, hsfar, hconn⟩ := ih _ hq
      exact ⟨s, hs, hsfar, hconn.trans (Relation.ReflTransGen.single ⟨hqfar, hadj, hpfar⟩)⟩


theorem fillIter_mono_card {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) {i j : ℕ} (h : i ≤ j) :
    (fillIter far seeds i).card ≤ (fillIter far seeds j).card :=
  Finset.card_le_card (fillIter_mono' far seeds h)

/-- **Fixpoint**: there is a stabilization point `K ≤ nx * ny * nz + 1` from
    which the closure stops growing. Cards are non-decreasing and bounded by
    `nx * ny * nz`, so a stable step exists among the first `nx * ny * nz + 1`
    steps; once stable, the chain stays stable. -/
theorem fillIter_stable {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) :
    ∃ k ≤ nx * (ny * nz), ∀ j ≥ k, fillIter far seeds j = fillIter far seeds k := by
  set T := nx * (ny * nz) with hT
  have hex : ∃ k ≤ T, (fillIter far seeds k).card = (fillIter far seeds (k + 1)).card := by
    by_contra hcon
    have hcon' : ∀ k ≤ T, (fillIter far seeds k).card ≠ (fillIter far seeds (k + 1)).card := by
      intro k hk heq
      exact hcon ⟨k, hk, heq⟩
    have hinc : ∀ k ≤ T, (fillIter far seeds k).card + 1 ≤ (fillIter far seeds (k + 1)).card := by
      intro k hk
      have h := fillIter_mono_card far seeds (i := k) (j := k + 1) (by omega)
      have hne := hcon' k hk
      omega
    have hgrow : ∀ n ≤ T + 1, (fillIter far seeds 0).card + n ≤ (fillIter far seeds n).card := by
      intro n hn
      induction n with
      | zero => simp
      | succ n ih =>
        have h3 := hinc n (by omega)
        omega
    have hbound := fillIter_card_le far seeds (T + 1)
    have hgrow' := hgrow (T + 1) (by omega)
    have h0 := Nat.zero_le (fillIter far seeds 0).card
    omega
  obtain ⟨k, hk, hcard⟩ := hex
  have hset : fillIter far seeds (k + 1) = fillIter far seeds k :=
    (Finset.eq_of_subset_of_card_le (fillIter_mono far seeds k) (le_of_eq hcard.symm)).symm
  refine ⟨k, by omega, ?_⟩
  intro j
  induction j with
  | zero =>
    intro hj
    have := Nat.le_zero.mp hj
    rw [this]
  | succ j ih =>
    intro hj
    by_cases hjk : k ≤ j
    · have h1 := ih hjk
      rw [show fillIter far seeds (j + 1) = fillStep far (fillIter far seeds j) from rfl, h1]
      show fillIter far seeds (k + 1) = fillIter far seeds k
      exact hset
    · have hjk2 : j + 1 = k := by omega
      rw [hjk2]


/-! ### Closure equality, interior and sign -/

/-- The flood-fill top iterate is a fixpoint of `fillStep`. -/
theorem fillIter_max_fixpoint {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) :
    fillStep far (fillIter far seeds (nx * (ny * nz) + 1)) =
      fillIter far seeds (nx * (ny * nz) + 1) := by
  obtain ⟨K, _, hstab⟩ := fillIter_stable far seeds
  have hK1 := hstab (nx * (ny * nz) + 1) (by omega)
  have hK2 := hstab (nx * (ny * nz) + 2) (by omega)
  calc fillStep far (fillIter far seeds (nx * (ny * nz) + 1))
      = fillIter far seeds (nx * (ny * nz) + 2) := rfl
    _ = fillIter far seeds K := hK2
    _ = fillIter far seeds (nx * (ny * nz) + 1) := hK1.symm

/-- Reachability direction: a seed-connected point enters the top iterate. -/
theorem farconn_mem_iter {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) {q p : GPoint nx ny nz}
    (hconn : FarConn far q p) :
    q ∈ fillIter far seeds (nx * (ny * nz) + 1) → p ∈ fillIter far seeds (nx * (ny * nz) + 1) := by
  have hfix := fillIter_max_fixpoint far seeds
  induction hconn with
  | refl => exact id
  | tail h hr ih =>
    intro hq
    obtain ⟨hb, hadj, hp⟩ := hr
    have hbc := ih hq
    rw [← hfix, mem_fillStep]
    exact Or.inr ⟨_, hbc, hb, hp, hadj⟩

/-- **Spec (BFS equality)**: the flood-fill top iterate is exactly the set of
    far points connected to the seed set through far points. -/
theorem fillIter_max {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) (seeds_far : ∀ q ∈ seeds, far q = true) :
    fillIter far seeds (nx * (ny * nz) + 1) =
      {p | ∃ q ∈ seeds, far q = true ∧ FarConn far q p} := by
  ext p
  constructor
  · intro hp
    exact mem_fillIter far seeds seeds_far (nx * (ny * nz) + 1) p hp
  · intro hp
    obtain ⟨q, hq, _, hconn⟩ := hp
    exact farconn_mem_iter far seeds hconn
      (fillIter_mono' far seeds (show 0 ≤ nx * (ny * nz) + 1 by omega) hq)

/-- The step relation is symmetric. -/
theorem farconn_step_symm {nx ny nz : ℕ} {far : GPoint nx ny nz → Bool} {a b : GPoint nx ny nz}
    (h : FarStep far a b) : FarStep far b a :=
  ⟨h.2.2, (adj6_symm _ _).mp h.2.1, h.1⟩

/-- The reachability relation is symmetric. -/
theorem farconn_symm {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool) {p q : GPoint nx ny nz}
    (h : FarConn far p q) : FarConn far q p := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h hr ih => exact (Relation.ReflTransGen.single (farconn_step_symm hr)).trans ih

/-- Every visitable point is far. -/
theorem fillIter_far {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) (seeds_far : ∀ q ∈ seeds, far q = true) :
    ∀ k p, p ∈ fillIter far seeds k → far p = true := by
  intro k
  induction k with
  | zero =>
    intro p hp
    exact seeds_far p hp
  | succ k ih =>
    intro p hp
    rw [fillIter, mem_fillStep] at hp
    rcases hp with h' | ⟨q, hq, hqfar, hpfar, _⟩
    · exact ih p h'
    · exact hpfar

/-- The exterior far set is the top iterate. -/
def exteriorFar {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool) (seeds : Finset (GPoint nx ny nz)) :
    Finset (GPoint nx ny nz) :=
  fillIter far seeds (nx * (ny * nz) + 1)

/-- The interior: far but seed-unreachable. -/
def interior {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool) (seeds : Finset (GPoint nx ny nz)) :
    Finset (GPoint nx ny nz) :=
  (Finset.univ.filter (fun p => far p = true)) \ fillIter far seeds (nx * (ny * nz) + 1)

theorem mem_interior {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) {p : GPoint nx ny nz} :
    p ∈ interior far seeds ↔ far p = true ∧ p ∉ fillIter far seeds (nx * (ny * nz) + 1) := by
  simp only [interior, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_exteriorFar {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) {p : GPoint nx ny nz} :
    p ∈ exteriorFar far seeds ↔ p ∈ fillIter far seeds (nx * (ny * nz) + 1) := Iff.rfl

theorem interior_exterior_disjoint {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) :
    Disjoint (interior far seeds) (fillIter far seeds (nx * (ny * nz) + 1)) :=
  Finset.sdiff_disjoint

/-- **Interior closure**: every far neighbour of an interior point is
    interior. -/
theorem interior_adj_closed {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz))
    {p q : GPoint nx ny nz} (hp : p ∈ interior far seeds) (hadj : adj6 p q)
    (hq : far q = true) : q ∈ interior far seeds := by
  rw [mem_interior] at hp ⊢
  obtain ⟨hpfar, hpnot⟩ := hp
  refine ⟨hq, ?_⟩
  intro hqext
  have hfix := fillIter_max_fixpoint far seeds
  rw [← hfix, mem_fillStep] at hpnot
  exact hpnot (Or.inr ⟨q, hqext, hq, hpfar, (adj6_symm _ _).mp hadj⟩)

/-- The filled sign is constant on each 6-connected far component. -/
theorem interior_farconn {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz))
    {p q : GPoint nx ny nz} (hp : p ∈ interior far seeds)
    (hconn : FarConn far p q) : q ∈ interior far seeds := by
  induction hconn with
  | refl => exact hp
  | tail h hr ih =>
    obtain ⟨hfa, hadj, hfb⟩ := hr
    exact interior_adj_closed far seeds ih hadj hfb

/-- The sign assignment: `+band` on the exterior, `−band` on the interior. -/
def fillSign {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool) (seeds : Finset (GPoint nx ny nz))
    (band : ℝ) (p : GPoint nx ny nz) : ℝ :=
  if p ∈ fillIter far seeds (nx * (ny * nz) + 1) then band else -band

/-- Two far points in the same 6-connected component get the same sign. -/
theorem fillSign_const_of_conn {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) (_seeds_far : ∀ q ∈ seeds, far q = true)
    (band : ℝ) {p q : GPoint nx ny nz}
    (_hpfar : far p = true) (_hqfar : far q = true) (hconn : FarConn far p q) :
    fillSign far seeds band p = fillSign far seeds band q := by
  have hiff : p ∈ fillIter far seeds (nx * (ny * nz) + 1) ↔ q ∈ fillIter far seeds (nx * (ny * nz) + 1) := by
    constructor
    · intro hp
      exact farconn_mem_iter far seeds hconn hp
    · intro hq
      exact farconn_mem_iter far seeds (farconn_symm far hconn) hq
  unfold fillSign
  by_cases hp : p ∈ fillIter far seeds (nx * (ny * nz) + 1) <;>
  by_cases hq : q ∈ fillIter far seeds (nx * (ny * nz) + 1) <;>
  simp_all


/-! ### Volume and staircase area -/

/-- The volume of a voxel set in units of h³. -/
def scaledVolume (h : ℝ) (s : Finset (GPoint nx ny nz)) : ℝ :=
  (s.card : ℝ) * h ^ 3

/-- The interior far voxels tile the far set together with the exterior. -/
theorem far_eq_interior_union_exterior {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) (seeds_far : ∀ q ∈ seeds, far q = true) :
    (Finset.univ.filter fun p => far p = true) =
      interior far seeds ∪ fillIter far seeds (nx * (ny * nz) + 1) := by
  ext p
  simp only [interior, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union]
  constructor
  · intro hp
    by_cases hp' : p ∈ fillIter far seeds (nx * (ny * nz) + 1)
    · exact Or.inr hp'
    · exact Or.inl ⟨hp, hp'⟩
  · intro hp
    rcases hp with ⟨hfar, _⟩ | hp'
    · exact hfar
    · exact fillIter_far far seeds seeds_far _ p hp'

/-- **Volume**: interior + exterior far voxel counts equal the far count;
    equivalently, the interior volume is the far volume minus the exterior. -/
theorem interiorVolume_add {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) (seeds_far : ∀ q ∈ seeds, far q = true) (h : ℝ) :
    scaledVolume h (interior far seeds) + scaledVolume h (fillIter far seeds (nx * (ny * nz) + 1)) =
      scaledVolume h (Finset.univ.filter fun p => far p = true) := by
  unfold scaledVolume
  rw [← add_mul]
  congr 1
  have hsub : fillIter far seeds (nx * (ny * nz) + 1) ⊆
      Finset.univ.filter (fun p => far p = true) := by
    intro p hp
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ p, fillIter_far far seeds seeds_far _ p hp⟩
  rw [far_eq_interior_union_exterior far seeds seeds_far]
  have hcard : (interior far seeds).card + (fillIter far seeds (nx * (ny * nz) + 1)).card =
      (interior far seeds ∪ fillIter far seeds (nx * (ny * nz) + 1)).card :=
    (Finset.card_union_of_disjoint (s := interior far seeds)
      (t := fillIter far seeds (nx * (ny * nz) + 1)) Finset.sdiff_disjoint).symm
  exact_mod_cast hcard


/-! ### Volume and staircase area -/

/-- The staircase face count of the interior: directed faces from an
    interior voxel to a non-interior neighbour (the standard staircase
    estimator). It is **not** consistent with the true surface area — a
    diagonal plane rasterised on the grid overestimates it in the worst
    directions. No consistency theorem is claimed; `staircaseFaces_le`
    proves the elementary count bound (at most six faces per interior
    voxel). -/
def staircaseFaces {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) : ℕ :=
  (interior far seeds).biUnion
    (fun p => (Finset.univ : Finset (GPoint nx ny nz)).filter fun q =>
      adj6 p q ∧ q ∉ interior far seeds) |>.card

/-! ### Staircase faces: the `6 · #interior` bound

Each interior voxel has at most six 6-connected neighbours, so the
estimator counts at most six faces per interior voxel. The neighbour set
is bounded *symbolically*: the earlier enumeration attempt indexed the
neighbours with `decide` over the lattice and did not scale; this proof
splits adjacency into the six direction cases and never enumerates the
grid. -/

/-- The set of in-box neighbours of `p`: the at-most-six candidate slots,
    restricted to the box (boundary voxels have fewer than six). Each
    present candidate is a singleton; absent (out-of-box) slots are empty. -/
def neighborFinset {nx ny nz : ℕ} (p : GPoint nx ny nz) : Finset (GPoint nx ny nz) :=
  (if h : p.1.val + 1 < nx then {(⟨⟨p.1.val + 1, h⟩, p.2⟩ : GPoint nx ny nz)} else ∅) ∪
  ((if h : 0 < p.1.val then {(⟨⟨p.1.val - 1, by omega⟩, p.2⟩ : GPoint nx ny nz)} else ∅) ∪
   ((if h : p.2.1.val + 1 < ny then {(⟨p.1, ⟨p.2.1.val + 1, h⟩, p.2.2⟩ : GPoint nx ny nz)} else ∅) ∪
    ((if h : 0 < p.2.1.val then {(⟨p.1, ⟨p.2.1.val - 1, by omega⟩, p.2.2⟩ : GPoint nx ny nz)} else ∅) ∪
     ((if h : p.2.2.val + 1 < nz then {(⟨p.1, p.2.1, ⟨p.2.2.val + 1, h⟩⟩ : GPoint nx ny nz)} else ∅) ∪
      (if h : 0 < p.2.2.val then {(⟨p.1, p.2.1, ⟨p.2.2.val - 1, by omega⟩⟩ : GPoint nx ny nz)} else ∅)))))

theorem neighborFinset_card_le {nx ny nz : ℕ} (p : GPoint nx ny nz) :
    (neighborFinset p).card ≤ 6 := by
  have e1 : (if h : p.1.val + 1 < nx then ({(⟨⟨p.1.val + 1, h⟩, p.2⟩ : GPoint nx ny nz)} : Finset _) else ∅).card ≤ 1 := by
    split_ifs <;> simp
  have e2 : (if h : 0 < p.1.val then ({(⟨⟨p.1.val - 1, by omega⟩, p.2⟩ : GPoint nx ny nz)} : Finset _) else ∅).card ≤ 1 := by
    split_ifs <;> simp
  have e3 : (if h : p.2.1.val + 1 < ny then ({(⟨p.1, ⟨p.2.1.val + 1, h⟩, p.2.2⟩ : GPoint nx ny nz)} : Finset _) else ∅).card ≤ 1 := by
    split_ifs <;> simp
  have e4 : (if h : 0 < p.2.1.val then ({(⟨p.1, ⟨p.2.1.val - 1, by omega⟩, p.2.2⟩ : GPoint nx ny nz)} : Finset _) else ∅).card ≤ 1 := by
    split_ifs <;> simp
  have e5 : (if h : p.2.2.val + 1 < nz then ({(⟨p.1, p.2.1, ⟨p.2.2.val + 1, h⟩⟩ : GPoint nx ny nz)} : Finset _) else ∅).card ≤ 1 := by
    split_ifs <;> simp
  have e6 : (if h : 0 < p.2.2.val then ({(⟨p.1, p.2.1, ⟨p.2.2.val - 1, by omega⟩⟩ : GPoint nx ny nz)} : Finset _) else ∅).card ≤ 1 := by
    split_ifs <;> simp
  have u56 : ((if h : p.2.2.val + 1 < nz then ({(⟨p.1, p.2.1, ⟨p.2.2.val + 1, h⟩⟩ : GPoint nx ny nz)} : Finset _) else ∅) ∪
      (if h : 0 < p.2.2.val then ({(⟨p.1, p.2.1, ⟨p.2.2.val - 1, by omega⟩⟩ : GPoint nx ny nz)} : Finset _) else ∅)).card ≤ 2 :=
    le_trans (Finset.card_union_le _ _) (add_le_add e5 e6)
  have u456 : ((if h : 0 < p.2.1.val then ({(⟨p.1, ⟨p.2.1.val - 1, by omega⟩, p.2.2⟩ : GPoint nx ny nz)} : Finset _) else ∅) ∪
      ((if h : p.2.2.val + 1 < nz then ({(⟨p.1, p.2.1, ⟨p.2.2.val + 1, h⟩⟩ : GPoint nx ny nz)} : Finset _) else ∅) ∪
       (if h : 0 < p.2.2.val then ({(⟨p.1, p.2.1, ⟨p.2.2.val - 1, by omega⟩⟩ : GPoint nx ny nz)} : Finset _) else ∅))).card ≤ 3 :=
    le_trans (Finset.card_union_le _ _) (add_le_add e4 u56)
  have u3456 : ((if h : p.2.1.val + 1 < ny then ({(⟨p.1, ⟨p.2.1.val + 1, h⟩, p.2.2⟩ : GPoint nx ny nz)} : Finset _) else ∅) ∪
      ((if h : 0 < p.2.1.val then ({(⟨p.1, ⟨p.2.1.val - 1, by omega⟩, p.2.2⟩ : GPoint nx ny nz)} : Finset _) else ∅) ∪
       ((if h : p.2.2.val + 1 < nz then ({(⟨p.1, p.2.1, ⟨p.2.2.val + 1, h⟩⟩ : GPoint nx ny nz)} : Finset _) else ∅) ∪
        (if h : 0 < p.2.2.val then ({(⟨p.1, p.2.1, ⟨p.2.2.val - 1, by omega⟩⟩ : GPoint nx ny nz)} : Finset _) else ∅)))).card ≤ 4 :=
    le_trans (Finset.card_union_le _ _) (add_le_add e3 u456)
  have u23456 : ((if h : 0 < p.1.val then ({(⟨⟨p.1.val - 1, by omega⟩, p.2⟩ : GPoint nx ny nz)} : Finset _) else ∅) ∪
      ((if h : p.2.1.val + 1 < ny then ({(⟨p.1, ⟨p.2.1.val + 1, h⟩, p.2.2⟩ : GPoint nx ny nz)} : Finset _) else ∅) ∪
       ((if h : 0 < p.2.1.val then ({(⟨p.1, ⟨p.2.1.val - 1, by omega⟩, p.2.2⟩ : GPoint nx ny nz)} : Finset _) else ∅) ∪
        ((if h : p.2.2.val + 1 < nz then ({(⟨p.1, p.2.1, ⟨p.2.2.val + 1, h⟩⟩ : GPoint nx ny nz)} : Finset _) else ∅) ∪
         (if h : 0 < p.2.2.val then ({(⟨p.1, p.2.1, ⟨p.2.2.val - 1, by omega⟩⟩ : GPoint nx ny nz)} : Finset _) else ∅))))).card ≤ 5 :=
    le_trans (Finset.card_union_le _ _) (add_le_add e2 u3456)
  show (neighborFinset p).card ≤ 6
  unfold neighborFinset
  exact le_trans (Finset.card_union_le _ _) (add_le_add e1 u23456)

theorem neighbor_mem {nx ny nz : ℕ} {p q : GPoint nx ny nz} (h : adj6 p q) :
    q ∈ neighborFinset p := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
              | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · -- q = p + eₓ
    have hnx : p.1.val + 1 < nx := by have := q.1.isLt; omega
    have hq : (⟨⟨p.1.val + 1, hnx⟩, p.2⟩ : GPoint nx ny nz) = q := by
      show (⟨p.1.val + 1, hnx⟩, p.2) = q
      apply Prod.ext
      · show (⟨p.1.val + 1, hnx⟩ : Fin nx) = q.1
        exact Fin.ext h1
      · show p.2 = q.2
        apply Prod.ext
        · exact h2
        · exact h3
    rw [← hq]
    unfold neighborFinset
    have hmem : (⟨⟨p.1.val + 1, hnx⟩, p.2⟩ : GPoint nx ny nz) ∈
        (if h : p.1.val + 1 < nx then ({(⟨⟨p.1.val + 1, h⟩, p.2⟩ : GPoint nx ny nz)} : Finset _) else ∅) := by
      split_ifs
      · exact Finset.mem_singleton_self _
    exact Finset.mem_union_left _ hmem
  · -- q = p − eₓ
    have hnx : 0 < p.1.val := by omega
    have hxis : q.1.val < nx := q.1.isLt
    have hq : (⟨⟨p.1.val - 1, by omega⟩, p.2⟩ : GPoint nx ny nz) = q := by
      show (⟨p.1.val - 1, by omega⟩, p.2) = q
      apply Prod.ext
      · show (⟨p.1.val - 1, by omega⟩ : Fin nx) = q.1
        exact Fin.ext (by omega : p.1.val - 1 = q.1.val)
      · show p.2 = q.2
        apply Prod.ext
        · exact h2
        · exact h3
    rw [← hq]
    unfold neighborFinset
    have hmem : (⟨⟨p.1.val - 1, by omega⟩, p.2⟩ : GPoint nx ny nz) ∈
        (if h : 0 < p.1.val then ({(⟨⟨p.1.val - 1, by omega⟩, p.2⟩ : GPoint nx ny nz)} : Finset _) else ∅) := by
      split_ifs
      · exact Finset.mem_singleton_self _
    exact Finset.mem_union_right _ (Finset.mem_union_left _ hmem)
  · -- q = p + e_y
    have hny : p.2.1.val + 1 < ny := by have := q.2.1.isLt; omega
    have hq : (⟨p.1, ⟨p.2.1.val + 1, hny⟩, p.2.2⟩ : GPoint nx ny nz) = q := by
      show (p.1, (⟨p.2.1.val + 1, hny⟩, p.2.2)) = q
      apply Prod.ext
      · show p.1 = q.1
        exact h1
      · show (⟨p.2.1.val + 1, hny⟩, p.2.2) = q.2
        apply Prod.ext
        · show (⟨p.2.1.val + 1, hny⟩ : Fin ny) = q.2.1
          exact Fin.ext h2
        · show p.2.2 = q.2.2
          exact h3
    rw [← hq]
    unfold neighborFinset
    have hmem : (⟨p.1, ⟨p.2.1.val + 1, hny⟩, p.2.2⟩ : GPoint nx ny nz) ∈
        (if h : p.2.1.val + 1 < ny then ({(⟨p.1, ⟨p.2.1.val + 1, h⟩, p.2.2⟩ : GPoint nx ny nz)} : Finset _) else ∅) := by
      split_ifs
      · exact Finset.mem_singleton_self _
    exact Finset.mem_union_right _
      (Finset.mem_union_right _ (Finset.mem_union_left _ hmem))
  · -- q = p − e_y
    have hny : 0 < p.2.1.val := by omega
    have hyis : q.2.1.val < ny := q.2.1.isLt
    have hq : (⟨p.1, ⟨p.2.1.val - 1, by omega⟩, p.2.2⟩ : GPoint nx ny nz) = q := by
      show (p.1, (⟨p.2.1.val - 1, by omega⟩, p.2.2)) = q
      apply Prod.ext
      · show p.1 = q.1
        exact h1
      · show (⟨p.2.1.val - 1, by omega⟩, p.2.2) = q.2
        apply Prod.ext
        · show (⟨p.2.1.val - 1, by omega⟩ : Fin ny) = q.2.1
          exact Fin.ext (by omega : p.2.1.val - 1 = q.2.1.val)
        · show p.2.2 = q.2.2
          exact h3
    rw [← hq]
    unfold neighborFinset
    have hmem : (⟨p.1, ⟨p.2.1.val - 1, by omega⟩, p.2.2⟩ : GPoint nx ny nz) ∈
        (if h : 0 < p.2.1.val then ({(⟨p.1, ⟨p.2.1.val - 1, by omega⟩, p.2.2⟩ : GPoint nx ny nz)} : Finset _) else ∅) := by
      split_ifs
      · exact Finset.mem_singleton_self _
    exact Finset.mem_union_right _
      (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _ hmem)))
  · -- q = p + e_z
    have hnz : p.2.2.val + 1 < nz := by have := q.2.2.isLt; omega
    have hq : (⟨p.1, p.2.1, ⟨p.2.2.val + 1, hnz⟩⟩ : GPoint nx ny nz) = q := by
      show (p.1, (p.2.1, ⟨p.2.2.val + 1, hnz⟩)) = q
      apply Prod.ext
      · show p.1 = q.1
        exact h1
      · show (p.2.1, ⟨p.2.2.val + 1, hnz⟩) = q.2
        apply Prod.ext
        · show p.2.1 = q.2.1
          exact h2
        · show (⟨p.2.2.val + 1, hnz⟩ : Fin nz) = q.2.2
          exact Fin.ext h3
    rw [← hq]
    unfold neighborFinset
    have hmem : (⟨p.1, p.2.1, ⟨p.2.2.val + 1, hnz⟩⟩ : GPoint nx ny nz) ∈
        (if h : p.2.2.val + 1 < nz then ({(⟨p.1, p.2.1, ⟨p.2.2.val + 1, h⟩⟩ : GPoint nx ny nz)} : Finset _) else ∅) := by
      split_ifs
      · exact Finset.mem_singleton_self _
    exact Finset.mem_union_right _
      (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_union_right _ (Finset.mem_union_left _ hmem))))
  · -- q = p − e_z
    have hnz : 0 < p.2.2.val := by omega
    have hzis : q.2.2.val < nz := q.2.2.isLt
    have hq : (⟨p.1, p.2.1, ⟨p.2.2.val - 1, by omega⟩⟩ : GPoint nx ny nz) = q := by
      show (p.1, (p.2.1, ⟨p.2.2.val - 1, by omega⟩)) = q
      apply Prod.ext
      · show p.1 = q.1
        exact h1
      · show (p.2.1, ⟨p.2.2.val - 1, by omega⟩) = q.2
        apply Prod.ext
        · show p.2.1 = q.2.1
          exact h2
        · show (⟨p.2.2.val - 1, by omega⟩ : Fin nz) = q.2.2
          exact Fin.ext (by omega : p.2.2.val - 1 = q.2.2.val)
    rw [← hq]
    unfold neighborFinset
    have hmem : (⟨p.1, p.2.1, ⟨p.2.2.val - 1, by omega⟩⟩ : GPoint nx ny nz) ∈
        (if h : 0 < p.2.2.val then ({(⟨p.1, p.2.1, ⟨p.2.2.val - 1, by omega⟩⟩ : GPoint nx ny nz)} : Finset _) else ∅) := by
      split_ifs
      · exact Finset.mem_singleton_self _
    exact Finset.mem_union_right _
      (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_union_right _ (Finset.mem_union_right _ hmem))))

/-- **Staircase faces are bounded by six times the interior size.**
    Each interior voxel contributes at most one face per in-box neighbour. -/
theorem staircaseFaces_le {nx ny nz : ℕ} (far : GPoint nx ny nz → Bool)
    (seeds : Finset (GPoint nx ny nz)) :
    staircaseFaces far seeds ≤ 6 * (interior far seeds).card := by
  unfold staircaseFaces
  refine le_trans (Finset.card_biUnion_le_card_mul
    (interior far seeds)
    (fun p => (Finset.univ : Finset (GPoint nx ny nz)).filter fun q =>
      adj6 p q ∧ q ∉ interior far seeds) 6 ?_) (le_of_eq (mul_comm _ _))
  · intro p _
    refine le_trans (Finset.card_le_card ?_) (neighborFinset_card_le p)
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    exact neighbor_mem hq.1

end Vdb
