/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Part decomposition of a dense signed-distance grid (the C APIs
  `tvdb_sdf_segmentation` and `tvdb_sdf_extract_enclosed_regions`). The
  specification is lattice-level: an interior predicate selects voxels, an
  adjacency relation (6 or 26) induces connectivity, and the components are the
  equivalence classes of interior voxels. The per-part field is the original SDF
  on its own component, background on the other components' interiors, and the
  original values everywhere outside the interior — exactly what the C routine
  writes into each output grid.

  Cavities are exterior voxels not connected to the grid boundary through
  exterior voxels; the cavity mask is `1` on them and `0` elsewhere.

  The connectivity machinery generalizes `FloodFill.FarConn`: it is stated over
  any finite type and any adjacency relation, with symmetry as an explicit
  premise. No geometry or floating point is involved, so every theorem is a
  finite combinatorial identity.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.FloodFill

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

namespace Vdb

-- Connectivity and cavity predicates are not decidable by construction; the
-- finite enumeration uses the classical decidability of propositions.
attribute [local instance] Classical.propDecidable

variable {α : Type} [Fintype α] [DecidableEq α]

/-! ### Connectivity inside a set -/

/-- One step of adjacency-bounded connectivity: both endpoints are in `s`
    (only the target needs recording; the source is guaranteed by induction). -/
def ConnStep (adj : α → α → Prop) (s : α → Prop) (a b : α) : Prop :=
  adj a b ∧ s b

/-- Connectivity from `a` to `b` through `s` under `adj`. -/
abbrev Conn (adj : α → α → Prop) (s : α → Prop) : α → α → Prop :=
  Relation.ReflTransGen (ConnStep adj s)

theorem conn_refl (adj : α → α → Prop) (s : α → Prop) (a : α) : Conn adj s a a :=
  Relation.ReflTransGen.refl

theorem conn_of_step {adj : α → α → Prop} {s : α → Prop} {a b : α}
    (hab : adj a b) (hb : s b) : Conn adj s a b :=
  Relation.ReflTransGen.single ⟨hab, hb⟩

theorem conn_tail {adj : α → α → Prop} {s : α → Prop} {a b c : α}
    (h : Conn adj s a b) (hbc : adj b c) (hc : s c) : Conn adj s a c :=
  h.tail ⟨hbc, hc⟩

/-- Every point reached by an `s`-bounded connection lies in `s`. -/
theorem conn_mem {adj : α → α → Prop} {s : α → Prop} {a b : α}
    (ha : s a) (h : Conn adj s a b) : s b := by
  induction h with
  | refl => exact ha
  | tail _ hstep _ => exact hstep.2

theorem conn_trans {adj : α → α → Prop} {s : α → Prop} {a b c : α}
    (h₁ : Conn adj s a b) (h₂ : Conn adj s b c) : Conn adj s a c :=
  Relation.ReflTransGen.trans h₁ h₂

/-- Connectivity is symmetric when the adjacency relation is, provided both
    endpoints lie in `s` (the return walk has to stay inside `s`). -/
theorem conn_symm (hsymm : ∀ a b : α, adj a b ↔ adj b a)
    {a b : α} (ha : s a) (hb : s b) (h : Conn adj s a b) : Conn adj s b a := by
  induction h with
  | refl => exact conn_refl adj s a
  | tail h₁ hstep ih =>
      have hbm : s _ := conn_mem ha h₁
      have hcb := conn_of_step (adj := adj) (s := s) ((hsymm _ _).mp hstep.1) hbm
      exact hcb.trans (ih hbm)

/-! ### Components -/

/-- The component of `p`: all points reachable from `p` inside `interior`. -/
def componentOf (adj : α → α → Prop) (interior : Finset α) (p : α) : Finset α :=
  Finset.univ.filter fun q => Conn adj (fun x => x ∈ interior) p q

/-- The set of components of an interior set. -/
def components (adj : α → α → Prop) (interior : Finset α) : Finset (Finset α) :=
  interior.image (componentOf adj interior)

theorem mem_componentOf {adj : α → α → Prop} {interior : Finset α} {p q : α} :
    q ∈ componentOf adj interior p ↔ Conn adj (fun x => x ∈ interior) p q := by
  simp [componentOf]

@[simp] theorem mem_componentOf_self {adj : α → α → Prop} {interior : Finset α}
    {p : α} : p ∈ componentOf adj interior p := by
  simp [componentOf, conn_refl]

theorem componentOf_subset {adj : α → α → Prop} {interior : Finset α} {p : α}
    (hp : p ∈ interior) : componentOf adj interior p ⊆ interior := by
  intro q hq
  exact conn_mem hp (mem_componentOf.mp hq)

theorem mem_components {adj : α → α → Prop} {interior : Finset α} {c : Finset α} :
    c ∈ components adj interior ↔ ∃ p ∈ interior, c = componentOf adj interior p := by
  constructor
  · intro hc
    simp only [components, Finset.mem_image] at hc
    rcases hc with ⟨p, hp, heq⟩
    exact ⟨p, hp, heq.symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

theorem componentOf_mem_components {adj : α → α → Prop} {interior : Finset α}
    {p : α} (hp : p ∈ interior) : componentOf adj interior p ∈ components adj interior :=
  mem_components.mpr ⟨p, hp, rfl⟩

theorem componentOf_nonempty {adj : α → α → Prop} {interior : Finset α}
    {p : α} : (componentOf adj interior p).Nonempty :=
  ⟨p, mem_componentOf_self⟩

theorem componentOf_eq_of_conn (hsymm : ∀ a b : α, adj a b ↔ adj b a)
    {interior : Finset α} {p q : α} (hp : p ∈ interior)
    (h : Conn adj (fun x => x ∈ interior) p q) :
    componentOf adj interior p = componentOf adj interior q := by
  have hq : q ∈ interior := conn_mem hp h
  have hqp : Conn adj (fun x => x ∈ interior) q p := conn_symm hsymm hp hq h
  ext x
  simp only [mem_componentOf]
  constructor
  · intro hx
    exact conn_trans hqp hx
  · intro hx
    exact conn_trans h hx

theorem componentOf_eq_iff (hsymm : ∀ a b : α, adj a b ↔ adj b a)
    {interior : Finset α} {p q : α} (hp : p ∈ interior) (hq : q ∈ interior) :
    componentOf adj interior p = componentOf adj interior q ↔
      Conn adj (fun x => x ∈ interior) p q := by
  constructor
  · intro heq
    have : q ∈ componentOf adj interior q := mem_componentOf_self
    rw [← heq] at this
    exact mem_componentOf.mp this
  · exact componentOf_eq_of_conn hsymm hp

theorem components_disjoint (hsymm : ∀ a b : α, adj a b ↔ adj b a)
    {interior : Finset α} {c₁ c₂ : Finset α}
    (hc₁ : c₁ ∈ components adj interior) (hc₂ : c₂ ∈ components adj interior)
    (hne : c₁ ≠ c₂) : Disjoint c₁ c₂ := by
  rcases mem_components.mp hc₁ with ⟨p, hp, rfl⟩
  rcases mem_components.mp hc₂ with ⟨q, hq, rfl⟩
  rw [Finset.disjoint_left]
  intro x hxp hxq
  have hpx : Conn adj (fun x => x ∈ interior) p x := mem_componentOf.mp hxp
  have hqx : Conn adj (fun x => x ∈ interior) q x := mem_componentOf.mp hxq
  have hxi : x ∈ interior := conn_mem hp hpx
  have hqp : Conn adj (fun x => x ∈ interior) q p :=
    conn_trans hqx (conn_symm hsymm hp hxi hpx)
  have heq := componentOf_eq_of_conn hsymm hq hqp
  exact hne heq.symm

/-- Every interior voxel lies in exactly one component, and the components
    cover exactly the interior. -/
theorem biUnion_components_eq (hsymm : ∀ a b : α, adj a b ↔ adj b a)
    (interior : Finset α) : (components adj interior).biUnion id = interior := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨c, hc, hxc⟩
    rcases mem_components.mp hc with ⟨p, hp, rfl⟩
    exact conn_mem hp (mem_componentOf.mp hxc)
  · intro hx
    exact Finset.mem_biUnion.mpr
      ⟨componentOf adj interior x, componentOf_mem_components hx, mem_componentOf_self⟩

/-! ### Per-part SDF fields -/

/-- The field of one part: the original SDF on its own interior, `bg` on every
    other component's interior, unchanged outside the interior. -/
def partField (adj : α → α → Prop) (interior : Finset α) (bg : ℝ) (φ : α → ℝ)
    (c : Finset α) (x : α) : ℝ :=
  if x ∈ interior ∧ x ∉ c then bg else φ x

theorem partField_eq_self_of_mem {adj : α → α → Prop} {interior : Finset α}
    {bg : ℝ} {φ : α → ℝ} {c : Finset α} {x : α} (hx : x ∈ c) :
    partField adj interior bg φ c x = φ x := by
  simp [partField, hx]

theorem partField_eq_bg_of_other {adj : α → α → Prop} {interior : Finset α}
    {bg : ℝ} {φ : α → ℝ} {c : Finset α} {x : α}
    (hxi : x ∈ interior) (hxc : x ∉ c) : partField adj interior bg φ c x = bg := by
  simp [partField, hxi, hxc]

theorem partField_eq_self_of_not_mem_interior {adj : α → α → Prop}
    {interior : Finset α} {bg : ℝ} {φ : α → ℝ} {c : Finset α} {x : α}
    (hxi : x ∉ interior) : partField adj interior bg φ c x = φ x := by
  simp [partField, hxi]

theorem partField_cover (hsymm : ∀ a b : α, adj a b ↔ adj b a)
    {interior : Finset α} {φ : α → ℝ} {bg : ℝ} {x : α} (hx : x ∈ interior) :
    ∃ c ∈ components adj interior, partField adj interior bg φ c x = φ x := by
  refine ⟨componentOf adj interior x, componentOf_mem_components hx, ?_⟩
  exact partField_eq_self_of_mem mem_componentOf_self

/-! ### Cavities (enclosed regions) -/

variable {nx ny nz : ℕ}

/-- A voxel touches the grid boundary along some axis. -/
def onBoundary (p : GPoint nx ny nz) : Prop :=
  p.1.val = 0 ∨ p.1.val + 1 = nx ∨
  p.2.1.val = 0 ∨ p.2.1.val + 1 = ny ∨
  p.2.2.val = 0 ∨ p.2.2.val + 1 = nz

/-- Boundary exterior seeds: exterior voxels touching the grid boundary. -/
def boundaryExterior (adj : GPoint nx ny nz → GPoint nx ny nz → Prop)
    (interior : Finset (GPoint nx ny nz)) : Finset (GPoint nx ny nz) :=
  Finset.univ.filter fun p => p ∉ interior ∧ onBoundary p

/-- Cavity voxels: exterior voxels with no exterior path to a boundary seed. -/
def cavity (adj : GPoint nx ny nz → GPoint nx ny nz → Prop)
    (interior : Finset (GPoint nx ny nz)) : Finset (GPoint nx ny nz) :=
  Finset.univ.filter fun p =>
    p ∉ interior ∧ ¬ ∃ s ∈ boundaryExterior adj interior,
      Conn adj (fun x => x ∉ interior) s p

theorem cavity_subset_exterior {adj : GPoint nx ny nz → GPoint nx ny nz → Prop}
    {interior : Finset (GPoint nx ny nz)} :
    cavity adj interior ⊆ Finset.univ.filter fun p => p ∉ interior := by
  intro p hp
  have hxi : p ∉ interior := (Finset.mem_filter.mp hp).2.1
  simp [hxi]

theorem not_cavity_iff_conn {adj : GPoint nx ny nz → GPoint nx ny nz → Prop}
    {interior : Finset (GPoint nx ny nz)} {p : GPoint nx ny nz}
    (hp : p ∉ interior) :
    p ∉ cavity adj interior ↔
      ∃ s ∈ boundaryExterior adj interior, Conn adj (fun x => x ∉ interior) s p := by
  simp [cavity, hp]

theorem cavity_disjoint_boundary {adj : GPoint nx ny nz → GPoint nx ny nz → Prop}
    {interior : Finset (GPoint nx ny nz)} :
    Disjoint (cavity adj interior) (boundaryExterior adj interior) := by
  rw [Finset.disjoint_left]
  intro p hp hseed
  have hnot : ¬ ∃ s ∈ boundaryExterior adj interior,
      Conn adj (fun x => x ∉ interior) s p := (Finset.mem_filter.mp hp).2.2
  exact hnot ⟨p, hseed, conn_refl adj (fun x => x ∉ interior) p⟩

/-- The cavity mask value is `1` exactly on cavity voxels. -/
theorem cavityMask_eq_one_iff {adj : GPoint nx ny nz → GPoint nx ny nz → Prop}
    {interior : Finset (GPoint nx ny nz)} {p : GPoint nx ny nz} :
    (if p ∈ cavity adj interior then (1 : ℝ) else 0) = 1 ↔ p ∈ cavity adj interior := by
  by_cases h : p ∈ cavity adj interior <;> simp [h]

/-! ### Standard adjacencies -/

/-- 26-connectivity (face, edge and corner neighbours) on a dense grid. -/
def adj26 {nx ny nz : ℕ} (p q : GPoint nx ny nz) : Prop :=
  p ≠ q ∧
  |(p.1.val : ℤ) - q.1.val| ≤ 1 ∧
  |(p.2.1.val : ℤ) - q.2.1.val| ≤ 1 ∧
  |(p.2.2.val : ℤ) - q.2.2.val| ≤ 1

theorem adj26_symm {nx ny nz : ℕ} (p q : GPoint nx ny nz) :
    adj26 p q ↔ adj26 q p := by
  constructor <;> intro h <;> rcases h with ⟨hne, hx, hy, hz⟩
  · exact ⟨Ne.symm hne, by simpa [abs_sub_comm] using hx,
      by simpa [abs_sub_comm] using hy, by simpa [abs_sub_comm] using hz⟩
  · exact ⟨Ne.symm hne, by simpa [abs_sub_comm] using hx,
      by simpa [abs_sub_comm] using hy, by simpa [abs_sub_comm] using hz⟩

theorem adj6_symm_wrap {nx ny nz : ℕ} (p q : GPoint nx ny nz) :
    adj6 p q ↔ adj6 q p := adj6_symm p q

end Vdb
