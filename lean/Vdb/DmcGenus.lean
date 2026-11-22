/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  The genus / connectivity content of the Euler characteristic of the
  DMC-0 cuberille mesh (`Vdb/PadGrid.lean`, `Vdb/QuadEulerPad.lean`,
  `Vdb/DmcNodup.lean`).

  What this module adds (no new axioms, pure cardinality algebra):

  * `chiEdges` — the Euler characteristic `V − E + F` of a quad mesh given
    by a directed edge list and a face count;
  * `chiEdges_append` / `chiEdges_flatten` — **additivity of χ over
    vertex-disjoint components**: if a family of closed quad surfaces has
    pairwise vertex-disjoint vertex sets, the χ of their concatenation is
    the sum of their χ's (vertices add by Finset union, edges add because
    an edge's endpoints lie in its vertex set, faces add by construction);
  * `IsSphereComponent` — a named package for "one component is a sphere at
    the level of χ": closed, duplicate-free, loop-free, `length = 4F` and
    `χ = 2` (the single-cell bump instance of this is the landed
    `DmcPinch.bump_euler_general`, which is deliberately **not** duplicated);
  * `chi_eq_two_mul_of_all_sphere` — if every component is sphere-like,
    `χ = 2 · #components`;
  * `chi_eq_two_mul_iff_all_chi_two` — under the explicit hypothesis that
    every component has `χ ≤ 2`, `χ = 2 · #components` **iff** every
    component has `χ = 2`. This is the χ-level reduction of "χ counts the
    components (spheres)"; the honest boundary is recorded in the doc of
    `chi_eq_two_mul_iff_all_chi_two`: no topological sphere / genus theory
    is formalised here, only the Euler-characteristic content.
  * `dmc0_chi_eq_sum_components` — the DMC-0 specialisation: for a
    checkerboard-free shell-pinned field, the χ of the assembled mesh
    (`V − F`) equals the sum of χ's of any vertex-disjoint decomposition
    of its directed edge list; the two sphere corollaries specialise the
    reductions to the actual DMC-0 mesh.

  The general `χ = 2 − 2g` statement and the topological "simply connected
  component" statement are out of reach in this slice (they need the
  orientability / homology machinery for the dual mesh); the counterexamples
  already in `Cuberille`/`DmcPinch` (pinched pairs with `χ = 3`) show that
  an upper bound per component is a necessary hypothesis for the iff.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.DmcNodup

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Vdb

namespace DmcGenus

open PadGrid

variable {ι : Type} [DecidableEq ι]

/-- The Euler characteristic of a quad mesh given by its directed edges and
    its number of faces: `χ = V − E + F`. -/
def chiEdges (es : List (ι × ι)) (F : Nat) : Int :=
  ((QuadEuler.vertices es).card : Int) - ((QuadEuler.undirected es).card : Int) + (F : Int)

/-! ### Vertex / edge bookkeeping under concatenation -/

/-- The tail of a directed edge is a mesh vertex. -/
theorem tail_mem_vertices {es : List (ι × ι)} {a b : ι} (hab : (a, b) ∈ es) :
    a ∈ QuadEuler.vertices es := by
  simp only [QuadEuler.vertices, List.mem_toFinset, List.mem_map]
  exact ⟨(a, b), hab, rfl⟩

/-- In a closed directed-edge list the head of every edge is also a tail of
    some edge, hence a mesh vertex. -/
theorem head_mem_vertices {es : List (ι × ι)} (hcl : EdgeClosed es) {a b : ι}
    (hab : (a, b) ∈ es) : b ∈ QuadEuler.vertices es := by
  apply tail_mem_vertices
  exact (hcl a b).mp hab

/-- Vertices of a concatenation are the union of the vertex sets. -/
theorem vertices_append (es₁ es₂ : List (ι × ι)) :
    QuadEuler.vertices (es₁ ++ es₂) =
      QuadEuler.vertices es₁ ∪ QuadEuler.vertices es₂ := by
  simp [QuadEuler.vertices]

/-- Undirected edges of a concatenation are the union of the edge sets. -/
theorem undirected_append (es₁ es₂ : List (ι × ι)) :
    QuadEuler.undirected (es₁ ++ es₂) =
      QuadEuler.undirected es₁ ∪ QuadEuler.undirected es₂ := by
  simp [QuadEuler.undirected]

/-- Closed quad surfaces with disjoint vertex sets also have disjoint
    undirected edge sets: both endpoints of a used edge are vertices (the
    head by closure), so a shared edge would give a shared vertex. -/
theorem undirected_disjoint_of_vertices_disjoint {es₁ es₂ : List (ι × ι)}
    (hcl₁ : EdgeClosed es₁) (hcl₂ : EdgeClosed es₂)
    (hv : Disjoint (QuadEuler.vertices es₁) (QuadEuler.vertices es₂)) :
    Disjoint (QuadEuler.undirected es₁) (QuadEuler.undirected es₂) := by
  rw [Finset.disjoint_left]
  intro t ht₁ ht₂
  simp only [QuadEuler.undirected, List.mem_toFinset, List.mem_map] at ht₁ ht₂
  obtain ⟨e₁, he₁, rfl⟩ := ht₁
  obtain ⟨e₂, he₂, heq⟩ := ht₂
  rcases e₁ with ⟨a, b⟩
  rcases e₂ with ⟨c, d⟩
  simp only [QuadEuler.unord] at heq
  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (Finset.disjoint_left.mp hv) (head_mem_vertices hcl₁ he₁) (head_mem_vertices hcl₂ he₂)
  · exact (Finset.disjoint_left.mp hv) (head_mem_vertices hcl₁ he₁) (tail_mem_vertices he₂)

/-- Closure is preserved under concatenation. -/
theorem edgeClosed_append {es₁ es₂ : List (ι × ι)} (h₁ : EdgeClosed es₁)
    (h₂ : EdgeClosed es₂) : EdgeClosed (es₁ ++ es₂) := by
  intro a b
  simp only [List.mem_append]
  constructor <;> intro h
  · rcases h with h | h
    · exact Or.inl ((h₁ a b).mp h)
    · exact Or.inr ((h₂ a b).mp h)
  · rcases h with h | h
    · exact Or.inl ((h₁ a b).mpr h)
    · exact Or.inr ((h₂ a b).mpr h)

/-- **Two-piece additivity**:χ is additive over two closed quad surfaces with
    disjoint vertex sets. -/
theorem chiEdges_append (es₁ es₂ : List (ι × ι)) (F₁ F₂ : Nat)
    (hcl₁ : EdgeClosed es₁) (hcl₂ : EdgeClosed es₂)
    (hv : Disjoint (QuadEuler.vertices es₁) (QuadEuler.vertices es₂)) :
    chiEdges (es₁ ++ es₂) (F₁ + F₂) = chiEdges es₁ F₁ + chiEdges es₂ F₂ := by
  have hV := vertices_append es₁ es₂
  have hE := undirected_append es₁ es₂
  have hEd := undirected_disjoint_of_vertices_disjoint hcl₁ hcl₂ hv
  have hVc : ((QuadEuler.vertices es₁ ∪ QuadEuler.vertices es₂).card : Int) =
      (QuadEuler.vertices es₁).card + (QuadEuler.vertices es₂).card := by
    have h := Finset.card_union_add_card_inter (QuadEuler.vertices es₁) (QuadEuler.vertices es₂)
    rw [Finset.disjoint_iff_inter_eq_empty.mp hv, Finset.card_empty] at h
    omega
  have hEc : ((QuadEuler.undirected es₁ ∪ QuadEuler.undirected es₂).card : Int) =
      (QuadEuler.undirected es₁).card + (QuadEuler.undirected es₂).card := by
    have h := Finset.card_union_add_card_inter (QuadEuler.undirected es₁) (QuadEuler.undirected es₂)
    rw [Finset.disjoint_iff_inter_eq_empty.mp hEd, Finset.card_empty] at h
    omega
  unfold chiEdges
  rw [hV, hE, hVc, hEc]
  omega

/-! ### Additivity over an arbitrary finite family of components -/

/-- Vertices of a flattened family equal the fold of the vertex sets. -/
theorem vertices_flatten (ps : List (List (ι × ι))) :
    QuadEuler.vertices ps.flatten =
      ps.foldr (fun p acc => QuadEuler.vertices p ∪ acc) ∅ := by
  induction ps with
  | nil => simp [QuadEuler.vertices]
  | cons p ps ih =>
      simp [List.flatten_cons, vertices_append, ih]

/-- Membership in that fold: a vertex is in the fold iff it is a vertex of
    one of the component meshes. -/
theorem mem_vertsFold {v : ι} {ps : List (List (ι × ι))} :
    v ∈ ps.foldr (fun p acc => QuadEuler.vertices p ∪ acc) ∅
      ↔ ∃ q ∈ ps, v ∈ QuadEuler.vertices q := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp [ih]

/-- Closure of a flattened family. -/
theorem edgeClosed_flatten (ps : List (List (ι × ι)))
    (hcl : ∀ p ∈ ps, EdgeClosed p) : EdgeClosed ps.flatten := by
  induction ps with
  | nil => simp [EdgeClosed]
  | cons p ps ih =>
      have hp : EdgeClosed p := hcl p (by simp)
      have hps : ∀ q ∈ ps, EdgeClosed q := fun q hq => hcl q (by simp [hq])
      rw [List.flatten_cons]
      exact edgeClosed_append hp (ih hps)

/-- **Additivity of χ over vertex-disjoint components** (every finite
    family): if each component is closed and the component meshes are
    pairwise vertex-disjoint, the χ of their concatenation is the sum of
    the individual χ's. -/
theorem chiEdges_flatten (ps : List (List (ι × ι) × Nat))
    (hcl : ∀ p ∈ ps, EdgeClosed p.1)
    (hpw : (ps.map Prod.fst).Pairwise
      (fun es₁ es₂ => Disjoint (QuadEuler.vertices es₁) (QuadEuler.vertices es₂))) :
    chiEdges (ps.map Prod.fst).flatten ((ps.map Prod.snd).sum) =
      (ps.map fun p => chiEdges p.1 p.2).sum := by
  induction ps with
  | nil => simp [chiEdges, QuadEuler.vertices, QuadEuler.undirected]
  | cons p ps ih =>
      rcases p with ⟨es, F⟩
      simp only [List.map_cons] at hpw ⊢
      rcases List.pairwise_cons.mp hpw with ⟨hhead, htail⟩
      have hcl_es : EdgeClosed es := hcl (es, F) (by simp)
      have hcl_ps : ∀ p ∈ ps, EdgeClosed p.1 := fun p hp => hcl p (by simp [hp])
      have hcl_ps' : ∀ q ∈ ps.map Prod.fst, EdgeClosed q := fun q hq => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        exact hcl p (by simp [hp])
      have hcl_flat : EdgeClosed (ps.map Prod.fst).flatten := edgeClosed_flatten _ hcl_ps'
      have ih' := ih hcl_ps htail
      have hv : Disjoint (QuadEuler.vertices es)
          (QuadEuler.vertices (ps.map Prod.fst).flatten) := by
        rw [vertices_flatten, Finset.disjoint_right]
        intro v hvflat hves
        rw [mem_vertsFold] at hvflat
        obtain ⟨q, hqmem, hvq⟩ := hvflat
        exact (Finset.disjoint_left.mp (hhead q hqmem)) hves hvq
      simp only [List.flatten_cons, List.sum_cons]
      rw [chiEdges_append es ((ps.map Prod.fst).flatten) F ((ps.map Prod.snd).sum)
        hcl_es hcl_flat hv, ih']

/-! ### The genus / connectivity reduction -/

/-- A component is **sphere-like** when it is a closed, duplicate-free,
    loop-free quad surface with `length = 4F` and Euler characteristic `2`.
    This is exactly the χ-level content of "a sphere"; no topology is
    asserted. (The single-cell bump instance is `DmcPinch.bump_euler_general`. ) -/
def IsSphereComponent (es : List (ι × ι)) (F : Nat) : Prop :=
  EdgeClosed es ∧ es.Nodup ∧ (∀ a b, (a, b) ∈ es → a ≠ b) ∧
    es.length = 4 * F ∧ chiEdges es F = 2

/-- The sum of the χ's of a family all of whose members have χ = 2 is
    `2 · #components`. -/
theorem sum_chi_eq_two_mul_length (ps : List (List (ι × ι) × Nat))
    (hchi : ∀ p ∈ ps, chiEdges p.1 p.2 = 2) :
    (ps.map fun p => chiEdges p.1 p.2).sum = 2 * (ps.length : Int) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hp : chiEdges p.1 p.2 = 2 := hchi p (by simp)
      have hps : ∀ q ∈ ps, chiEdges q.1 q.2 = 2 := fun q hq => hchi q (by simp [hq])
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [hp, ih hps]
      ring

/-- If every component is sphere-like, the χ of the assembled mesh is
    `2 · (#components)`. -/
theorem chi_eq_two_mul_of_all_sphere (ps : List (List (ι × ι) × Nat))
    (hcl : ∀ p ∈ ps, EdgeClosed p.1)
    (hpw : (ps.map Prod.fst).Pairwise
      (fun es₁ es₂ => Disjoint (QuadEuler.vertices es₁) (QuadEuler.vertices es₂)))
    (hs : ∀ p ∈ ps, IsSphereComponent p.1 p.2) :
    chiEdges (ps.map Prod.fst).flatten ((ps.map Prod.snd).sum) =
      2 * (ps.length : Int) := by
  rw [chiEdges_flatten ps hcl hpw]
  exact sum_chi_eq_two_mul_length ps (fun p hp => (hs p hp).2.2.2.2)

/-- Each component's χ is at most the sum, provided every component has
    χ ≤ 2. -/
theorem sum_chi_le_two_mul_length (ps : List (List (ι × ι) × Nat))
    (hup : ∀ p ∈ ps, chiEdges p.1 p.2 ≤ 2) :
    (ps.map fun p => chiEdges p.1 p.2).sum ≤ 2 * (ps.length : Int) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hp : chiEdges p.1 p.2 ≤ 2 := hup p (by simp)
      have hps : ∀ q ∈ ps, chiEdges q.1 q.2 ≤ 2 := fun q hq => hup q (by simp [hq])
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      have := ih hps
      omega

/-- A family of integers each ≤ 2 sums to `2 · #family` iff each is `2`. -/
theorem sum_eq_two_mul_length_iff_of_le (ps : List (List (ι × ι) × Nat))
    (hup : ∀ p ∈ ps, chiEdges p.1 p.2 ≤ 2) :
    (ps.map fun p => chiEdges p.1 p.2).sum = 2 * (ps.length : Int)
      ↔ ∀ p ∈ ps, chiEdges p.1 p.2 = 2 := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hp : chiEdges p.1 p.2 ≤ 2 := hup p (by simp)
      have hps : ∀ q ∈ ps, chiEdges q.1 q.2 ≤ 2 := fun q hq => hup q (by simp [hq])
      have ih' := ih hps
      have hrest_le := sum_chi_le_two_mul_length ps hps
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      constructor
      · intro hsum p' hp'
        have hc : chiEdges p.1 p.2 = 2 := by omega
        have hrest : (ps.map fun q => chiEdges q.1 q.2).sum = 2 * (ps.length : Int) := by omega
        rcases List.mem_cons.mp hp' with rfl | hp'mem
        · exact hc
        · exact ih'.mp hrest p' hp'mem
      · intro hall
        have hc : chiEdges p.1 p.2 = 2 := hall p (by simp)
        have hrest : ∀ q ∈ ps, chiEdges q.1 q.2 = 2 := fun q hq => hall q (by simp [hq])
        rw [hc, ih'.mpr hrest]
        ring

/-- **The χ-level genus/connectivity reduction.** Under the explicit
    hypothesis that every component has χ ≤ 2, `χ = 2 · #components` holds
    iff every component has χ = 2 (i.e. every component is sphere-like at
    the level of χ).

    Honest boundary: this is a statement about the *integer* χ of a
    vertex-disjoint decomposition, not a topological classification. No
    orientability, planar-graph embedding, or homology/gTheory is formalised,
    and `χ = 2 − 2g` for a genus-`g` component is not claimed. The per-
    component upper bound is necessary: the antipodal pair of `DmcPinch` is
    one connected mesh with `χ = 3 > 2`. -/
theorem chi_eq_two_mul_iff_all_chi_two (ps : List (List (ι × ι) × Nat))
    (hcl : ∀ p ∈ ps, EdgeClosed p.1)
    (hpw : (ps.map Prod.fst).Pairwise
      (fun es₁ es₂ => Disjoint (QuadEuler.vertices es₁) (QuadEuler.vertices es₂)))
    (hup : ∀ p ∈ ps, chiEdges p.1 p.2 ≤ 2) :
    chiEdges (ps.map Prod.fst).flatten ((ps.map Prod.snd).sum) = 2 * (ps.length : Int)
      ↔ ∀ p ∈ ps, chiEdges p.1 p.2 = 2 := by
  rw [chiEdges_flatten ps hcl hpw]
  exact sum_eq_two_mul_length_iff_of_le ps hup

/-! ### The DMC-0 specialisation -/

/-- The χ of the assembled DMC-0 mesh equals `chiEdges mesh (crossed.length)`,
    for a checkerboard-free shell-pinned field (`euler_of_noCheckerboard`). -/
theorem dmc0_chiEdges (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hnc : ∀ f : PadGrid.Face, InCells n f.1 → f.2 < 3 → ¬ Checkerboard s f) :
    chiEdges (cuberilleStencil n s).mesh (crossed n s).length =
      ((QuadEuler.vertices (cuberilleStencil n s).mesh).card : Int) -
        (crossed n s).length := by
  simpa [chiEdges] using (euler_of_noCheckerboard n s hpin hnc).2

/-- **Additivity of χ over vertex-disjoint components of the DMC-0 mesh**:
    if the directed mesh of a checkerboard-free shell-pinned field is the
    concatenation of a vertex-disjoint family of closed quad surfaces (and
    the face counts add), then `V − F` is the sum of the components' χ's. -/
theorem dmc0_chi_eq_sum_components (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hnc : ∀ f : PadGrid.Face, InCells n f.1 → f.2 < 3 → ¬ Checkerboard s f)
    (ps : List (List (Cell × Cell) × Nat))
    (hcat : (cuberilleStencil n s).mesh = (ps.map Prod.fst).flatten)
    (hF : (crossed n s).length = (ps.map Prod.snd).sum)
    (hcl : ∀ p ∈ ps, EdgeClosed p.1)
    (hpw : (ps.map Prod.fst).Pairwise
      (fun es₁ es₂ => Disjoint (QuadEuler.vertices es₁) (QuadEuler.vertices es₂))) :
    ((QuadEuler.vertices (cuberilleStencil n s).mesh).card : Int) -
        (crossed n s).length =
      (ps.map fun p => chiEdges p.1 p.2).sum := by
  have h0 := dmc0_chiEdges n s hpin hnc
  rw [hcat, hF] at h0 ⊢
  rw [chiEdges_flatten ps hcl hpw] at h0
  exact h0.symm

/-- DMC-0 specialisation of `chi_eq_two_mul_of_all_sphere`: a checkerboard-
    free shell-pinned field whose directed mesh splits into vertex-disjoint
    sphere-like components has `χ = 2 · #components`. -/
theorem dmc0_chi_eq_two_mul_of_all_sphere (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hnc : ∀ f : PadGrid.Face, InCells n f.1 → f.2 < 3 → ¬ Checkerboard s f)
    (ps : List (List (Cell × Cell) × Nat))
    (hcat : (cuberilleStencil n s).mesh = (ps.map Prod.fst).flatten)
    (hF : (crossed n s).length = (ps.map Prod.snd).sum)
    (hpw : (ps.map Prod.fst).Pairwise
      (fun es₁ es₂ => Disjoint (QuadEuler.vertices es₁) (QuadEuler.vertices es₂)))
    (hs : ∀ p ∈ ps, IsSphereComponent p.1 p.2) :
    ((QuadEuler.vertices (cuberilleStencil n s).mesh).card : Int) -
        (crossed n s).length = 2 * (ps.length : Int) := by
  rw [dmc0_chi_eq_sum_components n s hpin hnc ps hcat hF
    (fun p hp => (hs p hp).1) hpw]
  exact sum_chi_eq_two_mul_length ps (fun p hp => (hs p hp).2.2.2.2)

end DmcGenus

end Vdb
