/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Global assembly of the dual (DMC) surface.

  The DMC construction produces one dual quad per crossed *primal* edge; the
  quads are glued along their edges by the primal faces. The assembly
  criterion is purely combinatorial: an *index* mesh is watertight when every
  directed index edge appears with its reverse. This module proves that

  * a combinatorially watertight index mesh becomes a watertight concrete
    quad surface under any vertex placement (`watertight_of_ix`; vertex
    collisions only merge index edges, preserving the symmetry), and

  * the box boundary — the simplest closed quad complex, and the local model
    of a closed dual patch — is watertight, verified exhaustively over the
    64 corner pairs (`boxFaces_ixWatertight`, `watertight_box`).

  So the DMC assembly only has to establish the primal edge/face incidence
  pairing; the geometric watertightness follows.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.DualSurface

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Vdb

structure IxQuad (ι : Type) where
  a : ι
  b : ι
  c : ι
  d : ι

def IxQuad.edges (q : IxQuad ι) : List (ι × ι) :=
  [(q.a, q.b), (q.b, q.c), (q.c, q.d), (q.d, q.a)]

def IxQuad.map (V : ι → Point) (q : IxQuad ι) : Quad :=
  ⟨V q.a, V q.b, V q.c, V q.d⟩

theorem IxQuad.mem_edges_of_mem_map_edges {ι : Type} (V : ι → Point) (q : IxQuad ι)
    {a b : Point} (h : (a, b) ∈ (q.map V).edges) :
    ∃ i j : ι, V i = a ∧ V j = b ∧ (i, j) ∈ q.edges := by
  obtain ⟨a', b', c', d'⟩ := q
  simp only [IxQuad.map, Quad.edges, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, _, rfl, rfl, by simp [IxQuad.edges]⟩
  · exact ⟨_, _, rfl, rfl, by simp [IxQuad.edges]⟩
  · exact ⟨_, _, rfl, rfl, by simp [IxQuad.edges]⟩
  · exact ⟨_, _, rfl, rfl, by simp [IxQuad.edges]⟩

theorem IxQuad.mem_map_edges_of_mem_edges {ι : Type} (V : ι → Point) (q : IxQuad ι)
    {i j : ι} (h : (i, j) ∈ q.edges) : (V i, V j) ∈ (q.map V).edges := by
  obtain ⟨a', b', c', d'⟩ := q
  simp only [IxQuad.edges, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [IxQuad.map, Quad.edges]

def ixSurfaceEdges (qs : List (IxQuad ι)) : List (ι × ι) :=
  qs.flatMap IxQuad.edges

def IxWatertight (qs : List (IxQuad ι)) : Prop :=
  ∀ i j : ι, (i, j) ∈ ixSurfaceEdges qs ↔ (j, i) ∈ ixSurfaceEdges qs

theorem mem_surfaceEdges_map_forward {ι : Type} (qs : List (IxQuad ι)) (V : ι → Point)
    {a b : Point} (h : (a, b) ∈ surfaceEdges (qs.map (IxQuad.map V))) :
    ∃ i j : ι, V i = a ∧ V j = b ∧ (i, j) ∈ ixSurfaceEdges qs := by
  unfold surfaceEdges at h
  induction qs with
  | nil => simp at h
  | cons q qs ih =>
    simp only [List.map_cons, List.flatMap_cons, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨i, j, hi, hj, hmem⟩ := IxQuad.mem_edges_of_mem_map_edges V q h
      exact ⟨i, j, hi, hj, by simp [ixSurfaceEdges, hmem]⟩
    · obtain ⟨i, j, hi, hj, hmem⟩ := ih h
      exact ⟨i, j, hi, hj, by
        simp only [ixSurfaceEdges, List.flatMap_cons, List.mem_append]
        exact Or.inr hmem⟩

theorem mem_surfaceEdges_map_backward {ι : Type} (qs : List (IxQuad ι)) (V : ι → Point)
    {i j : ι} (h : (i, j) ∈ ixSurfaceEdges qs) :
    (V i, V j) ∈ surfaceEdges (qs.map (IxQuad.map V)) := by
  unfold ixSurfaceEdges at h
  induction qs with
  | nil => simp at h
  | cons q qs ih =>
    simp only [List.flatMap_cons, List.mem_append] at h
    unfold surfaceEdges
    simp only [List.map_cons, List.flatMap_cons, List.mem_append]
    rcases h with h | h
    · exact Or.inl (IxQuad.mem_map_edges_of_mem_edges V q h)
    · exact Or.inr (ih h)

theorem watertight_of_ix {ι : Type} {qs : List (IxQuad ι)} (h : IxWatertight qs)
    (V : ι → Point) : Watertight (qs.map (IxQuad.map V)) := by
  intro a b
  constructor
  · intro hab
    obtain ⟨i, j, hi, hj, hmem⟩ := mem_surfaceEdges_map_forward qs V hab
    subst hi; subst hj
    exact mem_surfaceEdges_map_backward qs V ((h i j).mp hmem)
  · intro hba
    obtain ⟨i, j, hi, hj, hmem⟩ := mem_surfaceEdges_map_forward qs V hba
    subst hi; subst hj
    exact mem_surfaceEdges_map_backward qs V ((h i j).mp hmem)

end Vdb

namespace Vdb

/-- The six outward-oriented faces of the unit box, as index quads on the
    eight corners (`k` bit 0 = x, bit 1 = y, bit 2 = z). -/
def boxFaces : List (IxQuad (Fin 8)) :=
  [ ⟨0, 2, 3, 1⟩,   -- z = 0
    ⟨4, 5, 7, 6⟩,   -- z = 1
    ⟨0, 1, 5, 4⟩,   -- y = 0
    ⟨2, 6, 7, 3⟩,   -- y = 1
    ⟨0, 4, 6, 2⟩,   -- x = 0
    ⟨1, 3, 7, 5⟩ ]  -- x = 1

/-- The box boundary is combinatorially watertight: every directed corner
    edge appears with its reverse (checked exhaustively over the 64 pairs). -/
theorem boxFaces_ixWatertight : IxWatertight boxFaces := by
  unfold IxWatertight ixSurfaceEdges IxQuad.edges
  decide

/-- **A closed quad surface**: the box boundary is watertight under *any*
    placement of its eight corners in space. This is the concrete instance of
    the assembly lemma, and the same argument applies to any combinatorially
    closed DMC complex. -/
theorem watertight_box (V : Fin 8 → Point) :
    Watertight (boxFaces.map (IxQuad.map V)) :=
  watertight_of_ix boxFaces_ixWatertight V

end Vdb
