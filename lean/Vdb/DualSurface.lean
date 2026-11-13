/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  The dual (DMC) surface as an oriented quad complex. A quad's four boundary
  edges are oriented; reversing the quad swaps every edge orientation, and a
  collection of quads is watertight when every oriented edge appears with its
  reverse (the shared edges cancel).

  `EdgeStencil` is the local stencil of the four cubes around a crossed
  primal edge; its quad is independent of the starting cube (rotation) and
  reverses when walked from the opposite side, which is exactly the
  watertightness hypothesis. This is the local part of the global dual
  surface; assembling all stencils into one closed complex is future work.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.DualVertex
import Vdb.LevelSet

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Vdb

/-- An oriented quad (four vertices in cyclic order). -/
structure Quad where
  v0 : Point
  v1 : Point
  v2 : Point
  v3 : Point

/-- The four oriented boundary edges of a quad. -/
def Quad.edges (q : Quad) : List (Point × Point) :=
  [(q.v0, q.v1), (q.v1, q.v2), (q.v2, q.v3), (q.v3, q.v0)]

/-- The same quad traversed in the opposite direction. -/
def Quad.reverse (q : Quad) : Quad :=
  ⟨q.v3, q.v2, q.v1, q.v0⟩

/-- The oriented edges of a finite quad collection. -/
def surfaceEdges (qs : List Quad) : List (Point × Point) :=
  qs.flatMap Quad.edges

/-- A quad collection is closed (watertight) when every oriented edge appears
    with its reverse: the shared edges cancel. -/
def Watertight (qs : List Quad) : Prop :=
  ∀ a b : Point, (a, b) ∈ surfaceEdges qs ↔ (b, a) ∈ surfaceEdges qs

/-- Reversing a quad's traversal swaps the orientation of every edge. -/
theorem Quad.mem_reverse_edges (q : Quad) (a b : Point) :
    (a, b) ∈ q.reverse.edges ↔ (b, a) ∈ q.edges := by
  obtain ⟨v0, v1, v2, v3⟩ := q
  simp only [Quad.reverse, Quad.edges, Prod.mk.injEq, List.mem_cons, List.not_mem_nil,
    or_false]
  tauto

theorem watertight_nil : Watertight [] := by
  intro a b
  simp [surfaceEdges, Watertight]

theorem watertight_pair (q : Quad) : Watertight [q, q.reverse] := by
  intro a b
  simp only [surfaceEdges, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append, Quad.mem_reverse_edges]
  tauto

theorem watertight_append {qs₁ qs₂ : List Quad} (h₁ : Watertight qs₁)
    (h₂ : Watertight qs₂) : Watertight (qs₁ ++ qs₂) := by
  intro a b
  simp only [surfaceEdges, List.flatMap_append, List.mem_append]
  exact or_congr (h₁ a b) (h₂ a b)

end Vdb

namespace Vdb

/-- The four dual vertices around a crossed primal edge, in cyclic order
    (the four cubes sharing the edge). -/
structure EdgeStencil where
  d0 : Point
  d1 : Point
  d2 : Point
  d3 : Point

/-- The dual quad of the stencil. -/
def EdgeStencil.quad (s : EdgeStencil) : Quad :=
  ⟨s.d0, s.d1, s.d2, s.d3⟩

/-- The same stencil walked from the opposite cube (reverse cyclic order). -/
def EdgeStencil.reverse (s : EdgeStencil) : EdgeStencil :=
  ⟨s.d3, s.d2, s.d1, s.d0⟩

/-- The same stencil with a different starting cube (cyclic rotation). -/
def EdgeStencil.rotate (s : EdgeStencil) : EdgeStencil :=
  ⟨s.d1, s.d2, s.d3, s.d0⟩

theorem EdgeStencil.reverse_quad (s : EdgeStencil) :
    s.reverse.quad = s.quad.reverse := rfl

/-- Starting the walk at a different cube gives the same quad edges. -/
theorem EdgeStencil.mem_rotate_edges (s : EdgeStencil) (a b : Point) :
    (a, b) ∈ s.rotate.quad.edges ↔ (a, b) ∈ s.quad.edges := by
  simp only [EdgeStencil.rotate, EdgeStencil.quad, Quad.edges, Prod.mk.injEq,
    List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- Walking the stencil from the opposite side reverses every quad edge. -/
theorem EdgeStencil.mem_reverse_edges (s : EdgeStencil) (a b : Point) :
    (a, b) ∈ s.reverse.quad.edges ↔ (b, a) ∈ s.quad.edges := by
  rw [EdgeStencil.reverse_quad]
  exact Quad.mem_reverse_edges s.quad a b

/-- **Local watertightness**: the two descriptions of the quad around a crossed
    primal edge (as seen from either side) cancel their shared edges. -/
theorem EdgeStencil.adjacent_quads_watertight (s : EdgeStencil) :
    Watertight [s.quad, s.reverse.quad] := by
  rw [EdgeStencil.reverse_quad]
  exact watertight_pair s.quad

end Vdb
