/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Homology-wall bridge group (§4.0 bounded tier): the mod-2 cubical boundary
  operator ∂ on a unit cube's cells. A chain is a Finset of cells over ZMod 2;
  ∂ is the symmetric difference of the cell boundaries. The module verifies
  ∂² = 0 for the unit cube (faces → edges → vertices and cube → faces → edges),
  the minimal algebraic bridge toward a cubical chain complex. The general
  Euler–Poincaré / duality theorem is not claimed.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Euler

namespace Vdb

namespace CubicalChainsBounded

abbrev Vertex := Int × Int × Int
abbrev Edge := Vertex × Vertex
abbrev Face := List Vertex
abbrev Cube := Vertex

def cubeVertices (c : Cube) : List Vertex :=
  [(c.1, c.2.1, c.2.2), (c.1+1, c.2.1, c.2.2),
   (c.1, c.2.1+1, c.2.2), (c.1+1, c.2.1+1, c.2.2),
   (c.1, c.2.1, c.2.2+1), (c.1+1, c.2.1, c.2.2+1),
   (c.1, c.2.1+1, c.2.2+1), (c.1+1, c.2.1+1, c.2.2+1)]

def cv (c : Cube) (n : Nat) : Vertex := (cubeVertices c)[n]!

def cubeEdges (c : Cube) : List Edge :=
  [(cv c 0, cv c 1), (cv c 2, cv c 3),
   (cv c 4, cv c 5), (cv c 6, cv c 7),
   (cv c 0, cv c 2), (cv c 1, cv c 3),
   (cv c 4, cv c 6), (cv c 5, cv c 7),
   (cv c 0, cv c 4), (cv c 1, cv c 5),
   (cv c 2, cv c 6), (cv c 3, cv c 7)]

def cubeFaces2 (c : Cube) : List Face :=
  [[cv c 0, cv c 1, cv c 3, cv c 2],
   [cv c 4, cv c 5, cv c 7, cv c 6],
   [cv c 0, cv c 1, cv c 5, cv c 4],
   [cv c 2, cv c 3, cv c 7, cv c 6],
   [cv c 0, cv c 2, cv c 6, cv c 4],
   [cv c 1, cv c 3, cv c 7, cv c 5]]

/-- Mod-2 boundary of a face: its four edges, with duplicate cancellation. -/
def mkEdge (a b : Vertex) : Edge := if a ≤ b then (a, b) else (b, a)

def faceEdges2 (f : Face) : Finset Edge :=
  let es := [mkEdge f[0]! f[1]!, mkEdge f[1]! f[2]!, mkEdge f[2]! f[3]!, mkEdge f[3]! f[0]!]
  es.foldl (fun s e => if e ∈ s then s.erase e else insert e s) ∅

/-- Mod-2 boundary of an edge: its two endpoints. -/
def edgeVerts2 (e : Edge) : Finset Vertex :=
  if e.1 == e.2 then ∅ else {e.1, e.2}

/-- Mod-2 boundary of a chain, lifted over a list of cells. -/
def boundary2 {α β : Type} [DecidableEq β] (cells : List α)
    (bd : α → Finset β) : Finset β :=
  cells.foldl (fun s a => (s \ bd a) ∪ (bd a \ s)) ∅

def faceEdgesList (f : Face) : List Edge :=
[mkEdge f[0]! f[1]!, mkEdge f[1]! f[2]!, mkEdge f[2]! f[3]!, mkEdge f[3]! f[0]!]

def d2_d1_zero : Bool :=
  let c : Cube := (0, 0, 0)
  (cubeFaces2 c).all fun f =>
    boundary2 (faceEdgesList f) edgeVerts2 = ∅

def d3_d2_zero : Bool :=
  let c : Cube := (0, 0, 0)
  boundary2 (cubeFaces2 c) faceEdges2 = ∅

theorem d2_d1_zero_true : d2_d1_zero = true := by native_decide

theorem d3_d2_zero_true : d3_d2_zero = true := by native_decide

end CubicalChainsBounded
end Vdb
