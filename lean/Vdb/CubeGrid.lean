/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  A concrete instantiation of the dual-surface assembly on a periodic cube
  grid. The grid is a `2 x 2 x 2` torus of unit cubes; a primal edge is an
  anchor plus a direction, and its four surrounding primal faces are given by
  the uniform cyclic formula

  * `i = next d`, `j = next² d`,
  * faces `(p - e_j, i)`, `(p, j)`, `(p, i)`, `(p - e_i, j)` with the
    directions a dual quad walks them.

  The sign field `p.x = 0` crosses exactly the four `x`-edges at `x = 0`; the
  emitted assembly is balanced (each primal face is used once in each
  direction) and therefore closed (`EdgeClosed`), and the same quads, viewed
  as `IxQuad`s, are watertight under any vertex placement.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Assembly
import Vdb.DualVertex

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Vdb

/-- A lattice point / cube index of the `2 x 2 x 2` periodic grid. -/
abbrev C3 : Type := Fin 2 × Fin 2 × Fin 2

/-- A primal direction. -/
abbrev Dir3 : Type := Fin 3

/-- A primal face: an anchor plus the normal direction. -/
abbrev FaceIdx : Type := C3 × Dir3

/-- A primal edge: an anchor plus its direction. -/
abbrev EdgeIdx : Type := C3 × Dir3

/-- Step one unit in direction `d`, periodically (`2` is the period). -/
def step (p : C3) (d : Dir3) : C3 :=
  match d with
  | 0 => (p.1 + 1, p.2.1, p.2.2)
  | 1 => (p.1, p.2.1 + 1, p.2.2)
  | _ => (p.1, p.2.1, p.2.2 + 1)

/-- The next direction cyclically. -/
def nextDir : Dir3 → Dir3
  | 0 => 1
  | 1 => 2
  | _ => 0

/-- The direction after the next cyclically. -/
def nextDir2 : Dir3 → Dir3
  | 0 => 2
  | 1 => 0
  | _ => 1

/-- The two cubes adjacent to a primal face: the cube at the anchor and the
    cube on the other side. -/
def faceEnds (f : FaceIdx) : C3 × C3 := (f.1, step f.1 f.2)

/-- The four labeled faces around a primal edge, in the cyclic order in which
    the dual quad visits them. `flip` swaps the perpendicular directions,
    which reverses the cycle: the quad is oriented counter-clockwise around
    the edge direction when `flip` is set (the edge starts inside). -/
def edgeLabels (p : C3) (d : Dir3) (flip : Bool) : List (LabeledEdge FaceIdx) :=
  let i := if flip then nextDir2 d else nextDir d
  let j := if flip then nextDir d else nextDir2 d
  [⟨(step p j, i), false⟩, ⟨(p, j), false⟩, ⟨(p, i), true⟩,
   ⟨(step p i, j), true⟩]

/-- The four cubes around a primal edge, in the same cyclic order. -/
def edgeCubes (p : C3) (d : Dir3) (flip : Bool) : C3 × C3 × C3 × C3 :=
  let i := if flip then nextDir2 d else nextDir d
  let j := if flip then nextDir d else nextDir2 d
  (step (step p i) j, step p j, p, step p i)

/-- The dual quad of a primal edge as an index quad. -/
def edgeQuad (p : C3) (d : Dir3) (flip : Bool) : IxQuad C3 :=
  let c := edgeCubes p d flip
  ⟨c.1, c.2.1, c.2.2.1, c.2.2.2⟩

/-- All eight lattice points. -/
def allCubes : List C3 :=
  [0, 1].product ([0, 1].product [0, 1]) |>.map fun x => (x.1, x.2.1, x.2.2)

/-- A primal edge is crossed when its endpoints have different signs. -/
def isCrossed (s : C3 → Bool) (e : EdgeIdx) : Bool :=
  s e.1 != s (step e.1 e.2)

/-- The crossed primal edges of the grid. -/
def crossedEdges (s : C3 → Bool) : List EdgeIdx :=
  (allCubes.product (List.finRange 3)).filter (fun e => isCrossed s e)

/-- The concrete stencil complex of the grid. -/
def cubeStencil (s : C3 → Bool) : StencilComplex C3 FaceIdx EdgeIdx :=
  { ends := faceEnds
    edgeFaces := fun e => edgeLabels e.1 e.2 (s e.1)
    crossedEdges := crossedEdges s }

/-- The plane sign field `x = 0`. -/
def signX (p : C3) : Bool := p.1 == 0

/-- **The concrete assembly is balanced**: for the plane sign field, every
    primal face is used once in each direction (checked by evaluation). -/
theorem cubeStencil_balanced :
    (cubeStencil signX).Balanced := by
  unfold StencilComplex.Balanced Balanced faceUses StencilComplex.quads
  decide

/-- **The concrete assembled dual surface is closed** (every directed edge
    appears with its reverse). -/
theorem cubeStencil_edgeClosed :
    EdgeClosed (cubeStencil signX).mesh :=
  (cubeStencil signX).watertight cubeStencil_balanced

/-- The emitted quads as index quads. -/
def stencilQuads : List (IxQuad C3) :=
  (crossedEdges signX).map fun e => edgeQuad e.1 e.2 (signX e.1)

/-- The index quads have exactly the assembled edge set. -/
theorem stencilQuads_edges :
    ixSurfaceEdges stencilQuads = (cubeStencil signX).mesh := by
  unfold stencilQuads ixSurfaceEdges StencilComplex.mesh StencilComplex.quads
    asmSurface crossedEdges cubeStencil edgeQuad edgeLabels edgeCubes faceEnds dirEdge
  decide

/-- **The concrete dual surface is watertight** under any placement of the
    grid's dual vertices. -/
theorem cubeStencil_watertight (V : C3 → Point) :
    Watertight (stencilQuads.map (IxQuad.map V)) :=
  watertight_concrete_of_edges (by rw [stencilQuads_edges]; exact cubeStencil_edgeClosed) V

end Vdb
