/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  End-to-end DMC on the concrete periodic cube grid: a scalar field is
  sampled at the lattice points, each cube's dual vertex is built from the
  crossings of its sign-changing edges (`crossing`/`dualVertex`), and the
  assembled index-quad surface is placed at those dual vertices. The result
  is the concrete `Watertight` surface of `Vdb/CubeGrid.lean`.

  The field `p.x - 1/2` changes sign across every `x`-edge, so every cube is
  mixed and the assembly is the eight-quad surface around the two `x = 0`
  sheets.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Vdb.CubeGrid
import Vdb.DualVertex
import Vdb.LevelSet

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Vdb

/-- Embed rational cube geometry into `Point`. -/
noncomputable def toPoint (q : Q3) : Point :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i => (q i : ℝ))

/-- The bit of `n` as a `Fin 2` increment. -/
def bit2 (n : Nat) : Fin 2 := if n % 2 = 1 then 1 else 0

/-- The lattice point at corner `k` of cube `c` (bits 0/1/2 = x/y/z). -/
def cornerOf (c : C3) (k : Fin 8) : C3 :=
  (c.1 + bit2 k.val, c.2.1 + bit2 (k.val / 2), c.2.2 + bit2 (k.val / 4))

/-- The scalar field `x - 1/2` at a lattice point. -/
def fieldVal (p : C3) : ℚ := (p.1.val : ℚ) - 1 / 2

/-- The sampled value at corner `k` of cube `c`. -/
def cubeVal (c : C3) (k : Fin 8) : ℚ := fieldVal (cornerOf c k)

/-- The sign-changing cube edges (the edges the surface crosses). -/
def cubeCrossings (c : C3) : List (Fin 8 × Fin 8) :=
  cubeEdges.filter (fun e => edgeCrosses (cubeVal c e.1) (cubeVal c e.2))

/-- The cube's dual vertex: the average of its crossed-edge crossings. -/
def cubeDualQ (c : C3) : Q3 :=
  Vdb.dualVertex (fun k => cubeVal c k) (cubeCrossings c)

/-- The cube's world-space anchor. -/
noncomputable def cubeAnchor (c : C3) : Q3
  | 0 => (c.1.val : ℚ)
  | 1 => (c.2.1.val : ℚ)
  | _ => (c.2.2.val : ℚ)

/-- The cube's dual vertex in world coordinates (anchor + local average). -/
noncomputable def cubeDual (c : C3) : Point :=
  toPoint (fun i => cubeAnchor c i + cubeDualQ c i)

/-- Every cube is mixed: the field `x - 1/2` gives it both a negative and a
    positive corner, so its dual vertex is a genuine average. -/
theorem cubeVal_mixed :
    ∀ c : C3, ∃ i j : Fin 8, isInside (cubeVal c i) ≠ isInside (cubeVal c j) := by
  intro c
  obtain ⟨x, y, z⟩ := c
  refine ⟨0, 1, ?_⟩
  fin_cases x <;> (simp [cubeVal, fieldVal, cornerOf, bit2, isInside]; norm_num)

/-- The end-to-end surface has the eight quads of the plane cut. -/
theorem stencilQuads_length : stencilQuads.length = 8 := by
  unfold stencilQuads crossedEdges allCubes
  decide

/-- **The end-to-end DMC surface**: the assembled index quads placed at the
    cubes' dual vertices are watertight. -/
theorem cubeDual_watertight :
    Watertight (stencilQuads.map (IxQuad.map cubeDual)) :=
  cubeStencil_watertight cubeDual


/-! ### Arbitrary sampled fields and a non-planar instance -/

/-- The sign-changing cube edges for an arbitrary sampled field. -/
def fieldCrossings (f : C3 → ℚ) (c : C3) : List (Fin 8 × Fin 8) :=
  cubeEdges.filter (fun e => edgeCrosses (f (cornerOf c e.1)) (f (cornerOf c e.2)))

def fieldDualQ (f : C3 → ℚ) (c : C3) : Q3 :=
  Vdb.dualVertex (fun k => f (cornerOf c k)) (fieldCrossings f c)

noncomputable def fieldDual (f : C3 → ℚ) (c : C3) : Point :=
  toPoint (fun i => cubeAnchor c i + fieldDualQ f c i)

/-- The index quads of a sign field's assembly. -/
def stencilQuadsOf (s : C3 → Bool) : List (IxQuad C3) :=
  (crossedEdges s).map fun e => edgeQuad e.1 e.2 (s e.1)

theorem edgeQuad_edges_agree : ∀ (p : C3) (d : Dir3) (flip : Bool),
    (edgeQuad p d flip).edges = (edgeLabels p d flip).map (dirEdge faceEnds) := by
  decide

theorem stencilQuadsOf_edges (s : C3 → Bool) :
    ixSurfaceEdges (stencilQuadsOf s) = (cubeStencil s).mesh := by
  unfold stencilQuadsOf ixSurfaceEdges StencilComplex.mesh StencilComplex.quads
    asmSurface cubeStencil
  induction crossedEdges s with
  | nil => rfl
  | cons e l ih => simp [ih, edgeQuad_edges_agree]

/-- A non-planar sampled field: one inside corner. -/
def bumpField : C3 → ℚ
  | (0, 0, 0) => -1
  | _ => 1

def bumpSign : C3 → Bool
  | (0, 0, 0) => true
  | _ => false

theorem bumpSign_iff : ∀ p : C3, bumpSign p = true ↔ bumpField p < 0 := by
  intro p
  obtain ⟨x, y, z⟩ := p
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [bumpSign, bumpField]

theorem bump_not_affine :
    bumpField (0, 0, 0) + bumpField (1, 1, 0) ≠
      bumpField (1, 0, 0) + bumpField (0, 1, 0) := by
  simp [bumpField]
  norm_num

theorem bumpStencil_balanced : (cubeStencil bumpSign).Balanced := by
  unfold StencilComplex.Balanced Vdb.Balanced faceUses StencilComplex.quads
    cubeStencil crossedEdges bumpSign
  decide

theorem bumpStencil_edgeClosed : EdgeClosed (cubeStencil bumpSign).mesh :=
  (cubeStencil bumpSign).watertight bumpStencil_balanced

theorem bumpDual_watertight :
    Watertight ((stencilQuadsOf bumpSign).map (IxQuad.map (fieldDual bumpField))) :=
  watertight_concrete_of_edges (by rw [stencilQuadsOf_edges]; exact bumpStencil_edgeClosed)
    (fieldDual bumpField)

end Vdb
