/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  The cuberille / DMC (surface-nets) assembly on a **bounded padded grid**
  — the standard construction with signs sampled at lattice points:

  * signs live on a `4 x 4 x 4` lattice of sample points; the boundary
    shell is pinned to `false` (the “outside” sign), so the surface never
    reaches the shell and every crossed lattice edge is surrounded by all
    four cells;
  * cells are the `3 x 3 x 3` unit cubes between the samples;
  * each sign-changing lattice edge emits one quad through the four cells
    around it;
  * cell faces (a cell plus a direction) are shared by exactly the two
    cells they separate; shell-facing faces pair a cell with itself as a
    dummy and never receive uses (every crossed edge is interior, and all
    its labeled faces pair two distinct cells).

  This is the construction in which `T-DMC0-CYCLE` is actually true on a
  bounded grid. The landed `Vdb/CubeGrid.lean` Fin 2 torus model (signs on
  cells, involutive step) is *not* generalizable: on bounded padded grids
  the assembled quad mesh is watertight only for the all-outside sign
  field — see `lean/VERIFICATION.md` (finding F17).

  What is proved here:

  * `facePerimeter_even` — every cell face's 4-cycle of corner signs has
    an even number of sign changes, for any sign field (grid-independent
    content, the `evenSignChanges4` core);
  * `balanced_of_padded` / `edgeClosed_of_padded` — **every** sign field
    pinned to `false` on the shell yields a balanced assembly, hence a
    watertight (`EdgeClosed`) one; machine-checked over all `2 ^ 8`
    interior sign fields (`native_decide`);
  * `paddedStencil_watertight` — the `Watertight` consequence under any
    vertex placement of the cells.

  What is not proved: the same theorem for arbitrary `n` (the proof is
  the same 4-cycle parity plus a per-face direction-alternation argument;
  landing it needs the generic bounded-grid lattice, not the concrete
  `Fin` triple). The 256-field exhaustive check covers the corner cases
  one generation deeper than the single-cell cases the DMC-1 analysis
  used.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Assembly
import Vdb.DualVertex
import Vdb.DmcManifold
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Vdb

namespace Cuberille

/-! ### The bounded model -/

/-- Sample points of the `4 x 4 x 4` lattice; the shell carries the outside sign. -/
abbrev Lat : Type := Fin 4 × Fin 4 × Fin 4
/-- Cells of the `3 x 3 x 3` cell grid between the samples. -/
abbrev Cell : Type := Fin 3 × Fin 3 × Fin 3
/-- A primal face: a cell anchor plus its normal direction. -/
abbrev Face : Type := Cell × Fin 3
/-- A primal lattice edge: an anchor plus its direction. -/
abbrev PadEdge : Type := Lat × Fin 3

/-- The interior sign field with index `k`: bit `j` of `k` is the sign at the
    `j`-th interior lattice point (lexicographic order), bit 0 = `(1,1,1)`.
    `k` ranges over `0..255`, enumerating all `2^8 = 256` shell-pinned fields. -/
def latSignOf (k : Nat) (p : Lat) : Bool :=
  if p.1.val = 1 ∧ p.2.1.val = 1 ∧ p.2.2.val = 1 then k / 1 % 2 = 1
  else if p.1.val = 1 ∧ p.2.1.val = 1 ∧ p.2.2.val = 2 then k / 2 % 2 = 1
  else if p.1.val = 1 ∧ p.2.1.val = 2 ∧ p.2.2.val = 1 then k / 4 % 2 = 1
  else if p.1.val = 1 ∧ p.2.1.val = 2 ∧ p.2.2.val = 2 then k / 8 % 2 = 1
  else if p.1.val = 2 ∧ p.2.1.val = 1 ∧ p.2.2.val = 1 then k / 16 % 2 = 1
  else if p.1.val = 2 ∧ p.2.1.val = 1 ∧ p.2.2.val = 2 then k / 32 % 2 = 1
  else if p.1.val = 2 ∧ p.2.1.val = 2 ∧ p.2.2.val = 1 then k / 64 % 2 = 1
  else if p.1.val = 2 ∧ p.2.1.val = 2 ∧ p.2.2.val = 2 then k / 128 % 2 = 1
  else false

/-- All 256 shell-pinned sign fields. -/
def allPaddedSignFields : List (Lat → Bool) :=
  (List.range 256).map latSignOf

def latAll : List Lat :=
  (List.finRange 4).product ((List.finRange 4).product (List.finRange 4))
    |>.map fun x => (x.1, x.2.1, x.2.2)

def cellAll : List Cell :=
  (List.finRange 3).product ((List.finRange 3).product (List.finRange 3))
    |>.map fun x => (x.1, x.2.1, x.2.2)

def cellOfNat (x y z : Nat) : Cell :=
  (⟨x % 3, by omega⟩, ⟨⟨y % 3, by omega⟩, ⟨z % 3, by omega⟩⟩)

/-- In-range step, clamped. -/
def addCell (c : Cell) (d : Fin 3) : Cell :=
  match d with
  | 0 => cellOfNat (min 2 (c.1.val + 1)) c.2.1.val c.2.2.val
  | 1 => cellOfNat c.1.val (min 2 (c.2.1.val + 1)) c.2.2.val
  | _ => cellOfNat c.1.val c.2.1.val (min 2 (c.2.2.val + 1))

/-- In-range step of a cell, `none` at the boundary. -/
def cellStep (p : Cell) (d : Fin 3) : Option Cell :=
  match d with
  | 0 => if h : p.1.val + 1 < 3 then some (⟨p.1.val + 1, h⟩, p.2) else none
  | 1 => if h : p.2.1.val + 1 < 3 then some (p.1, ⟨p.2.1.val + 1, h⟩, p.2.2) else none
  | _ => if h : p.2.2.val + 1 < 3 then some (p.1, p.2.1, ⟨p.2.2.val + 1, h⟩) else none

/-- The two cells of a face; shell-facing faces pair a cell with itself
    (dummy — they never receive uses; see `no_shell_uses`). -/
def faceEnds (f : Face) : Cell × Cell :=
  match cellStep f.1 f.2 with
  | some q => (f.1, q)
  | none => (f.1, f.1)

def fin4 (n : Nat) : Fin 4 := ⟨n % 4, by omega⟩

/-- Successor of a lattice point (in range only; `crossed` filters). -/
def latNext (p : Lat) (d : Fin 3) : Lat :=
  match d with
  | 0 => (fin4 (p.1.val + 1), p.2)
  | 1 => (p.1, fin4 (p.2.1.val + 1), p.2.2)
  | _ => (p.1, p.2.1, fin4 (p.2.2.val + 1))

/-- The crossed lattice edges of a shell-pinned field. Crossed edges are
    interior to the lattice frame (the shell is all-outside). -/
def crossed (s : Lat → Bool) : List PadEdge :=
  latAll.flatMap fun p =>
    (List.finRange 3).filterMap fun d =>
      let ok : Bool := match d with
        | 0 => p.1.val + 1 < 4
        | 1 => p.2.1.val + 1 < 4
        | _ => p.2.2.val + 1 < 4
      if ok && (s p != s (latNext p d)) then some (p, d) else none

/-- The anchor cell of a crossed edge: the transverse-lower-left cell.
    For a crossed edge the transverse coordinates are at least `1` and at
    most `2`, so the anchor is a genuine cell. -/
def anchorCell (p : Lat) (d : Fin 3) : Cell :=
  match d with
  | 0 => cellOfNat p.1.val (p.2.1.val - 1) (p.2.2.val - 1)
  | 1 => cellOfNat (p.1.val - 1) p.2.1.val (p.2.2.val - 1)
  | _ => cellOfNat (p.1.val - 1) (p.2.1.val - 1) p.2.2.val

/-- The two in-plane directions of an edge, swapped under `flip`. -/
def ij (d : Fin 3) (flip : Bool) : Fin 3 × Fin 3 :=
  match d with
  | 0 => if flip then (2, 1) else (1, 2)
  | 1 => if flip then (0, 2) else (2, 0)
  | _ => if flip then (1, 0) else (0, 1)

/-- The quad's labeled faces; the torus convention, rooted at the
    transverse-lower-left anchor cell. -/
def labels (p : Lat) (d : Fin 3) (flip : Bool) : List (LabeledEdge Face) :=
  let (i, j) := ij d flip
  let q := anchorCell p d
  [⟨(addCell q j, i), false⟩, ⟨(q, j), false⟩, ⟨(q, i), true⟩,
   ⟨(addCell q i, j), true⟩]

/-- The cuberille/DMC assembly of a sign field: one quad per crossed
    lattice edge. -/
def cuberilleStencil (s : Lat → Bool) : StencilComplex Cell Face PadEdge :=
  { ends := faceEnds
    edgeFaces := fun e => labels e.1 e.2 (s e.1)
    crossedEdges := crossed s }

/-! ### The parity theorem (any sign field) -/

/-- The four corner signs of a cell face's 4-cycle, as lattice points
    (Fin-4 samples). The face `(c, d)` is the face between cell `c` and
    the adjacent cell in direction `d`. -/
def perimeterCorners (f : Face) : Lat × Lat × Lat × Lat :=
  let c := f.1
  let cx := c.1.val; let cy := c.2.1.val; let cz := c.2.2.val
  match f.2 with
  | 0 =>
      ((fin4 (cx + 1), fin4 cy, fin4 cz),
       (fin4 (cx + 1), fin4 (cy + 1), fin4 cz),
       (fin4 (cx + 1), fin4 cy, fin4 (cz + 1)),
       (fin4 (cx + 1), fin4 (cy + 1), fin4 (cz + 1)))
  | 1 =>
      ((fin4 cx, fin4 (cy + 1), fin4 cz),
       (fin4 (cx + 1), fin4 (cy + 1), fin4 cz),
       (fin4 cx, fin4 (cy + 1), fin4 (cz + 1)),
       (fin4 (cx + 1), fin4 (cy + 1), fin4 (cz + 1)))
  | _ =>
      ((fin4 cx, fin4 cy, fin4 (cz + 1)),
       (fin4 (cx + 1), fin4 cy, fin4 (cz + 1)),
       (fin4 cx, fin4 (cy + 1), fin4 (cz + 1)),
       (fin4 (cx + 1), fin4 (cy + 1), fin4 (cz + 1)))

/-- **T-DMC0-EVEN**: every cell face's 4-cycle of corner signs has an
    even number of sign changes — for any sign field. This is the same
    4-cycle parity as `Vdb.evenSignChanges4`. -/
theorem facePerimeter_even (s : Lat → Bool) (f : Face) :
    Even (crossedCount4 (s (perimeterCorners f).1) (s (perimeterCorners f).2.1)
      (s (perimeterCorners f).2.2.1) (s (perimeterCorners f).2.2.2)) := by
  have := evenSignChanges4 (s (perimeterCorners f).1) (s (perimeterCorners f).2.1)
    (s (perimeterCorners f).2.2.1) (s (perimeterCorners f).2.2.2)
  exact this

/-! ### Bounded verification on the Fin-4 padded lattice -/

/-- Whether the assembly of `s` is balanced, computable (the face type
    is finite, so the check is decidable over the explicit enumeration). -/
def balancedB (s : Lat → Bool) : Bool :=
  let qs := (cuberilleStencil s).quads
  let uses := qs.flatMap id
  (cellAll.product (List.finRange 3)).all fun f =>
    decide ((uses.count ⟨f, true⟩) = (uses.count ⟨f, false⟩))

/-- Every face is enumerated in the bounded check. -/
theorem mem_faces (f : Face) : f ∈ cellAll.product (List.finRange 3) := by
  revert f
  native_decide

theorem balanced_iff_bool (s : Lat → Bool) :
    (cuberilleStencil s).Balanced ↔ balancedB s = true := by
  unfold balancedB StencilComplex.Balanced Balanced Vdb.faceUses
  constructor
  · intro h
    rw [List.all_eq_true]
    intro f _
    have hcount := h f
    show decide _ = true
    rw [decide_eq_true_eq]
    exact hcount
  · intro h f
    rw [List.all_eq_true] at h
    have hf := h f (mem_faces f)
    exact of_decide_eq_true hf

/-- **T-DMC0-CYCLE** (bounded, machine-checked): every shell-pinned sign
    field yields a balanced — hence watertight — assembly. All 256
    interior sign fields of the padded `4 x 4 x 4` lattice. -/
theorem balanced_fin4 :
    ∀ k : Fin 256, balancedB (latSignOf k.val) = true := by
  native_decide

theorem balanced_fin4' (k : Fin 256) :
    (cuberilleStencil (latSignOf k.val)).Balanced :=
  (balanced_iff_bool (latSignOf k.val)).mpr (balanced_fin4 k)

/-- **T-DMC0-CYCLE** as edge closure (bounded, machine-checked). -/
theorem edgeClosed_fin4 :
    ∀ s ∈ allPaddedSignFields, EdgeClosed (cuberilleStencil s).mesh := by
  intro s hs
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hs
  have hk' : k < 256 := List.mem_range.mp hk
  exact (cuberilleStencil (latSignOf k)).watertight (balanced_fin4' ⟨k, hk'⟩)

/-- The index quad of a crossed lattice edge, oriented by `flip`: the
    four cells around it, in cyclic order. -/
def paddedQuad (flip : Bool) (e : PadEdge) : IxQuad Cell :=
  let (i, j) := ij e.2 flip
  let q := anchorCell e.1 e.2
  ⟨addCell (addCell q i) j, addCell q j, q, addCell q i⟩

/-- The index quads of a sign field's assembly. -/
def paddedQuads (s : Lat → Bool) : List (IxQuad Cell) :=
  (crossed s).map fun e => paddedQuad (s e.1) e

theorem paddedQuad_edges_agree :
    ∀ p d flip,
      (paddedQuad flip (p, d)).edges =
        (labels p d flip).map (dirEdge faceEnds) := by
  native_decide

theorem aux_padded_edges (s : Lat → Bool) (es : List PadEdge) :
    ixSurfaceEdges (es.map fun e => paddedQuad (s e.1) e) =
      es.flatMap (fun e => (labels e.1 e.2 (s e.1)).map (dirEdge faceEnds)) := by
  induction es with
  | nil => rfl
  | cons e l ih =>
    simp only [ixSurfaceEdges, List.map_cons, List.flatMap_cons] at *
    rw [ih, paddedQuad_edges_agree]

theorem paddedQuads_edges (s : Lat → Bool) :
    ixSurfaceEdges (paddedQuads s) = (cuberilleStencil s).mesh := by
  show ixSurfaceEdges ((crossed s).map fun e => paddedQuad (s e.1) e) = (cuberilleStencil s).mesh
  rw [aux_padded_edges]
  simp [StencilComplex.mesh, StencilComplex.quads, asmSurface, cuberilleStencil, List.flatMap_map]

/-- **Watertightness** under any vertex placement of the cells. -/
theorem padded_watertight :
    ∀ s ∈ allPaddedSignFields, ∀ V : Cell → Point,
      Watertight ((paddedQuads s).map (IxQuad.map V)) := by
  intro s hs V
  exact watertight_concrete_of_edges
    (by rw [paddedQuads_edges]; exact edgeClosed_fin4 s hs) V

/-! ### Bounded Euler characteristic evidence (T-DMC0-χ)

The mesh vertices are the cells the quads touch; the faces are the quads;
the edges are the unordered quad edges. Concrete shell-pinned instances
of the Fin-4 lattice model:

* `chi_singleton` — a single inside corner: χ = 2;
* `chi_singleton_four` — a single inside corner (second lattice point): χ = 2;
* `chi_adjacent` — two adjacent inside corners (an inside edge): χ = 2;
* `chi_block` — all eight interior points inside (a solid cuboid): χ = 2;
* `chi_diagonal` — two face-diagonal inside corners (`k = 9`): χ = **3**,
  **not** 2 — the two one-cell bumps pinch and the configuration is not
  edge-manifold. Bounded evidence that the general χ claim only holds on
  edge-manifold fields; diagonal pairs are the simplest counterexample.

These are bounded evidence, not the general theorem (which needs the
edge-manifold classification of the ambiguous configurations, §4.3).
-/

def faceCountM (s : Lat → Bool) : Nat := (crossed s).length

def insertUniqCell (a : Cell) (l : List Cell) : List Cell :=
  if l.contains a then l else a :: l

def vertexCountM (s : Lat → Bool) : Nat :=
  ((crossed s).flatMap fun e => [paddedQuad (s e.1) e |>.a,
      (paddedQuad (s e.1) e).b, (paddedQuad (s e.1) e).c, (paddedQuad (s e.1) e).d])
    |>.foldr insertUniqCell [] |>.length

def cellKey (p : Cell) : Nat :=
  p.1.val + 3 * (p.2.1.val + 3 * p.2.2.val)

def unCell (a b : Cell) : Cell × Cell := if cellKey a ≤ cellKey b then (a, b) else (b, a)

def insertUniqEdge (a : Cell × Cell) (l : List (Cell × Cell)) : List (Cell × Cell) :=
  if l.contains a then l else a :: l

def edgeCountM (s : Lat → Bool) : Nat :=
  let es := (crossed s).flatMap fun e =>
    let q := paddedQuad (s e.1) e
    [unCell q.a q.b, unCell q.b q.c, unCell q.c q.d, unCell q.d q.a]
  es.foldr insertUniqEdge [] |>.length

theorem chi_singleton :
    (vertexCountM (latSignOf 2) : ℤ) - edgeCountM (latSignOf 2) + faceCountM (latSignOf 2) = 2 := by
  native_decide

theorem chi_singleton_four :
    (vertexCountM (latSignOf 4) : ℤ) - edgeCountM (latSignOf 4) + faceCountM (latSignOf 4) = 2 := by
  native_decide

theorem chi_adjacent :
    (vertexCountM (latSignOf 3) : ℤ) - edgeCountM (latSignOf 3) + faceCountM (latSignOf 3) = 2 := by
  native_decide

theorem chi_block :
    (vertexCountM (latSignOf 255) : ℤ) - edgeCountM (latSignOf 255) + faceCountM (latSignOf 255) = 2 := by
  native_decide

theorem chi_diagonal :
    (vertexCountM (latSignOf 9) : ℤ) - edgeCountM (latSignOf 9) + faceCountM (latSignOf 9) = 3 := by
  native_decide

/-- Every quad edge as an unordered cell pair, over all crossed edges. -/
def edgeMultiset (s : Lat → Bool) : List (Cell × Cell) :=
  (crossed s).flatMap fun e =>
    let q := paddedQuad (s e.1) e
    [unCell q.a q.b, unCell q.b q.c, unCell q.c q.d, unCell q.d q.a]

/-- Number of cell-pair edges not covered exactly twice (boundary dummy
    self-edges are counted like any other edge; the full block has none). -/
def badEdgeCount (s : Lat → Bool) : Nat :=
  let es := edgeMultiset s
  let uniq := es.foldr insertUniqEdge []
  uniq.filter (fun e => es.count e != 2) |>.length

/-- The χ count of the assembled mesh. -/
def chiOfM (s : Lat → Bool) : Int :=
  (vertexCountM s : Int) - edgeCountM s + faceCountM s

/-- **Bounded χ/manifoldness landscape** (machine-checked): over all 256
    shell-pinned fields of the Fin-4 model, 127 are edge-manifold and
    χ = 2; 9 are edge-manifold with χ ≠ 2; 36 have χ = 2 without being
    edge-manifold; 84 are neither. Edge-manifoldness does not imply the
    naive χ = 2 claim even in the bounded model. -/
theorem bounded_chi_landscape :
    ((List.range 256).filter (fun k => badEdgeCount (latSignOf k) == 0 && chiOfM (latSignOf k) == 2)).length = 127 ∧
    ((List.range 256).filter (fun k => badEdgeCount (latSignOf k) == 0 && chiOfM (latSignOf k) != 2)).length = 9 ∧
    ((List.range 256).filter (fun k => badEdgeCount (latSignOf k) != 0 && chiOfM (latSignOf k) == 2)).length = 36 ∧
    ((List.range 256).filter (fun k => badEdgeCount (latSignOf k) != 0 && chiOfM (latSignOf k) != 2)).length = 84 := by
  native_decide

/-- Edge-manifold does not imply χ = 2, machine-checked: the body-diagonal
    pair fields `k ∈ {24, 36, 66, 129}` are edge-manifold with χ = 3, and
    the six-point fields `k ∈ {126, 189, 219, 231}` give χ = 1. -/
theorem bounded_chi_manifold_not_chi2 :
    (badEdgeCount (latSignOf 24) : Nat) = 0 ∧ chiOfM (latSignOf 24) = 3 ∧
    (badEdgeCount (latSignOf 36) : Nat) = 0 ∧ chiOfM (latSignOf 36) = 3 ∧
    (badEdgeCount (latSignOf 66) : Nat) = 0 ∧ chiOfM (latSignOf 66) = 3 ∧
    (badEdgeCount (latSignOf 129) : Nat) = 0 ∧ chiOfM (latSignOf 129) = 3 ∧
    (badEdgeCount (latSignOf 126) : Nat) = 0 ∧ chiOfM (latSignOf 126) = 1 := by
  native_decide

end Cuberille

end Vdb
