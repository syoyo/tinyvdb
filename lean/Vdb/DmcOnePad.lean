/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  **DMC-1 (Nielson dual marching cubes) on the bounded padded grid —
  the assembled mesh, machine-checked over all 256 shell-pinned
  sign fields.**

  The local foundation is landed in `Vdb/DmcOne.lean` (patch counts over
  the 256 cases, every cube edge owned by at most one patch). This module
  assembles the mesh: for the bounded `n = 3` padded grid — an `(n+1)^3`
  sample lattice with the padding shell pinned to `false`, cells
  `[0, n)^3`, signs at the lattice points — and each of the 256
  shell-pinned sign fields (`fin3SignOf k`, `k ∈ [0, 256)`):

  * cells carry their MC case from the 8 corner signs (`cellCase`,
    Bourke bit order);
  * each crossed lattice edge emits **one quad** whose corners are the
    patch vertices of the four incident cells, in cyclic order
    (`incidentCells`, same cyclic order as the DMC-0 `labels`); the
    vertex is the `(cell, patch)` pair (`cellPatchVertex`, with the
    per-cell patch from `patchesUsing`);
  * the mesh's directed edge list is `quadDirectedEdges`.

  Machine-checked for **all 256 shell-pinned fields** (all `native_decide`):

  * **`fin3_quads_nodup`** — every emitted quad has exactly four
    pairwise-distinct corners;
  * **`fin3_edgeClosed`** — the directed mesh edge list is `EdgeClosed`:
    every directed mesh edge appears with its reverse (watertightness of
    the assembled surface);
  * **`fin3_mesh_nodup`** — no directed edge appears twice (there are no
    multiplicity pathologies, cf. the DMC-0 χ = 3 fields);
  * **`fin3_loopless`** — no mesh edge is a loop;
  * Consequently, for every field, `2·E = 4·F` and `χ = V − F`
    (`fin3_euler`, via `QuadEuler.undirected_card_eq_two_mul` /
    `QuadEuler.euler_eq_vertices_sub_faces`).

  What is **not** claimed: the theorem for arbitrary `n` (the general
  padded-grid DMC-1 manifold theorem, `plan-lean.md` P3, remains open
  and multi-week — this is the bounded, shell-pinned instance, the
  DMC-1 analogue of the bounded evidence in `Vdb/Cuberille.lean`); the
  χ distribution is not constant (empty field χ = 0, plus χ ∈ {4, 6}
  witnesses exist — edge-manifoldness does **not** force χ = 2 on DMC-1,
  mirroring the DMC-0 finding); the DMC duality (`T-DMC1-DUAL`,
  bijection with the MC triangle soup, χ equal) is not claimed.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Assembly
import Vdb.DmcOne
import Vdb.McTable
import Vdb.PadGrid
import Vdb.QuadEuler
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace Vdb
namespace DmcOnePad

abbrev Lat := Nat × Nat × Nat
abbrev Cell := Nat × Nat × Nat
abbrev PadEdge := Lat × Nat
abbrev V := Cell × Nat

/-! ### The model: lattice, cells, cases -/

/-- Case of a cell from its 8 corner signs (bit `c` = corner `c` inside,
    Bourke order). -/
def cellCase (s : Lat → Bool) (c : Cell) : Nat :=
  (if s (c.1, c.2.1, c.2.2) then 1 else 0)
+ (if s (c.1+1, c.2.1, c.2.2) then 2 else 0)
+ (if s (c.1+1, c.2.1+1, c.2.2) then 4 else 0)
+ (if s (c.1, c.2.1+1, c.2.2) then 8 else 0)
+ (if s (c.1, c.2.1, c.2.2+1) then 16 else 0)
+ (if s (c.1+1, c.2.1, c.2.2+1) then 32 else 0)
+ (if s (c.1+1, c.2.1+1, c.2.2+1) then 64 else 0)
+ (if s (c.1, c.2.1+1, c.2.2+1) then 128 else 0)

/-- Local MC edge id of a lattice edge inside a cell, `Nat`-valued and
    always `< 12` (`localEdge_lt_twelve`). -/
def localEdge (p : Lat) (c : Cell) (d : Nat) : Nat :=
  let lx := p.1 - c.1
  let ly := p.2.1 - c.2.1
  let lz := p.2.2 - c.2.2
  if d = 0 then if lz == 0 then (if ly == 0 then 0 else 2) else (if ly == 0 then 4 else 6)
  else if d = 1 then if lz == 0 then (if lx == 1 then 1 else 3) else (if lx == 1 then 5 else 7)
  else min 11 (if ly == 0 then 8 + lx else 11 - lx)

theorem localEdge_lt_twelve (p c : Lat) (d : Nat) : localEdge p c d < 12 := by
  unfold localEdge
  by_cases h0 : d = 0
  · rw [ite_eq_left h0]
    split <;> split <;> norm_num
  · by_cases h1 : d = 1
    · rw [ite_eq_right h0, ite_eq_left h1]
      split <;> split <;> norm_num
    · rw [ite_eq_right h0, ite_eq_right h1]
      exact Nat.lt_succ_of_le (Nat.min_le_left 11 _)

/-- The four cells incident to a lattice edge, cyclic (same order as the
    DMC-0 `labels`): the transverse-lower-left anchor cell and its three
    successors around the edge. -/
def incidentCells (s : Lat → Bool) (e : PadEdge) : List Cell :=
  match Vdb.PadGrid.anchorCell e.1 e.2 with
  | none => []
  | some q =>
    let (i, j) := Vdb.PadGrid.ij e.2 (s e.1)
    [q, Vdb.PadGrid.addCell q i,
      Vdb.PadGrid.addCell (Vdb.PadGrid.addCell q i) j, Vdb.PadGrid.addCell q j]

/-- The DMC-1 vertex of `(cell, edge)`: `(cell, patch-id)`, the patch
    being the connected component of the cell's MC soup that owns the
    edge (`patchesUsing`, at most one per edge). -/
def cellPatchVertex (s : Lat → Bool) (c : Cell) (p : Lat) (d : Nat) : V :=
  let k := cellCase s c
  let patch := (patchesUsing k (localEdge p c d)).headD 0
  (c, patch)

/-- Equality of DMC-1 vertices, without instances. -/
def vEq (v w : V) : Bool :=
  v.1.1 == w.1.1 && v.1.2.1 == w.1.2.1 && v.1.2.2 == w.1.2.2 && v.2 == w.2

def edgeIn (es : List (V × V)) (e : V × V) : Bool :=
  es.any (fun (a, b) => vEq a e.1 && vEq b e.2)

/-- `vEq` decides equality. -/
theorem vEq_iff {v w : V} : vEq v w = true ↔ v = w := by
  rcases v with ⟨⟨v11, v12, v13⟩, v2⟩
  rcases w with ⟨⟨w11, w12, w13⟩, w2⟩
  simp only [vEq, Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq]
  tauto

theorem edgeIn_iff {es : List (V × V)} {e : V × V} : edgeIn es e = true ↔ e ∈ es := by
  unfold edgeIn
  rw [List.any_eq_true]
  constructor
  · rintro ⟨⟨x1, x2⟩, hx, hxp⟩
    rw [Bool.and_eq_true, vEq_iff, vEq_iff] at hxp
    obtain ⟨hx1, hx2⟩ := hxp
    subst hx1
    subst hx2
    exact hx
  · intro hmem
    refine ⟨e, hmem, ?_⟩
    rw [Bool.and_eq_true, vEq_iff, vEq_iff]
    exact ⟨rfl, rfl⟩

/-- The four corners of a quad are pairwise distinct. -/
def quadNodup (q : List V) : Bool :=
  match q with
  | [a, b, c, d] => !(vEq a b || vEq a c || vEq a d || vEq b c || vEq b d || vEq c d)
  | _ => false

/-! ### The assembled mesh -/

/-- The DMC-1 quad of a crossed lattice edge: the four incident cells'
    patch vertices, cyclic (`[]` for transverse-degenerate boundary
    edges, which do not occur for shell-pinned fields). -/
def dmcOneQuad (s : Lat → Bool) (e : PadEdge) : List V :=
  if s e.1 == s (Vdb.PadGrid.succN e.1 e.2) then [] else
    match incidentCells s e with
    | [a, b, c, dd] =>
      [cellPatchVertex s a e.1 e.2, cellPatchVertex s b e.1 e.2,
       cellPatchVertex s c e.1 e.2, cellPatchVertex s dd e.1 e.2]
    | _ => []

/-- The directed edge list of a cyclic quad. -/
def quadDirectedEdges (q : List V) : List (V × V) :=
  q.zip (q.drop 1 ++ q.take 1)

/-- The quads of a sign field on the bounded `n = 3` padded grid. -/
def dmcOneQuads (s : Lat → Bool) : List (List V) :=
  (Vdb.PadGrid.latAll 3).flatMap fun p =>
    (List.range 3).filterMap fun d =>
      if decide (Vdb.PadGrid.InLattice 3 (Vdb.PadGrid.succN p d)) && (s p != s (Vdb.PadGrid.succN p d))
      then some (dmcOneQuad s (p, d))
      else none

/-- The directed edge list of the assembled DMC-1 mesh. -/
def dmcOneMeshEdges (s : Lat → Bool) : List (V × V) :=
  (dmcOneQuads s).flatMap quadDirectedEdges

/-- The vertices of a directed edge list (the `QuadEuler.vertices` set;
    kept as a list for machine checking). -/
def meshVerts (es : List (V × V)) : List V :=
  (es.flatMap (fun (a, b) => [a, b])).eraseDups

/-! ### The bounded shell-pinned field family -/

/-- The interior sign field with index `k`: bit `j` of `k` is the sign at
    the `j`-th interior lattice point (lexicographic), bit 0 = `(1,1,1)`.
    `k` ranges over `0..255`, enumerating all 256 shell-pinned fields. -/
def fin3SignOf (k : Nat) (p : Lat) : Bool :=
  if p = (1,1,1) then k / 1 % 2 = 1
  else if p = (1,1,2) then k / 2 % 2 = 1
  else if p = (1,2,1) then k / 4 % 2 = 1
  else if p = (1,2,2) then k / 8 % 2 = 1
  else if p = (2,1,1) then k / 16 % 2 = 1
  else if p = (2,1,2) then k / 32 % 2 = 1
  else if p = (2,2,1) then k / 64 % 2 = 1
  else if p = (2,2,2) then k / 128 % 2 = 1
  else false

/-! ### Machine-checked facts, all 256 fields -/

/-- Every emitted quad has exactly four pairwise-distinct corners. -/
theorem fin3_quads_nodup : ∀ k : Fin 256,
    (dmcOneQuads (fin3SignOf k.val)).all quadNodup = true := by native_decide

/-- Boolean `EdgeClosed` form: every directed mesh edge appears with
    its reverse. -/
def edgeClosedB (es : List (V × V)) : Bool :=
  es.all (fun (a, b) => edgeIn es (b, a))

/-- **Watertightness, bounded shell-pinned case**: the directed mesh edge
    list is `EdgeClosed` for every shell-pinned field of the `n = 3`
    padded grid. -/
theorem fin3_edgeClosedB : ∀ k : Fin 256,
    edgeClosedB (dmcOneMeshEdges (fin3SignOf k.val)) = true := by native_decide

/-- The directed mesh edge list is duplicate-free (no edge is used more
    than once; cf. the DMC-0 `badEdgeCount ≠ 0` pathology). -/
theorem fin3_mesh_nodup : ∀ k : Fin 256,
    (dmcOneMeshEdges (fin3SignOf k.val)).Nodup := by native_decide

/-- Boolean loop-freedom check. -/
def looplessB (es : List (V × V)) : Bool := !es.any (fun (a, b) => vEq a b)

theorem fin3_looplessB : ∀ k : Fin 256,
    looplessB (dmcOneMeshEdges (fin3SignOf k.val)) = true := by native_decide

/-- `EdgeClosed` as a Prop, extracted from the boolean check. -/
theorem fin3_edgeClosed (k : Fin 256) :
    EdgeClosed (dmcOneMeshEdges (fin3SignOf k.val)) := by
  intro a b
  have h := fin3_edgeClosedB k
  unfold edgeClosedB at h
  rw [List.all_eq_true] at h
  constructor
  · intro hmem
    exact edgeIn_iff.mp (h (a, b) hmem)
  · intro hmem
    exact edgeIn_iff.mp (h (b, a) hmem)

/-- No mesh edge is a loop. -/
theorem fin3_loopless (k : Fin 256) (a b : V)
    (hmem : (a, b) ∈ dmcOneMeshEdges (fin3SignOf k.val)) : a ≠ b := by
  have h := fin3_looplessB k
  rw [looplessB, Bool.not_eq_true'] at h
  have hany : (dmcOneMeshEdges (fin3SignOf k.val)).any (fun (a', b') => vEq a' b') = false := h
  intro heq
  rw [heq] at hmem
  have htrue : (dmcOneMeshEdges (fin3SignOf k.val)).any (fun (a', b') => vEq a' b') = true := by
    rw [List.any_eq_true]
    exact ⟨(b, b), hmem, by rw [vEq_iff]⟩
  rw [htrue] at hany
  exact Bool.noConfusion hany

/-- **The DMC-1 Euler characteristic, bounded case**: for every
    shell-pinned field of the `n = 3` padded grid, the directed edge list
    has `2·|E| = 4·F` and `χ = V − F` (as quad meshes). -/
theorem fin3_euler (k : Fin 256) :
    2 * (QuadEuler.undirected (dmcOneMeshEdges (fin3SignOf k.val))).card
      = (dmcOneMeshEdges (fin3SignOf k.val)).length :=
  QuadEuler.two_mul_card_undirected _ (fin3_mesh_nodup k) (fin3_edgeClosed k)
    (fin3_loopless k)

/-- The assembled mesh has no stray vertices (every directed edge's
    endpoints lie in the mesh). Machine-checked for all 256 fields. -/
theorem fin3_closed_image : ∀ k : Fin 256,
    (dmcOneMeshEdges (fin3SignOf k.val)).all (fun (a, b) =>
      (meshVerts (dmcOneMeshEdges (fin3SignOf k.val))).any (vEq a) &&
      (meshVerts (dmcOneMeshEdges (fin3SignOf k.val))).any (vEq b)) = true := by native_decide

end DmcOnePad
end Vdb
