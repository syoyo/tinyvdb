/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  **The DMC-1 mesh is dual to the MC soup — component count identity and
  χ = 2 · components, machine-checked over all 256 shell-pinned fields.**

  `Vdb/DmcOnePad.lean` assembles the Nielson dual marching cubes mesh on
  the bounded `n = 3` padded grid (all 256 shell-pinned sign fields) and
  machine-checks watertightness. This module machine-checks the sober
  half of the DMC duality (`plan-lean.md` P3, `T-DMC1-DUAL`):

  * **`soupComponents`** — the number of connected components of the
    global MC triangle soup (union-find over the `n ≤ 135` triangles of
    the grid, shared vertices = shared crossed lattice edges);
  * **`meshComponents`** — the number of connected components of the
    mesh's vertex graph (union-find over the `V` vertices via mesh
    edges);
  * **`fin3_dual_components`** — for every shell-pinned field of the
    `n = 3` padded grid, the mesh and the soup have exactly the same
    number of connected components (all `native_decide`);
  * **`fin3_chi_eq_two_mul_components`** — `χ = V − F = 2 · #components`
    for every shell-pinned field. Combined with `fin3_euler`
    (`DmcOnePad.lean`), the machine-checked χ landscape over the 256
    fields is: 167 fields with 1 component and χ = 2, 78 with 2
    components and χ = 4, 8 with 3 components and χ = 6
    (`[22, 41, 73, 97, 104, 134, 146, 148]`), 2 with 4 components and
    χ = 8 (`[105, 150]`), 1 empty field (χ = 0) — **every component is a
    topological sphere**, as far as the aggregate χ count is concerned.

  The second half of the duality (`T-DMC1-DUAL` beyond connectivity) is
  landed here as well:

  * **`mcPatchesOf`** — the cell-local MC patches `(cell, patch-id)`, one
    per connected component of each cell's MC triangle soup (`mcPatchCount`);
  * **`patchVertexEquiv`** — for every shell-pinned `n = 3` field, the MC
    cube-patches are in **bijection** with the DMC mesh vertices (machine-
    checked membership equivalence `fin3_patchVertex_iff` over all 256
    fields). This is the "triangle patch ↔ DMC vertex" half.
  * **`mcVertexQuadEquiv`** — for **every** `n`, the welded MC vertices
    (crossed lattice edges) are in **bijection** with the DMC quads, via
    `dmcOneQuadN` (kernel proof; it consumes the injectivity of
    `Vdb.DmcOneEuler.dmcOneQuadN_inj`). This is the "MC vertex ↔ DMC quad"
    half and holds generally.
  * **`mcIncident_iff_dmcIncident`** — the two complexes have the **same
    incidence relation** (general `n`): a cell-local patch uses a crossed
    edge iff the corresponding DMC vertex is a corner of that edge's quad.
  * **`chiMcDual` / `chiDmcMesh`** — with the shared incidence edge count,
    the two complexes have identical Euler characteristic `V − E + F`
    (general `n` unconditional via `chi_dual_eq`; bounded `n = 3` also via
    `fin3_chi_dual_eq`). The machine-checked
    landscape is `chiMcDual = V − F = 2 · #components`
    (`fin3_chi_dual_eq_two_mul_components`).

  The second half of the duality is unconditional for every `n`:

  * **`exists_crossed_realizing_patch`** — the cube-local-edge ↔
    global-crossed-edge lifting lemma: every cell-local patch id is
    realized as a corner of the quad of a crossed edge incident to the
    cell (machine-checked cube-local ingredients plus symbolic coordinate
    geometry);
  * **`mcPatches_mem_meshVerts_iff`** and **`patchVertexEquivN`** — the
    general-`n` patch ↔ vertex membership equivalence and bijection;
  * **`patch_card_general`** — the patch-cardinality identity, discharging
    the previously named hypothesis `hcard`;
  * **`chi_dual_eq`** — χ duality for every `n` and every shell-pinned
    field, now unconditional (`chi_dual_eq_of_patch_card` is kept as the
    modular form).

  What is **not** claimed: that each component is *literally* a sphere
  (genus is not computed), nor any other genus/homology content of the
  duality.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Assembly
import Vdb.DmcOne
import Vdb.DmcOneEuler
import Vdb.DmcOnePad
import Vdb.DmcOneQuadInject
import Vdb.McTable
import Vdb.PadGrid
import Vdb.QuadEuler
import Vdb.QuadEulerPad
import Mathlib.Tactic

open Vdb.McTable

set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace Vdb
namespace DmcOneDual

abbrev Lat := Nat × Nat × Nat
abbrev Cell := Nat × Nat × Nat
abbrev PadEdge := Lat × Nat
abbrev DV := DmcOnePad.V

/-! ### The global MC soup and its components -/

/-- All cells of the `n^3` cell grid of the padded grid. -/
def cellsAll (n : Nat) : List Cell :=
  (List.range n).flatMap fun x =>
    (List.range n).flatMap fun y =>
      (List.range n).map fun z => (x, y, z)

/-- The crossed lattice edges of `s`: both endpoints in the lattice,
    signs differ. -/
def crossedEdges (n : Nat) (s : Lat → Bool) : List PadEdge :=
  (List.range (n+1)).flatMap fun x =>
    (List.range (n+1)).flatMap fun y =>
      (List.range (n+1)).flatMap fun z =>
        (List.range 3).filterMap fun d =>
          if decide (Vdb.PadGrid.InLattice n (Vdb.PadGrid.succN (x, y, z) d)) &&
             (s (x, y, z) != s (Vdb.PadGrid.succN (x, y, z) d))
          then some ((x, y, z), d) else none

/-- The local MC edge id's direction (`d % 2` for the 8-face-ring edges,
    `2` for the verticals). -/
def localEdgeDir (e : Nat) : Nat := if e < 8 then e % 2 else 2

def cornerOffset : List (Nat × Nat × Nat) :=
  [(0,0,0), (1,0,0), (1,1,0), (0,1,0), (0,0,1), (1,0,1), (1,1,1), (0,1,1)]

def cornerOf (i : Nat) : Nat × Nat × Nat := cornerOffset.getD i (0, 0, 0)

def cellCorner (c : Cell) (i : Nat) : Lat :=
  let (dx, dy, dz) := cornerOf i
  (c.1 + dx, c.2.1 + dy, c.2.2 + dz)

def localEdgeEnds (c : Cell) (e : Nat) : Lat × Lat :=
  let (a, b) := mcEdgeVerts[e]!
  let pa := cellCorner c a
  let pb := cellCorner c b
  let d := localEdgeDir e
  if (if d = 0 then pa.1 ≤ pb.1 else if d = 1 then pa.2.1 ≤ pb.2.1 else pa.2.2 ≤ pb.2.2)
  then (pa, pb) else (pb, pa)

/-- The global MC soup of `s`: an array of triangles, each a triple of
    global MC vertex ids (crossed-edge indices in `crossedEdges n s`). -/
def mcSoup (n : Nat) (s : Lat → Bool) : List (List Nat) :=
  let es := crossedEdges n s
  (cellsAll n).flatMap fun c =>
    let k := DmcOnePad.cellCase s c
    (trisOf k).map fun (a, b, cc) =>
      [a, b, cc].map fun e =>
        let (p, _) := localEdgeEnds c e
        let d := localEdgeDir e
        (es.findIdx? (· == (p, d))).getD 9999

/-- Union-find parent array, one slot per triangle. -/
def findRoot (parent : Array Nat) (x : Nat) : Nat := Id.run do
  let mut y := x
  for _ in List.range (parent.size + 1) do
    let p := parent.getD y y
    if p = y then break
    y := p
  return y

/-- The soup data: triangles, union-find parent array and the distinct
    roots (one per component). -/
structure SoupData where
  soup : Array (List Nat)
  parent : Array Nat
  roots : List Nat

def buildSoup (n : Nat) (s : Lat → Bool) : SoupData := Id.run do
  let soup := (mcSoup n s).toArray
  let mut parent := Array.ofFn (fun (i : Fin soup.size) => i.1)
  for i in List.range soup.size do
    for j in List.range i do
      if soup[i]!.any (soup[j]!.contains ·) then
        let pi := findRoot parent i
        let pj := findRoot parent j
        if pi ≠ pj then
          parent := parent.set! pi pj
  let mut roots : Array Nat := #[]
  for i in List.range parent.size do
    let r := findRoot parent i
    if !roots.contains r then roots := roots.push r
  return ⟨soup, parent, roots.toList⟩

/-- The number of connected components of the MC soup. -/
def soupComponents (sd : SoupData) : Nat := sd.roots.length

/-! ### Components of the mesh's vertex graph -/

/-- The number of connected components of the mesh's vertex graph
    (mesh edges are adjacency). -/
def meshComponents (es : List (DV × DV)) : Nat := Id.run do
  let mut parent : Array Nat := #[]
  let mut count := 0
  let mut verts : Array DV := #[]
  for (a, b) in es do
    for v in [a, b] do
      if !verts.toList.any (DmcOnePad.vEq v) then
        verts := verts.push v
        parent := parent.push count
        count := count + 1
  for (a, b) in es do
    let ia := (verts.toList.findIdx? (DmcOnePad.vEq a)).getD 0
    let ib := (verts.toList.findIdx? (DmcOnePad.vEq b)).getD 0
    let pa := findRoot parent ia
    let pb := findRoot parent ib
    if pa ≠ pb then
      parent := parent.set! pa pb
  let mut c := 0
  for i in List.range parent.size do
    if findRoot parent i == i then c := c + 1
  return c

/-! ### The bounded `n = 3` family -/

/-- The interior sign field with index `k` (bit `j` of `k` = sign at
    the `j`-th interior lattice point, lexicographic). -/
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

/-- **Dual component identity**: for every shell-pinned field of the
    `n = 3` padded grid, the DMC-1 mesh and the MC soup have exactly
    the same number of connected components. -/
theorem fin3_dual_components : ∀ k : Fin 256,
    soupComponents (buildSoup 3 (fin3SignOf k.val))
      = meshComponents (DmcOnePad.dmcOneMeshEdges (fin3SignOf k.val)) := by native_decide

/-- The mesh Euler characteristic in terms of soup components:
    `χ = V − F = 2 · #components`. The machine-checked χ landscape is
    therefore 167 fields with 1 component and χ = 2, 78 with 2
    components and χ = 4, 8 with 3 components and χ = 6, 2 with
    4 components and χ = 8, 1 empty field. -/
theorem fin3_chi_eq_two_mul_components : ∀ k : Fin 256,
    (DmcOnePad.meshVerts (DmcOnePad.dmcOneMeshEdges (fin3SignOf k.val))).length
      - (DmcOnePad.dmcOneQuads (fin3SignOf k.val)).length
    = 2 * soupComponents (buildSoup 3 (fin3SignOf k.val)) := by native_decide

/-- No field's soup or mesh is left with components the other does not
    see: component counts agree everywhere. -/
theorem fin3_component_counts : ∀ k : Fin 256,
    meshComponents (DmcOnePad.dmcOneMeshEdges (fin3SignOf k.val))
      = soupComponents (buildSoup 3 (fin3SignOf k.val)) := fun k =>
  (fin3_dual_components k).symm

/-! ### T-DMC1-DUAL beyond connectivity: patch ↔ vertex, MC vertex ↔ quad

  Nielson's DMC is *dual* to the MC soup in two ways:

  * each connected component of a cube's MC triangle soup (a cell-local
    **patch**, `Vdb.mcPatchCount`) carries one DMC vertex — so MC patches
    are in bijection with DMC mesh vertices;
  * each welded MC vertex (a crossed lattice edge, `PadGrid.crossed`) is
    surrounded by one DMC quad — so MC vertices are in bijection with DMC
    quads.

  Both bijections and the incidence preservation are now general in `n`:
  the first is `patchVertexEquivN` (its bounded `n = 3` instance,
  `patchVertexEquiv`, is kept as the machine-checked exhaustive check).
  Consequently the patch-cardinality identity is unconditional and the
  named hypothesis `hcard` of `chi_dual_eq_of_patch_card` is discharged by
  `patch_card_general`.
-/

/-- The cell-local MC patches of `s`, one `(cell, patch-id)` per connected
    component of each cell's MC triangle soup (`mcPatchCount`). These are
    the MC-side faces dual to DMC vertices. -/
def mcPatchesOf (n : Nat) (s : Lat → Bool) : List (Cell × Nat) :=
  (cellsAll n).flatMap fun c =>
    (List.range (mcPatchCount (DmcOnePad.cellCase s c))).map fun i => (c, i)

/-! #### The patch ↔ vertex bijection (bounded `n = 3`) -/

/-- Boolean set-equality check of `mcPatchesOf 3 s` against the DMC mesh
    vertex set (both directions of membership). -/
def patchVertexB (s : Lat → Bool) : Bool :=
  let ps := mcPatchesOf 3 s
  let vs := DmcOnePad.meshVerts (DmcOnePad.dmcOneMeshEdges s)
  ps.all (fun p => decide (p ∈ vs)) && vs.all (fun v => decide (v ∈ ps))

set_option maxHeartbeats 800000 in
theorem patchVertexB_true : ∀ k : Fin 256, patchVertexB (fin3SignOf k.val) = true := by
  native_decide

/-- A cell-local patch is a DMC mesh vertex exactly when it appears as a
    corner of an assembled quad — for all 256 shell-pinned `n = 3` fields. -/
theorem fin3_patchVertex_iff (k : Fin 256) (p : Cell × Nat) :
    p ∈ mcPatchesOf 3 (fin3SignOf k.val) ↔
      p ∈ DmcOnePad.meshVerts (DmcOnePad.dmcOneMeshEdges (fin3SignOf k.val)) := by
  have h := patchVertexB_true k
  unfold patchVertexB at h
  rw [Bool.and_eq_true] at h
  constructor
  · intro hp
    exact of_decide_eq_true ((List.all_eq_true.mp h.1) p hp)
  · intro hv
    exact of_decide_eq_true ((List.all_eq_true.mp h.2) p hv)

/-- **Patch ↔ vertex bijection (bounded `n = 3`)**: the MC cube-patches
    and the DMC mesh vertices are in bijection for every shell-pinned
    field. This is the "MC triangle patch ↔ DMC vertex" half of
    `T-DMC1-DUAL`. -/
noncomputable def patchVertexEquiv (k : Fin 256) :
    {p // p ∈ mcPatchesOf 3 (fin3SignOf k.val)} ≃
      {v // v ∈ DmcOnePad.meshVerts (DmcOnePad.dmcOneMeshEdges (fin3SignOf k.val))} :=
  Equiv.ofBijective
    (fun p => ⟨p.val, (fin3_patchVertex_iff k p.val).mp p.property⟩)
    ⟨by
      intro a b h
      exact Subtype.ext
        (congrArg
          (fun z : {v // v ∈ DmcOnePad.meshVerts (DmcOnePad.dmcOneMeshEdges (fin3SignOf k.val))} => z.val)
          h),
     by
      intro v
      refine ⟨⟨v.val, (fin3_patchVertex_iff k v.val).mpr v.property⟩, ?_⟩
      exact Subtype.ext rfl⟩

/-! #### The MC vertex ↔ DMC quad bijection (general `n`) -/

/-- An MC vertex (a crossed lattice edge) maps to its DMC quad. -/
def quadOfMCVertex (n : Nat) (s : Lat → Bool)
    (e : {e // e ∈ PadGrid.crossed n s}) :
    {q // q ∈ DmcOneEuler.dmcOneQuads n s} :=
  ⟨DmcOneEuler.dmcOneQuadN s e.val, by
    rw [DmcOneEuler.dmcOneQuads_eq_map_crossed, List.mem_map]
    exact ⟨e.val, e.property, rfl⟩⟩

set_option maxHeartbeats 800000 in
theorem quadOfMCVertex_injective (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false) :
    Function.Injective (quadOfMCVertex n s) := by
  intro a b hab
  apply Subtype.ext
  have hq : DmcOneEuler.dmcOneQuadN s a.val = DmcOneEuler.dmcOneQuadN s b.val :=
    congrArg Subtype.val hab
  obtain ⟨hd, hp, _, hne⟩ := PadGrid.crossed_spec n s a.property
  obtain ⟨hd', hp', _, hne'⟩ := PadGrid.crossed_spec n s b.property
  exact DmcOneEuler.dmcOneQuadN_inj n s hpin hd hd' hp hp' hne hne' hq

set_option maxHeartbeats 800000 in
theorem quadOfMCVertex_surjective (n : Nat) (s : Lat → Bool) :
    Function.Surjective (quadOfMCVertex n s) := by
  intro q
  have hqmap : q.val ∈ (PadGrid.crossed n s).map (fun e => DmcOneEuler.dmcOneQuadN s e) := by
    rw [← DmcOneEuler.dmcOneQuads_eq_map_crossed]
    exact q.property
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hqmap
  refine ⟨⟨e, he⟩, ?_⟩
  exact Subtype.ext heq

/-- **MC vertex ↔ DMC quad equivalence (general `n`)**: welded MC vertices
    (crossed lattice edges) are in bijection with DMC quads. This is the
    "MC vertex ↔ DMC quad" half of `T-DMC1-DUAL` and holds for every shell-
    pinned sign field on a padded grid of any size. -/
noncomputable def mcVertexQuadEquiv (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false) :
    {e // e ∈ PadGrid.crossed n s} ≃ {q // q ∈ DmcOneEuler.dmcOneQuads n s} :=
  Equiv.ofBijective (quadOfMCVertex n s)
    ⟨quadOfMCVertex_injective n s hpin, quadOfMCVertex_surjective n s⟩

/-! #### Incidence preservation (general `n`) -/

/-- DMC side of the incidence relation: the DMC vertex `p` is a corner of
    the DMC quad of the crossed edge `e`. -/
def dmcIncident (s : Lat → Bool) (p : Cell × Nat) (e : PadEdge) : Prop :=
  p ∈ DmcOneEuler.dmcOneQuadN s e

/-- MC side of the incidence relation: the cell-local patch `p = (c, i)`
    owns the local edge of the crossed edge `e` inside cell `c`, and `c`
    is one of `e`'s incident cells. -/
def mcIncident (s : Lat → Bool) (p : Cell × Nat) (e : PadEdge) : Prop :=
  p.1 ∈ DmcOnePad.incidentCells s e ∧
    (patchesUsing (DmcOnePad.cellCase s p.1) (DmcOnePad.localEdge e.1 p.1 e.2)).headD 0 = p.2

set_option maxHeartbeats 800000 in
/-- **Incidence preservation (general `n`)**: the MC patch/MC vertex
    incidence relation and the DMC vertex/DMC quad incidence relation are
    the same relation, transported by the two bijections. -/
theorem mcIncident_iff_dmcIncident (n : Nat) (s : Lat → Bool)
    {p : Cell × Nat} {e : PadEdge} (he : e ∈ PadGrid.crossed n s) :
    mcIncident s p e ↔ dmcIncident s p e := by
  obtain ⟨hd, hp, _, hne⟩ := PadGrid.crossed_spec n s he
  have hbne : (s e.1 == s (PadGrid.succN e.1 e.2)) = false := by
    cases h1 : s e.1 <;> cases h2 : s (PadGrid.succN e.1 e.2) <;> simp_all
  unfold dmcIncident DmcOneEuler.dmcOneQuadN mcIncident
  rw [ite_eq_right (by simp [hbne])]
  rw [List.mem_map]
  constructor
  · rintro ⟨hc, hpatch⟩
    refine ⟨p.1, hc, ?_⟩
    change (p.1, (patchesUsing (DmcOnePad.cellCase s p.1)
      (DmcOnePad.localEdge e.1 p.1 e.2)).headD 0) = p
    rw [hpatch]
  · rintro ⟨c', hc', hv⟩
    have hc1 : c' = p.1 := by
      simpa [DmcOnePad.cellPatchVertex] using congrArg Prod.fst hv
    subst c'
    refine ⟨hc', ?_⟩
    simpa [DmcOnePad.cellPatchVertex] using congrArg Prod.snd hv

/-! #### Euler characteristic of the dual complex -/

/-- The Euler characteristic `V − E + F` of the assembled DMC quad mesh. -/
def chiDmcMesh (n : Nat) (s : Lat → Bool) : Int :=
  (DmcOnePad.meshVerts (DmcOneEuler.dmcOneMeshEdges n s)).length
    - (QuadEuler.undirected (DmcOneEuler.dmcOneMeshEdges n s)).card
    + (DmcOneEuler.dmcOneQuads n s).length

/-- The Euler characteristic of the dual MC patch complex: vertices are
    crossed lattice edges, faces are cell-local MC patches, and edges are
    the shared incidence graph (read from the DMC mesh). -/
def chiMcDual (n : Nat) (s : Lat → Bool) : Int :=
  (PadGrid.crossed n s).length
    - (QuadEuler.undirected (DmcOneEuler.dmcOneMeshEdges n s)).card
    + (mcPatchesOf n s).length

set_option maxHeartbeats 800000 in
/-- **χ duality (modular form)**: under the patch-cardinality identity the
    dual MC patch complex and the DMC mesh have the same Euler
    characteristic. The identity is now proved unconditionally for every
    `n` by `patch_card_general`, so `chi_dual_eq` is unconditional; the
    `quads ↔ crossed` count is `DmcOneEuler.dmcOneQuads_length`. -/
theorem chi_dual_eq_of_patch_card (n : Nat) (s : Lat → Bool)
    (hcard : (mcPatchesOf n s).length =
      (DmcOnePad.meshVerts (DmcOneEuler.dmcOneMeshEdges n s)).length) :
    chiMcDual n s = chiDmcMesh n s := by
  have hq : (DmcOneEuler.dmcOneQuads n s).length = (PadGrid.crossed n s).length :=
    DmcOneEuler.dmcOneQuads_length n s
  unfold chiMcDual chiDmcMesh
  omega

set_option maxHeartbeats 800000 in
/-- The patch-cardinality identity for all 256 shell-pinned `n = 3` fields
    (the bounded instance of the general-`n` gap). -/
theorem fin3_patchVertex_card : ∀ k : Fin 256,
    (mcPatchesOf 3 (fin3SignOf k.val)).length =
      (DmcOnePad.meshVerts (DmcOneEuler.dmcOneMeshEdges 3 (fin3SignOf k.val))).length := by
  native_decide

/-- **χ duality (bounded `n = 3`)**: the MC patch complex and the DMC mesh
    have the same Euler characteristic for all 256 shell-pinned fields. -/
theorem fin3_chi_dual_eq (k : Fin 256) :
    chiMcDual 3 (fin3SignOf k.val) = chiDmcMesh 3 (fin3SignOf k.val) := by
  exact chi_dual_eq_of_patch_card 3 (fin3SignOf k.val) (fin3_patchVertex_card k)

set_option maxHeartbeats 800000 in
/-- The dual MC patch χ equals `2 · #components` for all 256 shell-pinned
    `n = 3` fields — machine-checked end to end. Combined with the landed
    `fin3_chi_eq_two_mul_components`, this is the full χ equality of the
    dual pair on the bounded family. -/
theorem fin3_chi_dual_eq_two_mul_components : ∀ k : Fin 256,
    chiMcDual 3 (fin3SignOf k.val) =
      2 * soupComponents (buildSoup 3 (fin3SignOf k.val)) := by
  native_decide

set_option maxHeartbeats 800000 in
/-- The χ of the dual MC patch complex equals the bounded model's `V − F`
    for all 256 shell-pinned `n = 3` fields (machine-checked). -/
theorem fin3_chi_dual_matches_mesh : ∀ k : Fin 256,
    chiMcDual 3 (fin3SignOf k.val) =
      ((DmcOnePad.meshVerts (DmcOnePad.dmcOneMeshEdges (fin3SignOf k.val))).length : Int)
        - (DmcOnePad.dmcOneQuads (fin3SignOf k.val)).length := by
  native_decide

/-! #### General-`n` patch ↔ DMC-vertex bijection: cube-local ingredients -/

/-- Membership in the cell grid enumeration. -/
theorem mem_cellsAll {n : Nat} {c : Cell} :
    c ∈ cellsAll n ↔ c.1 < n ∧ c.2.1 < n ∧ c.2.2 < n := by
  unfold cellsAll
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨x, hx, y, hy, z, hz, rfl⟩
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨c.1, by omega, c.2.1, by omega, c.2.2, by omega, rfl⟩

/-- The cell grid enumeration is duplicate-free. -/
theorem cellsAll_nodup (n : Nat) : (cellsAll n).Nodup := by
  unfold cellsAll
  apply List.nodup_flatMap.mpr
  constructor
  · intro x hx
    apply List.nodup_flatMap.mpr
    constructor
    · intro y hy
      exact List.Nodup.map (f := fun z : Nat => (x, y, z)) (by
        intro a b h
        obtain ⟨_, h2⟩ := Prod.mk.inj h
        obtain ⟨_, h4⟩ := Prod.mk.inj h2
        exact h4) List.nodup_range
    · exact (List.nodup_iff_pairwise_ne.mp List.nodup_range).imp (fun hne => by
        intro e he he'
        obtain ⟨z1, _, rfl⟩ := List.mem_map.mp he
        obtain ⟨z2, _, hz2⟩ := List.mem_map.mp he'
        injection hz2 with h h'
        injection h' with h'' _
        exact hne h''.symm)
  · exact (List.nodup_iff_pairwise_ne.mp List.nodup_range).imp (fun hne => by
      intro e he he'
      obtain ⟨y1, _, hy1'⟩ := List.mem_flatMap.mp he
      obtain ⟨y2, _, hy2'⟩ := List.mem_flatMap.mp he'
      obtain ⟨z1, _, rfl⟩ := List.mem_map.mp hy1'
      obtain ⟨z2, _, hz2⟩ := List.mem_map.mp hy2'
      injection hz2 with h _
      exact hne h.symm)

set_option maxHeartbeats 800000 in
/-- **Patch-id bound** (all 256 cube cases): when a cube case has a patch,
    the patch id stored at any local edge is a valid patch id. -/
theorem patchesUsing_headD_lt_mcPatchCount_of_pos : ∀ k : Fin 256, ∀ le : Fin 12,
    0 < mcPatchCount k.val →
      (patchesUsing k.val le.val).headD 0 < mcPatchCount k.val := by
  native_decide

set_option maxHeartbeats 800000 in
/-- **Patch realization** (all 256 cube cases): every patch id of a case is
    realized by some local cube edge whose two corner signs differ. -/
theorem patch_realized_by_localEdge : ∀ k : Fin 256, ∀ i : Fin (mcPatchCount k.val),
    ∃ le : Fin 12,
      (let (a, b) := mcEdgeVerts[le.val]!;
        (k.val / 2^a % 2) ≠ (k.val / 2^b % 2)) ∧
      (patchesUsing k.val le.val).headD 0 = i.val := by
  native_decide

/-- A case assembled from eight corner-sign bits. -/
def caseOfBits (b : Fin 8 → Bool) : Nat :=
  (if b 0 then 1 else 0) + (if b 1 then 2 else 0) + (if b 2 then 4 else 0) + (if b 3 then 8 else 0)
  + (if b 4 then 16 else 0) + (if b 5 then 32 else 0) + (if b 6 then 64 else 0) + (if b 7 then 128 else 0)

set_option maxHeartbeats 800000 in
/-- Bit extraction from eight corner signs, machine-checked over the finite
    function space `Fin 8 → Bool`. -/
theorem caseOfBits_bit : ∀ (b : Fin 8 → Bool) (j : Fin 8),
    caseOfBits b / 2^j.val % 2 = if b j then 1 else 0 := by
  native_decide

/-- A cell's case is the case of its eight corner signs. -/
theorem cellCase_eq_caseOfBits (s : Lat → Bool) (c : Cell) :
    DmcOnePad.cellCase s c = caseOfBits (fun j : Fin 8 => s (cellCorner c j.val)) := by
  rfl

/-- The `j`-th case bit is the sign of the `j`-th Bourke corner. -/
theorem cellCase_bit (s : Lat → Bool) (c : Cell) (j : Fin 8) :
    DmcOnePad.cellCase s c / 2^j.val % 2 = if s (cellCorner c j.val) then 1 else 0 := by
  rw [cellCase_eq_caseOfBits]
  exact caseOfBits_bit _ _

set_option maxHeartbeats 800000 in
/-- Translation of a local edge's lower/upper corner with the cell. -/
theorem localEdgeEnds_translate (c : Cell) (le : Fin 12) :
    let (p0, q0) := localEdgeEnds (0, 0, 0) le.val
    let (p, q) := localEdgeEnds c le.val
    p = (c.1 + p0.1, c.2.1 + p0.2.1, c.2.2 + p0.2.2) ∧
    q = (c.1 + q0.1, c.2.1 + q0.2.1, c.2.2 + q0.2.2) := by
  fin_cases le <;>
    simp [localEdgeEnds, cellCorner, cornerOf, cornerOffset, mcEdgeVerts, localEdgeDir]

set_option maxHeartbeats 800000 in
/-- The local edge of a lattice edge starting at corner `p` of cell `c`
    (with `p` the lower end along direction `d`) has endpoints `p` and its
    successor. -/
theorem localEdgeEnds_of_edge_start (c : Cell) (p : Lat) (d : Nat) (hd : d < 3)
    (hpge : c.1 ≤ p.1 ∧ c.2.1 ≤ p.2.1 ∧ c.2.2 ≤ p.2.2)
    (hple : p.1 ≤ c.1 + 1 ∧ p.2.1 ≤ c.2.1 + 1 ∧ p.2.2 ≤ c.2.2 + 1)
    (hdir : (d = 0 → p.1 = c.1) ∧ (d = 1 → p.2.1 = c.2.1) ∧ (d = 2 → p.2.2 = c.2.2)) :
    localEdgeEnds c (DmcOnePad.localEdge p c d) = (p, PadGrid.succN p d) := by
  rcases c with ⟨x, y, z⟩
  rcases p with ⟨px, py, pz⟩
  simp only at hpge hple hdir ⊢
  interval_cases d <;> simp only [PadGrid.succN] at hdir ⊢
  · have hpx : px = x := hdir.1 trivial
    have hpy : py = y ∨ py = y + 1 := by omega
    have hpz : pz = z ∨ pz = z + 1 := by omega
    subst px
    rcases hpy with rfl | rfl <;> rcases hpz with rfl | rfl <;>
      simp [DmcOnePad.localEdge, localEdgeEnds, cellCorner, cornerOf, cornerOffset,
        mcEdgeVerts, localEdgeDir]
  · have hpy : py = y := hdir.2.1 trivial
    have hpx : px = x ∨ px = x + 1 := by omega
    have hpz : pz = z ∨ pz = z + 1 := by omega
    subst py
    rcases hpx with rfl | rfl <;> rcases hpz with rfl | rfl <;>
      simp [DmcOnePad.localEdge, localEdgeEnds, cellCorner, cornerOf, cornerOffset,
        mcEdgeVerts, localEdgeDir]
  · have hpz : pz = z := hdir.2.2 trivial
    have hpx : px = x ∨ px = x + 1 := by omega
    have hpy : py = y ∨ py = y + 1 := by omega
    subst pz
    rcases hpx with rfl | rfl <;> rcases hpy with rfl | rfl <;>
      simp [DmcOnePad.localEdge, localEdgeEnds, cellCorner, cornerOf, cornerOffset,
        mcEdgeVerts, localEdgeDir]

set_option maxHeartbeats 800000 in
/-- The endpoints of a local edge at the origin are cube corners. -/
theorem localEdgeEnds_zero_isCorner : ∀ le : Fin 12,
    let (p, q) := localEdgeEnds (0, 0, 0) le.val
    (∃ i : Fin 8, p = cellCorner (0, 0, 0) i.val) ∧
    (∃ j : Fin 8, q = cellCorner (0, 0, 0) j.val) := by
  native_decide

set_option maxHeartbeats 800000 in
/-- Finite bridge: a local edge of a case built from corner bits is a
    sign-change edge exactly when its two endpoint corner bits differ. -/
theorem signChange_caseOfBits_iff : ∀ (b : Fin 8 → Bool) (le : Fin 12),
    le.val ∈ signChangeEdges (caseOfBits b) ↔
      (let (p, q) := localEdgeEnds (0, 0, 0) le.val
       ∃ i : Fin 8, ∃ j : Fin 8,
         p = cellCorner (0, 0, 0) i.val ∧ q = cellCorner (0, 0, 0) j.val ∧ b i != b j) := by
  native_decide

set_option maxHeartbeats 800000 in
/-- A local cube edge is a sign-change edge of the case iff the signs at its
    two lattice endpoints differ. -/
theorem mem_signChangeEdges_iff_endpoints (s : Lat → Bool) (c : Cell) (le : Fin 12) :
    le.val ∈ signChangeEdges (DmcOnePad.cellCase s c) ↔
      (let (p, q) := localEdgeEnds c le.val; s p != s q) := by
  let b : Fin 8 → Bool := fun j => s (cellCorner c j.val)
  rw [cellCase_eq_caseOfBits]
  dsimp only
  have ht := localEdgeEnds_translate c le
  dsimp only at ht
  rcases ht with ⟨hpc, hqc⟩
  constructor
  · intro hle
    have h := (signChange_caseOfBits_iff b le).mp hle
    dsimp only at h
    rcases h with ⟨i, j, hp0, hq0, hb⟩
    rw [hpc, hqc, hp0, hq0]
    have hi : (c.1 + (cellCorner (0, 0, 0) i.val).1,
        c.2.1 + (cellCorner (0, 0, 0) i.val).2.1,
        c.2.2 + (cellCorner (0, 0, 0) i.val).2.2) = cellCorner c i.val := by
      simp [cellCorner, cornerOf, cornerOffset]
    have hj : (c.1 + (cellCorner (0, 0, 0) j.val).1,
        c.2.1 + (cellCorner (0, 0, 0) j.val).2.1,
        c.2.2 + (cellCorner (0, 0, 0) j.val).2.2) = cellCorner c j.val := by
      simp [cellCorner, cornerOf, cornerOffset]
    rw [hi, hj]
    exact hb
  · intro hend
    have hc0 := localEdgeEnds_zero_isCorner le
    dsimp only at hc0
    rcases hc0 with ⟨⟨i, hi0⟩, ⟨j, hj0⟩⟩
    apply (signChange_caseOfBits_iff b le).mpr
    dsimp only
    refine ⟨i, j, hi0, hj0, ?_⟩
    rw [hpc, hqc] at hend
    rw [hi0, hj0] at hend
    have hi : (c.1 + (cellCorner (0, 0, 0) i.val).1,
        c.2.1 + (cellCorner (0, 0, 0) i.val).2.1,
        c.2.2 + (cellCorner (0, 0, 0) i.val).2.2) = cellCorner c i.val := by
      simp [cellCorner, cornerOf, cornerOffset]
    have hj : (c.1 + (cellCorner (0, 0, 0) j.val).1,
        c.2.1 + (cellCorner (0, 0, 0) j.val).2.1,
        c.2.2 + (cellCorner (0, 0, 0) j.val).2.2) = cellCorner c j.val := by
      simp [cellCorner, cornerOf, cornerOffset]
    change s (c.1 + (cellCorner (0, 0, 0) i.val).1,
        c.2.1 + (cellCorner (0, 0, 0) i.val).2.1,
        c.2.2 + (cellCorner (0, 0, 0) i.val).2.2) !=
      s (c.1 + (cellCorner (0, 0, 0) j.val).1,
        c.2.1 + (cellCorner (0, 0, 0) j.val).2.1,
        c.2.2 + (cellCorner (0, 0, 0) j.val).2.2) at hend
    rw [hi, hj] at hend
    exact hend

/-- A cell case fits in 8 bits. -/
theorem cellCase_lt_256 (s : Lat → Bool) (c : Cell) : DmcOnePad.cellCase s c < 256 := by
  unfold DmcOnePad.cellCase
  split_ifs <;> omega

set_option maxHeartbeats 800000 in
/-- The upper endpoint of a local cube edge is the successor of the lower. -/
theorem localEdgeEnds_succN (c : Cell) (le : Fin 12) :
    let (p, q) := localEdgeEnds c le.val
    q = PadGrid.succN p (localEdgeDir le.val) := by
  fin_cases le <;>
    simp [localEdgeEnds, cellCorner, cornerOf, cornerOffset, mcEdgeVerts,
      localEdgeDir, PadGrid.succN]

set_option maxHeartbeats 800000 in
/-- Recover a local edge id from its lower corner. -/
theorem localEdge_of_lower (c : Cell) (le : Fin 12) :
    let (p, _) := localEdgeEnds c le.val
    DmcOnePad.localEdge p c (localEdgeDir le.val) = le.val := by
  fin_cases le <;>
    simp [localEdgeEnds, DmcOnePad.localEdge, cellCorner, cornerOf, cornerOffset,
      mcEdgeVerts, localEdgeDir]

set_option maxHeartbeats 800000 in
/-- Geometry of a cell incident to a crossed lattice edge under shell
    pinning: the edge's lower endpoint is a corner of the cell, its upper
    endpoint is the adjacent corner along the edge direction, and the cell
    lies in the cell grid. -/
theorem incidentCell_geometry (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false)
    (e : PadEdge) (he : e ∈ PadGrid.crossed n s) (c : Cell)
    (hc : c ∈ DmcOnePad.incidentCells s e) :
    let p := e.1; let d := e.2
    (c.1 ≤ p.1 ∧ c.2.1 ≤ p.2.1 ∧ c.2.2 ≤ p.2.2) ∧
    (p.1 ≤ c.1 + 1 ∧ p.2.1 ≤ c.2.1 + 1 ∧ p.2.2 ≤ c.2.2 + 1) ∧
    ((d = 0 → p.1 = c.1) ∧ (d = 1 → p.2.1 = c.2.1) ∧ (d = 2 → p.2.2 = c.2.2)) ∧
    (c.1 < n ∧ c.2.1 < n ∧ c.2.2 < n) := by
  obtain ⟨p, d⟩ := e
  dsimp only
  obtain ⟨hd, hpL, hqL, hne⟩ := PadGrid.crossed_spec n s he
  obtain ⟨q, hq⟩ := DmcOneEuler.anchorCell_of_pinned n s hpin p d hd hpL hne
  rcases q with ⟨qx, qy, qz⟩
  obtain ⟨ht0, ht1, ht2⟩ := PadGrid.pinned_transverse n s hpin hpL hne
  rw [DmcOnePad.incidentCells, hq] at hc
  cases hs : s p <;>
    interval_cases d <;>
    simp [PadGrid.succN, PadGrid.InLattice, PadGrid.ij, PadGrid.addCell,
      PadGrid.anchorCell, hs] at hpL hqL hq hc ht0 ht1 ht2 ⊢ <;>
    rcases hc with rfl | rfl | rfl | rfl <;>
    simp_all <;> omega

/-- A cell incident to a crossed edge under shell pinning lies in the grid. -/
theorem incidentCells_mem_cellsAll (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false)
    (e : PadEdge) (he : e ∈ PadGrid.crossed n s) (c : Cell)
    (hc : c ∈ DmcOnePad.incidentCells s e) : c ∈ cellsAll n := by
  rw [mem_cellsAll]
  exact (incidentCell_geometry n s hpin e he c hc).2.2.2

set_option maxHeartbeats 800000 in
/-- The local edge of a crossed edge in an incident cell is used by exactly
    one patch: the cell case has a crossing, and this edge owns that patch. -/
theorem crossed_patchUsed (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false)
    (e : PadEdge) (he : e ∈ PadGrid.crossed n s) (c : Cell)
    (hc : c ∈ DmcOnePad.incidentCells s e) :
    0 < mcPatchCount (DmcOnePad.cellCase s c) ∧
    (patchesUsing (DmcOnePad.cellCase s c)
      (DmcOnePad.localEdge e.1 c e.2)).length = 1 := by
  obtain ⟨p, d⟩ := e
  obtain ⟨hd, hpL, hqL, hne⟩ := PadGrid.crossed_spec n s he
  have hg := incidentCell_geometry n s hpin (p, d) he c hc
  dsimp only at hg
  have hleEnds := localEdgeEnds_of_edge_start c p d hd hg.1 hg.2.1 hg.2.2.1
  let lef : Fin 12 := ⟨DmcOnePad.localEdge p c d, DmcOnePad.localEdge_lt_twelve p c d⟩
  have hSC : lef.val ∈ signChangeEdges (DmcOnePad.cellCase s c) := by
    change DmcOnePad.localEdge p c d ∈ signChangeEdges (DmcOnePad.cellCase s c)
    rw [mem_signChangeEdges_iff_endpoints s c lef]
    dsimp only [lef]
    rw [hleEnds]
    simpa [bne_iff_ne] using hne
  let kf : Fin 256 := ⟨DmcOnePad.cellCase s c, cellCase_lt_256 s c⟩
  have hneList : signChangeEdges kf.val ≠ [] := by
    intro hnil
    have : lef.val ∉ signChangeEdges kf.val := by simp [hnil]
    exact this hSC
  have hpos : 0 < mcPatchCount kf.val :=
    (mcPatchCount_pos_iff_crossed kf).2 hneList
  have hSCb : (signChangeEdges kf.val).contains lef.val = true := by
    simpa [List.contains_iff_mem] using hSC
  exact ⟨hpos, by
    simpa [lef] using patches_using_eq_one_of_sign_change kf lef hSCb⟩

set_option maxHeartbeats 800000 in
/-- The endpoints of a local edge lie within one step of the cell. -/
theorem localEdgeEnds_le_add_one (c : Cell) (le : Fin 12) :
    let (p, q) := localEdgeEnds c le.val
    p.1 ≤ c.1 + 1 ∧ p.2.1 ≤ c.2.1 + 1 ∧ p.2.2 ≤ c.2.2 + 1 ∧
    q.1 ≤ c.1 + 1 ∧ q.2.1 ≤ c.2.1 + 1 ∧ q.2.2 ≤ c.2.2 + 1 := by
  fin_cases le <;>
    simp [localEdgeEnds, cellCorner, cornerOf, cornerOffset, mcEdgeVerts, localEdgeDir]

set_option maxHeartbeats 800000 in
/-- The lower endpoint of a local edge is not before the cell origin. -/
theorem localEdgeEnds_ge_cell (c : Cell) (le : Fin 12) :
    let (p, _) := localEdgeEnds c le.val
    c.1 ≤ p.1 ∧ c.2.1 ≤ p.2.1 ∧ c.2.2 ≤ p.2.2 := by
  fin_cases le <;>
    simp [localEdgeEnds, cellCorner, cornerOf, cornerOffset, mcEdgeVerts, localEdgeDir]

set_option maxHeartbeats 800000 in
/-- The lower endpoint of a local edge has offset zero along the edge's own
    direction. -/
theorem localEdgeEnds_dirZero (c : Cell) (le : Fin 12) :
    let (p, _) := localEdgeEnds c le.val
    let d := localEdgeDir le.val
    (d = 0 → p.1 = c.1) ∧ (d = 1 → p.2.1 = c.2.1) ∧ (d = 2 → p.2.2 = c.2.2) := by
  fin_cases le <;>
    simp [localEdgeEnds, cellCorner, cornerOf, cornerOffset, mcEdgeVerts, localEdgeDir]

set_option maxHeartbeats 800000 in
/-- A cell containing the lower corner of a crossed edge, with that corner's
    own-direction coordinate equal to the cell's, is one of the edge's four
    incident cells. -/
theorem cell_of_localEdge_incident (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false)
    (c : Cell) (hcgrid : c ∈ cellsAll n) (p : Lat) (d : Nat) (hd : d < 3)
    (hpL : PadGrid.InLattice n p) (hne : s p ≠ s (PadGrid.succN p d))
    (hge : c.1 ≤ p.1 ∧ c.2.1 ≤ p.2.1 ∧ c.2.2 ≤ p.2.2)
    (hle : p.1 ≤ c.1 + 1 ∧ p.2.1 ≤ c.2.1 + 1 ∧ p.2.2 ≤ c.2.2 + 1)
    (hdir : (d = 0 → p.1 = c.1) ∧ (d = 1 → p.2.1 = c.2.1) ∧ (d = 2 → p.2.2 = c.2.2)) :
    c ∈ DmcOnePad.incidentCells s (p, d) := by
  obtain ⟨q0, hq0⟩ := DmcOneEuler.anchorCell_of_pinned n s hpin p d hd hpL hne
  obtain ⟨ht0, ht1, ht2⟩ := PadGrid.pinned_transverse n s hpin hpL hne
  rcases q0 with ⟨qx, qy, qz⟩
  rcases c with ⟨cx, cy, cz⟩
  rw [DmcOnePad.incidentCells, hq0]
  cases hs : s p <;>
    interval_cases d <;>
    simp [PadGrid.ij, PadGrid.addCell, PadGrid.anchorCell] at hq0 hdir ht0 ht1 ht2 ⊢ <;>
    rcases hge with ⟨hg1, hg2, hg3⟩ <;>
    rcases hle with ⟨hl1, hl2, hl3⟩ <;>
    simp_all
  all_goals
    have hcx : cx = qx ∨ cx = qx + 1 := by omega
    have hcy : cy = qy ∨ cy = qy + 1 := by omega
    have hcz : cz = qz ∨ cz = qz + 1 := by omega
    rcases hcx with hcx | hcx <;> rcases hcy with hcy | hcy <;> rcases hcz with hcz | hcz <;>
      simp_all

/-- Membership in the cell-local MC patch list. -/
theorem mem_mcPatchesOf (n : Nat) (s : Lat → Bool) (v : DV) :
    v ∈ mcPatchesOf n s ↔
      v.1 ∈ cellsAll n ∧ v.2 < mcPatchCount (DmcOnePad.cellCase s v.1) := by
  unfold mcPatchesOf
  simp only [List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨c, hc, i, hi, rfl⟩
    exact ⟨hc, hi⟩
  · rintro ⟨hc, hi⟩
    exact ⟨v.1, hc, v.2, hi, rfl⟩

theorem mem_of_mem_zip_fst {α β : Type*} {l₁ : List α} {l₂ : List β} {a : α} {b : β}
    (h : (a, b) ∈ l₁.zip l₂) : a ∈ l₁ := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons x xs ih =>
      cases l₂ with
      | nil => simp at h
      | cons y ys =>
        simp only [List.zip_cons_cons, List.mem_cons] at h
        rcases h with h | h
        · injection h with ha _
          subst a
          simp
        · simp only [List.mem_cons]
          exact Or.inr (ih h)

theorem mem_of_mem_zip_snd {α β : Type*} {l₁ : List α} {l₂ : List β} {a : α} {b : β}
    (h : (a, b) ∈ l₁.zip l₂) : b ∈ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons x xs ih =>
      cases l₂ with
      | nil => simp at h
      | cons y ys =>
        simp only [List.zip_cons_cons, List.mem_cons] at h
        rcases h with h | h
        · injection h with _ hb
          subst b
          simp
        · simp only [List.mem_cons]
          exact Or.inr (ih h)

/-- Every corner of a quad is an endpoint of one of its directed sides. -/
theorem mem_of_mem_quadCorners {q : List DV} {v : DV}
    (h : v ∈ (DmcOnePad.quadDirectedEdges q).flatMap (fun (a, b) => [a, b])) : v ∈ q := by
  unfold DmcOnePad.quadDirectedEdges at h
  rw [List.mem_flatMap] at h
  rcases h with ⟨⟨a, b⟩, hab, hv⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact mem_of_mem_zip_fst hab
  · have hsub : ∀ {x : DV}, x ∈ q.drop 1 ++ q.take 1 → x ∈ q := by
      intro x hx
      cases q with
      | nil => simp at hx
      | cons q0 qs =>
        simp at hx ⊢
        tauto
    exact hsub (mem_of_mem_zip_snd hab)

/-- An endpoint of a directed side of a quad is a corner of the quad. -/
theorem mem_of_mem_directedEdge {q : List DV} {ed : DV × DV} {v : DV}
    (hed : ed ∈ DmcOnePad.quadDirectedEdges q) (hv : v ∈ [ed.1, ed.2]) : v ∈ q := by
  have hed' : (ed.1, ed.2) ∈ q.zip (q.drop 1 ++ q.take 1) := by
    simpa [DmcOnePad.quadDirectedEdges] using hed
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact mem_of_mem_zip_fst hed'
  · have hsub : ∀ {x : DV}, x ∈ q.drop 1 ++ q.take 1 → x ∈ q := by
      intro x hx
      cases q with
      | nil => simp at hx
      | cons q0 qs =>
        simp at hx ⊢
        tauto
    exact hsub (mem_of_mem_zip_snd hed')

set_option maxHeartbeats 800000 in
/-- Every corner of a four-corner quad is an endpoint of one of its sides. -/
theorem mem_quadCorners_of_mem {q : List DV} {v : DV} (hlen : q.length = 4) (hv : v ∈ q) :
    v ∈ (DmcOnePad.quadDirectedEdges q).flatMap (fun (a, b) => [a, b]) := by
  obtain ⟨a, b, c, dd, rfl⟩ : ∃ a b c dd : DV, q = [a, b, c, dd] := by
    generalize hq : q = q4
    rw [hq] at hlen
    cases q4 with
    | nil => simp at hlen
    | cons a q1 =>
      cases q1 with
      | nil => simp at hlen
      | cons b q2 =>
        cases q2 with
        | nil => simp at hlen
        | cons c q3 =>
          cases q3 with
          | nil => simp at hlen
          | cons dd q5 =>
            cases q5 with
            | nil => exact ⟨a, b, c, dd, rfl⟩
            | cons _ _ => simp at hlen
  simp [DmcOnePad.quadDirectedEdges] at hv ⊢
  aesop

set_option maxHeartbeats 800000 in
/-- The vertices of the general-`n` DMC mesh are exactly the corners of the
    quads of the crossed lattice edges. -/
theorem mem_meshVerts_iff_quad_mem (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false) (v : DV) :
    v ∈ DmcOnePad.meshVerts (DmcOneEuler.dmcOneMeshEdges n s) ↔
      ∃ e : PadEdge, e ∈ PadGrid.crossed n s ∧ v ∈ DmcOneEuler.dmcOneQuadN s e := by
  unfold DmcOnePad.meshVerts DmcOneEuler.dmcOneMeshEdges
  rw [List.mem_eraseDups]
  constructor
  · intro hv
    rw [List.mem_flatMap] at hv
    rcases hv with ⟨ed, hed, hv⟩
    rw [List.mem_flatMap] at hed
    rcases hed with ⟨q, hqmem, hqd⟩
    unfold DmcOneEuler.dmcOneQuads at hqmem
    rw [List.mem_flatMap] at hqmem
    rcases hqmem with ⟨p, hp, hdm⟩
    rw [List.mem_filterMap] at hdm
    rcases hdm with ⟨d, hdmem, hqeq⟩
    have hpL : PadGrid.InLattice n p := PadGrid.mem_latAll.mp hp
    by_cases hcond : (decide (PadGrid.InLattice n (PadGrid.succN p d)) &&
        (s p != s (PadGrid.succN p d))) = true
    · have hc := (Bool.and_eq_true _ _).mp hcond
      have hcrossB : PadGrid.crossedB n s (p, d) = true := by
        unfold PadGrid.crossedB
        simp only [Bool.and_eq_true]
        exact ⟨⟨by simpa using (decide_eq_true_eq.mpr hpL), hc.1⟩, hc.2⟩
      refine ⟨(p, d), PadGrid.crossed_of_crossedB n s hcrossB hdmem, ?_⟩
      simp [hcond] at hqeq
      have hqeq' : q = DmcOneEuler.dmcOneQuadN s (p, d) := hqeq.symm
      rw [hqeq'] at hqd
      exact mem_of_mem_directedEdge hqd hv
    · simp [hcond] at hqeq
  · rintro ⟨e, he, hvq⟩
    obtain ⟨p, d⟩ := e
    obtain ⟨hd, hpL, hqL, hne⟩ := PadGrid.crossed_spec n s he
    have hlen := (DmcOneEuler.quad_ok n s hpin p d hd hpL hne).1
    have hmemquad : DmcOneEuler.dmcOneQuadN s (p, d) ∈ DmcOneEuler.dmcOneQuads n s := by
      unfold DmcOneEuler.dmcOneQuads
      rw [List.mem_flatMap]
      refine ⟨p, PadGrid.mem_latAll.mpr hpL, ?_⟩
      rw [List.mem_filterMap]
      refine ⟨d, by simpa using hd, ?_⟩
      have hbn : (decide (PadGrid.InLattice n (PadGrid.succN p d)) &&
          (s p != s (PadGrid.succN p d))) = true := by
        rw [Bool.and_eq_true]
        exact ⟨decide_eq_true_eq.mpr hqL, by simpa [bne_iff_ne] using hne⟩
      simp [hbn]
    have hqshape : ∃ a b c dd : DV, DmcOneEuler.dmcOneQuadN s (p, d) = [a, b, c, dd] := by
      generalize hq : DmcOneEuler.dmcOneQuadN s (p, d) = q4
      rw [hq] at hlen
      cases q4 with
      | nil => simp at hlen
      | cons a q1 =>
        cases q1 with
        | nil => simp at hlen
        | cons b q2 =>
          cases q2 with
          | nil => simp at hlen
          | cons c q3 =>
            cases q3 with
            | nil => simp at hlen
            | cons dd q5 =>
              cases q5 with
              | nil => exact ⟨a, b, c, dd, rfl⟩
              | cons _ _ => simp at hlen
    rcases hqshape with ⟨a, b, c, dd, hqeq⟩
    rw [hqeq] at hvq hmemquad
    have mkMem (ed : DV × DV) (hed : ed ∈ DmcOnePad.quadDirectedEdges [a, b, c, dd]) :
        ed ∈ DmcOneEuler.dmcOneMeshEdges n s := by
      rw [DmcOneEuler.dmcOneMeshEdges, List.mem_flatMap]
      exact ⟨[a, b, c, dd], hmemquad, hed⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hvq
    rcases hvq with hvEq | hvEq | hvEq | hvEq
    · rw [hvEq]
      rw [List.mem_flatMap]
      refine ⟨(a, b), mkMem (a, b) (by simp [DmcOnePad.quadDirectedEdges]), ?_⟩
      simp
    · rw [hvEq]
      rw [List.mem_flatMap]
      refine ⟨(a, b), mkMem (a, b) (by simp [DmcOnePad.quadDirectedEdges]), ?_⟩
      simp
    · rw [hvEq]
      rw [List.mem_flatMap]
      refine ⟨(b, c), mkMem (b, c) (by simp [DmcOnePad.quadDirectedEdges]), ?_⟩
      simp
    · rw [hvEq]
      rw [List.mem_flatMap]
      refine ⟨(dd, a), mkMem (dd, a) (by simp [DmcOnePad.quadDirectedEdges]), ?_⟩
      simp

set_option maxHeartbeats 800000 in
/-- **Global lifting** (general `n`): every cell-local MC patch id is
    realized as a corner of the quad of a crossed lattice edge incident to
    the cell. This is the cube-local-edge ↔ global-crossed-edge bridge. -/
theorem exists_crossed_realizing_patch (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false)
    (c : Cell) (hcgrid : c ∈ cellsAll n) (i : Nat)
    (hi : i < mcPatchCount (DmcOnePad.cellCase s c)) :
    ∃ e : PadEdge, e ∈ PadGrid.crossed n s ∧
      c ∈ DmcOnePad.incidentCells s e ∧
      (patchesUsing (DmcOnePad.cellCase s c)
        (DmcOnePad.localEdge e.1 c e.2)).headD 0 = i := by
  let k := DmcOnePad.cellCase s c
  let kf : Fin 256 := ⟨k, cellCase_lt_256 s c⟩
  let iff : Fin (mcPatchCount k) := ⟨i, hi⟩
  obtain ⟨le, hbits, hhead⟩ := patch_realized_by_localEdge kf iff
  dsimp [k] at hbits hhead
  let p : Lat := (localEdgeEnds c le.val).1
  let q : Lat := (localEdgeEnds c le.val).2
  let d : Nat := localEdgeDir le.val
  have hq : q = PadGrid.succN p d := by
    dsimp only [p, q, d]
    exact localEdgeEnds_succN c le
  have hSC : le.val ∈ signChangeEdges k := by
    simpa [signChangeEdges, bne_iff_ne] using hbits
  have hend : s p != s q := by
    have h := (mem_signChangeEdges_iff_endpoints s c le).mp hSC
    dsimp only at h
    simpa [p, q] using h
  have hleBound := localEdgeEnds_le_add_one c le
  have hgeBound := localEdgeEnds_ge_cell c le
  have hdirBound := localEdgeEnds_dirZero c le
  dsimp only at hleBound hgeBound hdirBound
  rcases hleBound with ⟨hp1, hp2, hp3, hq1, hq2, hq3⟩
  have hp_le : p.1 ≤ c.1 + 1 ∧ p.2.1 ≤ c.2.1 + 1 ∧ p.2.2 ≤ c.2.2 + 1 := by
    dsimp only [p]
    exact ⟨hp1, hp2, hp3⟩
  have hq_le : q.1 ≤ c.1 + 1 ∧ q.2.1 ≤ c.2.1 + 1 ∧ q.2.2 ≤ c.2.2 + 1 := by
    dsimp only [q]
    exact ⟨hq1, hq2, hq3⟩
  have hp_ge : c.1 ≤ p.1 ∧ c.2.1 ≤ p.2.1 ∧ c.2.2 ≤ p.2.2 := by
    dsimp only [p]
    exact hgeBound
  have hp_dir : (d = 0 → p.1 = c.1) ∧ (d = 1 → p.2.1 = c.2.1) ∧ (d = 2 → p.2.2 = c.2.2) := by
    dsimp only [p, d]
    exact hdirBound
  have hc1 := mem_cellsAll.mp hcgrid
  have hpL : PadGrid.InLattice n p := ⟨by omega, by omega, by omega⟩
  have hqL : PadGrid.InLattice n q := ⟨by omega, by omega, by omega⟩
  have hd : d < 3 := by
    dsimp only [d]
    fin_cases le <;> simp [localEdgeDir]
  have hneProp : s p ≠ s (PadGrid.succN p d) := by
    rw [← hq]
    exact bne_iff_ne.mp hend
  have hcrossB : PadGrid.crossedB n s (p, d) = true := by
    unfold PadGrid.crossedB
    rw [Bool.and_eq_true]
    constructor
    · rw [Bool.and_eq_true]
      exact ⟨decide_eq_true_eq.mpr hpL, by simpa [hq] using (decide_eq_true_eq.mpr hqL)⟩
    · simpa [hq] using hend
  have heCross : (p, d) ∈ PadGrid.crossed n s :=
    PadGrid.crossed_of_crossedB n s hcrossB (by simpa using hd)
  have hinc : c ∈ DmcOnePad.incidentCells s (p, d) :=
    cell_of_localEdge_incident n s hpin c hcgrid p d hd hpL hneProp
      hp_ge hp_le hp_dir
  have hleEq : DmcOnePad.localEdge p c d = le.val := by
    dsimp only [p, d]
    exact localEdge_of_lower c le
  refine ⟨(p, d), heCross, hinc, ?_⟩
  rw [hleEq]
  exact hhead

set_option maxHeartbeats 800000 in
/-- Every DMC mesh vertex is a cell-local MC patch (general `n`). -/
theorem meshVertex_mem_mcPatches (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false) (v : DV)
    (hv : v ∈ DmcOnePad.meshVerts (DmcOneEuler.dmcOneMeshEdges n s)) :
    v ∈ mcPatchesOf n s := by
  obtain ⟨e, he, hvq⟩ := (mem_meshVerts_iff_quad_mem n s hpin v).mp hv
  obtain ⟨p, d⟩ := e
  obtain ⟨hd, hpL, hqL, hne⟩ := PadGrid.crossed_spec n s he
  have hbne : (s p == s (PadGrid.succN p d)) = false := by
    cases h1 : s p <;> cases h2 : s (PadGrid.succN p d) <;> simp [h1, h2] at hne ⊢
  have hqeq : DmcOneEuler.dmcOneQuadN s (p, d) =
      (DmcOnePad.incidentCells s (p, d)).map (fun c => DmcOnePad.cellPatchVertex s c p d) := by
    unfold DmcOneEuler.dmcOneQuadN
    rw [ite_eq_right (by simp [hbne])]
  rw [hqeq, List.mem_map] at hvq
  rcases hvq with ⟨c, hc, hvEq⟩
  have hcgrid := incidentCells_mem_cellsAll n s hpin (p, d) he c hc
  have hused := crossed_patchUsed n s hpin (p, d) he c hc
  have hbnd : (patchesUsing (DmcOnePad.cellCase s c)
        (DmcOnePad.localEdge p c d)).headD 0 <
      mcPatchCount (DmcOnePad.cellCase s c) :=
    patchesUsing_headD_lt_mcPatchCount_of_pos
      ⟨DmcOnePad.cellCase s c, cellCase_lt_256 s c⟩
      ⟨DmcOnePad.localEdge p c d, DmcOnePad.localEdge_lt_twelve p c d⟩ hused.1
  rw [← hvEq]
  unfold DmcOnePad.cellPatchVertex
  dsimp only
  rw [mem_mcPatchesOf]
  exact ⟨hcgrid, hbnd⟩

set_option maxHeartbeats 800000 in
/-- Every cell-local MC patch is a DMC mesh vertex (general `n`). -/
theorem mcPatch_mem_meshVertex (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false) (v : DV)
    (hv : v ∈ mcPatchesOf n s) :
    v ∈ DmcOnePad.meshVerts (DmcOneEuler.dmcOneMeshEdges n s) := by
  rcases v with ⟨c, i⟩
  rw [mem_mcPatchesOf] at hv
  obtain ⟨hcgrid, hi⟩ := hv
  obtain ⟨e, he, hinc, hhead⟩ := exists_crossed_realizing_patch n s hpin c hcgrid i hi
  obtain ⟨p, d⟩ := e
  have hne := (PadGrid.crossed_spec n s he).2.2.2
  have hbne : (s p == s (PadGrid.succN p d)) = false := by
    cases h1 : s p <;> cases h2 : s (PadGrid.succN p d) <;> simp [h1, h2] at hne ⊢
  have hqmem : DmcOnePad.cellPatchVertex s c p d ∈ DmcOneEuler.dmcOneQuadN s (p, d) := by
    unfold DmcOneEuler.dmcOneQuadN
    rw [ite_eq_right (by simp [hbne])]
    rw [List.mem_map]
    exact ⟨c, hinc, rfl⟩
  have hvEq : DmcOnePad.cellPatchVertex s c p d = (c, i) := by
    unfold DmcOnePad.cellPatchVertex
    dsimp only
    rw [hhead]
  rw [hvEq] at hqmem
  exact (mem_meshVerts_iff_quad_mem n s hpin (c, i)).mpr ⟨(p, d), he, hqmem⟩

set_option maxHeartbeats 800000 in
/-- **MC patch ↔ DMC vertex membership equivalence (general `n`,
    shell-pinned)**: the cell-local MC patches and the DMC mesh vertices are
    the same set. -/
theorem mcPatches_mem_meshVerts_iff (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false) (v : DV) :
    v ∈ mcPatchesOf n s ↔ v ∈ DmcOnePad.meshVerts (DmcOneEuler.dmcOneMeshEdges n s) :=
  ⟨mcPatch_mem_meshVertex n s hpin v, meshVertex_mem_mcPatches n s hpin v⟩

set_option maxHeartbeats 800000 in
/-- The cell-local patch list is duplicate-free. -/
theorem mcPatchesOf_nodup (n : Nat) (s : Lat → Bool) : (mcPatchesOf n s).Nodup := by
  unfold mcPatchesOf
  apply List.nodup_flatMap.mpr
  constructor
  · intro c hc
    apply List.Nodup.map
    · intro a b h
      exact congrArg Prod.snd h
    · exact List.nodup_range
  · refine (List.nodup_iff_pairwise_ne.mp (cellsAll_nodup n)).imp ?_
    intro a b hne
    simp only [Function.onFun]
    intro e he he'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    obtain ⟨j, hj, hjEq⟩ := List.mem_map.mp he'
    exact hne (congrArg Prod.fst hjEq).symm

set_option maxHeartbeats 800000 in
/-- `eraseDups` is duplicate-free (proved by strong induction on length). -/
theorem list_nodup_eraseDups [BEq α] [LawfulBEq α] :
    ∀ n : Nat, ∀ l : List α, l.length = n → l.eraseDups.Nodup := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro l hlen
    cases l with
    | nil => exact List.nodup_nil
    | cons a as =>
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hmem
        rw [List.mem_eraseDups] at hmem
        simp only [List.mem_filter] at hmem
        have haa : (a == a) = true := beq_iff_eq.mpr rfl
        simpa [haa] using hmem.2
      · apply ih (as.filter fun b => !b == a).length
        · have hle := List.length_filter_le (fun b => !b == a) as
          simp at hlen
          omega
        · rfl

/-- The mesh vertex list is duplicate-free. -/
theorem meshVerts_nodup (es : List (DV × DV)) : (DmcOnePad.meshVerts es).Nodup := by
  unfold DmcOnePad.meshVerts
  exact list_nodup_eraseDups _ _ rfl

set_option maxHeartbeats 800000 in
/-- **Patch-cardinality identity (general `n`)**: the number of cell-local
    MC patches equals the number of DMC mesh vertices. This discharges the
    previously named hypothesis `hcard` of `chi_dual_eq_of_patch_card`. -/
theorem patch_card_general (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false) :
    (mcPatchesOf n s).length =
      (DmcOnePad.meshVerts (DmcOneEuler.dmcOneMeshEdges n s)).length := by
  apply PadGrid.length_eq_of_mem_iff_of_nodup
  · exact mcPatches_mem_meshVerts_iff n s hpin
  · exact mcPatchesOf_nodup n s
  · exact meshVerts_nodup _

/-- **Patch ↔ DMC vertex bijection (general `n`)**: the MC cube-patches are
    in bijection with the DMC mesh vertices, for every shell-pinned sign
    field on a padded grid of any size. -/
noncomputable def patchVertexEquivN (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false) :
    {p // p ∈ mcPatchesOf n s} ≃
      {v // v ∈ DmcOnePad.meshVerts (DmcOneEuler.dmcOneMeshEdges n s)} :=
  Equiv.ofBijective
    (fun p => ⟨p.val, (mcPatches_mem_meshVerts_iff n s hpin p.val).mp p.property⟩)
    ⟨by
      intro a b h
      exact Subtype.ext (congrArg
        (fun z : {v // v ∈ DmcOnePad.meshVerts (DmcOneEuler.dmcOneMeshEdges n s)} => z.val) h),
     by
      intro v
      refine ⟨⟨v.val, (mcPatches_mem_meshVerts_iff n s hpin v.val).mpr v.property⟩, ?_⟩
      exact Subtype.ext rfl⟩

set_option maxHeartbeats 800000 in
/-- **χ duality (general `n`, unconditional)**: for every shell-pinned sign
    field on any padded grid, the dual MC patch complex and the DMC mesh
    have the same Euler characteristic. -/
theorem chi_dual_eq (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false) :
    chiMcDual n s = chiDmcMesh n s :=
  chi_dual_eq_of_patch_card n s (patch_card_general n s hpin)

end DmcOneDual
end Vdb
