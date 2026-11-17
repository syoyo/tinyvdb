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

  What is **not** claimed: that each component is *literally* a sphere
  (genus is not computed), the arbitrary-`n` statement (the bounded
  shell-pinned instance only; the general theorem remains open and
  multi-week), and any statement about the patch correspondence of the
  duality beyond connectivity.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Assembly
import Vdb.DmcOne
import Vdb.DmcOnePad
import Vdb.McTable
import Vdb.PadGrid
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

end DmcOneDual
end Vdb
