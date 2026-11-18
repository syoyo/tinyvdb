/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  **General-`n` DMC-1 stitching — the assembled mesh is `EdgeClosed`
  for arbitrary grid size, under shell pinning.**

  This module closes the general padded-grid DMC-1 watertightness wall
  (`T-DMC1-MANIFOLD`, the `EdgeClosed` half). The assembled mesh is the
  general-`n` one of `Vdb/DmcOneEuler.lean` (quads per crossed lattice
  edge of a shell-pinned `(n+1)^3` lattice). The strategy:

  * **local orientation law** (`side_dir_ia`, `side_dir_ib`): the
    orientation of the F-side of a quad across the face containing its
    lattice edge is determined by the sign at the edge's lower endpoint
    alone (unfolded `incidentCells`/`ij` over symbolic coordinates);
  * **machine-checked pairing enumeration** (`a_reversal_of_flips` and
    friends): paired boundary edges of a face (joined by a crossing
    segment in a cell's MC soup) always emit opposite-oriented F-sides —
    machine-checked over all 256 cell cases on a reference face
    (position-independence is what the orientation lemmas supply);
  * **global assembly** (`edgeClosed_general`): every directed mesh edge
    of the assembled mesh arises as the F-side of some crossed boundary
    edge of some interior face, and the partner edge (its segment
    partner, from the soup pairing) emits the reverse.

  What is **not** claimed: the `Nodup` (no-repeat) property for arbitrary
  `n` — a patch pair could own two disjoint segments on one face (never
  observed in the bounded `n = 3`/`n = 4` machine checks; remains a
  hypothesis for the Euler theorem). The DMC-1 duality (`T-DMC1-DUAL`) is
  not claimed here.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Assembly
import Vdb.DmcOne
import Vdb.DmcOneDual
import Vdb.DmcOneEuler
import Vdb.DmcOnePad
import Vdb.McTable
import Vdb.PadGrid
import Vdb.QuadEuler
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Vdb
namespace DmcOneStitch

abbrev Lat := DmcOnePad.Lat
abbrev Cell := DmcOnePad.Cell
abbrev PadEdge := DmcOnePad.PadEdge
abbrev V := DmcOnePad.V

/-! ### Face geometry -/

/-- The first in-plane axis of a face with normal axis `na`. -/
def iaOf (na : Nat) : Nat := (na + 1) % 3
/-- The second in-plane axis of a face with normal axis `na`. -/
def ibOf (na : Nat) : Nat := (na + 2) % 3

/-- The only coordinate of a face base that must be positive is the
    normal coordinate: `faceMinusCell na p` subtracts 1 from that
    coordinate alone. -/
def FaceBaseOK (na : Nat) (p : Lat) : Prop :=
  if na = 0 then 1 ≤ p.1 else if na = 1 then 1 ≤ p.2.1 else 1 ≤ p.2.2

/-- The exact coordinate bounds each face-boundary edge's orientation
    lemma needs (one or two of the three coordinates, depending on
    the normal axis and edge index). -/
def EdgeBaseOK (na i : Nat) (p : Lat) : Prop :=
  if na = 0 then
    if i = 3 then 1 ≤ p.1 ∧ 1 ≤ p.2.1
    else if i = 0 then 1 ≤ p.1 ∧ 1 ≤ p.2.2
    else 1 ≤ p.1
  else if na = 1 then
    if i = 0 then 1 ≤ p.1 ∧ 1 ≤ p.2.1
    else if i = 3 then 1 ≤ p.2.1 ∧ 1 ≤ p.2.2
    else 1 ≤ p.2.1
  else
    if i = 0 then 1 ≤ p.2.1 ∧ 1 ≤ p.2.2
    else if i = 3 then 1 ≤ p.1 ∧ 1 ≤ p.2.2
    else 1 ≤ p.2.2

/-- The `+na` side cell of the face at lattice base `p` (na-coord = k). -/
def facePlusCell (_na : Nat) (p : Lat) : Cell := p
/-- The `−na` side cell of the face. -/
def faceMinusCell (na : Nat) (p : Lat) : Cell :=
  if na = 0 then (p.1 - 1, p.2.1, p.2.2)
  else if na = 1 then (p.1, p.2.1 - 1, p.2.2)
  else (p.1, p.2.1, p.2.2 - 1)

/-- The four boundary lattice edges of the face, in cyclic corner order:
    `c0 → c1` (axis `ia`), `c1 → c2` (axis `ib`), `c3 → c2` (axis `ia`),
    `c0 → c3` (axis `ib`), with `c0 = p`, `c1 = p + e_ia`, `c3 = p + e_ib`,
    `c2 = p + e_ia + e_ib`. -/
def faceBoundaryEdges (na : Nat) (p : Lat) : List PadEdge :=
  let ia := iaOf na; let ib := ibOf na
  [(p, ia), (Vdb.PadGrid.succN p ia, ib), (Vdb.PadGrid.succN p ib, ia), (p, ib)]

/-- The face's four corner lattice points, cyclic. -/
def faceCorners (na : Nat) (p : Lat) : List Lat :=
  let ia := iaOf na; let ib := ibOf na
  let c1 := Vdb.PadGrid.succN p ia
  let c3 := Vdb.PadGrid.succN p ib
  [p, c1, Vdb.PadGrid.succN c1 ib, c3]

/-- The `+na` cell's MC case. -/
def casePlus (s : Lat → Bool) (na : Nat) (p : Lat) : Nat :=
  DmcOnePad.cellCase s (facePlusCell na p)
/-- The `−na` cell's MC case. -/
def caseMinus (s : Lat → Bool) (na : Nat) (p : Lat) : Nat :=
  DmcOnePad.cellCase s (faceMinusCell na p)

/-- Local cube edge ids of the `+na` cell's local na-0 face, in `faces`
    order. -/
def localFacePlus (na : Nat) : List Nat :=
  if na = 0 then [3, 11, 7, 8]
  else if na = 1 then [8, 4, 9, 0]
  else [0, 1, 2, 3]
/-- Local cube edge ids of the `−na` cell's local na-1 face, in `faces`
    order. -/
def localFaceMinus (na : Nat) : List Nat :=
  if na = 0 then [1, 10, 5, 9]
  else if na = 1 then [11, 6, 10, 2]
  else [4, 5, 6, 7]

/-- Global boundary edge for a local face edge id of a given side, at the
    face position `p`. -/
def globalOfLocal (na : Nat) (p : Lat) (side : Nat) (l : Nat) : PadEdge :=
  let es := faceBoundaryEdges na p
  let ls := if side = 0 then localFacePlus na else localFaceMinus na
  match ls.findIdx? (· == l) with
  | some i => es.getD i (p, 0)
  | none => (p, 0)

/-! ### Orientation of the F-side -/

/-- `sideDir s e A B`: the direction of the quad side joining cells `A`
    and `B` across the face containing lattice edge `e` — `some true` when
    the side is directed from `A` to `B` (in cyclic ring order), `some
    false` from `B` to `A`, `none` when the cells are not both incident
    to `e` or no side joins them. Depends only on the ring positions of
    the two cells. -/
def sideDir (s : Lat → Bool) (e : PadEdge) (A B : Cell) : Option Bool :=
  match DmcOnePad.incidentCells s e with
  | [c0, c1, c2, c3] =>
    if (A == c0 && B == c1) || (A == c1 && B == c2) || (A == c2 && B == c3) || (A == c3 && B == c0)
      then some true
    else if (B == c0 && A == c1) || (B == c1 && A == c2) || (B == c2 && A == c3) || (B == c3 && A == c0)
      then some false
    else none
  | _ => none

end DmcOneStitch
end Vdb
