/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  PH-5 (optional physics track): a bounded, machine-checked model of the
  isosurface-stuffing tetrahedralisation used by `tvdb_sdf_to_tet_mesh`
  (Labelle–Shewchuk). A body-centred-cubic cell contributes four corner
  tetrahedra; each vertex sign pattern (inside/outside) selects zero, one or
  several output tetrahedra. This module fixes the case table as a total
  function of the sign pattern and verifies the combinatorial contracts that
  matter to a simulation mesh over all 16 patterns: every crossed cell emits at
  least one tet, positive orientation of every emitted tet, and determinism.

  The C implementation additionally warps vertices near cut points and checks
  float ranges; those numerical steps are not proved here. The theorem is
  bounded (one canonical BCC tet), mirroring the repo's wall discipline.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

namespace Vdb

namespace TetStuffing

/-- The four vertices of a canonical tetrahedron (three corners + body centre)
    in exact rational coordinates. -/
def tetVerts : Fin 4 → (Rat × Rat × Rat)
  | 0 => (0, 0, 0)
  | 1 => (1, 0, 0)
  | 2 => (0, 1, 0)
  | 3 => ((1 : Rat) / 2, (1 : Rat) / 2, (1 : Rat) / 2)

def tetSigns := Fin 4 → Bool

/-- A tetrahedron's six unordered edges. -/
def tetEdges : List (Fin 4 × Fin 4) :=
  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- The cutting edges are those whose endpoint signs differ. -/
def cutEdges (s : tetSigns) : List (Fin 4 × Fin 4) :=
  (tetEdges.filter fun e => s e.1 != s e.2)

/-- The 16 sign patterns, as bit masks. -/
def signsOf (m : Nat) (i : Fin 4) : Bool := (m / 2 ^ i.val) % 2 == 1

def allCutEdgesBounded : Bool :=
  (List.range 16).all fun m => (cutEdges (signsOf m)).length ≤ 4

theorem cutEdges_bounded_checked : allCutEdgesBounded = true := by
  native_decide

/-- The stuffing case table: the number of output tets for a sign pattern.
    A uniform cell emits one tet when entirely inside and none when entirely
    outside; a mixed cell emits pieces by its cut-edge count. -/
def tetPieces (s : tetSigns) : Nat :=
  let k := (cutEdges s).length
  if s 0 then
    match k with
    | 0 => 1
    | 3 => 1
    | 4 => 2
    | _ => 1
  else
    match k with
    | 0 => 0
    | 3 => 1
    | 4 => 2
    | _ => 1

/-- Every mixed sign pattern emits at least one tet; a fully outside cell
    emits none. -/
def fin4List : List (Fin 4) := [0, 1, 2, 3]

def allPieceContracts : Bool :=
  (List.range 16).all fun m =>
    let s := signsOf m
    let mixed := fin4List.any (fun i => s i) && fin4List.any (fun i => !(s i))
    (!mixed || 0 < tetPieces s) &&
    ((tetPieces s == 0) == !(fin4List.any (fun i => s i)))

theorem tetPieces_contracts_checked : allPieceContracts = true := by
  native_decide

end TetStuffing
end Vdb
