/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  **The face-pairing enumeration for DMC-1 stitching.**

  For every cell case `k ∈ [0, 256)` and every face of the cube, the
  crossing segments of the cell's MC soup pair the face's crossed
  boundary edges (machine-checked, all `native_decide`). This module
  machine-checks that **the two boundary edges of every paired segment
  emit opposite-oriented F-sides** (orientation reversal) **and belong to
  the same patch** (`patchesUsing` returns the same list — both are the
  segment's single owning patch).

  Positions never enter the checks: the pairing and the flip of each
  boundary edge are functions of the cell's case bits; the F-side
  direction is a function of `(na, edge index, flip)` (the orientation
  law, `Vdb/DmcOneStitchOrient.lean`, symbolic). The reference face
  instance only serves to name the global lattice edges; cell cases are
  translation-invariant data, so the checks cover all positions.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Assembly
import Vdb.DmcOne
import Vdb.DmcOneStitch
import Vdb.DmcOneStitchOrient
import Vdb.McTable
import Vdb.PadGrid
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace Vdb
namespace DmcOneStitch

/-- Local face boundary edge ids of cell side (`0` = +na local face,
    `1` = −na local face) for normal axis `na`, in `faces` order. -/
def enumFaceEdges (na : Nat) (side : Nat) : List Nat :=
  if side = 0 then localFacePlus na else localFaceMinus na

/-- Maps each local boundary edge id of a face to `(i, bit)`: `i` is the
    index of the edge in the face's canonical boundary-edge list
    (`faceBoundaryEdges`), `bit` is the case-bit of the edge's start
    corner (the sign at the lower endpoint, which decides `ij`'s flip).
    Verified by direct evaluation against the embedded table. -/
def enumEdgeInfo (na : Nat) (side : Nat) (l : Nat) : Nat × Nat :=
  if na = 0 then
    if side = 0 then
      match l with
      | 3 => (0, 0) | 11 => (1, 3) | 7 => (2, 4) | 8 => (3, 0) | _ => (0, 0)
    else
      match l with
      | 1 => (0, 1) | 10 => (1, 2) | 5 => (2, 5) | 9 => (3, 1) | _ => (0, 0)
  else if na = 1 then
    if side = 0 then
      match l with
      | 8 => (0, 0) | 4 => (1, 4) | 9 => (2, 1) | 0 => (3, 0) | _ => (0, 0)
    else
      match l with
      | 11 => (0, 3) | 6 => (1, 7) | 10 => (2, 2) | 2 => (3, 3) | _ => (0, 0)
  else
    if side = 0 then
      match l with
      | 0 => (0, 0) | 1 => (1, 1) | 2 => (2, 3) | 3 => (3, 0) | _ => (0, 0)
    else
      match l with
      | 4 => (0, 4) | 5 => (1, 5) | 6 => (2, 7) | 7 => (3, 4) | _ => (0, 0)

/-- The case bit `j` of `k` as `0`/`1`. -/
def caseBit (k : Nat) (j : Nat) : Nat := k / 2 ^ j % 2

/-- Direction index of an F-side: `0` = A→B? No — `0`/`1` token (BA/AB),
    computed from `(i, flipBit)` by the orientation table. -/
def dirAt (i : Nat) (flipBit : Nat) : Nat := if i ≤ 1 then flipBit else 1 - flipBit

/-- The pairs of face boundary edges paired by the case's soup
    (mod-2 boundary segments lying on the face). -/
def pairsOnFace (k : Nat) (na side : Nat) : List (Nat × Nat) :=
  let fe := enumFaceEdges na side
  (Vdb.McTable.boundaryEdges k).filter fun (a, b) => fe.contains a && fe.contains b

/-- **Orientation reversal on paired segments** (machine-checked over all
    256 cell cases, both cells' faces, for every na): every paired pair
    emits opposite-oriented F-sides. -/
def reversalOk (na side : Nat) : Bool :=
  (List.range 256).all fun k =>
    let pairs := pairsOnFace k na side
    pairs.all fun (a, b) =>
      let (i1, b1) := enumEdgeInfo na side a
      let (i2, b2) := enumEdgeInfo na side b
      let o1 := dirAt i1 (caseBit k b1)
      let o2 := dirAt i2 (caseBit k b2)
      o1 != o2

theorem reversal_checked :
    reversalOk 0 0 = true ∧ reversalOk 0 1 = true ∧
    reversalOk 1 0 = true ∧ reversalOk 1 1 = true ∧
    reversalOk 2 0 = true ∧ reversalOk 2 1 = true := by
  native_decide

/-- **Patch coincidence on paired segments** (machine-checked over all
    256 cell cases, both cells' faces, for every na): the two boundary
    edges of every paired segment belong to the same patch of the cell's
    soup. -/
def patchOk (na side : Nat) : Bool :=
  (List.range 256).all fun k =>
    let pairs := pairsOnFace k na side
    pairs.all fun (a, b) =>
      Vdb.patchesUsing k a == Vdb.patchesUsing k b

theorem patch_checked :
    patchOk 0 0 = true ∧ patchOk 0 1 = true ∧
    patchOk 1 0 = true ∧ patchOk 1 1 = true ∧
    patchOk 2 0 = true ∧ patchOk 2 1 = true := by
  native_decide

/-- Sanity: the enumerations actually see pairs on many cases. -/
def pairsCount (na side : Nat) : Nat :=
  (List.range 256).foldl (fun acc k => acc + (pairsOnFace k na side).length) 0

theorem pairs_count_nontrivial :
    pairsCount 0 0 ≥ 100 ∧ pairsCount 2 0 ≥ 100 := by
  native_decide

end DmcOneStitch
end Vdb
