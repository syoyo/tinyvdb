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

/-- Face corner bits of cell `k` in cyclic corner order, for the plus
    (`side = 0`) and minus (`side = 1`) side frames. -/
def maskPlus (na k : Nat) : List Nat :=
  match na with
  | 0 => [0, 3, 7, 4].map (caseBit k)
  | 1 => [0, 1, 5, 4].map (caseBit k)
  | _ => [0, 1, 2, 3].map (caseBit k)

def maskMinus (na k : Nat) : List Nat :=
  match na with
  | 0 => [1, 2, 6, 5].map (caseBit k)
  | 1 => [3, 2, 6, 7].map (caseBit k)
  | _ => [4, 5, 6, 7].map (caseBit k)

/-- The index of the frame-local edge `l` in the face's boundary-edge
    list. Both frames traverse the face corners in the same cyclic
    order, so the index is frame-independent. -/
def edgeIndex (na side l : Nat) : Nat :=
  (enumFaceEdges na side).findIdx? (· == l) |>.getD 0

/-- The pairing of a case on a face, as index pairs (`min, max`-normalized). -/
def pairsIdx (k : Nat) (na side : Nat) : List (Nat × Nat) :=
  (pairsOnFace k na side).map fun (a, b) =>
    let i := edgeIndex na side a; let j := edgeIndex na side b
    if i ≤ j then (i, j) else (j, i)

/-- Multiset equality of pair lists (small, 4 indices). -/
def pairsMultiEq (l₁ l₂ : List (Nat × Nat)) : Bool :=
  let allPairs := (List.range 4).flatMap fun i => (List.range 4).map fun j => (i, j)
  allPairs.all fun p => l₁.count p == l₂.count p

/-- **Cross-cell pairing correspondence** (machine-checked over all
    256×256 pairs of cell cases, for every normal axis): two cells
    whose shared face carries the same corner signs pair the same
    geometric boundary edges — the paired-edge sets coincide index-wise
    between the two local frames (which traverse the face corners in the
    same cyclic order). -/
def pairingCrossOk (na : Nat) : Bool :=
  (List.range 256).all fun k1 =>
    (List.range 256).all fun k2 =>
      !(maskPlus na k1 == maskMinus na k2) || pairsMultiEq (pairsIdx k1 na 0) (pairsIdx k2 na 1)

theorem pairing_cross_checked :
    pairingCrossOk 0 = true ∧ pairingCrossOk 1 = true ∧ pairingCrossOk 2 = true := by
  native_decide

def pairingAgreeCount (na : Nat) : Nat :=
  (List.range 256).foldl (fun acc k1 =>
    acc + (List.range 256).countP (fun k2 => maskPlus na k1 == maskMinus na k2)) 0

theorem pairing_agree_nontrivial :
    1000 ≤ pairingAgreeCount 0 ∧ 1000 ≤ pairingAgreeCount 2 := by
  native_decide



/-- The cell case as a function of the 8 corner signs (in Bourke
    corner order). -/
def mkCase (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Nat :=
  (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) + (if b3 then 8 else 0)
  + (if b4 then 16 else 0) + (if b5 then 32 else 0) + (if b6 then 64 else 0) + (if b7 then 128 else 0)

/-- The `j`-th bit of the case is the `j`-th corner sign —
    machine-checked over all 256 sign assignments. -/
theorem mkCase_bit :
    ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) (j : Nat), j < 8 →
      mkCase b0 b1 b2 b3 b4 b5 b6 b7 / 2 ^ j % 2 =
        if ([b0, b1, b2, b3, b4, b5, b6, b7].getD j false) = true then 1 else 0 := by
  native_decide


/-- `caseBit` of a case built from sign bits — a symbolic accessor
    bridge for the mask reasoning. -/
theorem caseBit_mkCase :
    ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) (j : Nat), j < 8 →
      caseBit (mkCase b0 b1 b2 b3 b4 b5 b6 b7) j =
        if ([b0, b1, b2, b3, b4, b5, b6, b7].getD j false) = true then 1 else 0 := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 j hj
  exact mkCase_bit b0 b1 b2 b3 b4 b5 b6 b7 j hj

/-- The cell case as a function of the 8 corner sign values. -/
theorem mkCase_eq_cellCase (s : Vdb.PadGrid.Lat → Bool) (c : Vdb.DmcOnePad.Cell) :
    Vdb.DmcOnePad.cellCase s c =
      mkCase (s (c.1, c.2.1, c.2.2)) (s (c.1 + 1, c.2.1, c.2.2)) (s (c.1 + 1, c.2.1 + 1, c.2.2))
             (s (c.1, c.2.1 + 1, c.2.2)) (s (c.1, c.2.1, c.2.2 + 1)) (s (c.1 + 1, c.2.1, c.2.2 + 1))
             (s (c.1 + 1, c.2.1 + 1, c.2.2 + 1)) (s (c.1, c.2.1 + 1, c.2.2 + 1)) := rfl

/-- **Mask agreement across a shared face** (symbolic proof, all three
    normal axes): the four corner signs of the shared face occupy the
    same Bourke-corner bit positions in the two cells' unshared frames
    up to the involutive corner correspondence, so the face masks are
    literally equal. Holds for every sign field `s` and base point `p`
    with `1 ≤ p`. -/
theorem maskPlus_eq_maskMinus (na : Nat) (s : Vdb.PadGrid.Lat → Bool) (p : Vdb.PadGrid.Lat)
    (hna : na < 3) (hx : FaceBaseOK na p) :
    maskPlus na (Vdb.DmcOnePad.cellCase s (facePlusCell na p)) =
    maskMinus na (Vdb.DmcOnePad.cellCase s (faceMinusCell na p)) := by
  interval_cases na
  all_goals
    dsimp only [maskPlus, maskMinus]
  all_goals
    simp [facePlusCell, faceMinusCell]
  all_goals
    simp only [mkCase_eq_cellCase]
  all_goals
    simp only [caseBit_mkCase _ _ _ _ _ _ _ _ (0 : Nat) (by decide),
      caseBit_mkCase _ _ _ _ _ _ _ _ (1 : Nat) (by decide),
      caseBit_mkCase _ _ _ _ _ _ _ _ (2 : Nat) (by decide),
      caseBit_mkCase _ _ _ _ _ _ _ _ (3 : Nat) (by decide),
      caseBit_mkCase _ _ _ _ _ _ _ _ (4 : Nat) (by decide),
      caseBit_mkCase _ _ _ _ _ _ _ _ (5 : Nat) (by decide),
      caseBit_mkCase _ _ _ _ _ _ _ _ (6 : Nat) (by decide),
      caseBit_mkCase _ _ _ _ _ _ _ _ (7 : Nat) (by decide)]
  all_goals
    simp [Nat.sub_add_cancel (by simpa [FaceBaseOK] using hx)]

/-- The local cube-edge id of the `i`-th face boundary edge. -/
def edgeId (na side i : Nat) : Nat := (enumFaceEdges na side).getD i 0

/-- The Bourke corner bit at the start of the `i`-th face boundary
    edge, in the given cell frame. -/
def bitOf (na side i : Nat) : Nat := (enumEdgeInfo na side (edgeId na side i)).2

/-- The other endpoint's case bit, derived from the embedded MC
    edge table (`mcEdgeVerts`) so it cannot drift from the table. -/
def endBitOf (na side i : Nat) : Nat :=
  let l := edgeId na side i
  let (a, b) := Vdb.McTable.mcEdgeVerts[l]!
  let s := (enumEdgeInfo na side l).2
  if s == a then b else a

theorem crossed_has_partner :
    ∀ (na : Fin 3) (side : Fin 2) (k : Fin 256) (i : Fin 4),
      caseBit k (bitOf na side i) ≠ caseBit k (endBitOf na side i) →
        ∃ j : Fin 4, j ≠ i ∧
          (min i.val j.val, max i.val j.val) ∈ pairsIdx k.val na.val side.val := by
  native_decide

/-- Paired boundary edges emit opposite-oriented F-sides. -/
theorem paired_dirAt_ne :
    ∀ (na : Fin 3) (side : Fin 2) (k : Fin 256) (i j : Fin 4),
      (min i.val j.val, max i.val j.val) ∈ pairsIdx k.val na.val side.val →
        dirAt i.val (caseBit k.val (bitOf na.val side.val i.val)) ≠
        dirAt j.val (caseBit k.val (bitOf na.val side.val j.val)) := by
  native_decide

/-- The two boundary edges of a paired segment are owned by the same
    patch of the cell's soup. -/
theorem paired_patch_eq :
    ∀ (na : Fin 3) (side : Fin 2) (k : Fin 256) (i j : Fin 4),
      (min i.val j.val, max i.val j.val) ∈ pairsIdx k.val na.val side.val →
        Vdb.patchesUsing k.val (edgeId na.val side.val i.val) =
        Vdb.patchesUsing k.val (edgeId na.val side.val j.val) := by
  native_decide

/-- Cross-cell pairing correspondence, Prop form. -/
theorem pairing_cross_fin :
    ∀ (na : Fin 3) (kA kB : Fin 256),
      maskPlus na.val kA.val = maskMinus na.val kB.val →
        pairsMultiEq (pairsIdx kA.val na.val 0) (pairsIdx kB.val na.val 1) := by
  native_decide

/-- Membership transfer through multiset equality. -/
theorem mem_of_pairsMultiEq {l₁ l₂ : List (Nat × Nat)} (h : pairsMultiEq l₁ l₂ = true)
    {p : Nat × Nat} (hp : p ∈ l₁) (hp1 : p.1 < 4) (hp2 : p.2 < 4) : p ∈ l₂ := by
  unfold pairsMultiEq at h
  rw [List.all_eq_true] at h
  have hc := h p (List.mem_flatMap.mpr ⟨p.1, List.mem_range.mpr hp1,
    List.mem_map.mpr ⟨p.2, List.mem_range.mpr hp2, rfl⟩⟩)
  rw [beq_iff_eq] at hc
  by_contra hn
  have hc0 : List.count p l₂ = 0 := List.count_eq_zero.mpr hn
  have hc1 : List.count p l₁ = 0 := by rwa [hc0] at hc
  exact (List.count_eq_zero.mp hc1) hp


/-- If-based start-corner table (simp-friendly), with a machine-checked
    bridge to `enumEdgeInfo`. -/
def startCornerId (na side i : Nat) : Nat :=
  if na = 0 then
    if side = 0 then [0, 3, 4, 0].getD i 0 else [1, 2, 5, 1].getD i 0
  else if na = 1 then
    if side = 0 then [0, 4, 1, 0].getD i 0 else [3, 7, 2, 3].getD i 0
  else
    if side = 0 then [0, 1, 3, 0].getD i 0 else [4, 5, 7, 4].getD i 0

theorem startCornerId_eq_bitOf : ∀ (na : Fin 3) (side : Fin 2) (i : Fin 4),
    startCornerId na side i = bitOf na side i := by
  native_decide

/-- The case bit at the start corner of boundary edge `i` is exactly
    the sign at that edge's global start point. -/
theorem bitOf_start_sign (na : Fin 3) (side : Fin 2) (i : Fin 4) (s : Lat → Bool)
    (x y z : Nat)
    (hb : if na.val = 0 then 1 ≤ x else if na.val = 1 then 1 ≤ y else 1 ≤ z) :
    caseBit (Vdb.DmcOnePad.cellCase s (if side.val = 0 then facePlusCell na (x,y,z) else faceMinusCell na (x,y,z)))
      (startCornerId na side i) =
      (if s ((faceBoundaryEdges na (x,y,z)).getD i ((x,y,z),0)).1 then 1 else 0) := by
  fin_cases na <;> fin_cases side <;> fin_cases i <;> norm_num at *
  all_goals
    rw [mkCase_eq_cellCase, caseBit_mkCase]
    all_goals
      simp_all [startCornerId, faceBoundaryEdges, iaOf, ibOf,
        facePlusCell, faceMinusCell, Vdb.PadGrid.succN, Nat.sub_add_cancel hb]

/-- If-based start-corner table (simp-friendly), with a machine-checked
    bridge to `enumEdgeInfo`. -/
def endCornerId (na side i : Nat) : Nat :=
  if na = 0 then
    if side = 0 then [3, 7, 7, 4].getD i 0 else [2, 6, 6, 5].getD i 0
  else if na = 1 then
    if side = 0 then [4, 5, 5, 1].getD i 0 else [7, 6, 6, 2].getD i 0
  else
    if side = 0 then [1, 2, 2, 3].getD i 0 else [5, 6, 6, 7].getD i 0

theorem endCornerId_eq_endBitOf : ∀ (na : Fin 3) (side : Fin 2) (i : Fin 4),
    endCornerId na side i = endBitOf na side i := by
  native_decide

/-- The case bit at the start corner of boundary edge `i` is exactly
    the sign at that edge's global end point. -/
theorem endBitOf_start_sign (na : Fin 3) (side : Fin 2) (i : Fin 4) (s : Lat → Bool)
    (x y z : Nat)
    (hb : if na.val = 0 then 1 ≤ x else if na.val = 1 then 1 ≤ y else 1 ≤ z) :
    caseBit (Vdb.DmcOnePad.cellCase s (if side.val = 0 then facePlusCell na (x,y,z) else faceMinusCell na (x,y,z)))
      (endCornerId na side i) =
      (if s (Vdb.PadGrid.succN ((faceBoundaryEdges na (x,y,z)).getD i ((x,y,z),0)).1
        ((faceBoundaryEdges na (x,y,z)).getD i ((x,y,z),0)).2) then 1 else 0) := by
  fin_cases na <;> fin_cases side <;> fin_cases i <;> norm_num at *
  all_goals
    rw [mkCase_eq_cellCase, caseBit_mkCase]
    all_goals
      simp_all [endCornerId, faceBoundaryEdges, iaOf, ibOf,
        facePlusCell, faceMinusCell, Vdb.PadGrid.succN, Nat.sub_add_cancel hb]


/-- Paired boundary edges are crossed (their endpoint signs differ). -/
theorem paired_crossed :
    ∀ (na : Fin 3) (side : Fin 2) (k : Fin 256) (i j : Fin 4),
      (min i.val j.val, max i.val j.val) ∈ pairsIdx k.val na.val side.val →
        caseBit k.val (bitOf na.val side.val i.val) ≠
        caseBit k.val (endBitOf na.val side.val i.val) := by
  native_decide

end DmcOneStitch
end Vdb
