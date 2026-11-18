/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  **DMC-1 stitching — global assembly: `EdgeClosed` for arbitrary grid
  size, under shell pinning.**

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Assembly
import Vdb.DmcOne
import Vdb.DmcOneDual
import Vdb.DmcOneEuler
import Vdb.DmcOnePad
import Vdb.DmcOneStitch
import Vdb.DmcOneStitchEnum
import Vdb.DmcOneStitchOrient
import Vdb.McTable
import Vdb.PadGrid
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Vdb
namespace DmcOneStitch

open Vdb.DmcOnePad

/-- Mesh edges of a shell-pinned field connect distinct vertices (no loops). -/
theorem mesh_edge_of_quad (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false) {a b : V}
    (hmem : (a, b) ∈ Vdb.DmcOneEuler.dmcOneMeshEdges n s) :
    ∃ e : PadEdge, ∃ (_ : PadGrid.InLattice n e.1) (_ : e.2 < 3),
      (s e.1 ≠ s (PadGrid.succN e.1 e.2)) ∧
      (a, b) ∈ DmcOnePad.quadDirectedEdges (Vdb.DmcOneEuler.dmcOneQuadN s e) := by
  unfold Vdb.DmcOneEuler.dmcOneMeshEdges at hmem
  rw [List.mem_flatMap] at hmem
  obtain ⟨q, hqmem, hedgemem⟩ := hmem
  unfold Vdb.DmcOneEuler.dmcOneQuads at hqmem
  rw [List.mem_flatMap] at hqmem
  obtain ⟨p, hpmem, hdmem⟩ := hqmem
  rw [List.mem_filterMap] at hdmem
  obtain ⟨d, hdmem', hqeq⟩ := hdmem
  have hd3 : d < 3 := List.mem_range.mp hdmem'
  have hp3 : PadGrid.InLattice n p := PadGrid.mem_latAll.mp hpmem
  by_cases hcond : (decide (PadGrid.InLattice n (PadGrid.succN p d)) &&
      (s p != s (PadGrid.succN p d))) = true
  · have hne : s p ≠ s (PadGrid.succN p d) := by
      have hc := (Bool.and_eq_true _ _).mp hcond
      simpa [bne_iff_ne] using hc.2
    have hqE : Vdb.DmcOneEuler.dmcOneQuadN s (p, d) = q := by
      have h1 := hqeq
      rw [ite_eq_left hcond] at h1
      exact Option.some.inj h1
    exact ⟨(p, d), hp3, hd3, hne, by
      rw [← hqE] at hedgemem
      exact hedgemem⟩
  · rw [ite_eq_right (by simpa using hcond)] at hqeq
    simp at hqeq

/-- Which cell pair a mesh edge side connects (orientation of the ring). -/
theorem mesh_edge_side_cells (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false) {a b : V}
    (hmem : (a, b) ∈ Vdb.DmcOneEuler.dmcOneMeshEdges n s) :
    ∃ e : PadEdge, (s e.1 ≠ s (PadGrid.succN e.1 e.2)) ∧
      ∃ (cA cB : Cell),
        (a = DmcOnePad.cellPatchVertex s cA e.1 e.2 ∧ b = DmcOnePad.cellPatchVertex s cB e.1 e.2) ∨
        (b = DmcOnePad.cellPatchVertex s cA e.1 e.2 ∧ a = DmcOnePad.cellPatchVertex s cB e.1 e.2) := by
  obtain ⟨e, hp3, hd3, hne, hm⟩ := mesh_edge_of_quad n s hpin hmem
  obtain ⟨p, d⟩ := e
  obtain ⟨hnodup, hlen⟩ := Vdb.DmcOneEuler.incidentCells_nodup n s hpin p d hd3 hp3 hne
  obtain ⟨q, hq⟩ := Vdb.DmcOneEuler.anchorCell_of_pinned n s hpin p d hd3 hp3 hne
  cases hi : Vdb.PadGrid.ij d (s p) with
  | mk i j =>
    have hquad : Vdb.DmcOneEuler.dmcOneQuadN s (p, d) =
        [DmcOnePad.cellPatchVertex s q p d,
         DmcOnePad.cellPatchVertex s (Vdb.PadGrid.addCell q i) p d,
         DmcOnePad.cellPatchVertex s (Vdb.PadGrid.addCell (Vdb.PadGrid.addCell q i) j) p d,
         DmcOnePad.cellPatchVertex s (Vdb.PadGrid.addCell q j) p d] := by
      rw [Vdb.DmcOneEuler.dmcOneQuadN, ite_eq_right (by simpa using hne),
        DmcOnePad.incidentCells, hq, hi]
      rfl
    rw [hquad] at hm
    simp [DmcOnePad.quadDirectedEdges, List.drop, List.take, List.zip_cons_cons,
      List.zip_nil_right, List.mem_cons, List.mem_singleton] at hm
    rcases hm with h | h | h | h
    · obtain ⟨rfl, rfl⟩ := h
      exact ⟨(p, d), hne, q, Vdb.PadGrid.addCell q i, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨rfl, rfl⟩ := h
      exact ⟨(p, d), hne, Vdb.PadGrid.addCell q i,
        Vdb.PadGrid.addCell (Vdb.PadGrid.addCell q i) j, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨rfl, rfl⟩ := h
      exact ⟨(p, d), hne, Vdb.PadGrid.addCell (Vdb.PadGrid.addCell q i) j,
        Vdb.PadGrid.addCell q j, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨rfl, rfl⟩ := h
      exact ⟨(p, d), hne, Vdb.PadGrid.addCell q j, q, Or.inl ⟨rfl, rfl⟩⟩


/-! ### The local face and its boundary edges -/

/-- Global index → local edge id in the given side's frame. -/
def localEdgeAt (na : Nat) (side : Nat) (i : Nat) : Nat :=
  (enumFaceEdges na side).getD i 0

/-- Local corner id of the face's `i`-th corner in the given side's frame. -/
def localCornerAt (na : Nat) (side : Nat) (i : Nat) : Nat :=
  ((match na, side with
    | 0, 0 => [0, 3, 7, 4]
    | 0, _ => [1, 2, 6, 5]
    | 1, 0 => [0, 1, 5, 4]
    | 1, _ => [3, 2, 6, 7]
    | _, 0 => [0, 1, 2, 3]
    | _, _ => [4, 5, 6, 7])).getD i 0

/-- Case bits in the same corner order as the face edges. -/
def faceCornerBits (na side : Nat) (k : Nat) : List Nat :=
  (List.range 4).map fun i => k / 2 ^ localCornerAt na side i % 2

/-- **The local-edge function of a face's boundary edge, restricted to its
    four global indices.** -/
theorem localEdge_faceEdges (na : Nat) (side : Nat) (p : Lat)
    (i : Nat) (hna : na < 3) (hi : i < 4)
    (hx : FaceBaseOK na p) (hside : side < 2) :
    localEdge ((faceBoundaryEdges na p).getD i (p, 0)).1
      (if side = 0 then facePlusCell na p else faceMinusCell na p)
      ((faceBoundaryEdges na p).getD i (p, 0)).2
      = localEdgeAt na side i := by
  interval_cases i
  all_goals
    interval_cases na
  all_goals
    interval_cases side
  all_goals
    simp [FaceBaseOK] at hx
  all_goals
    simp only [localEdgeAt]
    simp [localEdge, faceBoundaryEdges, iaOf, ibOf, enumFaceEdges, localFacePlus,
      localFaceMinus, faceMinusCell, facePlusCell, PadGrid.succN]
    all_goals first | omega | (split_ifs <;> omega)



/-- A cell case fits in 8 bits. -/
theorem cellCase_lt_256 (s : Vdb.DmcOnePad.Lat → Bool) (c : Vdb.DmcOnePad.Cell) :
    Vdb.DmcOnePad.cellCase s c < 256 := by
  unfold Vdb.DmcOnePad.cellCase
  split_ifs <;> omega


def flipDir (i : Nat) (b : Bool) : Bool := if i ≤ 1 then b else !b

theorem edge_dir_fin (na : Fin 3) (i : Fin 4) (s : Lat → Bool) (x y z : Nat)
    (hb : EdgeBaseOK na i (x, y, z)) :
    sideDir s ((faceBoundaryEdges na (x, y, z)).getD i ((x, y, z), 0))
      (facePlusCell na (x, y, z)) (faceMinusCell na (x, y, z))
      = some (flipDir i (s ((faceBoundaryEdges na (x, y, z)).getD i ((x, y, z), 0)).1)) := by
  fin_cases na <;> fin_cases i
  · -- na=0 i=0
    have hx : 1 ≤ x := by simpa [EdgeBaseOK] using hb.1
    have hz : 1 ≤ z := by simpa [EdgeBaseOK] using hb.2
    by_cases hb : s (x, y, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_0_0_pos s x y z hx hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_0_0 s x y z hx hz (by simpa using hb))
  · -- na=0 i=1
    have hx : 1 ≤ x := by simpa [EdgeBaseOK] using hb.1
    have hy : 1 ≤ y := by simpa [EdgeBaseOK] using hb.2
    by_cases hb : s (x, y + 1, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_0_1_pos s x y z hx hy (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_0_1 s x y z hx hy (by simpa using hb))
  · -- na=0 i=2
    have hx : 1 ≤ x := by simpa [EdgeBaseOK] using hb.1
    have hz : 1 ≤ z := by simpa [EdgeBaseOK] using hb.2
    by_cases hb : s (x, y, z + 1)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_0_2_pos s x y z hx hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_0_2 s x y z hx hz (by simpa using hb))
  · -- na=0 i=3
    have hx : 1 ≤ x := by simpa [EdgeBaseOK] using hb.1
    have hy : 1 ≤ y := by simpa [EdgeBaseOK] using hb.2
    by_cases hb : s (x, y, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_0_3_pos s x y z hx hy (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_0_3 s x y z hx hy (by simpa using hb))
  · -- na=1 i=0
    have hy : 1 ≤ y := by simpa [EdgeBaseOK] using hb.1
    have hx : 1 ≤ x := by simpa [EdgeBaseOK] using hb.2
    by_cases hb : s (x, y, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_1_0_pos s x y z hx hy (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_1_0 s x y z hx hy (by simpa using hb))
  · -- na=1 i=1
    have hy : 1 ≤ y := by simpa [EdgeBaseOK] using hb.1
    have hz : 1 ≤ z := by simpa [EdgeBaseOK] using hb.2
    by_cases hb : s (x, y, z + 1)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_1_1_pos s x y z hy hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_1_1 s x y z hy hz (by simpa using hb))
  · -- na=1 i=2
    have hy : 1 ≤ y := by simpa [EdgeBaseOK] using hb.1
    have hx : 1 ≤ x := by simpa [EdgeBaseOK] using hb.2
    by_cases hb : s (x + 1, y, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_1_2_pos s x y z hx hy (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_1_2 s x y z hx hy (by simpa using hb))
  · -- na=1 i=3
    have hy : 1 ≤ y := by simpa [EdgeBaseOK] using hb.1
    have hz : 1 ≤ z := by simpa [EdgeBaseOK] using hb.2
    by_cases hb : s (x, y, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_1_3_pos s x y z hy hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_1_3 s x y z hy hz (by simpa using hb))
  · -- na=2 i=0
    have hz : 1 ≤ z := by simpa [EdgeBaseOK] using hb.1
    have hy : 1 ≤ y := by simpa [EdgeBaseOK] using hb.2
    by_cases hb : s (x, y, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_2_0_pos s x y z hy hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_2_0 s x y z hy hz (by simpa using hb))
  · -- na=2 i=1
    have hz : 1 ≤ z := by simpa [EdgeBaseOK] using hb.1
    have hx : 1 ≤ x := by simpa [EdgeBaseOK] using hb.2
    by_cases hb : s (x + 1, y, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_2_1_pos s x y z hx hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_2_1 s x y z hx hz (by simpa using hb))
  · -- na=2 i=2
    have hz : 1 ≤ z := by simpa [EdgeBaseOK] using hb.1
    have hy : 1 ≤ y := by simpa [EdgeBaseOK] using hb.2
    by_cases hb : s (x, y + 1, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_2_2_pos s x y z hy hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_2_2 s x y z hy hz (by simpa using hb))
  · -- na=2 i=3
    have hz : 1 ≤ z := by simpa [EdgeBaseOK] using hb.1
    have hx : 1 ≤ x := by simpa [EdgeBaseOK] using hb.2
    by_cases hb : s (x, y, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_2_3_pos s x y z hx hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_2_3 s x y z hx hz (by simpa using hb))

/-- Nat wrapper for the uniform orientation law. -/
theorem edge_dir (na : Nat) (hna : na < 3) (i : Nat) (hi : i < 4)
    (s : Lat → Bool) (x y z : Nat) (hb : EdgeBaseOK na i (x, y, z)) :
    sideDir s ((faceBoundaryEdges na (x, y, z)).getD i ((x, y, z), 0))
      (facePlusCell na (x, y, z)) (faceMinusCell na (x, y, z))
      = some (flipDir i (s ((faceBoundaryEdges na (x, y, z)).getD i ((x, y, z), 0)).1)) := by
  exact edge_dir_fin ⟨na, hna⟩ ⟨i, hi⟩ s x y z hb

/-- The enumeration's `dirAt` agrees with the orientation law's
    `flipDir` (machine-checked over the finite domains). -/
theorem dirAt_eq_flipDir :
    ∀ (i : Fin 4) (b : Bool),
      dirAt i (if b then 1 else 0) = if flipDir i b then 1 else 0 := by
  native_decide

/-- Two edges owned by the same patch of a cell yield the same DMC-1
    vertex in that cell. -/
theorem cellPatchVertex_eq_of_patches (s : Lat → Bool) (c : Cell) (e e' : PadEdge)
    (h : Vdb.patchesUsing (Vdb.DmcOnePad.cellCase s c) (Vdb.DmcOnePad.localEdge e.1 c e.2) =
         Vdb.patchesUsing (Vdb.DmcOnePad.cellCase s c) (Vdb.DmcOnePad.localEdge e'.1 c e'.2)) :
    Vdb.DmcOnePad.cellPatchVertex s c e.1 e.2 = Vdb.DmcOnePad.cellPatchVertex s c e'.1 e'.2 := by
  unfold Vdb.DmcOnePad.cellPatchVertex
  show (c, (Vdb.patchesUsing (Vdb.DmcOnePad.cellCase s c) (Vdb.DmcOnePad.localEdge e.1 c e.2)).headD 0) =
       (c, (Vdb.patchesUsing (Vdb.DmcOnePad.cellCase s c) (Vdb.DmcOnePad.localEdge e'.1 c e'.2)).headD 0)
  rw [h]

theorem side_of_sideDir (s : Lat → Bool) (e : PadEdge) (A B : Cell) (b : Bool)
    (hcross : s e.1 ≠ s (PadGrid.succN e.1 e.2))
    (h : sideDir s e A B = some b) :
    (if b then (DmcOnePad.cellPatchVertex s A e.1 e.2, DmcOnePad.cellPatchVertex s B e.1 e.2)
          else (DmcOnePad.cellPatchVertex s B e.1 e.2, DmcOnePad.cellPatchVertex s A e.1 e.2))
      ∈ DmcOnePad.quadDirectedEdges (Vdb.DmcOneEuler.dmcOneQuadN s e) := by
  have hbne : (s e.1 == s (PadGrid.succN e.1 e.2)) = false := by
    cases h1 : s e.1 <;> cases h2 : s (PadGrid.succN e.1 e.2) <;> simp_all
  unfold sideDir at h
  cases hcs : DmcOnePad.incidentCells s e with
  | nil => simp [hcs] at h
  | cons c0 r1 =>
    cases r1 with
    | nil => simp [hcs] at h
    | cons c1 r2 =>
      cases r2 with
      | nil => simp [hcs] at h
      | cons c2 r3 =>
        cases r3 with
        | nil => simp [hcs] at h
        | cons c3 r4 =>
          cases r4 with
          | nil =>
            simp only [hcs, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
            split_ifs at h with hb1 hb2
            · have hb : b = true := by cases h; rfl
              subst b
              have hb1p : ((((A = c0) ∧ (B = c1)) ∨ ((A = c1) ∧ (B = c2))) ∨
                    ((A = c2) ∧ (B = c3))) ∨ ((A = c3) ∧ (B = c0)) := by
                simpa [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] using hb1
              rcases hb1p with ((hcase | hcase) | hcase) | hcase
              all_goals rcases hcase with ⟨rfl, rfl⟩
              all_goals simp [Vdb.DmcOneEuler.dmcOneQuadN, hcs, hbne,
                DmcOnePad.quadDirectedEdges, DmcOnePad.cellPatchVertex]
            · have hb : b = false := by cases h; rfl
              subst b
              have hb2p : ((((B = c0) ∧ (A = c1)) ∨ ((B = c1) ∧ (A = c2))) ∨
                    ((B = c2) ∧ (A = c3))) ∨ ((B = c3) ∧ (A = c0)) := by
                simpa [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] using hb2
              rcases hb2p with ((hcase | hcase) | hcase) | hcase
              all_goals rcases hcase with ⟨rfl, rfl⟩
              all_goals simp [Vdb.DmcOneEuler.dmcOneQuadN, hcs, hbne,
                DmcOnePad.quadDirectedEdges, DmcOnePad.cellPatchVertex]
          | cons _ _ => simp [hcs] at h

/-- Point-form wrappers for the sign bridges. -/
theorem bitOf_start_sign_p (na : Fin 3) (side : Fin 2) (i : Fin 4) (s : Lat → Bool)
    (p : Lat) (hx : FaceBaseOK na p) :
    caseBit (Vdb.DmcOnePad.cellCase s (if side.val = 0 then facePlusCell na p else faceMinusCell na p))
      (bitOf na side i) =
      (if s ((faceBoundaryEdges na p).getD i (p, 0)).1 then 1 else 0) := by
  rcases p with ⟨x, y, z⟩
  rw [← startCornerId_eq_bitOf na side i]
  exact bitOf_start_sign na side i s x y z (by simpa [FaceBaseOK] using hx)

theorem endBitOf_end_sign_p (na : Fin 3) (side : Fin 2) (i : Fin 4) (s : Lat → Bool)
    (p : Lat) (hx : FaceBaseOK na p) :
    caseBit (Vdb.DmcOnePad.cellCase s (if side.val = 0 then facePlusCell na p else faceMinusCell na p))
      (endBitOf na side i) =
      (if s (Vdb.PadGrid.succN ((faceBoundaryEdges na p).getD i (p, 0)).1
        ((faceBoundaryEdges na p).getD i (p, 0)).2) then 1 else 0) := by
  rcases p with ⟨x, y, z⟩
  rw [← endCornerId_eq_endBitOf na side i]
  exact endBitOf_start_sign na side i s x y z (by simpa [FaceBaseOK] using hx)

/-- Uniform orientation law, point form. -/
theorem edge_dir_p (na : Nat) (hna : na < 3) (i : Nat) (hi : i < 4)
    (s : Lat → Bool) (p : Lat) (hb : EdgeBaseOK na i p) :
    sideDir s ((faceBoundaryEdges na p).getD i (p, 0))
      (facePlusCell na p) (faceMinusCell na p)
      = some (flipDir i (s ((faceBoundaryEdges na p).getD i (p, 0)).1)) := by
  rcases p with ⟨x, y, z⟩
  exact edge_dir na hna i hi s x y z (by simpa using hb)

/-- **Partner reversal across an interior face.** For any crossed
    boundary edge `e` of the face at base `p` with normal `na`, there
    is a crossed boundary edge `e'` of the same face whose quad side
    joins the same two patch vertices in the *opposite* direction. -/
theorem face_reverse (n : Nat) (s : Lat → Bool)
    (_hpin : ∀ p, PadGrid.isShell n p = true → s p = false)
    (na : Nat) (hna : na < 3) (p : Lat) (hx : FaceBaseOK na p)
    (hEdge : ∀ j : Nat, EdgeBaseOK na j p)
    (i : Nat) (hi : i < 4)
    (e : PadEdge) (he : e = (faceBoundaryEdges na p).getD i (p, 0))
    (hcross : s e.1 ≠ s (PadGrid.succN e.1 e.2)) :
    ∃ (e' : PadEdge) (b : Bool),
      s e'.1 ≠ s (PadGrid.succN e'.1 e'.2) ∧
      sideDir s e' (facePlusCell na p) (faceMinusCell na p) = some b ∧
      b = !flipDir i (s e.1) ∧
      DmcOnePad.cellPatchVertex s (facePlusCell na p) e'.1 e'.2 =
        DmcOnePad.cellPatchVertex s (facePlusCell na p) e.1 e.2 ∧
      DmcOnePad.cellPatchVertex s (faceMinusCell na p) e'.1 e'.2 =
        DmcOnePad.cellPatchVertex s (faceMinusCell na p) e.1 e.2 := by
  let A : Cell := facePlusCell na p
  let B : Cell := faceMinusCell na p
  let naF : Fin 3 := ⟨na, hna⟩
  let sideA : Fin 2 := ⟨0, by decide⟩
  let sideB : Fin 2 := ⟨1, by decide⟩
  let iF : Fin 4 := ⟨i, hi⟩
  let kA : Fin 256 := ⟨Vdb.DmcOnePad.cellCase s A, cellCase_lt_256 s A⟩
  let kB : Fin 256 := ⟨Vdb.DmcOnePad.cellCase s B, cellCase_lt_256 s B⟩
  have hbA : caseBit kA.val (bitOf naF sideA iF) = (if s e.1 then 1 else 0) := by
    have h := bitOf_start_sign_p naF sideA iF s p hx
    dsimp [kA, A, naF, sideA, iF] at h ⊢
    rw [he]
    exact h
  have heA : caseBit kA.val (endBitOf naF sideA iF) =
      (if s (PadGrid.succN e.1 e.2) then 1 else 0) := by
    have h := endBitOf_end_sign_p naF sideA iF s p hx
    dsimp [kA, A, naF, sideA, iF] at h ⊢
    rw [he]
    exact h
  have hcrossA : caseBit kA.val (bitOf naF sideA iF) ≠ caseBit kA.val (endBitOf naF sideA iF) := by
    rw [hbA, heA]
    cases h1 : s e.1 <;> cases h2 : s (PadGrid.succN e.1 e.2) <;> simp_all
  obtain ⟨jF, hjne, hjpair⟩ := crossed_has_partner naF sideA kA iF hcrossA
  let e' : PadEdge := (faceBoundaryEdges na p).getD jF.val (p, 0)
  have hcrossE' : s e'.1 ≠ s (PadGrid.succN e'.1 e'.2) := by
    have hpc := paired_crossed naF sideA kA jF iF (by
      simpa [Nat.min_comm, Nat.max_comm] using hjpair)
    have hs := bitOf_start_sign_p naF sideA jF s p hx
    have hend := endBitOf_end_sign_p naF sideA jF s p hx
    dsimp [kA, A, naF, sideA] at hpc hs hend
    have heq : (faceBoundaryEdges na p).getD jF.val (p, 0) = e' := rfl
    rw [heq] at hs hend
    rw [hs, hend] at hpc
    cases h1 : s e'.1 <;> cases h2 : s (PadGrid.succN e'.1 e'.2) <;> simp_all
  have hdir := paired_dirAt_ne naF sideA kA iF jF hjpair
  have hpatchA := paired_patch_eq naF sideA kA iF jF hjpair
  have hmask : maskPlus na kA.val = maskMinus na kB.val := by
    dsimp [kA, kB, A, B]
    exact maskPlus_eq_maskMinus na s p hna hx
  have hmulti := pairing_cross_fin naF kA kB hmask
  have hpairB : (min i jF.val, max i jF.val) ∈ pairsIdx kB.val na 1 := by
    exact mem_of_pairsMultiEq hmulti hjpair (by omega) (by omega)
  have hpatchB := paired_patch_eq naF sideB kB iF jF (by
    simpa [sideB] using hpairB)
  have hvA : DmcOnePad.cellPatchVertex s A e'.1 e'.2 = DmcOnePad.cellPatchVertex s A e.1 e.2 := by
    apply cellPatchVertex_eq_of_patches s A e' e
    dsimp [e', A]
    have hle_j : DmcOnePad.localEdge ((faceBoundaryEdges na p).getD jF.val (p, 0)).1
        (facePlusCell na p) ((faceBoundaryEdges na p).getD jF.val (p, 0)).2 =
        localEdgeAt na 0 jF.val := by
      simpa using localEdge_faceEdges na 0 p jF.val hna jF.isLt hx (by decide)
    have hle_i : DmcOnePad.localEdge ((faceBoundaryEdges na p).getD i (p, 0)).1
        (facePlusCell na p) ((faceBoundaryEdges na p).getD i (p, 0)).2 =
        localEdgeAt na 0 i := by
      simpa using localEdge_faceEdges na 0 p i hna hi hx (by decide)
    rw [he, hle_j, hle_i]
    simpa [edgeId, localEdgeAt, A, naF, sideA, iF, kA] using hpatchA.symm
  have hvB : DmcOnePad.cellPatchVertex s B e'.1 e'.2 = DmcOnePad.cellPatchVertex s B e.1 e.2 := by
    apply cellPatchVertex_eq_of_patches s B e' e
    dsimp [e', B]
    have hle_j : DmcOnePad.localEdge ((faceBoundaryEdges na p).getD jF.val (p, 0)).1
        (faceMinusCell na p) ((faceBoundaryEdges na p).getD jF.val (p, 0)).2 =
        localEdgeAt na 1 jF.val := by
      simpa using localEdge_faceEdges na 1 p jF.val hna jF.isLt hx (by decide)
    have hle_i : DmcOnePad.localEdge ((faceBoundaryEdges na p).getD i (p, 0)).1
        (faceMinusCell na p) ((faceBoundaryEdges na p).getD i (p, 0)).2 =
        localEdgeAt na 1 i := by
      simpa using localEdge_faceEdges na 1 p i hna hi hx (by decide)
    rw [he, hle_j, hle_i]
    simpa [edgeId, localEdgeAt, B, naF, sideB, iF, kB] using hpatchB.symm
  have hbAbit : (if s e.1 then 1 else 0) = caseBit kA.val (bitOf naF sideA iF) := hbA.symm
  have hsj := bitOf_start_sign_p naF sideA jF s p hx
  dsimp [kA, A, naF, sideA] at hsj
  have heq : (faceBoundaryEdges na p).getD jF.val (p, 0) = e' := rfl
  rw [heq] at hsj
  have hb' : flipDir jF.val (s e'.1) = !flipDir i (s e.1) := by
    have hdir2 := hdir
    have hbA2 := hbA
    dsimp [kA, A, naF, sideA, iF] at hdir2 hbA2
    have hdir' : dirAt i (if s e.1 then 1 else 0) ≠ dirAt jF.val (if s e'.1 then 1 else 0) := by
      simpa [hbA2, hsj] using hdir2
    rw [dirAt_eq_flipDir ⟨i, hi⟩ (s e.1), dirAt_eq_flipDir jF (s e'.1)] at hdir'
    cases hfi : flipDir i (s e.1) <;> cases hfj : flipDir jF.val (s e'.1) <;> simp_all
  refine ⟨e', flipDir jF.val (s e'.1), hcrossE', ?_, hb', hvA, hvB⟩
  exact edge_dir_p na hna jF.val jF.isLt s p (hEdge jF.val)

/-- Ring-pair classification for d=0, s p = false. -/
theorem ring_pair_0_false (s : Lat → Bool)
    (x y z : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hs : s (x, y, z) = false)
    (hne : s (x, y, z) ≠ s (PadGrid.succN (x, y, z) 0))
    (a b : V)
    (hm : (a, b) ∈ DmcOnePad.quadDirectedEdges (Vdb.DmcOneEuler.dmcOneQuadN s ((x, y, z), 0))) :
    (a = DmcOnePad.cellPatchVertex s (x, y - 1, z - 1) (x, y, z) 0 ∧
     b = DmcOnePad.cellPatchVertex s (x, y, z - 1) (x, y, z) 0) ∨
    (a = DmcOnePad.cellPatchVertex s (x, y, z - 1) (x, y, z) 0 ∧
     b = DmcOnePad.cellPatchVertex s (x, y, z) (x, y, z) 0) ∨
    (a = DmcOnePad.cellPatchVertex s (x, y, z) (x, y, z) 0 ∧
     b = DmcOnePad.cellPatchVertex s (x, y - 1, z) (x, y, z) 0) ∨
    (a = DmcOnePad.cellPatchVertex s (x, y - 1, z) (x, y, z) 0 ∧
     b = DmcOnePad.cellPatchVertex s (x, y - 1, z - 1) (x, y, z) 0) := by
  have hq : PadGrid.anchorCell (x, y, z) 0 = some (x, y - 1, z - 1) := by
    simp [PadGrid.anchorCell, hy, hz]
  have hcells : DmcOnePad.incidentCells s ((x, y, z), 0) = [(x, y - 1, z - 1), (x, y, z - 1), (x, y, z), (x, y - 1, z)] := by
    simp [DmcOnePad.incidentCells, hq, PadGrid.ij, hs, PadGrid.addCell,
    Nat.sub_add_cancel hx, Nat.sub_add_cancel hy, Nat.sub_add_cancel hz]
  have hbne : (s (x, y, z) == s (PadGrid.succN (x, y, z) 0)) = false := by
    cases h1 : s (x, y, z) <;> cases h2 : s (PadGrid.succN (x, y, z) 0) <;> simp_all
  unfold Vdb.DmcOneEuler.dmcOneQuadN at hm
  rw [hbne] at hm
  simp only [ite_false, hcells, List.map_cons, List.map_nil] at hm
  simp [DmcOnePad.quadDirectedEdges] at hm
  rcases hm with h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;> simp

/-- Ring-pair classification for d=0, s p = true. -/
theorem ring_pair_0_true (s : Lat → Bool)
    (x y z : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hs : s (x, y, z) = true)
    (hne : s (x, y, z) ≠ s (PadGrid.succN (x, y, z) 0))
    (a b : V)
    (hm : (a, b) ∈ DmcOnePad.quadDirectedEdges (Vdb.DmcOneEuler.dmcOneQuadN s ((x, y, z), 0))) :
    (a = DmcOnePad.cellPatchVertex s (x, y - 1, z - 1) (x, y, z) 0 ∧
     b = DmcOnePad.cellPatchVertex s (x, y - 1, z) (x, y, z) 0) ∨
    (a = DmcOnePad.cellPatchVertex s (x, y - 1, z) (x, y, z) 0 ∧
     b = DmcOnePad.cellPatchVertex s (x, y, z) (x, y, z) 0) ∨
    (a = DmcOnePad.cellPatchVertex s (x, y, z) (x, y, z) 0 ∧
     b = DmcOnePad.cellPatchVertex s (x, y, z - 1) (x, y, z) 0) ∨
    (a = DmcOnePad.cellPatchVertex s (x, y, z - 1) (x, y, z) 0 ∧
     b = DmcOnePad.cellPatchVertex s (x, y - 1, z - 1) (x, y, z) 0) := by
  have hq : PadGrid.anchorCell (x, y, z) 0 = some (x, y - 1, z - 1) := by
    simp [PadGrid.anchorCell, hy, hz]
  have hcells : DmcOnePad.incidentCells s ((x, y, z), 0) = [(x, y - 1, z - 1), (x, y - 1, z), (x, y, z), (x, y, z - 1)] := by
    simp [DmcOnePad.incidentCells, hq, PadGrid.ij, hs, PadGrid.addCell,
    Nat.sub_add_cancel hx, Nat.sub_add_cancel hy, Nat.sub_add_cancel hz]
  have hbne : (s (x, y, z) == s (PadGrid.succN (x, y, z) 0)) = false := by
    cases h1 : s (x, y, z) <;> cases h2 : s (PadGrid.succN (x, y, z) 0) <;> simp_all
  unfold Vdb.DmcOneEuler.dmcOneQuadN at hm
  rw [hbne] at hm
  simp only [ite_false, hcells, List.map_cons, List.map_nil] at hm
  simp [DmcOnePad.quadDirectedEdges] at hm
  rcases hm with h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;> simp

/-- Ring-pair classification for d=1, s p = false. -/
theorem ring_pair_1_false (s : Lat → Bool)
    (x y z : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hs : s (x, y, z) = false)
    (hne : s (x, y, z) ≠ s (PadGrid.succN (x, y, z) 1))
    (a b : V)
    (hm : (a, b) ∈ DmcOnePad.quadDirectedEdges (Vdb.DmcOneEuler.dmcOneQuadN s ((x, y, z), 1))) :
    (a = DmcOnePad.cellPatchVertex s (x - 1, y, z - 1) (x, y, z) 1 ∧
     b = DmcOnePad.cellPatchVertex s (x - 1, y, z) (x, y, z) 1) ∨
    (a = DmcOnePad.cellPatchVertex s (x - 1, y, z) (x, y, z) 1 ∧
     b = DmcOnePad.cellPatchVertex s (x, y, z) (x, y, z) 1) ∨
    (a = DmcOnePad.cellPatchVertex s (x, y, z) (x, y, z) 1 ∧
     b = DmcOnePad.cellPatchVertex s (x, y, z - 1) (x, y, z) 1) ∨
    (a = DmcOnePad.cellPatchVertex s (x, y, z - 1) (x, y, z) 1 ∧
     b = DmcOnePad.cellPatchVertex s (x - 1, y, z - 1) (x, y, z) 1) := by
  have hq : PadGrid.anchorCell (x, y, z) 1 = some (x - 1, y, z - 1) := by
    simp [PadGrid.anchorCell, hx, hz]
  have hcells : DmcOnePad.incidentCells s ((x, y, z), 1) = [(x - 1, y, z - 1), (x - 1, y, z), (x, y, z), (x, y, z - 1)] := by
    simp [DmcOnePad.incidentCells, hq, PadGrid.ij, hs, PadGrid.addCell,
    Nat.sub_add_cancel hx, Nat.sub_add_cancel hy, Nat.sub_add_cancel hz]
  have hbne : (s (x, y, z) == s (PadGrid.succN (x, y, z) 1)) = false := by
    cases h1 : s (x, y, z) <;> cases h2 : s (PadGrid.succN (x, y, z) 1) <;> simp_all
  unfold Vdb.DmcOneEuler.dmcOneQuadN at hm
  rw [hbne] at hm
  simp only [ite_false, hcells, List.map_cons, List.map_nil] at hm
  simp [DmcOnePad.quadDirectedEdges] at hm
  rcases hm with h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;> simp

/-- Ring-pair classification for d=1, s p = true. -/
theorem ring_pair_1_true (s : Lat → Bool)
    (x y z : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hs : s (x, y, z) = true)
    (hne : s (x, y, z) ≠ s (PadGrid.succN (x, y, z) 1))
    (a b : V)
    (hm : (a, b) ∈ DmcOnePad.quadDirectedEdges (Vdb.DmcOneEuler.dmcOneQuadN s ((x, y, z), 1))) :
    (a = DmcOnePad.cellPatchVertex s (x - 1, y, z - 1) (x, y, z) 1 ∧
     b = DmcOnePad.cellPatchVertex s (x, y, z - 1) (x, y, z) 1) ∨
    (a = DmcOnePad.cellPatchVertex s (x, y, z - 1) (x, y, z) 1 ∧
     b = DmcOnePad.cellPatchVertex s (x, y, z) (x, y, z) 1) ∨
    (a = DmcOnePad.cellPatchVertex s (x, y, z) (x, y, z) 1 ∧
     b = DmcOnePad.cellPatchVertex s (x - 1, y, z) (x, y, z) 1) ∨
    (a = DmcOnePad.cellPatchVertex s (x - 1, y, z) (x, y, z) 1 ∧
     b = DmcOnePad.cellPatchVertex s (x - 1, y, z - 1) (x, y, z) 1) := by
  have hq : PadGrid.anchorCell (x, y, z) 1 = some (x - 1, y, z - 1) := by
    simp [PadGrid.anchorCell, hx, hz]
  have hcells : DmcOnePad.incidentCells s ((x, y, z), 1) = [(x - 1, y, z - 1), (x, y, z - 1), (x, y, z), (x - 1, y, z)] := by
    simp [DmcOnePad.incidentCells, hq, PadGrid.ij, hs, PadGrid.addCell,
    Nat.sub_add_cancel hx, Nat.sub_add_cancel hy, Nat.sub_add_cancel hz]
  have hbne : (s (x, y, z) == s (PadGrid.succN (x, y, z) 1)) = false := by
    cases h1 : s (x, y, z) <;> cases h2 : s (PadGrid.succN (x, y, z) 1) <;> simp_all
  unfold Vdb.DmcOneEuler.dmcOneQuadN at hm
  rw [hbne] at hm
  simp only [ite_false, hcells, List.map_cons, List.map_nil] at hm
  simp [DmcOnePad.quadDirectedEdges] at hm
  rcases hm with h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;> simp

/-- Ring-pair classification for d=2, s p = false. -/
theorem ring_pair_2_false (s : Lat → Bool)
    (x y z : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hs : s (x, y, z) = false)
    (hne : s (x, y, z) ≠ s (PadGrid.succN (x, y, z) 2))
    (a b : V)
    (hm : (a, b) ∈ DmcOnePad.quadDirectedEdges (Vdb.DmcOneEuler.dmcOneQuadN s ((x, y, z), 2))) :
    (a = DmcOnePad.cellPatchVertex s (x - 1, y - 1, z) (x, y, z) 2 ∧
     b = DmcOnePad.cellPatchVertex s (x, y - 1, z) (x, y, z) 2) ∨
    (a = DmcOnePad.cellPatchVertex s (x, y - 1, z) (x, y, z) 2 ∧
     b = DmcOnePad.cellPatchVertex s (x, y, z) (x, y, z) 2) ∨
    (a = DmcOnePad.cellPatchVertex s (x, y, z) (x, y, z) 2 ∧
     b = DmcOnePad.cellPatchVertex s (x - 1, y, z) (x, y, z) 2) ∨
    (a = DmcOnePad.cellPatchVertex s (x - 1, y, z) (x, y, z) 2 ∧
     b = DmcOnePad.cellPatchVertex s (x - 1, y - 1, z) (x, y, z) 2) := by
  have hq : PadGrid.anchorCell (x, y, z) 2 = some (x - 1, y - 1, z) := by
    simp [PadGrid.anchorCell, hx, hy]
  have hcells : DmcOnePad.incidentCells s ((x, y, z), 2) = [(x - 1, y - 1, z), (x, y - 1, z), (x, y, z), (x - 1, y, z)] := by
    simp [DmcOnePad.incidentCells, hq, PadGrid.ij, hs, PadGrid.addCell,
    Nat.sub_add_cancel hx, Nat.sub_add_cancel hy, Nat.sub_add_cancel hz]
  have hbne : (s (x, y, z) == s (PadGrid.succN (x, y, z) 2)) = false := by
    cases h1 : s (x, y, z) <;> cases h2 : s (PadGrid.succN (x, y, z) 2) <;> simp_all
  unfold Vdb.DmcOneEuler.dmcOneQuadN at hm
  rw [hbne] at hm
  simp only [ite_false, hcells, List.map_cons, List.map_nil] at hm
  simp [DmcOnePad.quadDirectedEdges] at hm
  rcases hm with h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;> simp

/-- Ring-pair classification for d=2, s p = true. -/
theorem ring_pair_2_true (s : Lat → Bool)
    (x y z : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hs : s (x, y, z) = true)
    (hne : s (x, y, z) ≠ s (PadGrid.succN (x, y, z) 2))
    (a b : V)
    (hm : (a, b) ∈ DmcOnePad.quadDirectedEdges (Vdb.DmcOneEuler.dmcOneQuadN s ((x, y, z), 2))) :
    (a = DmcOnePad.cellPatchVertex s (x - 1, y - 1, z) (x, y, z) 2 ∧
     b = DmcOnePad.cellPatchVertex s (x - 1, y, z) (x, y, z) 2) ∨
    (a = DmcOnePad.cellPatchVertex s (x - 1, y, z) (x, y, z) 2 ∧
     b = DmcOnePad.cellPatchVertex s (x, y, z) (x, y, z) 2) ∨
    (a = DmcOnePad.cellPatchVertex s (x, y, z) (x, y, z) 2 ∧
     b = DmcOnePad.cellPatchVertex s (x, y - 1, z) (x, y, z) 2) ∨
    (a = DmcOnePad.cellPatchVertex s (x, y - 1, z) (x, y, z) 2 ∧
     b = DmcOnePad.cellPatchVertex s (x - 1, y - 1, z) (x, y, z) 2) := by
  have hq : PadGrid.anchorCell (x, y, z) 2 = some (x - 1, y - 1, z) := by
    simp [PadGrid.anchorCell, hx, hy]
  have hcells : DmcOnePad.incidentCells s ((x, y, z), 2) = [(x - 1, y - 1, z), (x - 1, y, z), (x, y, z), (x, y - 1, z)] := by
    simp [DmcOnePad.incidentCells, hq, PadGrid.ij, hs, PadGrid.addCell,
    Nat.sub_add_cancel hx, Nat.sub_add_cancel hy, Nat.sub_add_cancel hz]
  have hbne : (s (x, y, z) == s (PadGrid.succN (x, y, z) 2)) = false := by
    cases h1 : s (x, y, z) <;> cases h2 : s (PadGrid.succN (x, y, z) 2) <;> simp_all
  unfold Vdb.DmcOneEuler.dmcOneQuadN at hm
  rw [hbne] at hm
  simp only [ite_false, hcells, List.map_cons, List.map_nil] at hm
  simp [DmcOnePad.quadDirectedEdges] at hm
  rcases hm with h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;> simp

end DmcOneStitch
end Vdb
