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
    (hx : 1 ≤ p.1 ∧ 1 ≤ p.2.1 ∧ 1 ≤ p.2.2) (hside : side < 2) :
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
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    sideDir s ((faceBoundaryEdges na (x, y, z)).getD i ((x, y, z), 0))
      (facePlusCell na (x, y, z)) (faceMinusCell na (x, y, z))
      = some (flipDir i (s ((faceBoundaryEdges na (x, y, z)).getD i ((x, y, z), 0)).1)) := by
  fin_cases na <;> fin_cases i
  · -- na=0 i=0
    by_cases hb : s (x, y, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_0_0_pos s x y z hx hy hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_0_0 s x y z hx hy hz (by simpa using hb))
  · -- na=0 i=1
    by_cases hb : s (x, y + 1, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_0_1_pos s x y z hx hy hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_0_1 s x y z hx hy hz (by simpa using hb))
  · -- na=0 i=2
    by_cases hb : s (x, y, z + 1)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_0_2_pos s x y z hx hy hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_0_2 s x y z hx hy hz (by simpa using hb))
  · -- na=0 i=3
    by_cases hb : s (x, y, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_0_3_pos s x y z hx hy hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_0_3 s x y z hx hy hz (by simpa using hb))
  · -- na=1 i=0
    by_cases hb : s (x, y, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_1_0_pos s x y z hx hy hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_1_0 s x y z hx hy hz (by simpa using hb))
  · -- na=1 i=1
    by_cases hb : s (x, y, z + 1)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_1_1_pos s x y z hx hy hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_1_1 s x y z hx hy hz (by simpa using hb))
  · -- na=1 i=2
    by_cases hb : s (x + 1, y, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_1_2_pos s x y z hx hy hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_1_2 s x y z hx hy hz (by simpa using hb))
  · -- na=1 i=3
    by_cases hb : s (x, y, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_1_3_pos s x y z hx hy hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_1_3 s x y z hx hy hz (by simpa using hb))
  · -- na=2 i=0
    by_cases hb : s (x, y, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_2_0_pos s x y z hx hy hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_2_0 s x y z hx hy hz (by simpa using hb))
  · -- na=2 i=1
    by_cases hb : s (x + 1, y, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_2_1_pos s x y z hx hy hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_2_1 s x y z hx hy hz (by simpa using hb))
  · -- na=2 i=2
    by_cases hb : s (x, y + 1, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_2_2_pos s x y z hx hy hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_2_2 s x y z hx hy hz (by simpa using hb))
  · -- na=2 i=3
    by_cases hb : s (x, y, z)
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_2_3_pos s x y z hx hy hz (by simpa using hb))
    · simpa [faceBoundaryEdges, iaOf, ibOf, flipDir, PadGrid.succN, hb] using
        (orient_2_3 s x y z hx hy hz (by simpa using hb))

/-- Nat wrapper for the uniform orientation law. -/
theorem edge_dir (na : Nat) (hna : na < 3) (i : Nat) (hi : i < 4)
    (s : Lat → Bool) (x y z : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    sideDir s ((faceBoundaryEdges na (x, y, z)).getD i ((x, y, z), 0))
      (facePlusCell na (x, y, z)) (faceMinusCell na (x, y, z))
      = some (flipDir i (s ((faceBoundaryEdges na (x, y, z)).getD i ((x, y, z), 0)).1)) := by
  exact edge_dir_fin ⟨na, hna⟩ ⟨i, hi⟩ s x y z hx hy hz

/-- The enumeration's `dirAt` agrees with the orientation law's
    `flipDir` (machine-checked over the finite domains). -/
theorem dirAt_eq_flipDir :
    ∀ (i : Fin 4) (b : Bool),
      dirAt i (if b then 1 else 0) = if flipDir i b then 1 else 0 := by
  native_decide

end DmcOneStitch
end Vdb
