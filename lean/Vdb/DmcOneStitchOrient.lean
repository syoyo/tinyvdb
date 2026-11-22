/-
  DMC-1 orientation law — every face-boundary edge's F-side direction is
  determined by the sign at its lower endpoint.

  For an interior face (normal axis `na`) with the `+na` cell A and the
  `−na` cell B:

    * `E0 = (p, ia)` and `E1 = (succN p ia, ib)`: the F-side is directed
      `B → A` when the sign at the edge's start is `false`, `A → B` when
      `true`;
    * `E2 = (succN p ib, ia)` and `E3 = (p, ib)`: the reverse.

  Coordinate lower bounds `≥ 1` on all arguments follow from shell
  pinning for crossed edges of interior faces (any coordinate `0` or
  `n` pins the endpoint sign to false, so both signs are false and the
  edge is not crossed — shell faces never participate).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.DmcOneStitch
import Vdb.DmcOneEuler
import Vdb.PadGrid
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Vdb
namespace DmcOneStitch

-- flip = s (x, y, z) = false; F-side direction = some false
theorem orient_0_0 (s : Lat → Bool) (x y z : Nat) (hx : 1 ≤ x) (hz : 1 ≤ z) (hs : s (x, y, z) = false) :
    sideDir s ((x, y, z), 1) (facePlusCell 0 (x, y, z)) (faceMinusCell 0 (x, y, z))
      = some false := by
  have hring : DmcOnePad.incidentCells s ((x, y, z), 1) =
      [(x - 1, y, z - 1), (x - 1, y, z), (x, y, z), (x, y, z - 1)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [hx, hz]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_left (by decide : (0 = 0)),
    ite_eq_right (by decide : ¬ (0 = 1)),
    ite_eq_right (by decide : ¬ (0 = 2)),
    Nat.sub_add_cancel hx,  Nat.sub_add_cancel hz,
    show x ≠ x - 1 by omega, show z ≠ z - 1 by omega,
    show x - 1 ≠ x by omega, show z - 1 ≠ z by omega,
    show x ≠ x + 1 by omega, show z ≠ z + 1 by omega,
    show x + 1 ≠ x by omega, show z + 1 ≠ z by omega]
  simp
  omega

-- flip = s (x, y, z) = true; F-side direction = some true
theorem orient_0_0_pos (s : Lat → Bool) (x y z : Nat) (hx : 1 ≤ x) (hz : 1 ≤ z) (hs : s (x, y, z) = true) :
    sideDir s ((x, y, z), 1) (facePlusCell 0 (x, y, z)) (faceMinusCell 0 (x, y, z))
      = some true := by
  have hring : DmcOnePad.incidentCells s ((x, y, z), 1) =
      [(x - 1, y, z - 1), (x, y, z - 1), (x, y, z), (x - 1, y, z)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [hx, hz]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_left (by decide : (0 = 0)),
    ite_eq_right (by decide : ¬ (0 = 1)),
    ite_eq_right (by decide : ¬ (0 = 2)),
    Nat.sub_add_cancel hx,  Nat.sub_add_cancel hz,
    show x ≠ x - 1 by omega, show z ≠ z - 1 by omega,
    show x - 1 ≠ x by omega, show z - 1 ≠ z by omega,
    show x ≠ x + 1 by omega, show z ≠ z + 1 by omega,
    show x + 1 ≠ x by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x, y + 1, z) = false; F-side direction = some false
theorem orient_0_1 (s : Lat → Bool) (x y z : Nat) (hx : 1 ≤ x) (hs : s (x, y + 1, z) = false) :
    sideDir s ((x, y + 1, z), 2) (facePlusCell 0 (x, y, z)) (faceMinusCell 0 (x, y, z))
      = some false := by
  have hring : DmcOnePad.incidentCells s ((x, y + 1, z), 2) =
      [(x - 1, y, z), (x, y, z), (x, y + 1, z), (x - 1, y + 1, z)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [hx,]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_left (by decide : (0 = 0)),
    ite_eq_right (by decide : ¬ (0 = 1)),
    ite_eq_right (by decide : ¬ (0 = 2)),
    Nat.sub_add_cancel hx,
    show x ≠ x - 1 by omega,
    show x - 1 ≠ x by omega,
    show x ≠ x + 1 by omega, show y ≠ y + 1 by omega,
    show x + 1 ≠ x by omega, show y + 1 ≠ y by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x, y + 1, z) = true; F-side direction = some true
theorem orient_0_1_pos (s : Lat → Bool) (x y z : Nat) (hx : 1 ≤ x) (hs : s (x, y + 1, z) = true) :
    sideDir s ((x, y + 1, z), 2) (facePlusCell 0 (x, y, z)) (faceMinusCell 0 (x, y, z))
      = some true := by
  have hring : DmcOnePad.incidentCells s ((x, y + 1, z), 2) =
      [(x - 1, y, z), (x - 1, y + 1, z), (x, y + 1, z), (x, y, z)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [hx,]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_left (by decide : (0 = 0)),
    ite_eq_right (by decide : ¬ (0 = 1)),
    ite_eq_right (by decide : ¬ (0 = 2)),
    Nat.sub_add_cancel hx,
    show x ≠ x - 1 by omega,
    show x - 1 ≠ x by omega,
    show x ≠ x + 1 by omega, show y ≠ y + 1 by omega,
    show x + 1 ≠ x by omega, show y + 1 ≠ y by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x, y, z + 1) = false; F-side direction = some true
theorem orient_0_2 (s : Lat → Bool) (x y z : Nat) (hx : 1 ≤ x) (hs : s (x, y, z + 1) = false) :
    sideDir s ((x, y, z + 1), 1) (facePlusCell 0 (x, y, z)) (faceMinusCell 0 (x, y, z))
      = some true := by
  have hring : DmcOnePad.incidentCells s ((x, y, z + 1), 1) =
      [(x - 1, y, z), (x - 1, y, z + 1), (x, y, z + 1), (x, y, z)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [hx,]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_left (by decide : (0 = 0)),
    ite_eq_right (by decide : ¬ (0 = 1)),
    ite_eq_right (by decide : ¬ (0 = 2)),
    Nat.sub_add_cancel hx,
    show x ≠ x - 1 by omega,
    show x - 1 ≠ x by omega,
    show x ≠ x + 1 by omega, show z ≠ z + 1 by omega,
    show x + 1 ≠ x by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x, y, z + 1) = true; F-side direction = some false
theorem orient_0_2_pos (s : Lat → Bool) (x y z : Nat) (hx : 1 ≤ x) (hs : s (x, y, z + 1) = true) :
    sideDir s ((x, y, z + 1), 1) (facePlusCell 0 (x, y, z)) (faceMinusCell 0 (x, y, z))
      = some false := by
  have hring : DmcOnePad.incidentCells s ((x, y, z + 1), 1) =
      [(x - 1, y, z), (x, y, z), (x, y, z + 1), (x - 1, y, z + 1)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [hx,]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_left (by decide : (0 = 0)),
    ite_eq_right (by decide : ¬ (0 = 1)),
    ite_eq_right (by decide : ¬ (0 = 2)),
    Nat.sub_add_cancel hx,
    show x ≠ x - 1 by omega,
    show x - 1 ≠ x by omega,
    show x ≠ x + 1 by omega, show z ≠ z + 1 by omega,
    show x + 1 ≠ x by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x, y, z) = false; F-side direction = some true
theorem orient_0_3 (s : Lat → Bool) (x y z : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) (hs : s (x, y, z) = false) :
    sideDir s ((x, y, z), 2) (facePlusCell 0 (x, y, z)) (faceMinusCell 0 (x, y, z))
      = some true := by
  have hring : DmcOnePad.incidentCells s ((x, y, z), 2) =
      [(x - 1, y - 1, z), (x, y - 1, z), (x, y, z), (x - 1, y, z)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [hx, hy]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_left (by decide : (0 = 0)),
    ite_eq_right (by decide : ¬ (0 = 1)),
    ite_eq_right (by decide : ¬ (0 = 2)),
    Nat.sub_add_cancel hx, Nat.sub_add_cancel hy,
    show x ≠ x - 1 by omega, show y ≠ y - 1 by omega,
    show x - 1 ≠ x by omega, show y - 1 ≠ y by omega,
    show x ≠ x + 1 by omega, show y ≠ y + 1 by omega,
    show x + 1 ≠ x by omega, show y + 1 ≠ y by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x, y, z) = true; F-side direction = some false
theorem orient_0_3_pos (s : Lat → Bool) (x y z : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) (hs : s (x, y, z) = true) :
    sideDir s ((x, y, z), 2) (facePlusCell 0 (x, y, z)) (faceMinusCell 0 (x, y, z))
      = some false := by
  have hring : DmcOnePad.incidentCells s ((x, y, z), 2) =
      [(x - 1, y - 1, z), (x - 1, y, z), (x, y, z), (x, y - 1, z)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [hx, hy]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_left (by decide : (0 = 0)),
    ite_eq_right (by decide : ¬ (0 = 1)),
    ite_eq_right (by decide : ¬ (0 = 2)),
    Nat.sub_add_cancel hx, Nat.sub_add_cancel hy,
    show x ≠ x - 1 by omega, show y ≠ y - 1 by omega,
    show x - 1 ≠ x by omega, show y - 1 ≠ y by omega,
    show x ≠ x + 1 by omega, show y ≠ y + 1 by omega,
    show x + 1 ≠ x by omega, show y + 1 ≠ y by omega, show z + 1 ≠ z by omega]
  simp
  omega

-- flip = s (x, y, z) = false; F-side direction = some false
theorem orient_1_0 (s : Lat → Bool) (x y z : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) (hs : s (x, y, z) = false) :
    sideDir s ((x, y, z), 2) (facePlusCell 1 (x, y, z)) (faceMinusCell 1 (x, y, z))
      = some false := by
  have hring : DmcOnePad.incidentCells s ((x, y, z), 2) =
      [(x - 1, y - 1, z), (x, y - 1, z), (x, y, z), (x - 1, y, z)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [hx, hy]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_right (by decide : ¬ (1 = 0)),
    ite_eq_left (by decide : (1 = 1)),
    ite_eq_right (by decide : ¬ (1 = 2)),
    Nat.sub_add_cancel hx, Nat.sub_add_cancel hy,
    show x ≠ x - 1 by omega, show y ≠ y - 1 by omega,
    show x - 1 ≠ x by omega, show y - 1 ≠ y by omega,
    show x ≠ x + 1 by omega, show y ≠ y + 1 by omega,
    show x + 1 ≠ x by omega, show y + 1 ≠ y by omega, show z + 1 ≠ z by omega]
  simp
  omega

-- flip = s (x, y, z) = true; F-side direction = some true
theorem orient_1_0_pos (s : Lat → Bool) (x y z : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) (hs : s (x, y, z) = true) :
    sideDir s ((x, y, z), 2) (facePlusCell 1 (x, y, z)) (faceMinusCell 1 (x, y, z))
      = some true := by
  have hring : DmcOnePad.incidentCells s ((x, y, z), 2) =
      [(x - 1, y - 1, z), (x - 1, y, z), (x, y, z), (x, y - 1, z)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [hx, hy]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_right (by decide : ¬ (1 = 0)),
    ite_eq_left (by decide : (1 = 1)),
    ite_eq_right (by decide : ¬ (1 = 2)),
    Nat.sub_add_cancel hx, Nat.sub_add_cancel hy,
    show x ≠ x - 1 by omega, show y ≠ y - 1 by omega,
    show x - 1 ≠ x by omega, show y - 1 ≠ y by omega,
    show x ≠ x + 1 by omega, show y ≠ y + 1 by omega,
    show x + 1 ≠ x by omega, show y + 1 ≠ y by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x, y, z + 1) = false; F-side direction = some false
theorem orient_1_1 (s : Lat → Bool) (x y z : Nat) (hy : 1 ≤ y) (hs : s (x, y, z + 1) = false) :
    sideDir s ((x, y, z + 1), 0) (facePlusCell 1 (x, y, z)) (faceMinusCell 1 (x, y, z))
      = some false := by
  have hring : DmcOnePad.incidentCells s ((x, y, z + 1), 0) =
      [(x, y - 1, z), (x, y, z), (x, y, z + 1), (x, y - 1, z + 1)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [hy,]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_right (by decide : ¬ (1 = 0)),
    ite_eq_left (by decide : (1 = 1)),
    ite_eq_right (by decide : ¬ (1 = 2)),
     Nat.sub_add_cancel hy,  show y ≠ y - 1 by omega,  show y - 1 ≠ y by omega,  show y ≠ y + 1 by omega, show z ≠ z + 1 by omega, show y + 1 ≠ y by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x, y, z + 1) = true; F-side direction = some true
theorem orient_1_1_pos (s : Lat → Bool) (x y z : Nat) (hy : 1 ≤ y) (hs : s (x, y, z + 1) = true) :
    sideDir s ((x, y, z + 1), 0) (facePlusCell 1 (x, y, z)) (faceMinusCell 1 (x, y, z))
      = some true := by
  have hring : DmcOnePad.incidentCells s ((x, y, z + 1), 0) =
      [(x, y - 1, z), (x, y - 1, z + 1), (x, y, z + 1), (x, y, z)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [hy,]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_right (by decide : ¬ (1 = 0)),
    ite_eq_left (by decide : (1 = 1)),
    ite_eq_right (by decide : ¬ (1 = 2)),
     Nat.sub_add_cancel hy,  show y ≠ y - 1 by omega,  show y - 1 ≠ y by omega,  show y ≠ y + 1 by omega, show z ≠ z + 1 by omega, show y + 1 ≠ y by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x + 1, y, z) = false; F-side direction = some true
theorem orient_1_2 (s : Lat → Bool) (x y z : Nat) (hy : 1 ≤ y) (hs : s (x + 1, y, z) = false) :
    sideDir s ((x + 1, y, z), 2) (facePlusCell 1 (x, y, z)) (faceMinusCell 1 (x, y, z))
      = some true := by
  have hring : DmcOnePad.incidentCells s ((x + 1, y, z), 2) =
      [(x, y - 1, z), (x + 1, y - 1, z), (x + 1, y, z), (x, y, z)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [ hy]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_right (by decide : ¬ (1 = 0)),
    ite_eq_left (by decide : (1 = 1)),
    ite_eq_right (by decide : ¬ (1 = 2)),
     Nat.sub_add_cancel hy,
     show y ≠ y - 1 by omega,
     show y - 1 ≠ y by omega,
    show x ≠ x + 1 by omega, show y ≠ y + 1 by omega,
    show x + 1 ≠ x by omega, show y + 1 ≠ y by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x + 1, y, z) = true; F-side direction = some false
theorem orient_1_2_pos (s : Lat → Bool) (x y z : Nat) (hy : 1 ≤ y) (hs : s (x + 1, y, z) = true) :
    sideDir s ((x + 1, y, z), 2) (facePlusCell 1 (x, y, z)) (faceMinusCell 1 (x, y, z))
      = some false := by
  have hring : DmcOnePad.incidentCells s ((x + 1, y, z), 2) =
      [(x, y - 1, z), (x, y, z), (x + 1, y, z), (x + 1, y - 1, z)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [ hy]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_right (by decide : ¬ (1 = 0)),
    ite_eq_left (by decide : (1 = 1)),
    ite_eq_right (by decide : ¬ (1 = 2)),
     Nat.sub_add_cancel hy,
     show y ≠ y - 1 by omega,
     show y - 1 ≠ y by omega,
    show x ≠ x + 1 by omega, show y ≠ y + 1 by omega,
    show x + 1 ≠ x by omega, show y + 1 ≠ y by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x, y, z) = false; F-side direction = some true
theorem orient_1_3 (s : Lat → Bool) (x y z : Nat) (hy : 1 ≤ y) (hz : 1 ≤ z) (hs : s (x, y, z) = false) :
    sideDir s ((x, y, z), 0) (facePlusCell 1 (x, y, z)) (faceMinusCell 1 (x, y, z))
      = some true := by
  have hring : DmcOnePad.incidentCells s ((x, y, z), 0) =
      [(x, y - 1, z - 1), (x, y, z - 1), (x, y, z), (x, y - 1, z)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [hy, hz]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_right (by decide : ¬ (1 = 0)),
    ite_eq_left (by decide : (1 = 1)),
    ite_eq_right (by decide : ¬ (1 = 2)),
     Nat.sub_add_cancel hy, Nat.sub_add_cancel hz, show y ≠ y - 1 by omega, show z ≠ z - 1 by omega, show y - 1 ≠ y by omega, show z - 1 ≠ z by omega, show y ≠ y + 1 by omega, show z ≠ z + 1 by omega, show y + 1 ≠ y by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x, y, z) = true; F-side direction = some false
theorem orient_1_3_pos (s : Lat → Bool) (x y z : Nat) (hy : 1 ≤ y) (hz : 1 ≤ z) (hs : s (x, y, z) = true) :
    sideDir s ((x, y, z), 0) (facePlusCell 1 (x, y, z)) (faceMinusCell 1 (x, y, z))
      = some false := by
  have hring : DmcOnePad.incidentCells s ((x, y, z), 0) =
      [(x, y - 1, z - 1), (x, y - 1, z), (x, y, z), (x, y, z - 1)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [hy, hz]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_right (by decide : ¬ (1 = 0)),
    ite_eq_left (by decide : (1 = 1)),
    ite_eq_right (by decide : ¬ (1 = 2)),
     Nat.sub_add_cancel hy, Nat.sub_add_cancel hz, show y ≠ y - 1 by omega, show z ≠ z - 1 by omega, show y - 1 ≠ y by omega, show z - 1 ≠ z by omega, show y ≠ y + 1 by omega, show z ≠ z + 1 by omega, show y + 1 ≠ y by omega, show z + 1 ≠ z by omega]
  simp
  omega

-- flip = s (x, y, z) = false; F-side direction = some false
theorem orient_2_0 (s : Lat → Bool) (x y z : Nat) (hy : 1 ≤ y) (hz : 1 ≤ z) (hs : s (x, y, z) = false) :
    sideDir s ((x, y, z), 0) (facePlusCell 2 (x, y, z)) (faceMinusCell 2 (x, y, z))
      = some false := by
  have hring : DmcOnePad.incidentCells s ((x, y, z), 0) =
      [(x, y - 1, z - 1), (x, y, z - 1), (x, y, z), (x, y - 1, z)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [hy, hz]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_right (by decide : ¬ (2 = 0)),
    ite_eq_right (by decide : ¬ (2 = 1)),
     Nat.sub_add_cancel hy, Nat.sub_add_cancel hz, show y ≠ y - 1 by omega, show z ≠ z - 1 by omega, show y - 1 ≠ y by omega, show z - 1 ≠ z by omega, show y ≠ y + 1 by omega, show z ≠ z + 1 by omega, show y + 1 ≠ y by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x, y, z) = true; F-side direction = some true
theorem orient_2_0_pos (s : Lat → Bool) (x y z : Nat) (hy : 1 ≤ y) (hz : 1 ≤ z) (hs : s (x, y, z) = true) :
    sideDir s ((x, y, z), 0) (facePlusCell 2 (x, y, z)) (faceMinusCell 2 (x, y, z))
      = some true := by
  have hring : DmcOnePad.incidentCells s ((x, y, z), 0) =
      [(x, y - 1, z - 1), (x, y - 1, z), (x, y, z), (x, y, z - 1)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [hy, hz]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_right (by decide : ¬ (2 = 0)),
    ite_eq_right (by decide : ¬ (2 = 1)),
     Nat.sub_add_cancel hy, Nat.sub_add_cancel hz, show y ≠ y - 1 by omega, show z ≠ z - 1 by omega, show y - 1 ≠ y by omega, show z - 1 ≠ z by omega, show y ≠ y + 1 by omega, show z ≠ z + 1 by omega, show y + 1 ≠ y by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x + 1, y, z) = false; F-side direction = some false
theorem orient_2_1 (s : Lat → Bool) (x y z : Nat) (hz : 1 ≤ z) (hs : s (x + 1, y, z) = false) :
    sideDir s ((x + 1, y, z), 1) (facePlusCell 2 (x, y, z)) (faceMinusCell 2 (x, y, z))
      = some false := by
  have hring : DmcOnePad.incidentCells s ((x + 1, y, z), 1) =
      [(x, y, z - 1), (x, y, z), (x + 1, y, z), (x + 1, y, z - 1)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [ hz]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_right (by decide : ¬ (2 = 0)),
    ite_eq_right (by decide : ¬ (2 = 1)),
      Nat.sub_add_cancel hz,
     show z ≠ z - 1 by omega,
     show z - 1 ≠ z by omega,
    show x ≠ x + 1 by omega, show z ≠ z + 1 by omega,
    show x + 1 ≠ x by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x + 1, y, z) = true; F-side direction = some true
theorem orient_2_1_pos (s : Lat → Bool) (x y z : Nat) (hz : 1 ≤ z) (hs : s (x + 1, y, z) = true) :
    sideDir s ((x + 1, y, z), 1) (facePlusCell 2 (x, y, z)) (faceMinusCell 2 (x, y, z))
      = some true := by
  have hring : DmcOnePad.incidentCells s ((x + 1, y, z), 1) =
      [(x, y, z - 1), (x + 1, y, z - 1), (x + 1, y, z), (x, y, z)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [ hz]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_right (by decide : ¬ (2 = 0)),
    ite_eq_right (by decide : ¬ (2 = 1)),
      Nat.sub_add_cancel hz,
     show z ≠ z - 1 by omega,
     show z - 1 ≠ z by omega,
    show x ≠ x + 1 by omega, show z ≠ z + 1 by omega,
    show x + 1 ≠ x by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x, y + 1, z) = false; F-side direction = some true
theorem orient_2_2 (s : Lat → Bool) (x y z : Nat) (hz : 1 ≤ z) (hs : s (x, y + 1, z) = false) :
    sideDir s ((x, y + 1, z), 0) (facePlusCell 2 (x, y, z)) (faceMinusCell 2 (x, y, z))
      = some true := by
  have hring : DmcOnePad.incidentCells s ((x, y + 1, z), 0) =
      [(x, y, z - 1), (x, y + 1, z - 1), (x, y + 1, z), (x, y, z)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [ hz]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_right (by decide : ¬ (2 = 0)),
    ite_eq_right (by decide : ¬ (2 = 1)),
      Nat.sub_add_cancel hz,  show z ≠ z - 1 by omega,  show z - 1 ≠ z by omega, show y ≠ y + 1 by omega, show z ≠ z + 1 by omega, show y + 1 ≠ y by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x, y + 1, z) = true; F-side direction = some false
theorem orient_2_2_pos (s : Lat → Bool) (x y z : Nat) (hz : 1 ≤ z) (hs : s (x, y + 1, z) = true) :
    sideDir s ((x, y + 1, z), 0) (facePlusCell 2 (x, y, z)) (faceMinusCell 2 (x, y, z))
      = some false := by
  have hring : DmcOnePad.incidentCells s ((x, y + 1, z), 0) =
      [(x, y, z - 1), (x, y, z), (x, y + 1, z), (x, y + 1, z - 1)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [ hz]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_right (by decide : ¬ (2 = 0)),
    ite_eq_right (by decide : ¬ (2 = 1)),
      Nat.sub_add_cancel hz,  show z ≠ z - 1 by omega,  show z - 1 ≠ z by omega, show y ≠ y + 1 by omega, show z ≠ z + 1 by omega, show y + 1 ≠ y by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x, y, z) = false; F-side direction = some true
theorem orient_2_3 (s : Lat → Bool) (x y z : Nat) (hx : 1 ≤ x) (hz : 1 ≤ z) (hs : s (x, y, z) = false) :
    sideDir s ((x, y, z), 1) (facePlusCell 2 (x, y, z)) (faceMinusCell 2 (x, y, z))
      = some true := by
  have hring : DmcOnePad.incidentCells s ((x, y, z), 1) =
      [(x - 1, y, z - 1), (x - 1, y, z), (x, y, z), (x, y, z - 1)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [hx, hz]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_right (by decide : ¬ (2 = 0)),
    ite_eq_right (by decide : ¬ (2 = 1)),
    Nat.sub_add_cancel hx,  Nat.sub_add_cancel hz,
    show x ≠ x - 1 by omega, show z ≠ z - 1 by omega,
    show x - 1 ≠ x by omega, show z - 1 ≠ z by omega,
    show x ≠ x + 1 by omega, show z ≠ z + 1 by omega,
    show x + 1 ≠ x by omega, show z + 1 ≠ z by omega]
  simp

-- flip = s (x, y, z) = true; F-side direction = some false
theorem orient_2_3_pos (s : Lat → Bool) (x y z : Nat) (hx : 1 ≤ x) (hz : 1 ≤ z) (hs : s (x, y, z) = true) :
    sideDir s ((x, y, z), 1) (facePlusCell 2 (x, y, z)) (faceMinusCell 2 (x, y, z))
      = some false := by
  have hring : DmcOnePad.incidentCells s ((x, y, z), 1) =
      [(x - 1, y, z - 1), (x, y, z - 1), (x, y, z), (x - 1, y, z)] := by
    unfold DmcOnePad.incidentCells Vdb.PadGrid.anchorCell Vdb.PadGrid.ij Vdb.PadGrid.addCell
    rw [hs]; simp [hx, hz]
  unfold sideDir facePlusCell faceMinusCell
  rw [hring]
  simp only [beq_iff_eq, Prod.mk.injEq, Bool.and_eq_true, Bool.or_eq_true,
    ite_eq_right (by decide : ¬ (2 = 0)),
    ite_eq_right (by decide : ¬ (2 = 1)),
    Nat.sub_add_cancel hx,  Nat.sub_add_cancel hz,
    show x ≠ x - 1 by omega, show z ≠ z - 1 by omega,
    show x - 1 ≠ x by omega, show z - 1 ≠ z by omega,
    show x ≠ x + 1 by omega, show z ≠ z + 1 by omega,
    show x + 1 ≠ x by omega, show z + 1 ≠ z by omega]
  simp

end DmcOneStitch
end Vdb
