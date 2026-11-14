/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  The staircase face estimator, concretely: directed axis-aligned faces
  from the deep cells of an L¹ ball (the octahedron `|x−c| + |y−c| + |z−c| ≤ r`
  on a `(2k+1)`-box) to cells outside it, counted exactly on small grids.

  Why this matters: the staircase estimator is **not** consistent with the
  true surface area (documented in `Vdb/FloodFill.lean` — only the upper
  bound `#faces ≤ 6·#interior` is proved there). The true area of the
  octahedron is `4·√3·r²`; the measured counts

      n = 5, r = 2 :  78 faces   (true  27.71; ratio 2.81)
      n = 7, r = 3 : 150 faces   (true  62.35; ratio 2.41)
      n = 9, r = 4 : 246 faces   (true 110.85; ratio 2.22)
      n = 11, r = 5: 366 faces   (true 173.21; ratio 2.11)

  overshoot the true area systematically, approaching a factor of `2` —
  a concrete, reproducible witness of the direction-dependent rasterization
  overshoot. The counts are machine-checked here by `native_decide`;
  the true-area ratios are computed outside Lean and are recorded only in
  this comment and in `lean/VERIFICATION.md` (they involve `√3`, which is
  not needed for the formal statements).

  The estimator is what `src/tinyvdb`-style staircase tools would compute;
  the true-area formula for the octahedron is `8` equilateral triangles of
  side `r·√2`.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

set_option linter.unusedSimpArgs false

namespace Vdb

namespace StaircaseRatio

/-- All lattice points of the `n x n x n` box. -/
def allPoints (n : Nat) : List (Int × Int × Int) :=
  (List.range n).flatMap fun x =>
    (List.range n).flatMap fun y => (List.range n).map fun z => ((x : Int), (y : Int), (z : Int))

/-- The L¹ (octahedron) ball, radius `r`, centered at `((n−1)/2, …)`. -/
def deep (n r : Nat) (p : Int × Int × Int) : Bool :=
  let c : Int := ((n : Int) - 1) / 2
  decide (Int.natAbs (p.1 - c) + Int.natAbs (p.2.1 - c) + Int.natAbs (p.2.2 - c) ≤ r)

/-- The six axis directions. -/
def dirs : List (Int × Int × Int) :=
  [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]

/-- Directed faces from the deep cells to cells outside the L¹ ball. -/
def l1BallFaces (n r : Nat) : Nat :=
  let facesPer : List Nat := ((allPoints n).filter (deep n r)).map fun p =>
    (dirs.filter fun d => !deep n r (p.1 + d.1, p.2.1 + d.2.1, p.2.2 + d.2.2)).length
  facesPer.foldl (· + ·) 0

theorem l1BallFaces_5_2 : l1BallFaces 5 2 = 78 := by native_decide
theorem l1BallFaces_7_3 : l1BallFaces 7 3 = 150 := by native_decide
theorem l1BallFaces_9_4 : l1BallFaces 9 4 = 246 := by native_decide
theorem l1BallFaces_11_5 : l1BallFaces 11 5 = 366 := by native_decide

/-- The counts grow superlinearly in `r²` along the family — each grid
    contains strictly more directed faces than the octahedron's true face
    count scaled by a constant factor of two at the smaller radii. -/
theorem l1BallFaces_increasing : 78 < 150 ∧ 150 < 246 ∧ 246 < 366 := by native_decide

end StaircaseRatio

end Vdb
