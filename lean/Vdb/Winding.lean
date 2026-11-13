/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  A first piece of the winding/orientation sign for a closed polygonal
  surface: the exact signed area of a planar rational polygon, and the
  orientation it induces. The unit square has signed area `1` and its reverse
  traversal `-1`, which is the orientation convention the winding number
  builds on. (The full winding number for a closed oriented surface is future
  work; this fixes the orientation/sign foundation exactly over `ℚ`.)

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

set_option linter.unusedSimpArgs false

namespace Vdb

/-- Planar rational points. -/
abbrev P2 : Type := ℚ × ℚ

/-- The closed polygon's directed edges (last vertex back to the first). -/
def edgesOf (poly : List P2) : List (P2 × P2) :=
  poly.zip (poly.rotate 1)

/-- Twice the signed area of a closed polygon (shoelace sum). -/
def signedArea2 (poly : List P2) : ℚ :=
  ((edgesOf poly).foldl
    (fun acc (e : P2 × P2) => acc + (e.1.1 * e.2.2 - e.2.1 * e.1.2)) 0) / 2

/-- The orientation of a closed polygon: `1` counter-clockwise, `-1`
    clockwise, `0` degenerate. -/
def orientation (poly : List P2) : ℤ :=
  if 0 < signedArea2 poly then 1
  else if signedArea2 poly < 0 then -1 else 0

/-- The unit square, counter-clockwise. -/
def unitSquare : List P2 := [(0, 0), (1, 0), (1, 1), (0, 1)]

theorem unitSquare_area : signedArea2 unitSquare = 1 := by
  simp [signedArea2, edgesOf, unitSquare]

theorem unitSquare_area_reverse : signedArea2 unitSquare.reverse = -1 := by
  simp [signedArea2, edgesOf, unitSquare]

theorem unitSquare_orientation : orientation unitSquare = 1 := by
  simp [orientation, unitSquare_area]

theorem unitSquare_orientation_reverse : orientation unitSquare.reverse = -1 := by
  simp [orientation, unitSquare_area_reverse]

end Vdb
