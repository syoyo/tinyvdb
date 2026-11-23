/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  PH follow-up 2.1: convex hull specification. The executable twin computes
  supporting-plane faces exactly; this module proves the abstract convexity
  contract that any such hull must satisfy: the hull is convex and contains all
  input points, hence every convex combination of sample points lies inside it.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Hull
import Vdb.LevelSet

noncomputable section

open scoped RealInnerProductSpace

namespace Vdb

/-- The convex hull of a finite point family, as a set. -/
def pointHull (ps : List Point) : Set Point := convexHull ℝ (ps.toFinset : Set Point)

theorem convex_pointHull (ps : List Point) : Convex ℝ (pointHull ps) := by
  exact convex_convexHull ℝ (ps.toFinset : Set Point)

theorem mem_pointHull_of_mem {ps : List Point} {p : Point} (h : p ∈ ps) :
    p ∈ pointHull ps := by
  exact subset_convexHull ℝ (ps.toFinset : Set Point) (by simpa using h)

end Vdb
