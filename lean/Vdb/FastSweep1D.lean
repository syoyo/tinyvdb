/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  PH wall group (§4.0 bounded tier): one-dimensional fast sweeping. With two
  frozen boundary voxels at 0, a left sweep followed by a right sweep reaches
  the exact 1-D Eikonal solution `min(i, n+1-i)·h` in one pass each. The bounded
  check covers all grids up to 9 interior voxels and three spacings with exact
  rational arithmetic; the general Zhao 2005 multi-direction convergence remains
  a documented wall.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

namespace Vdb

namespace FastSweep1D

/-- One Gauss–Seidel sweep in increasing index order. -/
def leftPass (h : Rat) : List Rat → List Rat
  | [] => []
  | x :: xs =>
      let rec go : Rat → List Rat → List Rat
        | _, [] => []
        | prev, y :: ys =>
            let z := min y (prev + h)
            z :: go z ys
      x :: go x xs

/-- One Gauss–Seidel sweep in decreasing index order, implemented by sweeping
    the reversed list. -/
def rightPass (h : Rat) (v : List Rat) : List Rat :=
  (leftPass h v.reverse).reverse

def sweep1D (h : Rat) (n : Nat) : List Rat :=
  rightPass h (leftPass h (0 :: List.replicate n ((n + 1 : Nat) * h) ++ [0]))

def exact1D (h : Rat) (n : Nat) : List Rat :=
  (List.range (n + 2)).map fun i => min (i : Rat) (((n + 1 : Nat) : Rat) - (i : Rat)) * h

def allSweepsExact : Bool :=
  (List.range 9).all fun n =>
    (List.range 3).all fun k =>
      let h : Rat := (k : Rat) + 1
      sweep1D h n == exact1D h n

theorem allSweepsExact_true : allSweepsExact = true := by
  native_decide

theorem sweep1D_eq_exact {n k : Nat} (hn : n < 9) (hk : k < 3) :
    sweep1D ((k : Rat) + 1) n = exact1D ((k : Rat) + 1) n := by
  have hnmem := List.mem_range.mpr hn
  have hkmem := List.mem_range.mpr hk
  have houter := List.all_eq_true.mp allSweepsExact_true n hnmem
  have hres := List.all_eq_true.mp houter k hkmem
  simpa only [beq_iff_eq] using hres

end FastSweep1D
end Vdb
