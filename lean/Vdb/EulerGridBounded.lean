/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Homology-wall bounded group (§4.0): exact `Euler` duality for *adjacent*
  cubical solids, not just separated cubes. All 512 subsets of a 3×3×1 slab
  are checked with `native_decide`: `χ(∂K) = 2·χ(K)`. The general
  homology/Poincaré–Lefschetz theorem remains walled because mathlib 4.36 has
  no suitable cubical homology bridge.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Euler

namespace Vdb

namespace EulerGridBounded

def grid9 : List (Int × Int × Int) :=
  (List.range 3).flatMap fun j =>
    (List.range 3).map fun i => ((i : Int), (j : Int), 0)

def maskCubes (m : Nat) : Finset (Int × Int × Int) :=
  (grid9.zipIdx).foldl (fun s (c, i) =>
    if (m / 2^i) % 2 == 1 then insert c s else s) ∅

def dualityHolds (K : Finset (Int × Int × Int)) : Bool :=
  chiBoundary K == 2 * chiOf K

def cheb (a b : Int × Int × Int) : Nat :=
  max (a.1 - b.1).natAbs (max (a.2.1 - b.2.1).natAbs (a.2.2 - b.2.2).natAbs)

def manh (a b : Int × Int × Int) : Nat :=
  (a.1 - b.1).natAbs + (a.2.1 - b.2.1).natAbs + (a.2.2 - b.2.2).natAbs

/-- No corner/edge-only contact: any touching pair shares a face. -/
def manifoldContact (m : Nat) : Bool :=
  grid9.all fun a => grid9.all fun b =>
    !decide (a ∈ maskCubes m) || !decide (b ∈ maskCubes m) ||
      a == b || cheb a b != 1 || manh a b == 1

def allGridDuality : Bool :=
  (List.range 512).all fun m => !manifoldContact m || dualityHolds (maskCubes m)

theorem allGridDuality_true : allGridDuality = true := by
  native_decide

theorem grid_duality {m : Nat} (hm : m < 512) (hc : manifoldContact m = true) :
    chiBoundary (maskCubes m) = 2 * chiOf (maskCubes m) := by
  have h := List.all_eq_true.mp allGridDuality_true m (List.mem_range.mpr hm)
  have hb : dualityHolds (maskCubes m) = true := by simpa [hc] using h
  simpa [dualityHolds, beq_iff_eq] using hb

end EulerGridBounded
end Vdb
