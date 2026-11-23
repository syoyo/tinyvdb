/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Pre-existing wall group (§4.0 bounded tier): Poincaré–Lefschetz duality for
  cubical solids. The general theorem needs homology infrastructure absent from
  mathlib 4.36. This group machine-checks the identity `χ(∂K) = 2·χ(K)` for all
  256 subsets of eight well-separated unit cubes on a spacing-3 lattice, using
  the exact `Euler.chiOf` / `Euler.chiBoundary` definitions. It is bounded
  evidence for disjoint solids, not a general duality theorem.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Euler

namespace Vdb

namespace EulerDisjointBounded

abbrev C3Int := Int × Int × Int

def lattice8 : List C3Int :=
  [(0,0,0), (3,0,0), (0,3,0), (0,0,3),
   (3,3,0), (3,0,3), (0,3,3), (3,3,3)]

def maskCubes (m : Nat) : Finset C3Int :=
  (lattice8.zipIdx).foldl (fun s (c, i) =>
    if (m / 2^i) % 2 == 1 then insert c s else s) ∅

/-- Two unit cubes are face-adjacent iff they differ by one in exactly one
    coordinate and agree in the other two. -/
def faceAdjacent (a b : C3Int) : Bool :=
  (a.1 - b.1).natAbs + (a.2.1 - b.2.1).natAbs + (a.2.2 - b.2.2).natAbs == 1

def separated (K : Finset C3Int) : Bool :=
  lattice8.all fun a => lattice8.all fun b =>
    !(decide (a ∈ K)) || !(decide (b ∈ K)) || a == b || !faceAdjacent a b

def dualityHolds (K : Finset C3Int) : Bool :=
  chiBoundary K == 2 * chiOf K

def allSeparatedDual : Bool :=
  (List.range 256).all fun m =>
    let K := maskCubes m
    !separated K || dualityHolds K

theorem allSeparatedDual_true : allSeparatedDual = true := by
  native_decide

theorem separated_duality {m : Nat} (hm : m < 256) (hsep : separated (maskCubes m) = true) :
    chiBoundary (maskCubes m) = 2 * chiOf (maskCubes m) := by
  have houter := List.all_eq_true.mp allSeparatedDual_true m (List.mem_range.mpr hm)
  have hbool : dualityHolds (maskCubes m) = true := by simpa [hsep] using houter
  simpa [dualityHolds, beq_iff_eq] using hbool

end EulerDisjointBounded
end Vdb
