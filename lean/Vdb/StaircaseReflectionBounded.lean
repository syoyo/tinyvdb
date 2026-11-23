/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Staircase-wall bounded group (§4.0): the staircase face count of a lattice
  half-space is invariant under axis reflection, so the inconsistency families
  proved for positive coefficients transfer to signed planar cuts. This module
  machine-checks the invariance over all coefficient signs in {-2,-1,1,2} and
  grids up to 5³; the general continuous-set consistency wall is unchanged.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

namespace Vdb

namespace StaircaseReflectionBounded

abbrev P (T : Nat) := Fin T × Fin T × Fin T

def inside (T : Nat) (a b c d : Int) (p : P T) : Bool :=
  a * p.1.val + b * p.2.1.val + c * p.2.2.val ≤ d

def adjacent {T : Nat} (p q : P T) : Bool :=
  (p.1.val + 1 == q.1.val ∧ p.2 == q.2) ||
  (q.1.val + 1 == p.1.val ∧ p.2 == q.2) ||
  (p.1 == q.1 ∧ p.2.1.val + 1 == q.2.1.val ∧ p.2.2 == q.2.2) ||
  (p.1 == q.1 ∧ q.2.1.val + 1 == p.2.1.val ∧ p.2.2 == q.2.2) ||
  (p.1 == q.1 ∧ p.2.1 == q.2.1 ∧ p.2.2.val + 1 == q.2.2.val) ||
  (p.1 == q.1 ∧ p.2.1 == q.2.1 ∧ q.2.2.val + 1 == p.2.2.val)

def faceCount (T : Nat) (a b c d : Int) : Nat :=
  ((Finset.univ : Finset (P T)).product Finset.univ).filter (fun pq =>
    adjacent pq.1 pq.2 && inside T a b c d pq.1 && !inside T a b c d pq.2) |>.card

def reflectX (T : Nat) (p : P T) : P T :=
  (⟨T - 1 - p.1.val, by
    have hp := p.1.isLt
    omega⟩, p.2)

/-- Reflecting x negates the x coefficient and shifts the offset by a·(T−1). -/
def reflectionInvariant : Bool :=
  (List.range 4).all fun Ti =>
    let T := Ti + 2
    (List.range 4).all fun ai =>
      let a := ([-2, -1, 1, 2].getD ai 0 : Int)
      (List.range 4).all fun bi =>
        let b := ([-2, -1, 1, 2].getD bi 0 : Int)
        (List.range 4).all fun ci =>
          let c := ([-2, -1, 1, 2].getD ci 0 : Int)
          (List.range (T + 1)).all fun di =>
            let d := (di : Int) - T
            faceCount T a b c d == faceCount T (-a) b c (d - a * (T - 1 : Nat))

theorem reflectionInvariant_true : reflectionInvariant = true := by
  native_decide

end StaircaseReflectionBounded
end Vdb
