/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  PH wall group (§4.0, bounded tier): algebraic (S)-style positivity over a
  finite rational configuration. The true geometric seam (S) uses spherical
  corner angles `θ` and unit co-normals `n` and asks
  `∀ j, 0 < Σᵢ θᵢ ⟪nᵢ,nⱼ⟫`; for n ≥ 6 it remains walled. This module establishes
  the *uniform-weight* algebraic core for every pointed sub-configuration of
  the coordinate axes: with `θᵢ = 1`, the weighted sum over any pointed subset
  is positive at every member. Machine-checked over all 2^6 subsets with
  exact rational arithmetic. It is evidence for the algebra, not a proof of
  the geometric angle theorem.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

namespace Vdb

namespace AngleNFaceRatBounded

abbrev RV3 := Rat × Rat × Rat

def rdot (a b : RV3) : Rat := a.1*b.1 + a.2.1*b.2.1 + a.2.2*b.2.2
def radd (a b : RV3) : RV3 := (a.1+b.1, a.2.1+b.2.1, a.2.2+b.2.2)

def axes6 : List RV3 :=
  [(1,0,0), (-1,0,0), (0,1,0), (0,-1,0), (0,0,1), (0,0,-1)]

def maskList (m : Nat) : List RV3 :=
  (axes6.zipIdx).filterMap fun (v, i) => if (m / 2^i) % 2 == 1 then some v else none

def rsum (vs : List RV3) : RV3 := vs.foldl radd (0, 0, 0)

/-- Pointedness witness: the sum of the normals pairs positively with each. -/
def pointed (vs : List RV3) : Bool :=
  let s := rsum vs
  vs.all (fun v => 0 < rdot s v)

/-- Uniform-weight seam at every member of the configuration. -/
def seamPos (vs : List RV3) : Bool :=
  vs.all (fun j => 0 < (vs.map fun n => rdot n j).sum)

def allPointedSeamPos : Bool :=
  (List.range 64).all fun m =>
    let vs := maskList m
    !pointed vs || seamPos vs

theorem allPointedSeamPos_true : allPointedSeamPos = true := by
  native_decide

theorem axes6_pointed_seam {m : Nat} (hm : m < 64) (h : pointed (maskList m) = true) :
    seamPos (maskList m) = true := by
  have hall := List.all_eq_true.mp allPointedSeamPos_true m (List.mem_range.mpr hm)
  simpa [h] using hall

end AngleNFaceRatBounded
end Vdb
