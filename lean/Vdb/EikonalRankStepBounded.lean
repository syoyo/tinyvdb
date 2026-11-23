/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Zhao-tier wall group (§4.0 bounded tier): rank-decrease propagation for the
  1-D Eikonal relaxation. `eikonal_max_step` proves that a positive maximum
  propagates to some neighbour; the rank-decrease form needed by
  `DiscreteComparison` is checked here over all rational configurations with
  values 0..4 on a 4-voxel grid, h = 1. The check **fails**: the rank-decrease
  premise is too strong (a maximum plateau can extend away from the boundary),
  so convergence needs a different comparison argument. The concrete witness
  is u = [0,1,2,1], v = [0,0,1,1], where the maximum of u−v is shared by
  interior voxels with non-decreasing rank.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

namespace Vdb

namespace EikonalRankStepBounded

abbrev V4 := List Rat

def vals : List Rat := [0, 1, 2, 3, 4]

def enums4 : List V4 :=
  (List.range 4).foldl (fun fs _ =>
    fs.flatMap fun f => vals.map fun v => f ++ [v]) [[]]

def vAt (u : V4) (i : Nat) : Rat := u.getD i 0

def rank (i : Nat) : Nat := min i (3 - i)

def interiorOK (u v : V4) (i : Nat) : Bool :=
  i > 0 && i < 3 &&
  vAt u i ≤ min (vAt u (i-1)) (vAt u (i+1)) + 1 &&
  min (vAt v (i-1)) (vAt v (i+1)) + 1 ≤ vAt v i &&
  0 < vAt u i - vAt v i &&
  (List.range 4).all fun j => vAt u j - vAt v j ≤ vAt u i - vAt v i

def rankStepOK : Bool :=
  enums4.all fun u => enums4.all fun v =>
    (List.range 4).all fun i =>
      let M := vAt u i - vAt v i
      !interiorOK u v i ||
        ((vAt u (i-1) - vAt v (i-1) == M && rank (i-1) < rank i) ||
         (vAt u (i+1) - vAt v (i+1) == M && rank (i+1) < rank i))

theorem rankStepOK_false : rankStepOK = false := by
  native_decide

end EikonalRankStepBounded
end Vdb
