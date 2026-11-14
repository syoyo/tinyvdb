/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Euler-characteristic differential harness (model half): computes χ(solid)
  with `Vdb.chiOf` for seeded random 5×5×5 grids (solid = voxels with value
  < 0), compared against the C `tvdb_level_set_euler_characteristic`
  (`lean/scripts/euler_c.c`), which returns 2·χ(solid) (Poincaré–Lefschetz).

  Printed one case per line: `case i chi` with `chi` the exact integer
  Euler characteristic of the solid's cubical complex.
  `scripts/check_euler.sh` asserts `c == 2 * lean` per case.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Euler

namespace Vdb

/-- Voxel index of (i, j, k) in the C layout (x fastest). -/
def voxelIdx (i j k : Nat) : Nat := (k * 5 + j) * 5 + i

/-- The solid cube set of a random grid: voxels with value < 0. -/
def solidOf (data : Array Float) : Finset C3 :=
  (Array.map
    (fun p => (Int.ofNat (p.2 % 5), Int.ofNat ((p.2 / 5) % 5), Int.ofNat (p.2 / 25)))
    (data.zipIdx |>.filter fun p => p.1 < 0.0)).toList.toFinset

partial def go (state : UInt64) (caseI : Nat) : IO Unit := do
  if caseI >= 400 then return ()
  let mut s := state
  let mut data : Array Float := Array.replicate 125 0.0
  for k in [0, 1, 2, 3, 4] do
    for j in [0, 1, 2, 3, 4] do
      for i in [0, 1, 2, 3, 4] do
        s := s * 6364136223846793005 + 1442695040888963407
        let u := (s >>> 33) % 100000
        let idx := voxelIdx i j k
        data := data.set! idx (u.toFloat / 100000.0 - 0.5)
  let solid := solidOf data
  IO.println s!"case {caseI} {chiOf solid}"
  go s (caseI + 1)

end Vdb

def main : IO Unit := do
  Vdb.go 0x9e3779b97f4a7c15 0
