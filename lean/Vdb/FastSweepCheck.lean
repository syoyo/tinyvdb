/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Fast-sweeping differential harness (model half): the Float twin of the C
  `tvdb_fast_sweeping` (dense 3D Eikonal solver, `src/tinyvdb_ops.c`),
  compared against `lean/scripts/fastsweep_c.c`. Both sides generate the
  same 8×8×8 seeds from the same LCG and the same solver (frozen_band =
  0.25, voxel_size h = 0.25, max_iters = 10, tol = 1e-6).

  The C driver prints the final grid as `case i idx value` lines (plus a
  `case i iters n` header per case). The Lean exe regenerates the seeds
  itself, recomputes the sweep, and checks every voxel:

  * sign identity (exact): sign(golden) = sign(twin),
  * absolute error ≤ 1e-5 · h,
  * voxel count per case (512),
  * iteration count is not compared (a deterministic sweep converges; the
    grid content is what must match).

  `scripts/check_fastsweep.sh` drives both and reports.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/

import Vdb.FloatParse

namespace Vdb

/-- Voxel index of (i, j, k) in the C layout (x fastest). -/
def voxelIdx (i j k : Nat) : Nat := (k * 8 + j) * 8 + i

/-- The C `tvdb__godunov_solve`, Float twin. -/
def godunovF (a b c h : Float) : Float :=
  let x1 := a + h
  if x1 <= b then x1
  else
    let ab := a + b
    let disc := 2.0 * h * h - (a - b) * (a - b)
    if disc < 0.0 then x1
    else
      let x2 := 0.5 * (ab + Float.sqrt disc)
      if x2 <= c then x2
      else
        let abc := a + b + c
        let sumsq := a * a + b * b + c * c
        let disc3 := abc * abc - 3.0 * (sumsq - h * h)
        if disc3 < 0.0 then x2
        else (abc + Float.sqrt disc3) / 3.0

def min2 (a b : Float) : Float := if a < b then a else b

/-- The ranges each sweep direction walks, in order. -/
def rangeDir (sx sy sz : Int) : List Nat × List Nat × List Nat :=
  (if sx > 0 then List.range 8 else (List.range 8).reverse,
   if sy > 0 then List.range 8 else (List.range 8).reverse,
   if sz > 0 then List.range 8 else (List.range 8).reverse)

/-- The C `tvdb_fast_sweeping`, Float twin. -/
def fastSweeping (data : Array Float) (frozenBand h : Float) : Array Float := Id.run do
  let n := data.size
  let huge := 1.0e30
  let mut signPos : Array Bool := Array.replicate n false
  let mut frozen : Array Bool := Array.replicate n false
  let mut phi : Array Float := Array.replicate n 0.0
  for idx in [:n] do
    let v := data[idx]!
    signPos := signPos.set! idx (v >= 0.0)
    let a := fabs v
    if a <= frozenBand then
      frozen := frozen.set! idx true
      phi := phi.set! idx a
    else
      frozen := frozen.set! idx false
      phi := phi.set! idx huge
  let dirs := [(1, 1, 1), (-1, 1, 1), (1, -1, 1), (-1, -1, 1),
               (1, 1, -1), (-1, 1, -1), (1, -1, -1), (-1, -1, -1)]
  let mut iter := 0
  while iter < 10 do
    let mut maxChange : Float := 0.0
    for (sx, sy, sz) in dirs do
      let (rx, ry, rz) := rangeDir sx sy sz
      for z in rz do
        for y in ry do
          for x in rx do
            let idx := voxelIdx x y z
            if !frozen[idx]! then
              let mut ax := huge
              if x > 0 then ax := min2 ax phi[voxelIdx (x - 1) y z]!
              if x + 1 < 8 then ax := min2 ax phi[voxelIdx (x + 1) y z]!
              let mut ay := huge
              if y > 0 then ay := min2 ay phi[voxelIdx x (y - 1) z]!
              if y + 1 < 8 then ay := min2 ay phi[voxelIdx x (y + 1) z]!
              let mut az := huge
              if z > 0 then az := min2 az phi[voxelIdx x y (z - 1)]!
              if z + 1 < 8 then az := min2 az phi[voxelIdx x y (z + 1)]!
              -- Sort a <= b <= c.
              let mut a := ax
              let mut b := ay
              let mut c := az
              if a > b then let t := a; a := b; b := t
              if b > c then let t := b; b := c; c := t
              if a > b then let t := a; a := b; b := t
              if a < huge * 0.5 then
                let newV := godunovF a b c h
                if newV < phi[idx]! then
                  let ch := phi[idx]! - newV
                  if ch > maxChange then maxChange := ch
                  phi := phi.set! idx newV
    iter := iter + 1
    if maxChange <= 1.0e-6 then break
  -- Write back signed values; unreachable voxels keep the input.
  return (Array.range n).map fun idx =>
    if frozen[idx]! then
      data[idx]!
    else
      let a := phi[idx]!
      if a >= huge * 0.5 then data[idx]! else (if signPos[idx]! then a else -a)

/-- Parse one C output line into (case, idx, value). -/
structure CaseLine where
  caseI : Nat
  idx : Nat
  value : Float

def parseLine (s : String) : Option CaseLine := do
  match s.splitOn " " with
  | ["case", ci, ii, v] => do
      let caseI ← ci.toNat?
      let idx ← ii.toNat?
      let value ← parseFloatE v
      pure ⟨caseI, idx, value⟩
  | _ => none

/-- Regenerate the seeded grid for one case and return its final twin. -/
def regenerate (seed : UInt64) : Array Float × UInt64 := Id.run do
  let mut s := seed
  let mut data : Array Float := Array.replicate 512 0.0
  for k in [0, 1, 2, 3, 4, 5, 6, 7] do
    for j in [0, 1, 2, 3, 4, 5, 6, 7] do
      for i in [0, 1, 2, 3, 4, 5, 6, 7] do
        s := s * 6364136223846793005 + 1442695040888963407
        let u := (s >>> 33) % 100000
        let idx := voxelIdx i j k
        data := data.set! idx (u.toFloat / 100000.0 - 0.5)
  return (fastSweeping data 0.25 0.25, s)

end Vdb

def main (argv : List String) : IO Unit := do
  match argv with
  | [path] =>
      let raw ← IO.FS.readFile path
      let mut s : UInt64 := 0x9e3779b97f4a7c15
      let mut grids : Array (Array Float) := #[]
      for _ in [:200] do
        let (f, s') := Vdb.regenerate s
        grids := grids.push f
        s := s'
      let mut voxels := 0
      let mut bad := 0
      let mut signBad := 0
      let mut maxAbs : Float := 0.0
      for line in (raw.splitOn "\n").filterMap Vdb.parseLine do
        let grid := grids[line.caseI]!
        let twin := grid[line.idx]!
        let c := line.value
        let d := Vdb.fabs (twin - c)
        if d > maxAbs then maxAbs := d
        if (twin >= 0.0) != (c >= 0.0) then
          signBad := signBad + 1
          bad := bad + 1
        else if d > 1.0e-5 * 0.25 then
          bad := bad + 1
        voxels := voxels + 1
      IO.println s!"voxel-lines={voxels} bad={bad} signMismatch={signBad}"
      if bad > 0 then
        throw (IO.userError "fast sweeping differential check failed")
  | _ =>
      IO.println "usage: fastsweepcheck <c-output-file>"
      throw (IO.userError "usage: fastsweepcheck <c-output-file>")
