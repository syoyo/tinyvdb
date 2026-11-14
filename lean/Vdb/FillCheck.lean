/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Flood-fill differential harness (model half): the Float twin of the C
  `tvdb_signed_flood_fill` (dense, `src/tinyvdb_ops.c`), compared against
  `lean/scripts/fill_c.c`. Both sides generate the same 8×8×8 grids from
  the same LCG and run the same algorithm: boundary far voxels are the
  seeds, the exterior is the seed-connected far set, and far voxels are
  written `+band` (exterior) or `-band` (interior); band voxels are
  unchanged.

  Printed one case per line: `case i sign*` with `+` / `-` / `.` per voxel.
  `scripts/check_fill.sh` compares byte-wise.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/

namespace Vdb

/-- The 6 von Neumann neighbours of a lattice point (in-bounds only). -/
def neighbors (p : Nat × Nat × Nat) : List (Nat × Nat × Nat) :=
  let (i, j, k) := p
  ((if i > 0 then [(i - 1, j, k)] else [])
   ++ (if i + 1 < 8 then [(i + 1, j, k)] else [])
   ++ (if j > 0 then [(i, j - 1, k)] else [])
   ++ (if j + 1 < 8 then [(i, j + 1, k)] else [])
   ++ (if k > 0 then [(i, j, k - 1)] else [])
   ++ (if k + 1 < 8 then [(i, j, k + 1)] else []))

/-- Voxel index of (i, j, k) in the C layout (x fastest). -/
def voxelIdx (i j k : Nat) : Nat := (k * 8 + j) * 8 + i

/-- Unindex a flat voxel number into (i, j, k). -/
def voxelCoord (v : Nat) : Nat × Nat × Nat :=
  (v % 8, (v / 8) % 8, v / 64)

def isFar (d : Array Float) (idx : Nat) (band : Float) : Bool :=
  let v := d[idx]!
  let a := if v < 0.0 then -v else v
  a >= band

/-- The C `tvdb_signed_flood_fill`, Float twin. -/
def signedFloodFill (d : Array Float) (band : Float) : Array Float := Id.run do
  let n := d.size
  -- Seed: far voxels on the grid boundary.
  let mut vis : Array Bool := Array.replicate n false
  let mut stack : Array Nat := #[]
  for idx in [:n] do
    let (i, j, k) := voxelCoord idx
    let boundary := i == 0 || i == 7 || j == 0 || j == 7 || k == 0 || k == 7
    if boundary && isFar d idx band && !vis[idx]! then
      vis := vis.set! idx true
      stack := stack.push idx
  -- Flood the exterior through far voxels only.
  while !stack.isEmpty do
    let v := stack[stack.size - 1]!
    stack := stack.pop
    for (ni, nj, nk) in neighbors (voxelCoord v) do
      let nidx := voxelIdx ni nj nk
      if isFar d nidx band && !vis[nidx]! then
        vis := vis.set! nidx true
        stack := stack.push nidx
  -- Assign signs: reached far = exterior (+band), unreached = interior (-band).
  return (Array.range n).map fun idx =>
    if isFar d idx band then (if vis[idx]! then band else -band) else d[idx]!

/-- The sign character for a post-fill voxel. -/
def signChar (v : Float) (band : Float) : Char :=
  let a := if v < 0.0 then -v else v
  if a < band then '.' else (if v > 0.0 then '+' else '-')

partial def go (state : UInt64) (caseI : Nat) : IO Unit := do
  if caseI >= 400 then return ()
  let mut s := state
  let mut data : Array Float := Array.replicate 512 0.0
  for k in [0, 1, 2, 3, 4, 5, 6, 7] do
    for j in [0, 1, 2, 3, 4, 5, 6, 7] do
      for i in [0, 1, 2, 3, 4, 5, 6, 7] do
        s := s * 6364136223846793005 + 1442695040888963407
        let u := (s >>> 33) % 100000
        let idx := voxelIdx i j k
        data := data.set! idx (u.toFloat / 100000.0 - 0.5)
  let filled := signedFloodFill data 0.25
  let signs := String.ofList ((List.range 512).map fun idx => signChar filled[idx]! 0.25)
  IO.println s!"case {caseI} {signs}"
  go s (caseI + 1)

end Vdb

def main : IO Unit := do
  Vdb.go 0x9e3779b97f4a7c15 0
