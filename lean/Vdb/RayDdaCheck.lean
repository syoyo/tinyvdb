/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Model half of the `check_ray_dda.sh` gate: recomputes the voxel sequence of
  `tvdb_voxels_along_ray_dense` with the exact-rational DDA in `Vdb/RayDda.lean`.
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.RayDda

def main (argv : List String) : IO Unit := do
  let path ← match argv with
    | [p] => pure p
    | _ => throw (IO.userError "usage: rayddacheck <c-dump>")
  let raw ← IO.FS.readFile path
  let mut out : Array String := #[]
  for line in raw.splitOn "\n" do
    match line.splitOn " " with
    | "ray" :: rest =>
        match rest.mapM String.toInt? with
        | some [ox, oy, oz, dx, dy, dz, tmin, tmax] =>
            let o : Vdb.R3 := ((ox : Rat)/1000, (oy : Rat)/1000, (oz : Rat)/1000)
            let d : Vdb.R3 := ((dx : Rat)/1000, (dy : Rat)/1000, (dz : Rat)/1000)
            let vs := Vdb.ddaWalk (6, 6, 6) o d ((tmin : Rat)/1000) ((tmax : Rat)/1000)
            out := out.push s!"out {vs.length}"
            for v in vs do out := out.push s!"voxel {v.1} {v.2.1} {v.2.2}"
        | _ => pure ()
    | _ => pure ()
  IO.print ((out.toList.map fun s => s ++ "\n").foldl (fun a b => a ++ b) "")
