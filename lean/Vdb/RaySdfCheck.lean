/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Model half of the `check_ray_sdf.sh` gate. Recomputes the zero-crossing pairs
  of `tvdb_segments_along_ray` over a step field using exact rationals and the
  `scanCrossings` model in `Vdb/RaySdf.lean`.

  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.RaySdf

namespace Vdb

def sampleCoordR (x : Rat) (n : Nat) : Rat :=
  if x < -1 then -1 else if x ≥ (n - 1 : Nat) then (n - 1 : Nat) else x

def sampleFloorR (x : Rat) (n : Nat) : Int :=
  if x < 0 then -1 else if x ≥ (n - 1 : Nat) then (n - 1 : Nat) else Int.floor x

def clampIdxR (x : Int) (n : Nat) : Nat :=
  if x < 0 then 0 else if x ≥ n then n - 1 else x.natAbs

def fieldVal (i : Nat) : Rat := if i ≥ 2 ∧ i ≤ 5 then -1 else 1

def sampleX (t : Rat) (n : Nat) : Rat :=
  let vx := t - 1/2
  let c := sampleCoordR vx n
  let fl := sampleFloorR c n
  let fx := c - fl
  let x0 := clampIdxR fl n
  let x1 := clampIdxR (fl + 1) n
  fieldVal x0 * (1 - fx) + fieldVal x1 * fx

def raySamples (originX tmin dt : Rat) (steps : Nat) : List Rat :=
  (List.range steps).map fun i => Vdb.sampleX (originX + tmin + dt * i) 8

end Vdb

def main (argv : List String) : IO Unit := do
  let path ← match argv with
    | [p] => pure p
    | _ => throw (IO.userError "usage: raysdfcheck <c-dump>")
  let raw ← IO.FS.readFile path
  let mut out : Array String := #[]
  for line in raw.splitOn "\n" do
    match line.splitOn " " with
    | "ray" :: rest =>
        let steps_nat := (rest.getD 2 "0").toNat?.getD 0
        match rest.take 2 |>.mapM String.toInt? with
        | some [tmin, tmax] =>
            let t0 : Rat := (tmin : Rat) / 1000
            let t1 : Rat := (tmax : Rat) / 1000
            let dt := (t1 - t0) / (steps_nat - 1 : Nat)
            let vs := Vdb.raySamples t0 t0 dt steps_nat
            let cs := Vdb.scanCrossings vs 0 dt
            out := out.push s!"out {cs.length}"
            for c in cs do out := out.push s!"pair {c.1 + t0} {c.2 + t0}"
        | _ => pure ()
    | _ => pure ()
  IO.print ((out.toList.map fun s => s ++ "\n").foldl (fun a b => a ++ b) "")
