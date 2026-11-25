/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Model half of the `check_collision_pipeline.sh` gate: recomputes the
  broadphase AABB rejection and the narrowphase contacts of
  `tvdb_collision_sphere_mesh_ex` over exact rationals. Contact face indices and
  counts are compared exactly.

  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

namespace Vdb

abbrev P3 := Rat × Rat × Rat

def qsub (a b : P3) : P3 := (a.1-b.1, a.2.1-b.2.1, a.2.2-b.2.2)
def qdot (a b : P3) : Rat := a.1*b.1 + a.2.1*b.2.1 + a.2.2*b.2.2
def qaddmul (a b : P3) (s : Rat) : P3 :=
  (a.1 + b.1*s, a.2.1 + b.2.1*s, a.2.2 + b.2.2*s)

def closestTri (p a b c : P3) : P3 :=
  let ab := qsub b a
  let ac := qsub c a
  let ap := qsub p a
  let d1 := qdot ab ap
  let d2 := qdot ac ap
  if d1 ≤ 0 ∧ d2 ≤ 0 then a else
  let bp := qsub p b
  let d3 := qdot ab bp
  let d4 := qdot ac bp
  if d3 ≥ 0 ∧ d4 ≤ d3 then b else
  let vc := d1*d4 - d3*d2
  if vc ≤ 0 ∧ d1 ≥ 0 ∧ d3 ≤ 0 then qaddmul a ab (d1/(d1-d3)) else
  let cp := qsub p c
  let d5 := qdot ab cp
  let d6 := qdot ac cp
  if d6 ≥ 0 ∧ d5 ≤ d6 then c else
  let vb := d5*d2 - d1*d6
  if vb ≤ 0 ∧ d2 ≥ 0 ∧ d6 ≤ 0 then qaddmul a ac (d2/(d2-d6)) else
  let va := d3*d6 - d5*d4
  if va ≤ 0 ∧ d4-d3 ≥ 0 ∧ d5-d6 ≥ 0 then
    qaddmul b (qsub c b) ((d4-d3)/((d4-d3)+(d5-d6))) else
  let den := 1/(va+vb+vc)
  qaddmul (qaddmul a ab (vb*den)) ac (vc*den)

structure RawContact where
  face : Nat
  dsq : Rat
  point : P3
  deriving Inhabited

def makeContact (pos : List P3) (center : P3) (radius2 : Rat)
    (face : Nat) (t : Nat × Nat × Nat) : Option RawContact :=
  let q := closestTri center pos[t.1]! pos[t.2.1]! pos[t.2.2]!
  let d := qsub center q
  let dsq := qdot d d
  if dsq < radius2 then some ⟨face, dsq, q⟩ else none

def rawContacts (pos : List P3) (fs : List (Nat × Nat × Nat))
    (center : P3) (radius2 : Rat) : List RawContact :=
  (fs.zipIdx).filterMap fun (t, fi) => makeContact pos center radius2 fi t

def reduceContacts (merge2 : Rat) (cs : List RawContact) : List RawContact :=
  cs.foldl (fun keep c =>
    if keep.any (fun k => qdot (qsub c.point k.point) (qsub c.point k.point) ≤ merge2)
    then keep else keep ++ [c]) []

def axis (p : P3) : Nat → Rat
  | 0 => p.1
  | 1 => p.2.1
  | _ => p.2.2

def separatedQuery (pos : List P3) (c : P3) (r : Rat) : Bool :=
  (List.range 3).any fun d =>
    let lo := (pos.map (fun p => axis p d)).foldl min (axis pos[0]! d)
    let hi := (pos.map (fun p => axis p d)).foldl max (axis pos[0]! d)
    axis c d + r < lo || axis c d - r > hi

end Vdb

def main (argv : List String) : IO Unit := do
  let path ← match argv with
    | [p] => pure p
    | _ => throw (IO.userError "usage: collisioncheck <c-dump>")
  let raw ← IO.FS.readFile path
  let mut pos : List Vdb.P3 := []
  let mut fs : List (Nat × Nat × Nat) := []
  let mut center : Vdb.P3 := (0, 0, 0)
  let mut radius : Rat := 0
  let mut merge : Rat := 0
  let mut out : Array String := #[]
  for line in raw.splitOn "\n" do
    match line.splitOn " " with
    | "case" :: _ => pos := []; fs := []
    | "v" :: _ :: rest =>
        match rest.mapM String.toInt? with
        | some [x, y, z] => pos := pos ++ [((x : Rat)/1000, (y : Rat)/1000, (z : Rat)/1000)]
        | _ => pure ()
    | "f" :: rest =>
        match rest.mapM String.toNat? with
        | some [a, b, c] => fs := fs ++ [(a, b, c)]
        | _ => pure ()
    | "query" :: rest =>
        match rest.mapM String.toInt? with
        | some [x, y, z, r, m] =>
            center := ((x : Rat)/1000, (y : Rat)/1000, (z : Rat)/1000)
            radius := (r : Rat)/1000
            merge := (m : Rat)/1000
        | _ => pure ()
    | "out" :: _ =>
        let cs :=
          if Vdb.separatedQuery pos center radius then []
          else
            let raw := Vdb.rawContacts pos fs center (radius^2)
            let sorted := raw.mergeSort (fun a b => (a.dsq, a.face) ≤ (b.dsq, b.face))
            Vdb.reduceContacts (merge^2) sorted
        out := out.push s!"out {cs.length}"
        for c in cs do out := out.push s!"contact {c.face}"
        pos := []; fs := []
    | _ => pure ()
  IO.print ((out.toList.map fun s => s ++ "\n").foldl (fun a b => a ++ b) "")
