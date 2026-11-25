/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Model half of the `check_contact.sh` gate. Recomputes sphere/triangle contacts
  from the C dump with exact rational arithmetic: the closest point on a
  triangle uses Ericson's region tests, ranking uses squared distances (no
  square roots), and the same greedy separation rule reduces the manifold. Face
  indices are compared exactly; positions are printed for diagnostics only.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

namespace Vdb

abbrev Q3 := Rat × Rat × Rat

def qsub (a b : Q3) : Q3 := (a.1-b.1, a.2.1-b.2.1, a.2.2-b.2.2)
def qdot (a b : Q3) : Rat := a.1*b.1 + a.2.1*b.2.1 + a.2.2*b.2.2
def qaddmul (a b : Q3) (s : Rat) : Q3 :=
  (a.1 + b.1*s, a.2.1 + b.2.1*s, a.2.2 + b.2.2*s)

def closestTri (p a b c : Q3) : Q3 :=
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
  point : Q3

def makeContact (pos : List Q3) (center : Q3) (radius2 : Rat)
    (face : Nat) (t : Nat × Nat × Nat) : Option RawContact :=
  let q := closestTri center pos[t.1]! pos[t.2.1]! pos[t.2.2]!
  let d := qsub center q
  let dsq := qdot d d
  if dsq < radius2 then some ⟨face, dsq, q⟩ else none

def rawContacts (pos : List Q3) (fs : List (Nat × Nat × Nat))
    (center : Q3) (radius2 : Rat) : List RawContact :=
  (fs.zipIdx).filterMap fun (t, fi) => makeContact pos center radius2 fi t

def contactKey (c : RawContact) : Rat × Nat := (c.dsq, c.face)

def reduceContacts (merge2 : Rat) (cs : List RawContact) : List RawContact :=
  cs.foldl (fun keep c =>
    if keep.any (fun k => qdot (qsub c.point k.point) (qsub c.point k.point) ≤ merge2)
    then keep else keep ++ [c]) []

def renderContact (c : RawContact) : String :=
  s!"contact {c.face} {c.point.1} {c.point.2.1} {c.point.2.2}"

end Vdb

def main (argv : List String) : IO Unit := do
  let path ← match argv with
    | [p] => pure p
    | _ => throw (IO.userError "usage: contactcheck <c-dump>")
  let raw ← IO.FS.readFile path
  let mut pos : List Vdb.Q3 := []
  let mut fs : List (Nat × Nat × Nat) := []
  let mut center : Vdb.Q3 := (0, 0, 0)
  let mut radius2 : Rat := 0
  let mut merge2 : Rat := 0
  let mut out : Array String := #[]
  for line in raw.splitOn "\n" do
    match line.splitOn " " with
    | "case" :: _ => pos := []; fs := []
    | "v" :: _ :: rest =>
        match rest.mapM String.toInt? with
        | some [x, y, z] => pos := pos ++ [((x:Rat)/2, (y:Rat)/2, (z:Rat)/2)]
        | _ => pure ()
    | "f" :: rest =>
        match rest.mapM String.toNat? with
        | some [a, b, c] => fs := fs ++ [(a, b, c)]
        | _ => pure ()
    | "query" :: rest =>
        match rest.mapM String.toInt? with
        | some [cx, cy, cz, r, m] =>
            center := ((cx:Rat)/1000, (cy:Rat)/1000, (cz:Rat)/1000)
            radius2 := ((r:Rat)/1000)^2
            merge2 := ((m:Rat)/1000)^2
        | _ => pure ()
    | "out" :: _ =>
        let cs := (Vdb.rawContacts pos fs center radius2).mergeSort
          (fun a b => Vdb.contactKey a ≤ Vdb.contactKey b)
        let reduced := Vdb.reduceContacts merge2 cs
        out := out.push s!"out {reduced.length}"
        for c in reduced do out := out.push (Vdb.renderContact c)
        pos := []; fs := []
    | _ => pure ()
  IO.print ((out.toList.map fun s => s ++ "\n").foldl (fun a b => a ++ b) "")
