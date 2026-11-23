/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Model half of the `check_convex_hull.sh` gate: exact-rational supporting-plane
  hull of a small point cloud, compared face-for-face with the C
  `tvdb_points_convex_hull_ex` implementation.

  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

namespace Vdb

abbrev Q3 := Rat × Rat × Rat

def qsub (a b : Q3) : Q3 := (a.1-b.1, a.2.1-b.2.1, a.2.2-b.2.2)
def qdot (a b : Q3) : Rat := a.1*b.1 + a.2.1*b.2.1 + a.2.2*b.2.2
def qcross (a b : Q3) : Q3 :=
  (a.2.1*b.2.2 - a.2.2*b.2.1, a.2.2*b.1 - a.1*b.2.2, a.1*b.2.1 - a.2.1*b.1)

def hullFaces (ps : List Q3) : List (Nat × Nat × Nat) :=
  (ps.zipIdx).foldl (fun out pi =>
    (ps.zipIdx).foldl (fun out pj =>
      (ps.zipIdx).foldl (fun out pk =>
        if pi.2 >= pj.2 || pj.2 >= pk.2 then out else
          let n := qcross (qsub pj.1 pi.1) (qsub pk.1 pi.1)
          if qdot n n == 0 then out else
          let supports := (ps.zipIdx).all fun pl =>
            pl.2 == pi.2 || pl.2 == pj.2 || pl.2 == pk.2 ||
              qdot n (qsub pl.1 pi.1) ≤ 0
          if supports then out ++ [(pi.2, pj.2, pk.2)] else out) out) out) []

end Vdb

def main (argv : List String) : IO Unit := do
  let path ← match argv with
    | [p] => pure p
    | _ => throw (IO.userError "usage: convexhullcheck <c-dump>")
  let raw ← IO.FS.readFile path
  let mut ps : List Vdb.Q3 := []
  let mut out : Array String := #[]
  for line in raw.splitOn "\n" do
    match line.splitOn " " with
    | "case" :: _ => ps := []
    | "p" :: _ :: rest =>
        match rest.mapM String.toInt? with
        | some [x, y, z] => ps := ps ++ [((x : Rat)/1000, (y : Rat)/1000, (z : Rat)/1000)]
        | _ => pure ()
    | "out" :: _ =>
        let fs := Vdb.hullFaces ps
        out := out.push s!"out {fs.length}"
        for f in fs do out := out.push s!"face {f.1} {f.2.1} {f.2.2}"
        ps := []
    | _ => pure ()
  IO.print ((out.toList.map fun s => s ++ "\n").foldl (fun a b => a ++ b) "")
