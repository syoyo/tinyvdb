/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Model half of the `check_convex_parts.sh` gate. Recomputes the shared-vertex
  union-find components and their axis-aligned boxes from the C dump, using
  exact integer arithmetic on doubled coordinates. Output is compared with the
  real `tvdb_mesh_convex_decompose_ex` dump.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

namespace Vdb

abbrev P3i := Int × Int × Int
abbrev TriN := Nat × Nat × Nat

def findRootF : Nat → List Nat → Nat → Nat
  | 0, _, x => x
  | n + 1, p, x => if p[x]! == x then x else findRootF n p p[x]!

def findRoot (p : List Nat) (x : Nat) : Nat := findRootF p.length p x

def unionRoot (p : List Nat) (a b : Nat) : List Nat :=
  let ra := findRoot p a
  let rb := findRoot p b
  if ra == rb then p
  else if ra < rb then p.set rb ra else p.set ra rb

def unionAll (nv : Nat) (fs : List TriN) : List Nat :=
  fs.foldl (fun p t => unionRoot (unionRoot p t.1 t.2.1) t.1 t.2.2)
    (List.range nv)

def rootsOf (nv : Nat) (p : List Nat) : List Nat :=
  (List.range nv).map (findRoot p) |>.eraseDups

def componentMin (p : List Nat) (root : Nat) : Nat :=
  (List.range p.length).filter (fun v => findRoot p v == root) |>.headD 0

def sortedRoots (nv : Nat) (p : List Nat) : List Nat :=
  (rootsOf nv p).mergeSort (fun a b => componentMin p a ≤ componentMin p b)

def labelOf (p : List Nat) (roots : List Nat) (v : Nat) : Nat :=
  (List.range roots.length).find? (fun k => roots[k]! == findRoot p v) |>.getD 0

def axisMin (xs : List Int) : Int := xs.foldl min (xs.headD 0)
def axisMax (xs : List Int) : Int := xs.foldl max (xs.headD 0)

def boxOf (p : List Nat) (pos : List P3i) (root : Nat) : String :=
  let vs := (List.range p.length).filter (fun v => findRoot p v == root)
  let xs := vs.map fun v => pos[v]!.1
  let ys := vs.map fun v => pos[v]!.2.1
  let zs := vs.map fun v => pos[v]!.2.2
  s!"part {axisMin xs} {axisMin ys} {axisMin zs} {axisMax xs} {axisMax ys} {axisMax zs} {componentMin p root}"

end Vdb

def main (argv : List String) : IO Unit := do
  let path ← match argv with
    | [p] => pure p
    | _ => throw (IO.userError "usage: convexcheck <c-dump>")
  let raw ← IO.FS.readFile path
  let mut nv := 0
  let mut pos : List Vdb.P3i := []
  let mut fs : List Vdb.TriN := []
  let mut out : Array String := #[]
  for line in raw.splitOn "\n" do
    match line.splitOn " " with
    | "case" :: _ => nv := 0; pos := []; fs := []
    | "v" :: _ :: rest =>
        match rest.mapM String.toInt? with
        | some [x, y, z] => pos := pos ++ [(x, y, z)]; nv := nv + 1
        | _ => pure ()
    | "f" :: rest =>
        match rest.mapM String.toNat? with
        | some [a, b, c] => fs := fs ++ [(a, b, c)]
        | _ => pure ()
    | "parts" :: _ =>
        let p := Vdb.unionAll nv fs
        let roots := Vdb.sortedRoots nv p
        for r in roots do out := out.push (Vdb.boxOf p pos r)
        for v in [:nv] do out := out.push s!"label {v} {Vdb.labelOf p roots v}"
        nv := 0; pos := []; fs := []
    | _ => pure ()
  IO.print ((out.toList.map fun s => s ++ "\n").foldl (fun a b => a ++ b) "")
