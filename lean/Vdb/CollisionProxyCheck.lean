/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Model half of the `check_proxy.sh` differential gate. The C driver
  (`lean/scripts/simplify_c.c`) calls the real `tvdb_mesh_simplify_ex` on small
  closed integer meshes and dumps the input geometry plus the resulting face
  list. This executable recomputes the simplification independently over exact
  rationals (the C driver scales plane quadrics by 1/|n|² instead of using a
  square root, so all ranking costs are rational) and prints the output topology
  in the same format. Topological agreement is exact; positions are not compared
  here (the C output stores floats).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

namespace Vdb

abbrev P3 := Rat × Rat × Rat

def padd (a b : P3) : P3 := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)
def psub (a b : P3) : P3 := (a.1 - b.1, a.2.1 - b.2.1, a.2.2 - b.2.2)
def pscale (k : Rat) (a : P3) : P3 := (k * a.1, k * a.2.1, k * a.2.2)
def dot3 (a b : P3) : Rat := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2
def cross3 (a b : P3) : P3 :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1,
   a.2.2 * b.1 - a.1 * b.2.2,
   a.1 * b.2.1 - a.2.1 * b.1)

abbrev Tri := Nat × Nat × Nat

structure Q10 where
  a0 : Rat
  a1 : Rat
  a2 : Rat
  a3 : Rat
  a4 : Rat
  a5 : Rat
  b0 : Rat
  b1 : Rat
  b2 : Rat
  c : Rat
  deriving Inhabited, DecidableEq

def qzero : Q10 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def qadd (q r : Q10) : Q10 :=
  ⟨q.a0 + r.a0, q.a1 + r.a1, q.a2 + r.a2, q.a3 + r.a3, q.a4 + r.a4,
   q.a5 + r.a5, q.b0 + r.b0, q.b1 + r.b1, q.b2 + r.b2, q.c + r.c⟩

def qeval (q : Q10) (v : P3) : Rat :=
  q.a0 * v.1 * v.1 + 2 * q.a1 * v.1 * v.2.1 + 2 * q.a2 * v.1 * v.2.2 +
  q.a3 * v.2.1 * v.2.1 + 2 * q.a4 * v.2.1 * v.2.2 + q.a5 * v.2.2 * v.2.2 +
  2 * (q.b0 * v.1 + q.b1 * v.2.1 + q.b2 * v.2.2) + q.c

/-- The plane quadric scaled by `1 / ⟪n,n⟫`, as in the C implementation. -/
def planeQ (p0 p1 p2 : P3) : Option Q10 :=
  let n := cross3 (psub p1 p0) (psub p2 p0)
  let len2 := dot3 n n
  if len2 == 0 then none else
    let d := dot3 n p0
    let nv := 1 / len2
    some ⟨nv * n.1 * n.1, nv * n.1 * n.2.1, nv * n.1 * n.2.2,
          nv * n.2.1 * n.2.1, nv * n.2.1 * n.2.2, nv * n.2.2 * n.2.2,
          -nv * d * n.1, -nv * d * n.2.1, -nv * d * n.2.2, nv * d * d⟩

def vertexOfTri (t : Tri) : List Nat := [t.1, t.2.1, t.2.2]

def triHas (t : Tri) (v : Nat) : Bool :=
  t.1 == v || t.2.1 == v || t.2.2 == v

def retargetTri (a b : Nat) (t : Tri) : Tri :=
  (if t.1 == b then a else t.1,
   if t.2.1 == b then a else t.2.1,
   if t.2.2 == b then a else t.2.2)

def nondeg (t : Tri) : Bool := t.1 != t.2.1 && t.2.1 != t.2.2 && t.1 != t.2.2

def edgeKey (a b : Nat) : Nat :=
  if a < b then a * 1000000 + b else b * 1000000 + a

def undirectedEdges (fs : List Tri) : List Nat :=
  fs.flatMap (fun t => [edgeKey t.1 t.2.1, edgeKey t.2.1 t.2.2, edgeKey t.2.2 t.1])

def boundaryVertices (fs : List Tri) : List Nat :=
  let es := undirectedEdges fs
  let singles := es.filter (fun e => es.countP (fun x => x == e) == 1)
  singles.flatMap (fun e => [e / 1000000, e % 1000000])

/-- The link condition: exactly two distinct opposite vertices. -/
def linkOk (fs : List Tri) (a b : Nat) : Bool :=
  let opps := (fs.filter (fun t => triHas t a && triHas t b)).map fun t =>
    (vertexOfTri t).find? (fun v => v != a && v != b) |>.getD 0
  (opps.eraseDups.length == 2)

structure Cand where
  cost : Rat
  i : Nat
  j : Nat

def buildCands (pos : List P3) (quad : List Q10)
    (fs : List Tri) (boundary : List Nat) : List Cand :=
  let edges := (undirectedEdges fs).eraseDups
  edges.filterMap fun e =>
    let a := e / 1000000
    let b := e % 1000000
    if boundary.contains a || boundary.contains b then none
    else if !linkOk fs a b then none
    else
      let mid := pscale (1 / 2 : Rat) (padd pos[a]! pos[b]!)
      let q := qadd quad[a]! quad[b]!
      some ⟨qeval q mid, a, b⟩

def candKey (c : Cand) : Rat × Nat × Nat := (c.cost, c.i, c.j)

def sortedCands (cs : List Cand) : List Cand :=
  cs.mergeSort (fun a b => candKey a ≤ candKey b)

structure State where
  pos : List P3
  alive : List Bool
  faces : List Tri

def applyCand (target : Nat) (s : State) (c : Cand) : State :=
  if s.faces.length ≤ target then s
  else if !s.alive[c.i]! || !s.alive[c.j]! then s
  else if !linkOk s.faces c.i c.j then s
  else
    let p := pscale (1 / 2 : Rat) (padd s.pos[c.i]! s.pos[c.j]!)
    { pos := s.pos.set c.i p,
      alive := s.alive.set c.j false,
      faces := ((s.faces.map (retargetTri c.i c.j)).filter nondeg).eraseDups }

def simplify (nv : Nat) (pos : List P3) (fs : List Tri) (target : Nat) : State :=
  let quad := (List.range nv).map fun _ => qzero
  let quad' := fs.foldl (fun acc t =>
    match planeQ pos[t.1]! pos[t.2.1]! pos[t.2.2]! with
    | none => acc
    | some q =>
        let a1 := acc.set t.1 (qadd acc[t.1]! q)
        let a2 := a1.set t.2.1 (qadd a1[t.2.1]! q)
        a2.set t.2.2 (qadd a2[t.2.2]! q)) quad
  let cands := sortedCands (buildCands pos quad' fs (boundaryVertices fs))
  cands.foldl (applyCand target) { pos := pos, alive := List.replicate nv true, faces := fs }

def compact (s : State) : List Tri × Nat :=
  let table := (List.range s.alive.length).filterMap fun i =>
    if s.alive[i]! then some i else none
  let idx (v : Nat) : Nat :=
    (List.range table.length).find? (fun k => table[k]! == v) |>.getD 0
  (s.faces.map (fun t => (idx t.1, idx t.2.1, idx t.2.2)), table.length)

end Vdb

def parseInts (s : String) : Option (List Int) :=
  match s.splitOn " " with
  | [] => none
  | _ :: rest => rest.mapM String.toInt?

def parseNats (s : String) : Option (List Nat) :=
  match s.splitOn " " with
  | [] => none
  | _ :: rest => rest.mapM String.toNat?

def renderTri (t : Vdb.Tri) : String := s!"of {t.1} {t.2.1} {t.2.2}"

def main (argv : List String) : IO Unit := do
  let path ← match argv with
    | [p] => pure p
    | _ => throw (IO.userError "usage: proxycheck <c-dump>")
  let raw ← IO.FS.readFile path
  let mut nv := 0
  let mut pos : List Vdb.P3 := []
  let mut fs : List Vdb.Tri := []
  let mut target := 0
  let mut out : Array String := #[]
  for line in raw.splitOn "\n" do
    match line.splitOn " " with
    | "case" :: _ :: "target" :: t :: _ =>
        target := t.toNat?.getD 0; pos := []; fs := []
    | "v" :: _ :: rest =>
        match rest.mapM String.toInt? with
        | some [x, y, z] =>
            nv := nv + 1
            pos := pos ++ [((x : Rat) / 2, (y : Rat) / 2, (z : Rat) / 2)]
        | _ => pure ()
    | "f" :: rest =>
        match rest.mapM String.toNat? with
        | some [a, b, c] => fs := fs ++ [(a, b, c)]
        | _ => pure ()
    | "outv" :: _ =>
        let s := Vdb.simplify nv pos fs target
        let (outs, noutv) := Vdb.compact s
        out := out.push s!"outv {noutv}"
        out := out.push s!"outf {outs.length}"
        for t in outs do out := out.push (renderTri t)
        nv := 0; pos := []; fs := []
    | _ => pure ()
  IO.print ((out.toList.map fun s => s ++ "\n").foldl (fun a b => a ++ b) "")
