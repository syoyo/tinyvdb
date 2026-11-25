/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Model half of the `check_sdf_parts.sh` differential gate. The C driver
  (`lean/scripts/sdf_parts_c.c`) calls the real `tvdb_sdf_segmentation` and
  `tvdb_sdf_extract_enclosed_regions` on seeded 6³ fields and dumps the field,
  the per-part index sets and the cavity mask. This executable recomputes them
  from the field line with computable BFS closures mirroring `Vdb.Segmentation`'s
  `Conn` (the proven, noncomputable specification) and prints the same format.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Segmentation

namespace Vdb

abbrev G6 := GPoint 6 6 6

def mkP (i j k : Nat) : G6 :=
  (⟨i % 6, Nat.mod_lt i (by decide)⟩,
    (⟨j % 6, Nat.mod_lt j (by decide)⟩, ⟨k % 6, Nat.mod_lt k (by decide)⟩))

def scanIdx (p : G6) : Nat := (p.2.2.val * 6 + p.2.1.val) * 6 + p.1.val

def pointOfIdx (i : Nat) : G6 := mkP (i % 6) ((i / 6) % 6) (i / 36)

/-- Computable 6-adjacency (the Bool twin of `Vdb.adj6`). -/
def adj6Bool (p q : G6) : Bool :=
  (p.1.val + 1 == q.1.val && p.2.1.val == q.2.1.val && p.2.2.val == q.2.2.val) ||
  (q.1.val + 1 == p.1.val && p.2.1.val == q.2.1.val && p.2.2.val == q.2.2.val) ||
  (p.1.val == q.1.val && p.2.1.val + 1 == q.2.1.val && p.2.2.val == q.2.2.val) ||
  (p.1.val == q.1.val && q.2.1.val + 1 == p.2.1.val && p.2.2.val == q.2.2.val) ||
  (p.1.val == q.1.val && p.2.1.val == q.2.1.val && p.2.2.val + 1 == q.2.2.val) ||
  (p.1.val == q.1.val && p.2.1.val == q.2.1.val && q.2.2.val + 1 == p.2.2.val)

/-- Computable 26-adjacency (the Bool twin of `Vdb.adj26`). -/
def adj26Bool (p q : G6) : Bool :=
  scanIdx p != scanIdx q &&
  Int.natAbs ((p.1.val : Int) - q.1.val) <= 1 &&
  Int.natAbs ((p.2.1.val : Int) - q.2.1.val) <= 1 &&
  Int.natAbs ((p.2.2.val : Int) - q.2.2.val) <= 1

def adjOf (conn : Nat) (p q : G6) : Bool :=
  if conn == 6 then adj6Bool p q else adj26Bool p q

def onBoundaryBool (p : G6) : Bool :=
  p.1.val == 0 || p.1.val + 1 == 6 ||
  p.2.1.val == 0 || p.2.1.val + 1 == 6 ||
  p.2.2.val == 0 || p.2.2.val + 1 == 6

/-- One BFS growth step inside `interior`. -/
def growParts (adj : G6 → G6 → Bool) (interior : Finset G6) (s : Finset G6) : Finset G6 :=
  s ∪ s.biUnion (fun p => Finset.univ.filter fun q => adj p q && decide (q ∈ interior))

/-- Transitive closure by fixed-point iteration (216 voxels, so 216 steps
    suffice); this is the executable twin of `Conn` on the whole grid. -/
def reachParts (adj : G6 → G6 → Bool) (interior : Finset G6) (seed : Finset G6) : Finset G6 :=
  Nat.iterate (growParts adj interior) 216 seed

def compsOf (conn : Nat) (interior : Finset G6) : List (Finset G6) :=
  (List.range 216).foldl (fun acc i =>
    let p := pointOfIdx i
    if decide (p ∈ interior) && !acc.any (fun c => decide (p ∈ c)) then
      acc ++ [reachParts (adjOf conn) interior {p}]
    else acc) []

def compKey (c : Finset G6) : Nat :=
  (List.range 216).find? (fun i => decide (pointOfIdx i ∈ c)) |>.getD 999

def sortedComps (conn : Nat) (interior : Finset G6) : List (Finset G6) :=
  (compsOf conn interior).mergeSort (fun a b => compKey a ≤ compKey b)

def sortedIdxs (c : Finset G6) : List Nat :=
  (List.range 216).filter (fun i => decide (pointOfIdx i ∈ c))

def exteriorOf (interior : Finset G6) : Finset G6 :=
  Finset.univ.filter fun p => decide (p ∉ interior)

def boundarySeeds (interior : Finset G6) : Finset G6 :=
  Finset.univ.filter fun p => decide (p ∉ interior) && onBoundaryBool p

def cavityOf (conn : Nat) (interior : Finset G6) : Finset G6 :=
  let ext := exteriorOf interior
  ext \ reachParts (adjOf conn) ext (boundarySeeds interior)

def render (tag : String) (idxs : List Nat) : String :=
  idxs.foldl (fun s i => s ++ " " ++ toString i) tag

/-- A parsed case header. -/
def parseHeader (s : String) : Option (Nat × Nat × Nat) :=
  match s.splitOn " " with
  | ["case", ci, "conn", conn, "parts", parts] =>
      match ci.toNat?, conn.toNat?, parts.toNat? with
      | some a, some b, some c => some (a, b, c)
      | _, _, _ => none
  | _ => none

def parseIdxs (s : String) : Option (List Nat) :=
  match s.splitOn " " with
  | [] => none
  | _ :: rest => rest.mapM String.toNat?

end Vdb

def main (argv : List String) : IO Unit := do
  let path ← match argv with
    | [p] => pure p
    | _ => throw (IO.userError "usage: sdfpartcheck <c-dump>")
  let raw ← IO.FS.readFile path
  let mut header : Option (Nat × Nat × Nat) := none
  let mut interior : Finset Vdb.G6 := ∅
  let mut out : Array String := #[]
  for line in raw.splitOn "\n" do
    if line == "" then continue
    match Vdb.parseHeader line with
    | some h => header := some h; interior := ∅
    | none =>
      match line.splitOn " " with
      | "field" :: _ =>
          let idxs := Vdb.parseIdxs line |>.getD []
          interior := idxs.foldl (fun s i => insert (Vdb.pointOfIdx i) s) (∅ : Finset Vdb.G6)
          match header with
          | none => throw (IO.userError "field line before case header")
          | some (ci, conn, parts) =>
            out := out.push s!"case {ci} conn {conn} parts {parts}"
            out := out.push (Vdb.render "field" (Vdb.sortedIdxs interior))
            for c in Vdb.sortedComps conn interior do
              out := out.push (Vdb.render "part" (Vdb.sortedIdxs c))
            out := out.push (Vdb.render "cavity" (Vdb.sortedIdxs (Vdb.cavityOf conn interior)))
      | _ => continue  -- C's own part/cavity lines are not needed by the twin
  IO.print ((out.toList.map fun s => s ++ "\n").foldl (fun a b => a ++ b) "")
