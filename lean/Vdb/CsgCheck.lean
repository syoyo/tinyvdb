/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Dense CSG differential harness (model half): the Float32 twin of the C
  `tvdb_csg_union`/`tvdb_csg_intersection`/`tvdb_csg_difference`
  (`src/tinyvdb_ops.c`), compared against `lean/scripts/csg_c.c`, which prints
  float **bit patterns** (`%08x`) of both inputs and the C outputs, so the
  comparison is bit-exact with no tolerance. Shared generator: the same LCG,
  tie/zero/NaN injection rules (see `csg_c.c`).

  Printed one line per (case, stream): `case i ins a|b|op 0|1|2 <512 hex>`.
  `scripts/check_csg.sh` drives both and reports.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/

namespace Vdb

/-- The three dense CSG ops, branch by branch, in `Float32`. -/
def csgUnion (a b : Float32) : Float32 := if a < b then a else b
def csgIntersection (a b : Float32) : Float32 := if a > b then a else b
/-- Negation as a sign-bit flip: exact, including NaN payloads. -/
def csgNeg (b : Float32) : Float32 :=
  Float32.ofBits (Float32.toBits b ^^^ (2147483648 : UInt32))
def csgDifference (a b : Float32) : Float32 := if a > csgNeg b then a else csgNeg b

def hexVal (c : Char) : Option UInt32 :=
  match c with
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
  | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
  | '8' => some 8 | '9' => some 9 | 'a' => some 10 | 'b' => some 11
  | 'c' => some 12 | 'd' => some 13 | 'e' => some 14 | 'f' => some 15
  | _ => none

/-- Parse exactly 8 lowercase hex digits into a `UInt32` bit pattern. -/
def parseHex8 (s : String) : Option UInt32 := do
  let cs := s.toList
  if cs.length != 8 then none
  else cs.foldlM (fun acc c => (hexVal c).map fun v => acc * 16 + v) 0

def float32OfHex (s : String) : Option Float32 :=
  (parseHex8 s).map Float32.ofBits

/-- Parse `case i ins a|b <512x hex>` and `case i op 0|1|2 <512x hex>` lines. -/
structure GridLine where
  caseI : Nat
  kind : String   -- "a", "b", or "0"/"1"/"2"
  values : Array Float32

def parseLine (s : String) : Option GridLine := do
  match s.splitOn " " with
  | "case" :: ci :: "ins" :: sub :: rest =>
      let caseI ← ci.toNat?
      let vals ← rest.toArray.mapM float32OfHex
      pure { caseI := caseI, kind := sub, values := vals }
  | "case" :: ci :: "op" :: sub :: rest =>
      let caseI ← ci.toNat?
      let vals ← rest.toArray.mapM float32OfHex
      pure { caseI := caseI, kind := sub, values := vals }
  | _ => none

end Vdb

def main (argv : List String) : IO Unit := do
  match argv with
  | [path] =>
      let raw ← IO.FS.readFile path
      let mut gridsA : Array (Array Float32) := Array.replicate 400 #[]
      let mut gridsB : Array (Array Float32) := Array.replicate 400 #[]
      let mut bad := 0
      let mut compared := 0
      let mut caseCount := 0
      for line in (raw.splitOn "\n").filterMap Vdb.parseLine do
        match line.kind with
        | "a" =>
            caseCount := caseCount + 1
            gridsA := gridsA.set! line.caseI line.values
        | "b" => gridsB := gridsB.set! line.caseI line.values
        | op =>
            let opI ← match op.toNat? with
              | some n => pure n
              | none => throw (IO.userError s!"bad op token: {op}")
            let a := gridsA[line.caseI]!
            let b := gridsB[line.caseI]!
            for k in [:512] do
              let expected := line.values[k]!
              let twin :=
                if opI == 0 then Vdb.csgUnion a[k]! b[k]!
                else if opI == 1 then Vdb.csgIntersection a[k]! b[k]!
                else Vdb.csgDifference a[k]! b[k]!
              if Float32.toBits twin != Float32.toBits expected then
                bad := bad + 1
                if bad <= 5 then
                  IO.println s!"MISMATCH case {line.caseI} op {op} voxel {k}: c={Float32.toBits expected} lean={Float32.toBits twin}"
              compared := compared + 1
      IO.println s!"cases={caseCount} ops=3 voxels={compared} bad={bad}"
      if bad > 0 then
        throw (IO.userError "csg differential check failed")
  | _ =>
      IO.println "usage: csgcheck <c-output-file>"
      throw (IO.userError "usage: csgcheck <c-output-file>")
