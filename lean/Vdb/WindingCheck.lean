/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Winding-number executable check (model half, no proof): reads the dump
  produced by `lean/scripts/winding_c.c` — `pt <mesh> <kind> <x|y|z|we|wf bits>`
  lines, where kind `0`/`2` are strictly-interior sample points (expected
  winding number 1) and kind `1` strictly-exterior points (expected 0) — and
  asserts against IEEE doubles:

    * EXACT mode: |w − expected| ≤ 1e-9  (the exact solid-angle sum)
    * FAST mode:  |w − expected| ≤ 1e-6  (the dipole far-field tree; observed
      ≈ 4.4e-16 on these small meshes — the tolerance is set for the two
      fixed meshes only, not as a universal FAST guarantee)

  Printed: `pts=<n> inside=<n> outside=<n> bad=<n>`.
  `scripts/check_winding.sh` drives both halves.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/

namespace Vdb

def hexVal (c : Char) : Option UInt64 :=
  match c with
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
  | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
  | '8' => some 8 | '9' => some 9 | 'a' => some 10 | 'b' => some 11
  | 'c' => some 12 | 'd' => some 13 | 'e' => some 14 | 'f' => some 15
  | _ => none

/-- Parse exactly 16 lowercase hex digits into a `UInt64` bit pattern. -/
def parseHex16 (s : String) : Option UInt64 :=
  match s.toList with
  | [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, cA, cB, cC, cD, cE, cF] =>
      [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, cA, cB, cC, cD, cE, cF].foldlM
        (fun acc c => (hexVal c).map (acc * 16 + ·)) 0
  | _ => none

structure Pt where
  mesh : Nat
  kind : Nat          -- 0 = interior, 1 = exterior, 2 = origin (interior)
  we : Float          -- EXACT mode
  wf : Float          -- FAST mode

def parseLine (s : String) : Option Pt := do
  match s.splitOn " " with
  | ["pt", mesh, kind, _x, _y, _z, we, wf] =>
      let mesh ← mesh.toNat?
      let kind ← kind.toNat?
      let weBits ← parseHex16 we
      let wfBits ← parseHex16 wf
      pure { mesh, kind, we := Float.ofBits weBits, wf := Float.ofBits wfBits }
  | _ => none

end Vdb

def main (argv : List String) : IO Unit := do
  match argv with
  | [path] =>
      let raw ← IO.FS.readFile path
      let mut pts := 0
      let mut inside := 0
      let mut outside := 0
      let mut bad := 0
      for line in (raw.splitOn "\n").filterMap Vdb.parseLine do
        let expected : Float := if line.kind == 1 then 0.0 else 1.0
        if line.kind == 1 then outside := outside + 1 else inside := inside + 1
        let errex := (line.we - expected).abs
        let errfa := (line.wf - expected).abs
        if errex > 1e-9 || errfa > 1e-6 then
          bad := bad + 1
          if bad <= 5 then
            IO.println s!"MISMATCH mesh {line.mesh} kind {line.kind}: we={line.we} wf={line.wf}"
        pts := pts + 1
      IO.println s!"pts={pts} inside={inside} outside={outside} bad={bad}"
      if bad > 0 then
        throw (IO.userError "winding check failed")
  | _ =>
      IO.println "usage: windingcheck <c-output-file>"
      throw (IO.userError "windingcheck: bad args")
