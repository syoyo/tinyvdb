/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Godunov differential harness (model half): the Float twin of the C
  `tvdb__godunov_solve` (and of `Vdb.Godunov.godunov` over `ℝ`), compared
  against the C driver `lean/scripts/godunov_c.c`, which prints
  `i a b c h out` with `%.17e`.

  The Lean side re-parses the C output with a small `%e`-notation parser
  (exact enough for 1e-12 comparisons), recomputes the solver on the parsed
  inputs, and reports the maximum relative error and any violation of
  `|a-b| <= max(1e-12, 1e-12*max(|a|,|b|))`.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/

import Vdb.FloatParse

namespace Vdb

/-- The C `tvdb__godunov_solve`, branch by branch, in `Float`. -/
def godunovF (a b c h : Float) : Float :=
  let x1 := a + h
  if x1 <= b then x1
  else
    let ab := a + b
    let disc := 2.0 * h * h - (a - b) * (a - b)
    if disc < 0.0 then x1
    else
      let x2 := 0.5 * (ab + Float.sqrt disc)
      if x2 <= c then x2
      else
        let abc := a + b + c
        let sumsq := a * a + b * b + c * c
        let disc3 := abc * abc - 3.0 * (sumsq - h * h)
        if disc3 < 0.0 then x2
        else (abc + Float.sqrt disc3) / 3.0

/-- Insertion sort of three floats (kept for symmetry with the C driver). -/
def sort3 (a b c : Float) : Float × Float × Float :=
  let (m1, M1) := if a <= b then (a, b) else (b, a)
  if c < m1 then (c, m1, M1)
  else if c < M1 then (m1, c, M1)
  else (m1, M1, c)

/-- Parse one output line `i a b c h out` (C side prints indices first). -/
structure Case where
  idx : Nat
  a : Float
  b : Float
  c : Float
  h : Float
  out : Float

def parseLine (s : String) : Option Case := do
  match s.splitOn " " with
  | ["i"] => none
  | [i, a, b, c, h, o] => do
      let idx ← i.toNat?
      let a ← parseFloatE a
      let b ← parseFloatE b
      let c ← parseFloatE c
      let h ← parseFloatE h
      let o ← parseFloatE o
      pure ⟨idx, a, b, c, h, o⟩
  | _ => none

/-- Compare C and Lean outputs; return (maxAbsDiff, maxRelDiff, violations). -/
def check (xs : List Case) : IO Unit := do
  let mut maxRel : Float := 0.0
  let mut maxAbs : Float := 0.0
  let mut bad := 0
  let mut lines := 0
  for c in xs do
    lines := lines + 1
    let leanOut := godunovF c.a c.b c.c c.h
    let d := fabs (leanOut - c.out)
    let m := fmax (fabs leanOut) (fabs c.out)
    if d > maxAbs then maxAbs := d
    let rel := if m > 0.0 then d / m else d
    if rel > maxRel then maxRel := rel
    if d > fmax 1.0e-12 (1.0e-12 * m) then
      bad := bad + 1
      if bad <= 5 then
        IO.println s!"MISMATCH idx {c.idx}: c={c.out} lean={leanOut} (a={c.a} b={c.b} c={c.c} h={c.h})"
  IO.println s!"cases={lines} bad={bad}"
  if bad > 0 then
    throw (IO.userError "godunov differential check failed")

end Vdb

def main (argv : List String) : IO Unit := do
  match argv with
  | [path] =>
      let data ← IO.FS.readFile path
      let cases := (data.splitOn "\n").filterMap Vdb.parseLine
      Vdb.check cases
  | _ =>
      IO.println "usage: godunovcheck <c-output-file>"
      throw (IO.userError "usage: godunovcheck <c-output-file>")
