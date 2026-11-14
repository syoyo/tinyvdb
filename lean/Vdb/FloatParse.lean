/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Shared helpers for the Float differential harnesses: `%e`-notation parsing
  (exact enough for 1e-12 comparisons), plus `fmax`/`fabs`.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/

namespace Vdb

def fmax (a b : Float) : Float := if a <= b then b else a
def fabs (a : Float) : Float := if a < 0.0 then -a else a

private def digitsToNat (cs : List Char) : Option Nat :=
  cs.foldlM (fun n c =>
    if _ : '0' ≤ c ∧ c ≤ '9' then
      some (n * 10 + (c.toNat - '0'.toNat))
    else none) 0

private def splitE (cs : List Char) : Option (List Char × List Char) :=
  let rec go : List Char → List Char → Option (List Char × List Char)
    | [], _ => none
    | c :: cs', acc =>
        if c == 'e' || c == 'E' then
          some (acc.reverse, cs')
        else go cs' (c :: acc)
  go cs []

private def digitsOf (cs : List Char) : Option (List Char) :=
  if cs.all (fun c => '0' ≤ c ∧ c ≤ '9') then some cs else none

/-- Parse `%e`-notation like `-1.17336528983142174e+00` into a `Float`
    (magnitude digits-first, errors bounded by a couple of ulps). -/
def parseFloatE (s : String) : Option Float := do
  let cs := s.toList
  let (neg, cs0) := match cs with
    | '-' :: rest => (true, rest)
    | _ => (false, cs)
  let (mant, expS) ← splitE cs0
  let (intPart, fracPart) :=
    match mant.splitOn '.' with
    | [i, f] => (i, f)
    | [i] => (i, [])
    | _ => ([], [])
  let parseInt (sign : Int) (ds : List Char) : Option Int := do
    let ds' ← digitsOf ds
    let n ← digitsToNat ds'
    pure (sign * (n : Int))
  let signExp ←
    match expS with
    | '+' :: rest => parseInt 1 rest
    | '-' :: rest => parseInt (-1) rest
    | rest => parseInt 1 rest
  let digits ← digitsOf (intPart ++ fracPart)
  let m ← digitsToNat digits
  let fracLen := fracPart.length
  let mantV := m.toFloat / (10 ^ fracLen).toFloat
  let scale : Float :=
    if signExp >= 0 then (10 ^ signExp.toNat).toFloat
    else 1.0 / (10 ^ (-signExp).toNat).toFloat
  let v := mantV * scale
  pure (if neg then -v else v)

end Vdb
