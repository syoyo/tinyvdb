/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Grid type names: `Tree_<valueType>_<L1>_..._<Ln>`, e.g. `Tree_float_5_4_3`.

  The C reader (`tvdb__read_grid_type`) splits on `_`, maps the first token
  through a prefix table, and parses the remaining tokens as decimal
  `log2dim`s. Its grammar is deliberately lenient (trailing junk such as
  `5_4_3x` yields extra zero levels instead of an error); here we give the
  *strict* grammar used by the encoder, and a separate `parseLenient`
  model that documents the reader's behaviour.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Coord
import Vdb.Value

namespace Vdb

/-! ### Small character-level helpers -/

/-- Split a character list on a separator (no empty-token merging: the C
    `strtok`-style split drops empty tokens). -/
def splitOnChar (sep : Char) : List Char → List (List Char)
  | [] => []
  | c :: cs =>
    if c = sep then
      match splitOnChar sep cs with
      | [] => []
      | head :: tail => [] :: head :: tail
    else
      match splitOnChar sep cs with
      | [] => [[c]]
      | head :: tail => (c :: head) :: tail

/-- Parse a non-empty decimal digit string. -/
def digitsToNat : List Char → Option Nat
  | [] => none
  | cs =>
    if cs.all Char.isDigit then
      some (cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0)
    else none

/-- Render a `log2dim` (`Nat` ≤ 99 prints as one or two digits). -/
def natToDigits (n : Nat) : List Char :=
  if n < 10 then [Char.ofNat (n + '0'.toNat)]
  else
    let hi := n / 10
    let lo := n % 10
    [Char.ofNat (hi + '0'.toNat), Char.ofNat (lo + '0'.toNat)]

/-- `"Tree_"` as a character list. -/
def treePrefixChars : List Char := ['T', 'r', 'e', 'e', '_']

/-! ### Grid types -/

/-- A parsed grid type: value type plus the full level list (root level 0
    first). -/
structure GridType where
  valueType : ValueType
  layout : Layout
  deriving Repr, DecidableEq

/-- Strict well-formedness of a parsed grid type: at least a root, one
    internal level and a leaf; every level fits the reader's `log2dim` bound
    and the total depth fits `TVDB_MAX_TREE_DEPTH`. -/
def GridType.WellFormed (g : GridType) : Prop :=
  g.valueType ≠ .null ∧ g.valueType ≠ .string ∧
  g.layout.WellFormed 10

/-- Parsed levels are `0 :: rest`, matching the C layout array. -/
def mkGridType (vt : ValueType) (rest : List Nat) : GridType :=
  ⟨vt, ⟨0 :: rest⟩⟩

/-- Parse the strict grammar: `Tree_<type>_<digits>...` with at least two
    level numbers, each ≤ 10. -/
def parseGridType (s : String) : Option GridType :=
  let cs := s.toList
  if treePrefixChars.isPrefixOf cs then
    match splitOnChar '_' (cs.drop treePrefixChars.length) with
    | [] => none
    | name :: nums =>
      match ValueType.ofTreeName (String.ofList name), nums.mapM digitsToNat with
      | some vt, some ls =>
        if ls.length ≥ 2 ∧ ls.all (fun L => L ≤ 10) then some (mkGridType vt ls)
        else none
      | _, _ => none
  else none

/-- The C reader's lenient behaviour: unknown tokens and trailing junk are
    treated as zero `log2dim`s rather than errors. Documented here so the
    difference is explicit; the file layer never emits such names. -/
def parseGridTypeLenient (s : String) : Option GridType :=
  let cs := s.toList
  if treePrefixChars.isPrefixOf cs then
    match splitOnChar '_' (cs.drop treePrefixChars.length) with
    | [] => none
    | name :: nums =>
      match ValueType.ofTreeName (String.ofList name) with
      | some vt => some (mkGridType vt (nums.map (fun tok => (digitsToNat tok).getD 0)))
      | none => none
  else none

/-- Render a grid type in the strict grammar. -/
def GridType.toString (g : GridType) : String :=
  let rest := g.layout.levels.drop 1
  "Tree_" ++ g.valueType.treeName ++
    String.join (rest.map (fun L => "_" ++ String.ofList (natToDigits L)))

/-- The standard float grid type. -/
def GridType.float543 : GridType := ⟨.float, Layout.standard⟩

theorem parseGridType_float543 :
    parseGridType "Tree_float_5_4_3" = some GridType.float543 := by
  decide

theorem float543_wellFormed : GridType.float543.WellFormed := by
  unfold GridType.WellFormed GridType.float543
  refine ⟨by decide, by decide, ?_⟩
  unfold Layout.WellFormed Layout.standard
  decide

end Vdb
