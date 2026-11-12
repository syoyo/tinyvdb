/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Metadata entries (`tvdb__read_meta` / `tvdb__write_meta`):

  * `i32` count (0..4096), then for each entry
  * name: VDB string,
  * type name: VDB string,
  * value: for `"string"` a VDB string; for a known type an `i32` byte size
    (exactly the type's width) followed by the value; for an unknown type an
    `i32` byte size followed by that many opaque bytes.

  Known type names: `bool`, `float`, `double`, `int32`, `int64`, `vec3i`,
  `vec3d`, `vec3s`.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Chunks
import Vdb.Value

namespace Vdb

/-! ### Type names -/

def strTypeName : Bytes := "string".toUTF8
def boolTypeName : Bytes := "bool".toUTF8
def floatTypeName : Bytes := "float".toUTF8
def doubleTypeName : Bytes := "double".toUTF8
def int32TypeName : Bytes := "int32".toUTF8
def int64TypeName : Bytes := "int64".toUTF8
def vec3iTypeName : Bytes := "vec3i".toUTF8
def vec3sTypeName : Bytes := "vec3s".toUTF8
def vec3dTypeName : Bytes := "vec3d".toUTF8
def halfTypeName : Bytes := "half".toUTF8

/-- The names the reader decodes into typed values (the C `strcmp` chain). -/
def knownTypeName (b : Bytes) : Bool :=
  b = boolTypeName || b = floatTypeName || b = doubleTypeName ||
  b = int32TypeName || b = int64TypeName || b = vec3iTypeName ||
  b = vec3sTypeName || b = vec3dTypeName

/-! ### Entries -/

/-- A metadata entry. `raw` holds the payload of an unknown type; `str` the
    payload of a string entry. -/
structure MetaEntry where
  name : Bytes
  typeName : Bytes
  value : MetaValue
  deriving Repr, Inhabited

/-- The entry's value agrees with its type name. Unknown names carry raw
    bytes, and a raw value is only allowed for unknown names. -/
def MetaEntry.TypeOK (e : MetaEntry) : Prop :=
  match e.value with
  | .str _ => e.typeName = strTypeName
  | .boolean _ => e.typeName = boolTypeName
  | .int32 _ => e.typeName = int32TypeName
  | .int64 _ => e.typeName = int64TypeName
  | .f32 _ => e.typeName = floatTypeName
  | .f64 _ => e.typeName = doubleTypeName
  | .vec3i _ _ _ => e.typeName = vec3iTypeName
  | .vec3f _ _ _ => e.typeName = vec3sTypeName
  | .vec3d _ _ _ => e.typeName = vec3dTypeName
  | .raw _ => knownTypeName e.typeName = false

/-- The entry's variable-length fields fit the wire lengths. -/
def MetaEntry.SizesOK (e : MetaEntry) : Prop :=
  e.name.size < 2 ^ 32 ∧ e.typeName.size < 2 ^ 32 ∧
  (match e.value with
   | .str s => s.size < 2 ^ 32
   | .raw b => b.size < 2 ^ 31
   | _ => True)

/-- Wire well-formedness of an entry. -/
def MetaEntry.WellFormed (e : MetaEntry) : Prop :=
  e.TypeOK ∧ e.SizesOK

/-- The chunks written after the name and type-name strings. -/
def MetaEntry.valueChunks (e : MetaEntry) : List Bytes :=
  match e.value with
  | .str s => [putString s ByteArray.empty]
  | .boolean b => [putU32LE 1 ByteArray.empty, putU8 (if b then 1 else 0) ByteArray.empty]
  | .int32 i => [putU32LE 4 ByteArray.empty, putI32LE i ByteArray.empty]
  | .int64 i => [putU32LE 8 ByteArray.empty, putI64LE i ByteArray.empty]
  | .f32 b => [putU32LE 4 ByteArray.empty, putU32LE b ByteArray.empty]
  | .f64 b => [putU32LE 8 ByteArray.empty, putU64LE b ByteArray.empty]
  | .vec3i x y z =>
      [putU32LE 12 ByteArray.empty, putI32LE x ByteArray.empty,
       putI32LE y ByteArray.empty, putI32LE z ByteArray.empty]
  | .vec3f x y z =>
      [putU32LE 12 ByteArray.empty, putU32LE x ByteArray.empty,
       putU32LE y ByteArray.empty, putU32LE z ByteArray.empty]
  | .vec3d x y z =>
      [putU32LE 24 ByteArray.empty, putU64LE x ByteArray.empty,
       putU64LE y ByteArray.empty, putU64LE z ByteArray.empty]
  | .raw b => [putU32LE (UInt32.ofNat b.size) ByteArray.empty, b]

/-- The entry's wire chunks: name, type name, value. -/
def MetaEntry.chunks (e : MetaEntry) : List Bytes :=
  putString e.name ByteArray.empty :: putString e.typeName ByteArray.empty ::
    e.valueChunks

/-- Emit an entry after `acc`. -/
def MetaEntry.emitFrom (e : MetaEntry) (acc : Bytes) : Bytes :=
  acc ++ concatChunks e.chunks

/-- Emit an entry. -/
def MetaEntry.emit (e : MetaEntry) : Bytes := e.emitFrom ByteArray.empty

/-- Emitted size. -/
theorem MetaEntry.emitFrom_size (e : MetaEntry) (acc : Bytes) :
    (e.emitFrom acc).size = acc.size + (e.chunks.map (·.size)).sum := by
  unfold MetaEntry.emitFrom
  rw [ByteArray.size_append, concatChunks_size]

/-! ### Parsing -/

/-- Read a value of a known-or-unknown type at `off`, after the type name.
    `size` is the `i32` byte count that precedes the payload. -/
def parseValue (tn : Bytes) (b : Bytes) (off : Nat) : Option (MetaValue × Nat) :=
  match getI32LE b off with
  | none => none
  | some sz =>
    if sz < 0 then none
    else
      let len := sz.toNatClampNeg
      let vo := off + 4
      if tn = boolTypeName then
        (if len = 1 then
          (getU8? b vo).map fun v => (.boolean (v != 0), vo + 1)
         else none)
      else if tn = int32TypeName then
        (if len = 4 then (getI32LE b vo).map fun v => (.int32 v, vo + 4) else none)
      else if tn = int64TypeName then
        (if len = 8 then (getI64LE b vo).map fun v => (.int64 v, vo + 8) else none)
      else if tn = floatTypeName then
        (if len = 4 then (getU32LE b vo).map fun v => (.f32 v, vo + 4) else none)
      else if tn = doubleTypeName then
        (if len = 8 then (getU64LE b vo).map fun v => (.f64 v, vo + 8) else none)
      else if tn = vec3iTypeName then
        (if len = 12 then
          (getI32LE b vo).bind fun x =>
            (getI32LE b (vo + 4)).bind fun y =>
              (getI32LE b (vo + 8)).map fun z => (.vec3i x y z, vo + 12)
         else none)
      else if tn = vec3sTypeName then
        (if len = 12 then
          (getU32LE b vo).bind fun x =>
            (getU32LE b (vo + 4)).bind fun y =>
              (getU32LE b (vo + 8)).map fun z => (.vec3f x y z, vo + 12)
         else none)
      else if tn = vec3dTypeName then
        (if len = 24 then
          (getU64LE b vo).bind fun x =>
            (getU64LE b (vo + 8)).bind fun y =>
              (getU64LE b (vo + 16)).map fun z => (.vec3d x y z, vo + 24)
         else none)
      else
        (getBytes? b vo len).map fun raw => (.raw raw, vo + len)

/-- Parse an entry at `off`. -/
def MetaEntry.parseFrom (b : Bytes) (off : Nat) : Option (MetaEntry × Nat) :=
  match getString? b off with
  | none => none
  | some (name, o1) =>
    match getString? b o1 with
    | none => none
    | some (tn, o2) =>
      if tn = strTypeName then
        (getString? b o2).map fun p => (⟨name, tn, .str p.1⟩, p.2)
      else
        (parseValue tn b o2).map fun p => (⟨name, tn, p.1⟩, p.2)



end Vdb
