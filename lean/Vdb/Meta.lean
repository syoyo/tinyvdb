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

/-- The metadata value kinds the reader decodes. -/
inductive MetaKind where
  | str
  | boolean
  | int32
  | int64
  | float
  | double
  | vec3i
  | vec3s
  | vec3d
  deriving Repr, DecidableEq

/-- Map-name lookup for metadata types. -/
def MetaKind.ofName? (b : Bytes) : Option MetaKind :=
  if b = strTypeName then some .str
  else if b = boolTypeName then some .boolean
  else if b = int32TypeName then some .int32
  else if b = int64TypeName then some .int64
  else if b = floatTypeName then some .float
  else if b = doubleTypeName then some .double
  else if b = vec3iTypeName then some .vec3i
  else if b = vec3sTypeName then some .vec3s
  else if b = vec3dTypeName then some .vec3d
  else none

@[simp] theorem MetaKind.ofName_str : MetaKind.ofName? strTypeName = some .str := by
  native_decide
@[simp] theorem MetaKind.ofName_bool : MetaKind.ofName? boolTypeName = some .boolean := by
  native_decide
@[simp] theorem MetaKind.ofName_int32 : MetaKind.ofName? int32TypeName = some .int32 := by
  native_decide
@[simp] theorem MetaKind.ofName_int64 : MetaKind.ofName? int64TypeName = some .int64 := by
  native_decide
@[simp] theorem MetaKind.ofName_float : MetaKind.ofName? floatTypeName = some .float := by
  native_decide
@[simp] theorem MetaKind.ofName_double : MetaKind.ofName? doubleTypeName = some .double := by
  native_decide
@[simp] theorem MetaKind.ofName_vec3i : MetaKind.ofName? vec3iTypeName = some .vec3i := by
  native_decide
@[simp] theorem MetaKind.ofName_vec3s : MetaKind.ofName? vec3sTypeName = some .vec3s := by
  native_decide
@[simp] theorem MetaKind.ofName_vec3d : MetaKind.ofName? vec3dTypeName = some .vec3d := by
  native_decide

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

/-- Read a value of the given kind at `off`, after the type name. `size` is
    the `i32` byte count that precedes the payload (the C reader rejects
    negative counts and requires the exact width for known kinds). -/
def parseValue (k : MetaKind) (b : Bytes) (off : Nat) : Option (MetaValue × Nat) :=
  match getI32LE b off with
  | none => none
  | some sz =>
    if sz < 0 then none
    else match k with
      | .str => none
      | .boolean =>
        if sz.toNatClampNeg = 1 then
          (getU8? b (off + 4)).map fun v => (.boolean (v != 0), off + 5)
        else none
      | .int32 =>
        if sz.toNatClampNeg = 4 then
          (getI32LE b (off + 4)).map fun v => (.int32 v, off + 8)
        else none
      | .int64 =>
        if sz.toNatClampNeg = 8 then
          (getI64LE b (off + 4)).map fun v => (.int64 v, off + 12)
        else none
      | .float =>
        if sz.toNatClampNeg = 4 then
          (getU32LE b (off + 4)).map fun v => (.f32 v, off + 8)
        else none
      | .double =>
        if sz.toNatClampNeg = 8 then
          (getU64LE b (off + 4)).map fun v => (.f64 v, off + 12)
        else none
      | .vec3i =>
        if sz.toNatClampNeg = 12 then
          (getI32LE b (off + 4)).bind fun x =>
            (getI32LE b (off + 8)).bind fun y =>
              (getI32LE b (off + 12)).map fun z => (.vec3i x y z, off + 16)
        else none
      | .vec3s =>
        if sz.toNatClampNeg = 12 then
          (getU32LE b (off + 4)).bind fun x =>
            (getU32LE b (off + 8)).bind fun y =>
              (getU32LE b (off + 12)).map fun z => (.vec3f x y z, off + 16)
        else none
      | .vec3d =>
        if sz.toNatClampNeg = 24 then
          (getU64LE b (off + 4)).bind fun x =>
            (getU64LE b (off + 12)).bind fun y =>
              (getU64LE b (off + 20)).map fun z => (.vec3d x y z, off + 28)
        else none

/-- Parse an entry at `off`. -/
def MetaEntry.parseFrom (b : Bytes) (off : Nat) : Option (MetaEntry × Nat) :=
  match getString? b off with
  | none => none
  | some (name, o1) =>
    match getString? b o1 with
    | none => none
    | some (tn, o2) =>
      match MetaKind.ofName? tn with
      | some .str =>
        (getString? b o2).map fun p => (⟨name, tn, .str p.1⟩, p.2)
      | some k =>
        (parseValue k b o2).map fun p => (⟨name, tn, p.1⟩, p.2)
      | none =>
        (parseValue .boolean b o2).map fun p => (⟨name, tn, p.1⟩, p.2)


/-! ### Round trip -/

/-- Reading a signed 32-bit value chunk. -/
theorem getI32LE_chunk (pre : List Bytes) (v : Int32) (post : List Bytes) :
    getI32LE (concatChunks (pre ++ putI32LE v ByteArray.empty :: post))
      (concatChunks pre).size = some v := by
  unfold getI32LE putI32LE
  rw [getU32LE_chunk]
  rfl

end Vdb
