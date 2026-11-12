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

set_option linter.unusedSimpArgs false

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
  | .raw _ => knownTypeName e.typeName = false ∧ e.typeName ≠ strTypeName

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

/-- Read an unknown-type value at `off`: an `i32` byte count followed by that
    many opaque bytes (the C reader's fallback). -/
def parseRaw (b : Bytes) (off : Nat) : Option (MetaValue × Nat) :=
  match getI32LE b off with
  | none => none
  | some sz =>
    if sz < 0 then none
    else
      (getBytes? b (off + 4) sz.toNatClampNeg).map fun raw =>
        (.raw raw, off + 4 + sz.toNatClampNeg)

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
        (parseRaw b o2).map fun p => (⟨name, tn, p.1⟩, p.2)


/-! ### Round trip -/

/-- Reading a signed 32-bit value chunk. -/
theorem getI32LE_chunk (pre : List Bytes) (v : Int32) (post : List Bytes) :
    getI32LE (concatChunks (pre ++ putI32LE v ByteArray.empty :: post))
      (concatChunks pre).size = some v := by
  unfold getI32LE putI32LE
  rw [getU32LE_chunk]
  rfl

theorem pv_bool (pre : List Bytes) (b : Bool) (post : List Bytes) :
    parseValue .boolean (concatChunks (pre ++ [putU32LE 1 ByteArray.empty,
        putU8 (if b then 1 else 0) ByteArray.empty] ++ post)) (concatChunks pre).size =
      some (.boolean b, (concatChunks pre).size + 5) := by
  unfold parseValue
  rw [show concatChunks (pre ++ [putU32LE 1 ByteArray.empty,
      putU8 (if b then 1 else 0) ByteArray.empty] ++ post) =
      concatChunks (pre ++ putU32LE 1 ByteArray.empty ::
        (putU8 (if b then 1 else 0) ByteArray.empty :: post)) from by simp]
  unfold getI32LE
  rw [getU32LE_chunk]
  simp only [Option.map_some]
  rw [show ((1 : UInt32).toInt32) = 1 from rfl]
  rw [ite_eq_right (by decide : ¬ (1 : Int32) < 0)]
  rw [ite_eq_left (by decide : ((1 : Int32).toNatClampNeg) = 1)]
  rw [show (concatChunks pre).size + 4 =
      (concatChunks (pre ++ [putU32LE 1 ByteArray.empty])).size from by
    simp [concatChunks_size]]
  rw [show concatChunks (pre ++ putU32LE 1 ByteArray.empty ::
      (putU8 (if b then 1 else 0) ByteArray.empty :: post)) =
      concatChunks (pre ++ [putU32LE 1 ByteArray.empty] ++
        (putU8 (if b then 1 else 0) ByteArray.empty :: post)) from by simp]
  rw [getU8?_chunk]
  cases b <;> rfl

theorem pv_int32 (pre : List Bytes) (v : Int32) (post : List Bytes) :
    parseValue .int32 (concatChunks (pre ++ [putU32LE 4 ByteArray.empty,
        putI32LE v ByteArray.empty] ++ post)) (concatChunks pre).size =
      some (.int32 v, (concatChunks pre).size + 8) := by
  unfold parseValue
  rw [show concatChunks (pre ++ [putU32LE 4 ByteArray.empty,
      putI32LE v ByteArray.empty] ++ post) =
      concatChunks (pre ++ putU32LE 4 ByteArray.empty ::
        (putI32LE v ByteArray.empty :: post)) from by simp]
  have hsz : getI32LE (concatChunks (pre ++ putU32LE 4 ByteArray.empty ::
        (putI32LE v ByteArray.empty :: post))) (concatChunks pre).size = some 4 := by
    unfold getI32LE
    rw [getU32LE_chunk]
    rfl
  rw [hsz]
  dsimp only
  rw [ite_eq_right (by decide : ¬ (4 : Int32) < 0)]
  rw [ite_eq_left (by decide : ((4 : Int32).toNatClampNeg) = 4)]
  rw [show (concatChunks pre).size + 4 =
      (concatChunks (pre ++ [putU32LE 4 ByteArray.empty])).size from by
    simp [concatChunks_size]]
  rw [show concatChunks (pre ++ putU32LE 4 ByteArray.empty ::
      (putI32LE v ByteArray.empty :: post)) =
      concatChunks (pre ++ [putU32LE 4 ByteArray.empty] ++
        (putI32LE v ByteArray.empty :: post)) from by simp]
  rw [getI32LE_chunk]
  simp only [Option.map_some]

theorem pv_f32 (pre : List Bytes) (v : UInt32) (post : List Bytes) :
    parseValue .float (concatChunks (pre ++ [putU32LE 4 ByteArray.empty,
        putU32LE v ByteArray.empty] ++ post)) (concatChunks pre).size =
      some (.f32 v, (concatChunks pre).size + 8) := by
  unfold parseValue
  rw [show concatChunks (pre ++ [putU32LE 4 ByteArray.empty,
      putU32LE v ByteArray.empty] ++ post) =
      concatChunks (pre ++ putU32LE 4 ByteArray.empty ::
        (putU32LE v ByteArray.empty :: post)) from by simp]
  have hsz : getI32LE (concatChunks (pre ++ putU32LE 4 ByteArray.empty ::
        (putU32LE v ByteArray.empty :: post))) (concatChunks pre).size = some 4 := by
    unfold getI32LE
    rw [getU32LE_chunk]
    rfl
  rw [hsz]
  dsimp only
  rw [ite_eq_right (by decide : ¬ (4 : Int32) < 0)]
  rw [ite_eq_left (by decide : ((4 : Int32).toNatClampNeg) = 4)]
  rw [show (concatChunks pre).size + 4 =
      (concatChunks (pre ++ [putU32LE 4 ByteArray.empty])).size from by
    simp [concatChunks_size]]
  rw [show concatChunks (pre ++ putU32LE 4 ByteArray.empty ::
      (putU32LE v ByteArray.empty :: post)) =
      concatChunks (pre ++ [putU32LE 4 ByteArray.empty] ++
        (putU32LE v ByteArray.empty :: post)) from by simp]
  rw [getU32LE_chunk]
  simp only [Option.map_some]

theorem pv_int64 (pre : List Bytes) (v : Int64) (post : List Bytes) :
    parseValue .int64 (concatChunks (pre ++ [putU32LE 8 ByteArray.empty,
        putI64LE v ByteArray.empty] ++ post)) (concatChunks pre).size =
      some (.int64 v, (concatChunks pre).size + 12) := by
  unfold parseValue
  rw [show concatChunks (pre ++ [putU32LE 8 ByteArray.empty,
      putI64LE v ByteArray.empty] ++ post) =
      concatChunks (pre ++ putU32LE 8 ByteArray.empty ::
        (putI64LE v ByteArray.empty :: post)) from by simp]
  have hsz : getI32LE (concatChunks (pre ++ putU32LE 8 ByteArray.empty ::
        (putI64LE v ByteArray.empty :: post))) (concatChunks pre).size = some 8 := by
    unfold getI32LE
    rw [getU32LE_chunk]
    rfl
  rw [hsz]
  dsimp only
  rw [ite_eq_right (by decide : ¬ (8 : Int32) < 0)]
  rw [ite_eq_left (by decide : ((8 : Int32).toNatClampNeg) = 8)]
  rw [show (concatChunks pre).size + 4 =
      (concatChunks (pre ++ [putU32LE 8 ByteArray.empty])).size from by
    simp [concatChunks_size]]
  rw [show concatChunks (pre ++ putU32LE 8 ByteArray.empty ::
      (putI64LE v ByteArray.empty :: post)) =
      concatChunks (pre ++ [putU32LE 8 ByteArray.empty] ++
        (putI64LE v ByteArray.empty :: post)) from by simp]
  rw [getI64LE_chunk]
  simp only [Option.map_some]

theorem pv_f64 (pre : List Bytes) (v : UInt64) (post : List Bytes) :
    parseValue .double (concatChunks (pre ++ [putU32LE 8 ByteArray.empty,
        putU64LE v ByteArray.empty] ++ post)) (concatChunks pre).size =
      some (.f64 v, (concatChunks pre).size + 12) := by
  unfold parseValue
  rw [show concatChunks (pre ++ [putU32LE 8 ByteArray.empty,
      putU64LE v ByteArray.empty] ++ post) =
      concatChunks (pre ++ putU32LE 8 ByteArray.empty ::
        (putU64LE v ByteArray.empty :: post)) from by simp]
  have hsz : getI32LE (concatChunks (pre ++ putU32LE 8 ByteArray.empty ::
        (putU64LE v ByteArray.empty :: post))) (concatChunks pre).size = some 8 := by
    unfold getI32LE
    rw [getU32LE_chunk]
    rfl
  rw [hsz]
  dsimp only
  rw [ite_eq_right (by decide : ¬ (8 : Int32) < 0)]
  rw [ite_eq_left (by decide : ((8 : Int32).toNatClampNeg) = 8)]
  rw [show (concatChunks pre).size + 4 =
      (concatChunks (pre ++ [putU32LE 8 ByteArray.empty])).size from by
    simp [concatChunks_size]]
  rw [show concatChunks (pre ++ putU32LE 8 ByteArray.empty ::
      (putU64LE v ByteArray.empty :: post)) =
      concatChunks (pre ++ [putU32LE 8 ByteArray.empty] ++
        (putU64LE v ByteArray.empty :: post)) from by simp]
  rw [getU64LE_chunk]
  simp only [Option.map_some]

theorem pv_vec3i (pre : List Bytes) (x y z : Int32) (post : List Bytes) :
    parseValue .vec3i (concatChunks (pre ++ [putU32LE 12 ByteArray.empty,
        putI32LE x ByteArray.empty, putI32LE y ByteArray.empty,
        putI32LE z ByteArray.empty] ++ post)) (concatChunks pre).size =
      some (.vec3i x y z, (concatChunks pre).size + 16) := by
  unfold parseValue
  rw [show concatChunks (pre ++ [putU32LE 12 ByteArray.empty,
      putI32LE x ByteArray.empty, putI32LE y ByteArray.empty,
      putI32LE z ByteArray.empty] ++ post) =
      concatChunks (pre ++ putU32LE 12 ByteArray.empty ::
        (putI32LE x ByteArray.empty :: putI32LE y ByteArray.empty ::
          putI32LE z ByteArray.empty :: post)) from by simp]
  have hsz : getI32LE (concatChunks (pre ++ putU32LE 12 ByteArray.empty ::
        (putI32LE x ByteArray.empty :: putI32LE y ByteArray.empty ::
          putI32LE z ByteArray.empty :: post))) (concatChunks pre).size = some 12 := by
    unfold getI32LE
    rw [getU32LE_chunk]
    rfl
  rw [hsz]
  dsimp only
  rw [ite_eq_right (by decide : ¬ (12 : Int32) < 0)]
  rw [ite_eq_left (by decide : ((12 : Int32).toNatClampNeg) = 12)]
  -- first component
  rw [show (concatChunks pre).size + 4 =
      (concatChunks (pre ++ [putU32LE 12 ByteArray.empty])).size from by
    simp [concatChunks_size]]
  rw [show concatChunks (pre ++ putU32LE 12 ByteArray.empty ::
      (putI32LE x ByteArray.empty :: putI32LE y ByteArray.empty ::
        putI32LE z ByteArray.empty :: post)) =
      concatChunks (pre ++ [putU32LE 12 ByteArray.empty] ++
        (putI32LE x ByteArray.empty :: putI32LE y ByteArray.empty ::
          putI32LE z ByteArray.empty :: post)) from by simp]
  rw [getI32LE_chunk]
  simp only [Option.bind_some]
  -- second component
  rw [show (concatChunks pre).size + 8 =
      (concatChunks (pre ++ [putU32LE 12 ByteArray.empty,
        putI32LE x ByteArray.empty])).size from by
    simp [concatChunks_size]]
  rw [show concatChunks (pre ++ [putU32LE 12 ByteArray.empty] ++
      (putI32LE x ByteArray.empty :: putI32LE y ByteArray.empty ::
        putI32LE z ByteArray.empty :: post)) =
      concatChunks (pre ++ [putU32LE 12 ByteArray.empty,
        putI32LE x ByteArray.empty] ++
        (putI32LE y ByteArray.empty :: putI32LE z ByteArray.empty :: post)) from by simp]
  rw [getI32LE_chunk]
  simp only [Option.bind_some]
  -- third component
  rw [show (concatChunks pre).size + 12 =
      (concatChunks (pre ++ [putU32LE 12 ByteArray.empty,
        putI32LE x ByteArray.empty, putI32LE y ByteArray.empty])).size from by
    simp [concatChunks_size]]
  rw [show concatChunks (pre ++ [putU32LE 12 ByteArray.empty,
      putI32LE x ByteArray.empty] ++
      (putI32LE y ByteArray.empty :: putI32LE z ByteArray.empty :: post)) =
      concatChunks (pre ++ [putU32LE 12 ByteArray.empty,
        putI32LE x ByteArray.empty, putI32LE y ByteArray.empty] ++
        (putI32LE z ByteArray.empty :: post)) from by simp]
  rw [getI32LE_chunk]
  simp only [Option.map_some]


theorem pv_vec3f (pre : List Bytes) (x y z : UInt32) (post : List Bytes) :
    parseValue .vec3s (concatChunks (pre ++ [putU32LE 12 ByteArray.empty,
        putU32LE x ByteArray.empty, putU32LE y ByteArray.empty,
        putU32LE z ByteArray.empty] ++ post)) (concatChunks pre).size =
      some (.vec3f x y z, (concatChunks pre).size + 16) := by
  unfold parseValue
  rw [show concatChunks (pre ++ [putU32LE 12 ByteArray.empty,
      putU32LE x ByteArray.empty, putU32LE y ByteArray.empty,
      putU32LE z ByteArray.empty] ++ post) =
      concatChunks (pre ++ putU32LE 12 ByteArray.empty ::
        (putU32LE x ByteArray.empty :: putU32LE y ByteArray.empty ::
          putU32LE z ByteArray.empty :: post)) from by simp]
  have hsz : getI32LE (concatChunks (pre ++ putU32LE 12 ByteArray.empty ::
        (putU32LE x ByteArray.empty :: putU32LE y ByteArray.empty ::
          putU32LE z ByteArray.empty :: post))) (concatChunks pre).size = some 12 := by
    unfold getI32LE
    rw [getU32LE_chunk]
    rfl
  rw [hsz]
  dsimp only
  rw [ite_eq_right (by decide : ¬ (12 : Int32) < 0)]
  rw [ite_eq_left (by decide : ((12 : Int32).toNatClampNeg) = 12)]
  -- first component
  rw [show (concatChunks pre).size + 4 =
      (concatChunks (pre ++ [putU32LE 12 ByteArray.empty])).size from by
    simp [concatChunks_size]]
  rw [show concatChunks (pre ++ putU32LE 12 ByteArray.empty ::
      (putU32LE x ByteArray.empty :: putU32LE y ByteArray.empty ::
        putU32LE z ByteArray.empty :: post)) =
      concatChunks (pre ++ [putU32LE 12 ByteArray.empty] ++
        (putU32LE x ByteArray.empty :: putU32LE y ByteArray.empty ::
          putU32LE z ByteArray.empty :: post)) from by simp]
  rw [getU32LE_chunk]
  simp only [Option.bind_some]
  -- second component
  rw [show (concatChunks pre).size + 8 =
      (concatChunks (pre ++ [putU32LE 12 ByteArray.empty,
        putU32LE x ByteArray.empty])).size from by
    simp [concatChunks_size]]
  rw [show concatChunks (pre ++ [putU32LE 12 ByteArray.empty] ++
      (putU32LE x ByteArray.empty :: putU32LE y ByteArray.empty ::
        putU32LE z ByteArray.empty :: post)) =
      concatChunks (pre ++ [putU32LE 12 ByteArray.empty,
        putU32LE x ByteArray.empty] ++
        (putU32LE y ByteArray.empty :: putU32LE z ByteArray.empty :: post)) from by simp]
  rw [getU32LE_chunk]
  simp only [Option.bind_some]
  -- third component
  rw [show (concatChunks pre).size + 12 =
      (concatChunks (pre ++ [putU32LE 12 ByteArray.empty,
        putU32LE x ByteArray.empty, putU32LE y ByteArray.empty])).size from by
    simp [concatChunks_size]]
  rw [show concatChunks (pre ++ [putU32LE 12 ByteArray.empty,
      putU32LE x ByteArray.empty] ++
      (putU32LE y ByteArray.empty :: putU32LE z ByteArray.empty :: post)) =
      concatChunks (pre ++ [putU32LE 12 ByteArray.empty,
        putU32LE x ByteArray.empty, putU32LE y ByteArray.empty] ++
        (putU32LE z ByteArray.empty :: post)) from by simp]
  rw [getU32LE_chunk]
  simp only [Option.map_some]


theorem pv_vec3d (pre : List Bytes) (x y z : UInt64) (post : List Bytes) :
    parseValue .vec3d (concatChunks (pre ++ [putU32LE 24 ByteArray.empty,
        putU64LE x ByteArray.empty, putU64LE y ByteArray.empty,
        putU64LE z ByteArray.empty] ++ post)) (concatChunks pre).size =
      some (.vec3d x y z, (concatChunks pre).size + 28) := by
  unfold parseValue
  rw [show concatChunks (pre ++ [putU32LE 24 ByteArray.empty,
      putU64LE x ByteArray.empty, putU64LE y ByteArray.empty,
      putU64LE z ByteArray.empty] ++ post) =
      concatChunks (pre ++ putU32LE 24 ByteArray.empty ::
        (putU64LE x ByteArray.empty :: putU64LE y ByteArray.empty ::
          putU64LE z ByteArray.empty :: post)) from by simp]
  have hsz : getI32LE (concatChunks (pre ++ putU32LE 24 ByteArray.empty ::
        (putU64LE x ByteArray.empty :: putU64LE y ByteArray.empty ::
          putU64LE z ByteArray.empty :: post))) (concatChunks pre).size = some 24 := by
    unfold getI32LE
    rw [getU32LE_chunk]
    rfl
  rw [hsz]
  dsimp only
  rw [ite_eq_right (by decide : ¬ (24 : Int32) < 0)]
  rw [ite_eq_left (by decide : ((24 : Int32).toNatClampNeg) = 24)]
  rw [show (concatChunks pre).size + 4 =
      (concatChunks (pre ++ [putU32LE 24 ByteArray.empty])).size from by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]]
  rw [show concatChunks (pre ++ putU32LE 24 ByteArray.empty ::
      (putU64LE x ByteArray.empty :: putU64LE y ByteArray.empty ::
        putU64LE z ByteArray.empty :: post)) =
      concatChunks (pre ++ [putU32LE 24 ByteArray.empty] ++
        (putU64LE x ByteArray.empty :: putU64LE y ByteArray.empty ::
          putU64LE z ByteArray.empty :: post)) from by simp]
  rw [getU64LE_chunk]
  simp only [Option.bind_some]
  rw [show (concatChunks pre).size + 12 =
      (concatChunks (pre ++ [putU32LE 24 ByteArray.empty,
        putU64LE x ByteArray.empty])).size from by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]]
  rw [show concatChunks (pre ++ [putU32LE 24 ByteArray.empty] ++
      (putU64LE x ByteArray.empty :: putU64LE y ByteArray.empty ::
        putU64LE z ByteArray.empty :: post)) =
      concatChunks (pre ++ [putU32LE 24 ByteArray.empty,
        putU64LE x ByteArray.empty] ++
        (putU64LE y ByteArray.empty :: putU64LE z ByteArray.empty :: post)) from by simp]
  rw [getU64LE_chunk]
  simp only [Option.bind_some]
  rw [show (concatChunks pre).size + 20 =
      (concatChunks (pre ++ [putU32LE 24 ByteArray.empty,
        putU64LE x ByteArray.empty, putU64LE y ByteArray.empty])).size from by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]]
  rw [show concatChunks (pre ++ [putU32LE 24 ByteArray.empty,
      putU64LE x ByteArray.empty] ++
      (putU64LE y ByteArray.empty :: putU64LE z ByteArray.empty :: post)) =
      concatChunks (pre ++ [putU32LE 24 ByteArray.empty,
        putU64LE x ByteArray.empty, putU64LE y ByteArray.empty] ++
        (putU64LE z ByteArray.empty :: post)) from by simp]
  rw [getU64LE_chunk]
  simp only [Option.map_some]

theorem MetaEntry.parseFrom_emitFrom_bool (name : Bytes) (hn : name.size < 2 ^ 32)
    (b : Bool) (acc : Bytes) :
    ∃ out, MetaEntry.parseFrom
        ((⟨name, boolTypeName, .boolean b⟩ : MetaEntry).emitFrom acc) acc.size =
      some (⟨name, boolTypeName, .boolean b⟩, out) := by
  constructor
  unfold MetaEntry.parseFrom MetaEntry.emitFrom MetaEntry.chunks MetaEntry.valueChunks
  rw [acc_append_concatChunks]
  rw [show acc :: (putString name ByteArray.empty :: (putString boolTypeName ByteArray.empty ::
      [putU32LE 1 ByteArray.empty, putU8 (if b then 1 else 0) ByteArray.empty])) =
      [acc] ++ putString name ByteArray.empty :: (putString boolTypeName ByteArray.empty ::
        [putU32LE 1 ByteArray.empty, putU8 (if b then 1 else 0) ByteArray.empty]) from rfl]
  rw [show acc.size = (concatChunks [acc]).size from by simp [concatChunks]]
  rw [getString?_chunk (pre := [acc]) (s := name)
    (post := putString boolTypeName ByteArray.empty :: [putU32LE 1 ByteArray.empty, putU8 (if b then 1 else 0) ByteArray.empty]) hn]
  dsimp only
  have h1 : (concatChunks [acc]).size + 4 + name.size =
      (concatChunks [acc, putString name ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h1]
  rw [show [acc] ++ (putString name ByteArray.empty :: (putString boolTypeName ByteArray.empty ::
      [putU32LE 1 ByteArray.empty, putU8 (if b then 1 else 0) ByteArray.empty])) =
      [acc, putString name ByteArray.empty] ++ (putString boolTypeName ByteArray.empty ::
        [putU32LE 1 ByteArray.empty, putU8 (if b then 1 else 0) ByteArray.empty]) from rfl]
  rw [getString?_chunk (pre := [acc, putString name ByteArray.empty]) (s := boolTypeName)
    (post := [putU32LE 1 ByteArray.empty, putU8 (if b then 1 else 0) ByteArray.empty]) (by decide)]
  dsimp only
  have h2 : (concatChunks [acc, putString name ByteArray.empty]).size + 4 + boolTypeName.size =
      (concatChunks [acc, putString name ByteArray.empty, putString boolTypeName ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h2]
  rw [MetaKind.ofName_bool]
  dsimp only
  rw [show concatChunks ([acc, putString name ByteArray.empty] ++
      (putString boolTypeName ByteArray.empty :: [putU32LE 1 ByteArray.empty, putU8 (if b then 1 else 0) ByteArray.empty])) =
      concatChunks ([acc, putString name ByteArray.empty, putString boolTypeName ByteArray.empty] ++
        [putU32LE 1 ByteArray.empty, putU8 (if b then 1 else 0) ByteArray.empty] ++ []) from by simp]
  rw [pv_bool]
  simp only [Option.map_some]
  rfl

theorem MetaEntry.parseFrom_emitFrom_int32 (name : Bytes) (hn : name.size < 2 ^ 32)
    (v : Int32) (acc : Bytes) :
    ∃ out, MetaEntry.parseFrom
        ((⟨name, int32TypeName, .int32 v⟩ : MetaEntry).emitFrom acc) acc.size =
      some (⟨name, int32TypeName, .int32 v⟩, out) := by
  constructor
  unfold MetaEntry.parseFrom MetaEntry.emitFrom MetaEntry.chunks MetaEntry.valueChunks
  rw [acc_append_concatChunks]
  rw [show acc :: (putString name ByteArray.empty :: (putString int32TypeName ByteArray.empty ::
      [putU32LE 4 ByteArray.empty, putI32LE v ByteArray.empty])) =
      [acc] ++ putString name ByteArray.empty :: (putString int32TypeName ByteArray.empty ::
        [putU32LE 4 ByteArray.empty, putI32LE v ByteArray.empty]) from rfl]
  rw [show acc.size = (concatChunks [acc]).size from by simp [concatChunks]]
  rw [getString?_chunk (pre := [acc]) (s := name)
    (post := putString int32TypeName ByteArray.empty :: [putU32LE 4 ByteArray.empty, putI32LE v ByteArray.empty]) hn]
  dsimp only
  have h1 : (concatChunks [acc]).size + 4 + name.size =
      (concatChunks [acc, putString name ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h1]
  rw [show [acc] ++ (putString name ByteArray.empty :: (putString int32TypeName ByteArray.empty ::
      [putU32LE 4 ByteArray.empty, putI32LE v ByteArray.empty])) =
      [acc, putString name ByteArray.empty] ++ (putString int32TypeName ByteArray.empty ::
        [putU32LE 4 ByteArray.empty, putI32LE v ByteArray.empty]) from rfl]
  rw [getString?_chunk (pre := [acc, putString name ByteArray.empty]) (s := int32TypeName)
    (post := [putU32LE 4 ByteArray.empty, putI32LE v ByteArray.empty]) (by decide)]
  dsimp only
  have h2 : (concatChunks [acc, putString name ByteArray.empty]).size + 4 + int32TypeName.size =
      (concatChunks [acc, putString name ByteArray.empty, putString int32TypeName ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h2]
  rw [MetaKind.ofName_int32]
  dsimp only
  rw [show concatChunks ([acc, putString name ByteArray.empty] ++
      (putString int32TypeName ByteArray.empty :: [putU32LE 4 ByteArray.empty, putI32LE v ByteArray.empty])) =
      concatChunks ([acc, putString name ByteArray.empty, putString int32TypeName ByteArray.empty] ++
        [putU32LE 4 ByteArray.empty, putI32LE v ByteArray.empty] ++ []) from by simp]
  rw [pv_int32]
  simp only [Option.map_some]
  rfl

theorem MetaEntry.parseFrom_emitFrom_int64 (name : Bytes) (hn : name.size < 2 ^ 32)
    (v : Int64) (acc : Bytes) :
    ∃ out, MetaEntry.parseFrom
        ((⟨name, int64TypeName, .int64 v⟩ : MetaEntry).emitFrom acc) acc.size =
      some (⟨name, int64TypeName, .int64 v⟩, out) := by
  constructor
  unfold MetaEntry.parseFrom MetaEntry.emitFrom MetaEntry.chunks MetaEntry.valueChunks
  rw [acc_append_concatChunks]
  rw [show acc :: (putString name ByteArray.empty :: (putString int64TypeName ByteArray.empty ::
      [putU32LE 8 ByteArray.empty, putI64LE v ByteArray.empty])) =
      [acc] ++ putString name ByteArray.empty :: (putString int64TypeName ByteArray.empty ::
        [putU32LE 8 ByteArray.empty, putI64LE v ByteArray.empty]) from rfl]
  rw [show acc.size = (concatChunks [acc]).size from by simp [concatChunks]]
  rw [getString?_chunk (pre := [acc]) (s := name)
    (post := putString int64TypeName ByteArray.empty :: [putU32LE 8 ByteArray.empty, putI64LE v ByteArray.empty]) hn]
  dsimp only
  have h1 : (concatChunks [acc]).size + 4 + name.size =
      (concatChunks [acc, putString name ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h1]
  rw [show [acc] ++ (putString name ByteArray.empty :: (putString int64TypeName ByteArray.empty ::
      [putU32LE 8 ByteArray.empty, putI64LE v ByteArray.empty])) =
      [acc, putString name ByteArray.empty] ++ (putString int64TypeName ByteArray.empty ::
        [putU32LE 8 ByteArray.empty, putI64LE v ByteArray.empty]) from rfl]
  rw [getString?_chunk (pre := [acc, putString name ByteArray.empty]) (s := int64TypeName)
    (post := [putU32LE 8 ByteArray.empty, putI64LE v ByteArray.empty]) (by decide)]
  dsimp only
  have h2 : (concatChunks [acc, putString name ByteArray.empty]).size + 4 + int64TypeName.size =
      (concatChunks [acc, putString name ByteArray.empty, putString int64TypeName ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h2]
  rw [MetaKind.ofName_int64]
  dsimp only
  rw [show concatChunks ([acc, putString name ByteArray.empty] ++
      (putString int64TypeName ByteArray.empty :: [putU32LE 8 ByteArray.empty, putI64LE v ByteArray.empty])) =
      concatChunks ([acc, putString name ByteArray.empty, putString int64TypeName ByteArray.empty] ++
        [putU32LE 8 ByteArray.empty, putI64LE v ByteArray.empty] ++ []) from by simp]
  rw [pv_int64]
  simp only [Option.map_some]
  rfl

theorem MetaEntry.parseFrom_emitFrom_f32 (name : Bytes) (hn : name.size < 2 ^ 32)
    (v : UInt32) (acc : Bytes) :
    ∃ out, MetaEntry.parseFrom
        ((⟨name, floatTypeName, .f32 v⟩ : MetaEntry).emitFrom acc) acc.size =
      some (⟨name, floatTypeName, .f32 v⟩, out) := by
  constructor
  unfold MetaEntry.parseFrom MetaEntry.emitFrom MetaEntry.chunks MetaEntry.valueChunks
  rw [acc_append_concatChunks]
  rw [show acc :: (putString name ByteArray.empty :: (putString floatTypeName ByteArray.empty ::
      [putU32LE 4 ByteArray.empty, putU32LE v ByteArray.empty])) =
      [acc] ++ putString name ByteArray.empty :: (putString floatTypeName ByteArray.empty ::
        [putU32LE 4 ByteArray.empty, putU32LE v ByteArray.empty]) from rfl]
  rw [show acc.size = (concatChunks [acc]).size from by simp [concatChunks]]
  rw [getString?_chunk (pre := [acc]) (s := name)
    (post := putString floatTypeName ByteArray.empty :: [putU32LE 4 ByteArray.empty, putU32LE v ByteArray.empty]) hn]
  dsimp only
  have h1 : (concatChunks [acc]).size + 4 + name.size =
      (concatChunks [acc, putString name ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h1]
  rw [show [acc] ++ (putString name ByteArray.empty :: (putString floatTypeName ByteArray.empty ::
      [putU32LE 4 ByteArray.empty, putU32LE v ByteArray.empty])) =
      [acc, putString name ByteArray.empty] ++ (putString floatTypeName ByteArray.empty ::
        [putU32LE 4 ByteArray.empty, putU32LE v ByteArray.empty]) from rfl]
  rw [getString?_chunk (pre := [acc, putString name ByteArray.empty]) (s := floatTypeName)
    (post := [putU32LE 4 ByteArray.empty, putU32LE v ByteArray.empty]) (by decide)]
  dsimp only
  have h2 : (concatChunks [acc, putString name ByteArray.empty]).size + 4 + floatTypeName.size =
      (concatChunks [acc, putString name ByteArray.empty, putString floatTypeName ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h2]
  rw [MetaKind.ofName_float]
  dsimp only
  rw [show concatChunks ([acc, putString name ByteArray.empty] ++
      (putString floatTypeName ByteArray.empty :: [putU32LE 4 ByteArray.empty, putU32LE v ByteArray.empty])) =
      concatChunks ([acc, putString name ByteArray.empty, putString floatTypeName ByteArray.empty] ++
        [putU32LE 4 ByteArray.empty, putU32LE v ByteArray.empty] ++ []) from by simp]
  rw [pv_f32]
  simp only [Option.map_some]
  rfl

theorem MetaEntry.parseFrom_emitFrom_f64 (name : Bytes) (hn : name.size < 2 ^ 32)
    (v : UInt64) (acc : Bytes) :
    ∃ out, MetaEntry.parseFrom
        ((⟨name, doubleTypeName, .f64 v⟩ : MetaEntry).emitFrom acc) acc.size =
      some (⟨name, doubleTypeName, .f64 v⟩, out) := by
  constructor
  unfold MetaEntry.parseFrom MetaEntry.emitFrom MetaEntry.chunks MetaEntry.valueChunks
  rw [acc_append_concatChunks]
  rw [show acc :: (putString name ByteArray.empty :: (putString doubleTypeName ByteArray.empty ::
      [putU32LE 8 ByteArray.empty, putU64LE v ByteArray.empty])) =
      [acc] ++ putString name ByteArray.empty :: (putString doubleTypeName ByteArray.empty ::
        [putU32LE 8 ByteArray.empty, putU64LE v ByteArray.empty]) from rfl]
  rw [show acc.size = (concatChunks [acc]).size from by simp [concatChunks]]
  rw [getString?_chunk (pre := [acc]) (s := name)
    (post := putString doubleTypeName ByteArray.empty :: [putU32LE 8 ByteArray.empty, putU64LE v ByteArray.empty]) hn]
  dsimp only
  have h1 : (concatChunks [acc]).size + 4 + name.size =
      (concatChunks [acc, putString name ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h1]
  rw [show [acc] ++ (putString name ByteArray.empty :: (putString doubleTypeName ByteArray.empty ::
      [putU32LE 8 ByteArray.empty, putU64LE v ByteArray.empty])) =
      [acc, putString name ByteArray.empty] ++ (putString doubleTypeName ByteArray.empty ::
        [putU32LE 8 ByteArray.empty, putU64LE v ByteArray.empty]) from rfl]
  rw [getString?_chunk (pre := [acc, putString name ByteArray.empty]) (s := doubleTypeName)
    (post := [putU32LE 8 ByteArray.empty, putU64LE v ByteArray.empty]) (by decide)]
  dsimp only
  have h2 : (concatChunks [acc, putString name ByteArray.empty]).size + 4 + doubleTypeName.size =
      (concatChunks [acc, putString name ByteArray.empty, putString doubleTypeName ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h2]
  rw [MetaKind.ofName_double]
  dsimp only
  rw [show concatChunks ([acc, putString name ByteArray.empty] ++
      (putString doubleTypeName ByteArray.empty :: [putU32LE 8 ByteArray.empty, putU64LE v ByteArray.empty])) =
      concatChunks ([acc, putString name ByteArray.empty, putString doubleTypeName ByteArray.empty] ++
        [putU32LE 8 ByteArray.empty, putU64LE v ByteArray.empty] ++ []) from by simp]
  rw [pv_f64]
  simp only [Option.map_some]
  rfl

theorem MetaEntry.parseFrom_emitFrom_vec3i (name : Bytes) (hn : name.size < 2 ^ 32)
    (x y z : Int32) (acc : Bytes) :
    ∃ out, MetaEntry.parseFrom
        ((⟨name, vec3iTypeName, .vec3i x y z⟩ : MetaEntry).emitFrom acc) acc.size =
      some (⟨name, vec3iTypeName, .vec3i x y z⟩, out) := by
  constructor
  unfold MetaEntry.parseFrom MetaEntry.emitFrom MetaEntry.chunks MetaEntry.valueChunks
  rw [acc_append_concatChunks]
  rw [show acc :: (putString name ByteArray.empty :: (putString vec3iTypeName ByteArray.empty ::
      [putU32LE 12 ByteArray.empty, putI32LE x ByteArray.empty, putI32LE y ByteArray.empty, putI32LE z ByteArray.empty])) =
      [acc] ++ putString name ByteArray.empty :: (putString vec3iTypeName ByteArray.empty ::
        [putU32LE 12 ByteArray.empty, putI32LE x ByteArray.empty, putI32LE y ByteArray.empty, putI32LE z ByteArray.empty]) from rfl]
  rw [show acc.size = (concatChunks [acc]).size from by simp [concatChunks]]
  rw [getString?_chunk (pre := [acc]) (s := name)
    (post := putString vec3iTypeName ByteArray.empty :: [putU32LE 12 ByteArray.empty, putI32LE x ByteArray.empty, putI32LE y ByteArray.empty, putI32LE z ByteArray.empty]) hn]
  dsimp only
  have h1 : (concatChunks [acc]).size + 4 + name.size =
      (concatChunks [acc, putString name ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h1]
  rw [show [acc] ++ (putString name ByteArray.empty :: (putString vec3iTypeName ByteArray.empty ::
      [putU32LE 12 ByteArray.empty, putI32LE x ByteArray.empty, putI32LE y ByteArray.empty, putI32LE z ByteArray.empty])) =
      [acc, putString name ByteArray.empty] ++ (putString vec3iTypeName ByteArray.empty ::
        [putU32LE 12 ByteArray.empty, putI32LE x ByteArray.empty, putI32LE y ByteArray.empty, putI32LE z ByteArray.empty]) from rfl]
  rw [getString?_chunk (pre := [acc, putString name ByteArray.empty]) (s := vec3iTypeName)
    (post := [putU32LE 12 ByteArray.empty, putI32LE x ByteArray.empty, putI32LE y ByteArray.empty, putI32LE z ByteArray.empty]) (by decide)]
  dsimp only
  have h2 : (concatChunks [acc, putString name ByteArray.empty]).size + 4 + vec3iTypeName.size =
      (concatChunks [acc, putString name ByteArray.empty, putString vec3iTypeName ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h2]
  rw [MetaKind.ofName_vec3i]
  dsimp only
  rw [show concatChunks ([acc, putString name ByteArray.empty] ++
      (putString vec3iTypeName ByteArray.empty :: [putU32LE 12 ByteArray.empty, putI32LE x ByteArray.empty, putI32LE y ByteArray.empty, putI32LE z ByteArray.empty])) =
      concatChunks ([acc, putString name ByteArray.empty, putString vec3iTypeName ByteArray.empty] ++
        [putU32LE 12 ByteArray.empty, putI32LE x ByteArray.empty, putI32LE y ByteArray.empty, putI32LE z ByteArray.empty] ++ []) from by simp]
  rw [pv_vec3i]
  simp only [Option.map_some]
  rfl

theorem MetaEntry.parseFrom_emitFrom_vec3f (name : Bytes) (hn : name.size < 2 ^ 32)
    (x y z : UInt32) (acc : Bytes) :
    ∃ out, MetaEntry.parseFrom
        ((⟨name, vec3sTypeName, .vec3f x y z⟩ : MetaEntry).emitFrom acc) acc.size =
      some (⟨name, vec3sTypeName, .vec3f x y z⟩, out) := by
  constructor
  unfold MetaEntry.parseFrom MetaEntry.emitFrom MetaEntry.chunks MetaEntry.valueChunks
  rw [acc_append_concatChunks]
  rw [show acc :: (putString name ByteArray.empty :: (putString vec3sTypeName ByteArray.empty ::
      [putU32LE 12 ByteArray.empty, putU32LE x ByteArray.empty, putU32LE y ByteArray.empty, putU32LE z ByteArray.empty])) =
      [acc] ++ putString name ByteArray.empty :: (putString vec3sTypeName ByteArray.empty ::
        [putU32LE 12 ByteArray.empty, putU32LE x ByteArray.empty, putU32LE y ByteArray.empty, putU32LE z ByteArray.empty]) from rfl]
  rw [show acc.size = (concatChunks [acc]).size from by simp [concatChunks]]
  rw [getString?_chunk (pre := [acc]) (s := name)
    (post := putString vec3sTypeName ByteArray.empty :: [putU32LE 12 ByteArray.empty, putU32LE x ByteArray.empty, putU32LE y ByteArray.empty, putU32LE z ByteArray.empty]) hn]
  dsimp only
  have h1 : (concatChunks [acc]).size + 4 + name.size =
      (concatChunks [acc, putString name ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h1]
  rw [show [acc] ++ (putString name ByteArray.empty :: (putString vec3sTypeName ByteArray.empty ::
      [putU32LE 12 ByteArray.empty, putU32LE x ByteArray.empty, putU32LE y ByteArray.empty, putU32LE z ByteArray.empty])) =
      [acc, putString name ByteArray.empty] ++ (putString vec3sTypeName ByteArray.empty ::
        [putU32LE 12 ByteArray.empty, putU32LE x ByteArray.empty, putU32LE y ByteArray.empty, putU32LE z ByteArray.empty]) from rfl]
  rw [getString?_chunk (pre := [acc, putString name ByteArray.empty]) (s := vec3sTypeName)
    (post := [putU32LE 12 ByteArray.empty, putU32LE x ByteArray.empty, putU32LE y ByteArray.empty, putU32LE z ByteArray.empty]) (by decide)]
  dsimp only
  have h2 : (concatChunks [acc, putString name ByteArray.empty]).size + 4 + vec3sTypeName.size =
      (concatChunks [acc, putString name ByteArray.empty, putString vec3sTypeName ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h2]
  rw [MetaKind.ofName_vec3s]
  dsimp only
  rw [show concatChunks ([acc, putString name ByteArray.empty] ++
      (putString vec3sTypeName ByteArray.empty :: [putU32LE 12 ByteArray.empty, putU32LE x ByteArray.empty, putU32LE y ByteArray.empty, putU32LE z ByteArray.empty])) =
      concatChunks ([acc, putString name ByteArray.empty, putString vec3sTypeName ByteArray.empty] ++
        [putU32LE 12 ByteArray.empty, putU32LE x ByteArray.empty, putU32LE y ByteArray.empty, putU32LE z ByteArray.empty] ++ []) from by simp]
  rw [pv_vec3f]
  simp only [Option.map_some]
  rfl

theorem MetaEntry.parseFrom_emitFrom_vec3d (name : Bytes) (hn : name.size < 2 ^ 32)
    (x y z : UInt64) (acc : Bytes) :
    ∃ out, MetaEntry.parseFrom
        ((⟨name, vec3dTypeName, .vec3d x y z⟩ : MetaEntry).emitFrom acc) acc.size =
      some (⟨name, vec3dTypeName, .vec3d x y z⟩, out) := by
  constructor
  unfold MetaEntry.parseFrom MetaEntry.emitFrom MetaEntry.chunks MetaEntry.valueChunks
  rw [acc_append_concatChunks]
  rw [show acc :: (putString name ByteArray.empty :: (putString vec3dTypeName ByteArray.empty ::
      [putU32LE 24 ByteArray.empty, putU64LE x ByteArray.empty, putU64LE y ByteArray.empty, putU64LE z ByteArray.empty])) =
      [acc] ++ putString name ByteArray.empty :: (putString vec3dTypeName ByteArray.empty ::
        [putU32LE 24 ByteArray.empty, putU64LE x ByteArray.empty, putU64LE y ByteArray.empty, putU64LE z ByteArray.empty]) from rfl]
  rw [show acc.size = (concatChunks [acc]).size from by simp [concatChunks]]
  rw [getString?_chunk (pre := [acc]) (s := name)
    (post := putString vec3dTypeName ByteArray.empty :: [putU32LE 24 ByteArray.empty, putU64LE x ByteArray.empty, putU64LE y ByteArray.empty, putU64LE z ByteArray.empty]) hn]
  dsimp only
  have h1 : (concatChunks [acc]).size + 4 + name.size =
      (concatChunks [acc, putString name ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h1]
  rw [show [acc] ++ (putString name ByteArray.empty :: (putString vec3dTypeName ByteArray.empty ::
      [putU32LE 24 ByteArray.empty, putU64LE x ByteArray.empty, putU64LE y ByteArray.empty, putU64LE z ByteArray.empty])) =
      [acc, putString name ByteArray.empty] ++ (putString vec3dTypeName ByteArray.empty ::
        [putU32LE 24 ByteArray.empty, putU64LE x ByteArray.empty, putU64LE y ByteArray.empty, putU64LE z ByteArray.empty]) from rfl]
  rw [getString?_chunk (pre := [acc, putString name ByteArray.empty]) (s := vec3dTypeName)
    (post := [putU32LE 24 ByteArray.empty, putU64LE x ByteArray.empty, putU64LE y ByteArray.empty, putU64LE z ByteArray.empty]) (by decide)]
  dsimp only
  have h2 : (concatChunks [acc, putString name ByteArray.empty]).size + 4 + vec3dTypeName.size =
      (concatChunks [acc, putString name ByteArray.empty, putString vec3dTypeName ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h2]
  rw [MetaKind.ofName_vec3d]
  dsimp only
  rw [show concatChunks ([acc, putString name ByteArray.empty] ++
      (putString vec3dTypeName ByteArray.empty :: [putU32LE 24 ByteArray.empty, putU64LE x ByteArray.empty, putU64LE y ByteArray.empty, putU64LE z ByteArray.empty])) =
      concatChunks ([acc, putString name ByteArray.empty, putString vec3dTypeName ByteArray.empty] ++
        [putU32LE 24 ByteArray.empty, putU64LE x ByteArray.empty, putU64LE y ByteArray.empty, putU64LE z ByteArray.empty] ++ []) from by simp]
  rw [pv_vec3d]
  simp only [Option.map_some]
  rfl

theorem MetaEntry.parseFrom_emitFrom_str (name : Bytes) (hn : name.size < 2 ^ 32)
    (payload : Bytes) (hp : payload.size < 2 ^ 32) (acc : Bytes) :
    ∃ out, MetaEntry.parseFrom
        ((⟨name, strTypeName, .str payload⟩ : MetaEntry).emitFrom acc) acc.size =
      some (⟨name, strTypeName, .str payload⟩, out) := by
  constructor
  unfold MetaEntry.parseFrom MetaEntry.emitFrom MetaEntry.chunks MetaEntry.valueChunks
  rw [acc_append_concatChunks]
  rw [show acc :: (putString name ByteArray.empty :: (putString strTypeName ByteArray.empty ::
      [putString payload ByteArray.empty])) =
      [acc] ++ putString name ByteArray.empty :: (putString strTypeName ByteArray.empty ::
        [putString payload ByteArray.empty]) from rfl]
  rw [show acc.size = (concatChunks [acc]).size from by simp [concatChunks]]
  rw [getString?_chunk (pre := [acc]) (s := name)
    (post := putString strTypeName ByteArray.empty :: [putString payload ByteArray.empty]) hn]
  dsimp only
  have h1 : (concatChunks [acc]).size + 4 + name.size =
      (concatChunks [acc, putString name ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h1]
  rw [show [acc] ++ (putString name ByteArray.empty :: (putString strTypeName ByteArray.empty ::
      [putString payload ByteArray.empty])) =
      [acc, putString name ByteArray.empty] ++ (putString strTypeName ByteArray.empty ::
        [putString payload ByteArray.empty]) from rfl]
  rw [getString?_chunk (pre := [acc, putString name ByteArray.empty]) (s := strTypeName)
    (post := [putString payload ByteArray.empty]) (by decide)]
  dsimp only
  have h2 : (concatChunks [acc, putString name ByteArray.empty]).size + 4 + strTypeName.size =
      (concatChunks [acc, putString name ByteArray.empty, putString strTypeName ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h2]
  rw [MetaKind.ofName_str]
  dsimp only
  rw [show concatChunks ([acc, putString name ByteArray.empty] ++
      (putString strTypeName ByteArray.empty :: [putString payload ByteArray.empty])) =
      concatChunks ([acc, putString name ByteArray.empty, putString strTypeName ByteArray.empty] ++
        putString payload ByteArray.empty :: []) from by simp]
  rw [getString?_chunk (pre := [acc, putString name ByteArray.empty,
      putString strTypeName ByteArray.empty]) (s := payload) (post := []) hp]
  simp only [Option.map_some]
  rfl

theorem pv_raw (pre : List Bytes) (s : Bytes) (hb : s.size < 2 ^ 31) (post : List Bytes) :
    parseRaw (concatChunks (pre ++ [putU32LE (UInt32.ofNat s.size) ByteArray.empty, s] ++ post))
      (concatChunks pre).size = some (.raw s, (concatChunks pre).size + 4 + s.size) := by
  unfold parseRaw
  rw [show concatChunks (pre ++ [putU32LE (UInt32.ofNat s.size) ByteArray.empty, s] ++ post) =
      concatChunks (pre ++ putU32LE (UInt32.ofNat s.size) ByteArray.empty :: (s :: post)) from by simp]
  have hsz : getI32LE (concatChunks (pre ++ putU32LE (UInt32.ofNat s.size) ByteArray.empty ::
        (s :: post))) (concatChunks pre).size = some (UInt32.ofNat s.size).toInt32 := by
    unfold getI32LE
    rw [getU32LE_chunk]
    rfl
  rw [hsz]
  dsimp only
  rw [show ((UInt32.ofNat s.size).toInt32) = Int32.ofNat s.size from by
    simp [UInt32.toInt32_ofNat']]
  rw [ite_eq_right (by
    rw [Int32.lt_iff_toInt_lt, Int32.toInt_ofNat_of_lt hb, Int32.toInt_zero]
    omega)]
  rw [Int32.toNatClampNeg_ofNat_of_lt hb]
  rw [show (concatChunks pre).size + 4 =
      (concatChunks (pre ++ [putU32LE (UInt32.ofNat s.size) ByteArray.empty])).size from by
    simp [concatChunks_size]]
  rw [show concatChunks (pre ++ putU32LE (UInt32.ofNat s.size) ByteArray.empty :: (s :: post)) =
      concatChunks (pre ++ [putU32LE (UInt32.ofNat s.size) ByteArray.empty] ++ (s :: post)) from by
    simp]
  rw [getBytes?_chunk]
  rw [show (concatChunks (pre ++ [putU32LE (UInt32.ofNat s.size) ByteArray.empty])).size + s.size =
      (concatChunks pre).size + 4 + s.size from by
    rw [concatChunks_snoc_size]
    simp]
  simp only [Option.map_some]

theorem MetaEntry.parseFrom_emitFrom_raw (name : Bytes) (hn : name.size < 2 ^ 32)
    (s : Bytes) (hb : s.size < 2 ^ 31) (htn : tn.size < 2 ^ 32)
    (hunk : MetaKind.ofName? tn = none) (acc : Bytes) :
    ∃ out, MetaEntry.parseFrom
        ((⟨name, tn, .raw s⟩ : MetaEntry).emitFrom acc) acc.size =
      some (⟨name, tn, .raw s⟩, out) := by
  constructor
  unfold MetaEntry.parseFrom MetaEntry.emitFrom MetaEntry.chunks MetaEntry.valueChunks
  rw [acc_append_concatChunks]
  rw [show acc :: (putString name ByteArray.empty :: (putString tn ByteArray.empty ::
      [putU32LE (UInt32.ofNat s.size) ByteArray.empty, s])) =
      [acc] ++ putString name ByteArray.empty :: (putString tn ByteArray.empty ::
        [putU32LE (UInt32.ofNat s.size) ByteArray.empty, s]) from rfl]
  rw [show acc.size = (concatChunks [acc]).size from by simp [concatChunks]]
  rw [getString?_chunk (pre := [acc]) (s := name)
    (post := putString tn ByteArray.empty :: [putU32LE (UInt32.ofNat s.size) ByteArray.empty, s]) hn]
  dsimp only
  have h1 : (concatChunks [acc]).size + 4 + name.size =
      (concatChunks [acc, putString name ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h1]
  rw [show [acc] ++ (putString name ByteArray.empty :: (putString tn ByteArray.empty ::
      [putU32LE (UInt32.ofNat s.size) ByteArray.empty, s])) =
      [acc, putString name ByteArray.empty] ++ (putString tn ByteArray.empty ::
        [putU32LE (UInt32.ofNat s.size) ByteArray.empty, s]) from rfl]
  rw [getString?_chunk (pre := [acc, putString name ByteArray.empty]) (s := tn)
    (post := [putU32LE (UInt32.ofNat s.size) ByteArray.empty, s]) htn]
  dsimp only
  have h2 : (concatChunks [acc, putString name ByteArray.empty]).size + 4 + tn.size =
      (concatChunks [acc, putString name ByteArray.empty, putString tn ByteArray.empty]).size := by
    simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putU32LE_size, putU64LE_size, putString_size]
    omega
  rw [h2]
  rw [hunk]
  dsimp only
  rw [show concatChunks ([acc, putString name ByteArray.empty] ++
      (putString tn ByteArray.empty :: [putU32LE (UInt32.ofNat s.size) ByteArray.empty, s])) =
      concatChunks ([acc, putString name ByteArray.empty, putString tn ByteArray.empty] ++
        [putU32LE (UInt32.ofNat s.size) ByteArray.empty, s] ++ []) from by simp]
  rw [pv_raw (hb := hb)]
  simp only [Option.map_some]
  rfl


theorem MetaKind.ofName?_eq_none {tn : Bytes} (h : knownTypeName tn = false)
    (hs : tn ≠ strTypeName) : MetaKind.ofName? tn = none := by
  unfold MetaKind.ofName?
  unfold knownTypeName at h
  by_cases h1 : tn = strTypeName
  · subst h1; exact absurd rfl hs
  · by_cases h2 : tn = boolTypeName
    · subst h2; simp_all
    · by_cases h3 : tn = floatTypeName
      · subst h3; simp_all
      · by_cases h4 : tn = doubleTypeName
        · subst h4; simp_all
        · by_cases h5 : tn = int32TypeName
          · subst h5; simp_all
          · by_cases h6 : tn = int64TypeName
            · subst h6; simp_all
            · by_cases h7 : tn = vec3iTypeName
              · subst h7; simp_all
              · by_cases h8 : tn = vec3sTypeName
                · subst h8; simp_all
                · by_cases h9 : tn = vec3dTypeName
                  · subst h9; simp_all
                  · simp [h1, h2, h3, h4, h5, h6, h7, h8, h9]

theorem MetaEntry.parseFrom_emitFrom (e : MetaEntry) (hwf : e.WellFormed) (acc : Bytes) :
    ∃ out, MetaEntry.parseFrom (e.emitFrom acc) acc.size = some (e, out) := by
  obtain ⟨hty, hsz⟩ := hwf
  obtain ⟨hn, htn, hsl⟩ := hsz
  rcases e with ⟨name, tn, val⟩
  cases val with
  | «str» s =>
    simp only [MetaEntry.TypeOK] at hty
    subst hty
    exact MetaEntry.parseFrom_emitFrom_str name hn s hsl acc
  | boolean b =>
    simp only [MetaEntry.TypeOK] at hty
    subst hty
    exact MetaEntry.parseFrom_emitFrom_bool name hn b acc
  | int32 v =>
    simp only [MetaEntry.TypeOK] at hty
    subst hty
    exact MetaEntry.parseFrom_emitFrom_int32 name hn v acc
  | int64 v =>
    simp only [MetaEntry.TypeOK] at hty
    subst hty
    exact MetaEntry.parseFrom_emitFrom_int64 name hn v acc
  | f32 v =>
    simp only [MetaEntry.TypeOK] at hty
    subst hty
    exact MetaEntry.parseFrom_emitFrom_f32 name hn v acc
  | f64 v =>
    simp only [MetaEntry.TypeOK] at hty
    subst hty
    exact MetaEntry.parseFrom_emitFrom_f64 name hn v acc
  | vec3i x y z =>
    simp only [MetaEntry.TypeOK] at hty
    subst hty
    exact MetaEntry.parseFrom_emitFrom_vec3i name hn x y z acc
  | vec3f x y z =>
    simp only [MetaEntry.TypeOK] at hty
    subst hty
    exact MetaEntry.parseFrom_emitFrom_vec3f name hn x y z acc
  | vec3d x y z =>
    simp only [MetaEntry.TypeOK] at hty
    subst hty
    exact MetaEntry.parseFrom_emitFrom_vec3d name hn x y z acc
  | raw s =>
    simp only [MetaEntry.TypeOK] at hty
    obtain ⟨htyk, hstr⟩ := hty
    have hsl' : s.size < 2 ^ 31 := hsl
    exact MetaEntry.parseFrom_emitFrom_raw name hn s hsl' htn
      (MetaKind.ofName?_eq_none htyk hstr) acc



/-! ### Metadata lists -/

/-- A metadata list: an `i32` count followed by that many entries. The C
    reader accepts counts in `0..4096`. -/
structure MetaList where
  entries : List MetaEntry
  deriving Repr

/-- The list's wire chunks. -/
def MetaList.chunks (m : MetaList) : List Bytes :=
  putI32LE (Int32.ofNat m.entries.length) ByteArray.empty ::
    m.entries.flatMap MetaEntry.chunks

/-- Emit a metadata list after `acc`. -/
def MetaList.emitFrom (m : MetaList) (acc : Bytes) : Bytes :=
  acc ++ concatChunks m.chunks

/-- Emit a metadata list. -/
def MetaList.emit (m : MetaList) : Bytes := m.emitFrom ByteArray.empty

/-- Read `n` entries in sequence. -/
def parseEntries : Nat → Bytes → Nat → Option (List MetaEntry × Nat)
  | 0, _, off => some ([], off)
  | n + 1, b, off =>
    match MetaEntry.parseFrom b off with
    | none => none
    | some (e, o) =>
      match parseEntries n b o with
      | none => none
      | some (es, o') => some (e :: es, o')

/-- Parse a metadata list at `off`. -/
def MetaList.parseFrom (b : Bytes) (off : Nat) : Option (MetaList × Nat) :=
  match getI32LE b off with
  | none => none
  | some count =>
    if count < 0 then none
    else
      match parseEntries count.toNatClampNeg b (off + 4) with
      | none => none
      | some (es, o) => some (⟨es⟩, o)

theorem MetaEntry.parseFromChunks_bool (pre : List Bytes) (name : Bytes) (hn : name.size < 2 ^ 32)
    (b : Bool) (rest : List Bytes) :
    MetaEntry.parseFrom
      (concatChunks (pre ++ (putString name ByteArray.empty :: (putString boolTypeName ByteArray.empty ::
        ([putU32LE 1 ByteArray.empty, putU8 (if b then 1 else 0) ByteArray.empty] ++ rest)))))
      (concatChunks pre).size =
      some ((⟨name, boolTypeName, .boolean b⟩ : MetaEntry), (concatChunks pre).size + ((⟨name, boolTypeName, .boolean b⟩ : MetaEntry).chunks.map (·.size)).sum) := by
  unfold MetaEntry.parseFrom MetaEntry.chunks MetaEntry.valueChunks
  dsimp only
  rw [getString?_chunk (pre := pre) (s := name)
    (post := putString boolTypeName ByteArray.empty :: ([putU32LE 1 ByteArray.empty, putU8 (if b then 1 else 0) ByteArray.empty] ++ rest)) hn]
  dsimp only
  have h1 : (concatChunks pre).size + 4 + name.size =
      (concatChunks (pre ++ [putString name ByteArray.empty])).size := by
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h1]
  rw [show concatChunks (pre ++ (putString name ByteArray.empty :: (putString boolTypeName ByteArray.empty ::
      ([putU32LE 1 ByteArray.empty, putU8 (if b then 1 else 0) ByteArray.empty] ++ rest)))) =
      concatChunks ((pre ++ [putString name ByteArray.empty]) ++ (putString boolTypeName ByteArray.empty ::
      ([putU32LE 1 ByteArray.empty, putU8 (if b then 1 else 0) ByteArray.empty] ++ rest))) from by simp]
  rw [getString?_chunk (pre := pre ++ [putString name ByteArray.empty]) (s := boolTypeName)
    (post := [putU32LE 1 ByteArray.empty, putU8 (if b then 1 else 0) ByteArray.empty] ++ rest) (by decide)]
  dsimp only
  have h2 : (concatChunks (pre ++ [putString name ByteArray.empty])).size + 4 + boolTypeName.size =
      (concatChunks (pre ++ [putString name ByteArray.empty,
        putString boolTypeName ByteArray.empty])).size := by
    rw [← h1]
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h2]
  rw [MetaKind.ofName_bool]
  dsimp only
  rw [show concatChunks ((pre ++ [putString name ByteArray.empty]) ++
      (putString boolTypeName ByteArray.empty :: ([putU32LE 1 ByteArray.empty, putU8 (if b then 1 else 0) ByteArray.empty] ++ rest))) =
      concatChunks (((pre ++ [putString name ByteArray.empty, putString boolTypeName ByteArray.empty]) ++
      [putU32LE 1 ByteArray.empty, putU8 (if b then 1 else 0) ByteArray.empty]) ++ rest) from by simp]
  rw [pv_bool]
  simp only [Option.map_some]
  simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putString_size, putU32LE_size, putI32LE_size, putI64LE_size, putU64LE_size]
  omega

theorem MetaEntry.parseFromChunks_int32 (pre : List Bytes) (name : Bytes) (hn : name.size < 2 ^ 32)
    (v : Int32) (rest : List Bytes) :
    MetaEntry.parseFrom
      (concatChunks (pre ++ (putString name ByteArray.empty :: (putString int32TypeName ByteArray.empty ::
        ([putU32LE 4 ByteArray.empty, putI32LE v ByteArray.empty] ++ rest)))))
      (concatChunks pre).size =
      some ((⟨name, int32TypeName, .int32 v⟩ : MetaEntry), (concatChunks pre).size + ((⟨name, int32TypeName, .int32 v⟩ : MetaEntry).chunks.map (·.size)).sum) := by
  unfold MetaEntry.parseFrom MetaEntry.chunks MetaEntry.valueChunks
  dsimp only
  rw [getString?_chunk (pre := pre) (s := name)
    (post := putString int32TypeName ByteArray.empty :: ([putU32LE 4 ByteArray.empty, putI32LE v ByteArray.empty] ++ rest)) hn]
  dsimp only
  have h1 : (concatChunks pre).size + 4 + name.size =
      (concatChunks (pre ++ [putString name ByteArray.empty])).size := by
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h1]
  rw [show concatChunks (pre ++ (putString name ByteArray.empty :: (putString int32TypeName ByteArray.empty ::
      ([putU32LE 4 ByteArray.empty, putI32LE v ByteArray.empty] ++ rest)))) =
      concatChunks ((pre ++ [putString name ByteArray.empty]) ++ (putString int32TypeName ByteArray.empty ::
      ([putU32LE 4 ByteArray.empty, putI32LE v ByteArray.empty] ++ rest))) from by simp]
  rw [getString?_chunk (pre := pre ++ [putString name ByteArray.empty]) (s := int32TypeName)
    (post := [putU32LE 4 ByteArray.empty, putI32LE v ByteArray.empty] ++ rest) (by decide)]
  dsimp only
  have h2 : (concatChunks (pre ++ [putString name ByteArray.empty])).size + 4 + int32TypeName.size =
      (concatChunks (pre ++ [putString name ByteArray.empty,
        putString int32TypeName ByteArray.empty])).size := by
    rw [← h1]
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h2]
  rw [MetaKind.ofName_int32]
  dsimp only
  rw [show concatChunks ((pre ++ [putString name ByteArray.empty]) ++
      (putString int32TypeName ByteArray.empty :: ([putU32LE 4 ByteArray.empty, putI32LE v ByteArray.empty] ++ rest))) =
      concatChunks (((pre ++ [putString name ByteArray.empty, putString int32TypeName ByteArray.empty]) ++
      [putU32LE 4 ByteArray.empty, putI32LE v ByteArray.empty]) ++ rest) from by simp]
  rw [pv_int32]
  simp only [Option.map_some]
  simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putString_size, putU32LE_size, putI32LE_size, putI64LE_size, putU64LE_size]
  omega

theorem MetaEntry.parseFromChunks_int64 (pre : List Bytes) (name : Bytes) (hn : name.size < 2 ^ 32)
    (v : Int64) (rest : List Bytes) :
    MetaEntry.parseFrom
      (concatChunks (pre ++ (putString name ByteArray.empty :: (putString int64TypeName ByteArray.empty ::
        ([putU32LE 8 ByteArray.empty, putI64LE v ByteArray.empty] ++ rest)))))
      (concatChunks pre).size =
      some ((⟨name, int64TypeName, .int64 v⟩ : MetaEntry), (concatChunks pre).size + ((⟨name, int64TypeName, .int64 v⟩ : MetaEntry).chunks.map (·.size)).sum) := by
  unfold MetaEntry.parseFrom MetaEntry.chunks MetaEntry.valueChunks
  dsimp only
  rw [getString?_chunk (pre := pre) (s := name)
    (post := putString int64TypeName ByteArray.empty :: ([putU32LE 8 ByteArray.empty, putI64LE v ByteArray.empty] ++ rest)) hn]
  dsimp only
  have h1 : (concatChunks pre).size + 4 + name.size =
      (concatChunks (pre ++ [putString name ByteArray.empty])).size := by
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h1]
  rw [show concatChunks (pre ++ (putString name ByteArray.empty :: (putString int64TypeName ByteArray.empty ::
      ([putU32LE 8 ByteArray.empty, putI64LE v ByteArray.empty] ++ rest)))) =
      concatChunks ((pre ++ [putString name ByteArray.empty]) ++ (putString int64TypeName ByteArray.empty ::
      ([putU32LE 8 ByteArray.empty, putI64LE v ByteArray.empty] ++ rest))) from by simp]
  rw [getString?_chunk (pre := pre ++ [putString name ByteArray.empty]) (s := int64TypeName)
    (post := [putU32LE 8 ByteArray.empty, putI64LE v ByteArray.empty] ++ rest) (by decide)]
  dsimp only
  have h2 : (concatChunks (pre ++ [putString name ByteArray.empty])).size + 4 + int64TypeName.size =
      (concatChunks (pre ++ [putString name ByteArray.empty,
        putString int64TypeName ByteArray.empty])).size := by
    rw [← h1]
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h2]
  rw [MetaKind.ofName_int64]
  dsimp only
  rw [show concatChunks ((pre ++ [putString name ByteArray.empty]) ++
      (putString int64TypeName ByteArray.empty :: ([putU32LE 8 ByteArray.empty, putI64LE v ByteArray.empty] ++ rest))) =
      concatChunks (((pre ++ [putString name ByteArray.empty, putString int64TypeName ByteArray.empty]) ++
      [putU32LE 8 ByteArray.empty, putI64LE v ByteArray.empty]) ++ rest) from by simp]
  rw [pv_int64]
  simp only [Option.map_some]
  simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putString_size, putU32LE_size, putI32LE_size, putI64LE_size, putU64LE_size]
  omega

theorem MetaEntry.parseFromChunks_f32 (pre : List Bytes) (name : Bytes) (hn : name.size < 2 ^ 32)
    (v : UInt32) (rest : List Bytes) :
    MetaEntry.parseFrom
      (concatChunks (pre ++ (putString name ByteArray.empty :: (putString floatTypeName ByteArray.empty ::
        ([putU32LE 4 ByteArray.empty, putU32LE v ByteArray.empty] ++ rest)))))
      (concatChunks pre).size =
      some ((⟨name, floatTypeName, .f32 v⟩ : MetaEntry), (concatChunks pre).size + ((⟨name, floatTypeName, .f32 v⟩ : MetaEntry).chunks.map (·.size)).sum) := by
  unfold MetaEntry.parseFrom MetaEntry.chunks MetaEntry.valueChunks
  dsimp only
  rw [getString?_chunk (pre := pre) (s := name)
    (post := putString floatTypeName ByteArray.empty :: ([putU32LE 4 ByteArray.empty, putU32LE v ByteArray.empty] ++ rest)) hn]
  dsimp only
  have h1 : (concatChunks pre).size + 4 + name.size =
      (concatChunks (pre ++ [putString name ByteArray.empty])).size := by
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h1]
  rw [show concatChunks (pre ++ (putString name ByteArray.empty :: (putString floatTypeName ByteArray.empty ::
      ([putU32LE 4 ByteArray.empty, putU32LE v ByteArray.empty] ++ rest)))) =
      concatChunks ((pre ++ [putString name ByteArray.empty]) ++ (putString floatTypeName ByteArray.empty ::
      ([putU32LE 4 ByteArray.empty, putU32LE v ByteArray.empty] ++ rest))) from by simp]
  rw [getString?_chunk (pre := pre ++ [putString name ByteArray.empty]) (s := floatTypeName)
    (post := [putU32LE 4 ByteArray.empty, putU32LE v ByteArray.empty] ++ rest) (by decide)]
  dsimp only
  have h2 : (concatChunks (pre ++ [putString name ByteArray.empty])).size + 4 + floatTypeName.size =
      (concatChunks (pre ++ [putString name ByteArray.empty,
        putString floatTypeName ByteArray.empty])).size := by
    rw [← h1]
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h2]
  rw [MetaKind.ofName_float]
  dsimp only
  rw [show concatChunks ((pre ++ [putString name ByteArray.empty]) ++
      (putString floatTypeName ByteArray.empty :: ([putU32LE 4 ByteArray.empty, putU32LE v ByteArray.empty] ++ rest))) =
      concatChunks (((pre ++ [putString name ByteArray.empty, putString floatTypeName ByteArray.empty]) ++
      [putU32LE 4 ByteArray.empty, putU32LE v ByteArray.empty]) ++ rest) from by simp]
  rw [pv_f32]
  simp only [Option.map_some]
  simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putString_size, putU32LE_size, putI32LE_size, putI64LE_size, putU64LE_size]
  omega

theorem MetaEntry.parseFromChunks_f64 (pre : List Bytes) (name : Bytes) (hn : name.size < 2 ^ 32)
    (v : UInt64) (rest : List Bytes) :
    MetaEntry.parseFrom
      (concatChunks (pre ++ (putString name ByteArray.empty :: (putString doubleTypeName ByteArray.empty ::
        ([putU32LE 8 ByteArray.empty, putU64LE v ByteArray.empty] ++ rest)))))
      (concatChunks pre).size =
      some ((⟨name, doubleTypeName, .f64 v⟩ : MetaEntry), (concatChunks pre).size + ((⟨name, doubleTypeName, .f64 v⟩ : MetaEntry).chunks.map (·.size)).sum) := by
  unfold MetaEntry.parseFrom MetaEntry.chunks MetaEntry.valueChunks
  dsimp only
  rw [getString?_chunk (pre := pre) (s := name)
    (post := putString doubleTypeName ByteArray.empty :: ([putU32LE 8 ByteArray.empty, putU64LE v ByteArray.empty] ++ rest)) hn]
  dsimp only
  have h1 : (concatChunks pre).size + 4 + name.size =
      (concatChunks (pre ++ [putString name ByteArray.empty])).size := by
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h1]
  rw [show concatChunks (pre ++ (putString name ByteArray.empty :: (putString doubleTypeName ByteArray.empty ::
      ([putU32LE 8 ByteArray.empty, putU64LE v ByteArray.empty] ++ rest)))) =
      concatChunks ((pre ++ [putString name ByteArray.empty]) ++ (putString doubleTypeName ByteArray.empty ::
      ([putU32LE 8 ByteArray.empty, putU64LE v ByteArray.empty] ++ rest))) from by simp]
  rw [getString?_chunk (pre := pre ++ [putString name ByteArray.empty]) (s := doubleTypeName)
    (post := [putU32LE 8 ByteArray.empty, putU64LE v ByteArray.empty] ++ rest) (by decide)]
  dsimp only
  have h2 : (concatChunks (pre ++ [putString name ByteArray.empty])).size + 4 + doubleTypeName.size =
      (concatChunks (pre ++ [putString name ByteArray.empty,
        putString doubleTypeName ByteArray.empty])).size := by
    rw [← h1]
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h2]
  rw [MetaKind.ofName_double]
  dsimp only
  rw [show concatChunks ((pre ++ [putString name ByteArray.empty]) ++
      (putString doubleTypeName ByteArray.empty :: ([putU32LE 8 ByteArray.empty, putU64LE v ByteArray.empty] ++ rest))) =
      concatChunks (((pre ++ [putString name ByteArray.empty, putString doubleTypeName ByteArray.empty]) ++
      [putU32LE 8 ByteArray.empty, putU64LE v ByteArray.empty]) ++ rest) from by simp]
  rw [pv_f64]
  simp only [Option.map_some]
  simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putString_size, putU32LE_size, putI32LE_size, putI64LE_size, putU64LE_size]
  omega

theorem MetaEntry.parseFromChunks_vec3i (pre : List Bytes) (name : Bytes) (hn : name.size < 2 ^ 32)
    (x y z : Int32) (rest : List Bytes) :
    MetaEntry.parseFrom
      (concatChunks (pre ++ (putString name ByteArray.empty :: (putString vec3iTypeName ByteArray.empty ::
        ([putU32LE 12 ByteArray.empty, putI32LE x ByteArray.empty, putI32LE y ByteArray.empty, putI32LE z ByteArray.empty] ++ rest)))))
      (concatChunks pre).size =
      some ((⟨name, vec3iTypeName, .vec3i x y z⟩ : MetaEntry), (concatChunks pre).size + ((⟨name, vec3iTypeName, .vec3i x y z⟩ : MetaEntry).chunks.map (·.size)).sum) := by
  unfold MetaEntry.parseFrom MetaEntry.chunks MetaEntry.valueChunks
  dsimp only
  rw [getString?_chunk (pre := pre) (s := name)
    (post := putString vec3iTypeName ByteArray.empty :: ([putU32LE 12 ByteArray.empty, putI32LE x ByteArray.empty, putI32LE y ByteArray.empty, putI32LE z ByteArray.empty] ++ rest)) hn]
  dsimp only
  have h1 : (concatChunks pre).size + 4 + name.size =
      (concatChunks (pre ++ [putString name ByteArray.empty])).size := by
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h1]
  rw [show concatChunks (pre ++ (putString name ByteArray.empty :: (putString vec3iTypeName ByteArray.empty ::
      ([putU32LE 12 ByteArray.empty, putI32LE x ByteArray.empty, putI32LE y ByteArray.empty, putI32LE z ByteArray.empty] ++ rest)))) =
      concatChunks ((pre ++ [putString name ByteArray.empty]) ++ (putString vec3iTypeName ByteArray.empty ::
      ([putU32LE 12 ByteArray.empty, putI32LE x ByteArray.empty, putI32LE y ByteArray.empty, putI32LE z ByteArray.empty] ++ rest))) from by simp]
  rw [getString?_chunk (pre := pre ++ [putString name ByteArray.empty]) (s := vec3iTypeName)
    (post := [putU32LE 12 ByteArray.empty, putI32LE x ByteArray.empty, putI32LE y ByteArray.empty, putI32LE z ByteArray.empty] ++ rest) (by decide)]
  dsimp only
  have h2 : (concatChunks (pre ++ [putString name ByteArray.empty])).size + 4 + vec3iTypeName.size =
      (concatChunks (pre ++ [putString name ByteArray.empty,
        putString vec3iTypeName ByteArray.empty])).size := by
    rw [← h1]
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h2]
  rw [MetaKind.ofName_vec3i]
  dsimp only
  rw [show concatChunks ((pre ++ [putString name ByteArray.empty]) ++
      (putString vec3iTypeName ByteArray.empty :: ([putU32LE 12 ByteArray.empty, putI32LE x ByteArray.empty, putI32LE y ByteArray.empty, putI32LE z ByteArray.empty] ++ rest))) =
      concatChunks (((pre ++ [putString name ByteArray.empty, putString vec3iTypeName ByteArray.empty]) ++
      [putU32LE 12 ByteArray.empty, putI32LE x ByteArray.empty, putI32LE y ByteArray.empty, putI32LE z ByteArray.empty]) ++ rest) from by simp]
  rw [pv_vec3i]
  simp only [Option.map_some]
  simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putString_size, putU32LE_size, putI32LE_size, putI64LE_size, putU64LE_size]
  omega

theorem MetaEntry.parseFromChunks_vec3f (pre : List Bytes) (name : Bytes) (hn : name.size < 2 ^ 32)
    (x y z : UInt32) (rest : List Bytes) :
    MetaEntry.parseFrom
      (concatChunks (pre ++ (putString name ByteArray.empty :: (putString vec3sTypeName ByteArray.empty ::
        ([putU32LE 12 ByteArray.empty, putU32LE x ByteArray.empty, putU32LE y ByteArray.empty, putU32LE z ByteArray.empty] ++ rest)))))
      (concatChunks pre).size =
      some ((⟨name, vec3sTypeName, .vec3f x y z⟩ : MetaEntry), (concatChunks pre).size + ((⟨name, vec3sTypeName, .vec3f x y z⟩ : MetaEntry).chunks.map (·.size)).sum) := by
  unfold MetaEntry.parseFrom MetaEntry.chunks MetaEntry.valueChunks
  dsimp only
  rw [getString?_chunk (pre := pre) (s := name)
    (post := putString vec3sTypeName ByteArray.empty :: ([putU32LE 12 ByteArray.empty, putU32LE x ByteArray.empty, putU32LE y ByteArray.empty, putU32LE z ByteArray.empty] ++ rest)) hn]
  dsimp only
  have h1 : (concatChunks pre).size + 4 + name.size =
      (concatChunks (pre ++ [putString name ByteArray.empty])).size := by
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h1]
  rw [show concatChunks (pre ++ (putString name ByteArray.empty :: (putString vec3sTypeName ByteArray.empty ::
      ([putU32LE 12 ByteArray.empty, putU32LE x ByteArray.empty, putU32LE y ByteArray.empty, putU32LE z ByteArray.empty] ++ rest)))) =
      concatChunks ((pre ++ [putString name ByteArray.empty]) ++ (putString vec3sTypeName ByteArray.empty ::
      ([putU32LE 12 ByteArray.empty, putU32LE x ByteArray.empty, putU32LE y ByteArray.empty, putU32LE z ByteArray.empty] ++ rest))) from by simp]
  rw [getString?_chunk (pre := pre ++ [putString name ByteArray.empty]) (s := vec3sTypeName)
    (post := [putU32LE 12 ByteArray.empty, putU32LE x ByteArray.empty, putU32LE y ByteArray.empty, putU32LE z ByteArray.empty] ++ rest) (by decide)]
  dsimp only
  have h2 : (concatChunks (pre ++ [putString name ByteArray.empty])).size + 4 + vec3sTypeName.size =
      (concatChunks (pre ++ [putString name ByteArray.empty,
        putString vec3sTypeName ByteArray.empty])).size := by
    rw [← h1]
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h2]
  rw [MetaKind.ofName_vec3s]
  dsimp only
  rw [show concatChunks ((pre ++ [putString name ByteArray.empty]) ++
      (putString vec3sTypeName ByteArray.empty :: ([putU32LE 12 ByteArray.empty, putU32LE x ByteArray.empty, putU32LE y ByteArray.empty, putU32LE z ByteArray.empty] ++ rest))) =
      concatChunks (((pre ++ [putString name ByteArray.empty, putString vec3sTypeName ByteArray.empty]) ++
      [putU32LE 12 ByteArray.empty, putU32LE x ByteArray.empty, putU32LE y ByteArray.empty, putU32LE z ByteArray.empty]) ++ rest) from by simp]
  rw [pv_vec3f]
  simp only [Option.map_some]
  simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putString_size, putU32LE_size, putI32LE_size, putI64LE_size, putU64LE_size]
  omega

theorem MetaEntry.parseFromChunks_vec3d (pre : List Bytes) (name : Bytes) (hn : name.size < 2 ^ 32)
    (x y z : UInt64) (rest : List Bytes) :
    MetaEntry.parseFrom
      (concatChunks (pre ++ (putString name ByteArray.empty :: (putString vec3dTypeName ByteArray.empty ::
        ([putU32LE 24 ByteArray.empty, putU64LE x ByteArray.empty, putU64LE y ByteArray.empty, putU64LE z ByteArray.empty] ++ rest)))))
      (concatChunks pre).size =
      some ((⟨name, vec3dTypeName, .vec3d x y z⟩ : MetaEntry), (concatChunks pre).size + ((⟨name, vec3dTypeName, .vec3d x y z⟩ : MetaEntry).chunks.map (·.size)).sum) := by
  unfold MetaEntry.parseFrom MetaEntry.chunks MetaEntry.valueChunks
  dsimp only
  rw [getString?_chunk (pre := pre) (s := name)
    (post := putString vec3dTypeName ByteArray.empty :: ([putU32LE 24 ByteArray.empty, putU64LE x ByteArray.empty, putU64LE y ByteArray.empty, putU64LE z ByteArray.empty] ++ rest)) hn]
  dsimp only
  have h1 : (concatChunks pre).size + 4 + name.size =
      (concatChunks (pre ++ [putString name ByteArray.empty])).size := by
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h1]
  rw [show concatChunks (pre ++ (putString name ByteArray.empty :: (putString vec3dTypeName ByteArray.empty ::
      ([putU32LE 24 ByteArray.empty, putU64LE x ByteArray.empty, putU64LE y ByteArray.empty, putU64LE z ByteArray.empty] ++ rest)))) =
      concatChunks ((pre ++ [putString name ByteArray.empty]) ++ (putString vec3dTypeName ByteArray.empty ::
      ([putU32LE 24 ByteArray.empty, putU64LE x ByteArray.empty, putU64LE y ByteArray.empty, putU64LE z ByteArray.empty] ++ rest))) from by simp]
  rw [getString?_chunk (pre := pre ++ [putString name ByteArray.empty]) (s := vec3dTypeName)
    (post := [putU32LE 24 ByteArray.empty, putU64LE x ByteArray.empty, putU64LE y ByteArray.empty, putU64LE z ByteArray.empty] ++ rest) (by decide)]
  dsimp only
  have h2 : (concatChunks (pre ++ [putString name ByteArray.empty])).size + 4 + vec3dTypeName.size =
      (concatChunks (pre ++ [putString name ByteArray.empty,
        putString vec3dTypeName ByteArray.empty])).size := by
    rw [← h1]
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h2]
  rw [MetaKind.ofName_vec3d]
  dsimp only
  rw [show concatChunks ((pre ++ [putString name ByteArray.empty]) ++
      (putString vec3dTypeName ByteArray.empty :: ([putU32LE 24 ByteArray.empty, putU64LE x ByteArray.empty, putU64LE y ByteArray.empty, putU64LE z ByteArray.empty] ++ rest))) =
      concatChunks (((pre ++ [putString name ByteArray.empty, putString vec3dTypeName ByteArray.empty]) ++
      [putU32LE 24 ByteArray.empty, putU64LE x ByteArray.empty, putU64LE y ByteArray.empty, putU64LE z ByteArray.empty]) ++ rest) from by simp]
  rw [pv_vec3d]
  simp only [Option.map_some]
  simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putString_size, putU32LE_size, putI32LE_size, putI64LE_size, putU64LE_size]
  omega

theorem MetaEntry.parseFromChunks_str (pre : List Bytes) (name : Bytes) (hn : name.size < 2 ^ 32)
    (payload : Bytes) (hp : payload.size < 2 ^ 32) (rest : List Bytes) :
    MetaEntry.parseFrom
      (concatChunks (pre ++ (putString name ByteArray.empty :: (putString strTypeName ByteArray.empty ::
        ([putString payload ByteArray.empty] ++ rest)))))
      (concatChunks pre).size =
      some ((⟨name, strTypeName, .str payload⟩ : MetaEntry), (concatChunks pre).size + ((⟨name, strTypeName, .str payload⟩ : MetaEntry).chunks.map (·.size)).sum) := by
  unfold MetaEntry.parseFrom MetaEntry.chunks MetaEntry.valueChunks
  dsimp only
  rw [getString?_chunk (pre := pre) (s := name)
    (post := putString strTypeName ByteArray.empty :: ([putString payload ByteArray.empty] ++ rest)) hn]
  dsimp only
  have h1 : (concatChunks pre).size + 4 + name.size =
      (concatChunks (pre ++ [putString name ByteArray.empty])).size := by
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h1]
  rw [show concatChunks (pre ++ (putString name ByteArray.empty :: (putString strTypeName ByteArray.empty ::
      ([putString payload ByteArray.empty] ++ rest)))) =
      concatChunks ((pre ++ [putString name ByteArray.empty]) ++ (putString strTypeName ByteArray.empty ::
      ([putString payload ByteArray.empty] ++ rest))) from by simp]
  rw [getString?_chunk (pre := pre ++ [putString name ByteArray.empty]) (s := strTypeName)
    (post := [putString payload ByteArray.empty] ++ rest) (by decide)]
  dsimp only
  have h2 : (concatChunks (pre ++ [putString name ByteArray.empty])).size + 4 + strTypeName.size =
      (concatChunks (pre ++ [putString name ByteArray.empty,
        putString strTypeName ByteArray.empty])).size := by
    rw [← h1]
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h2]
  rw [MetaKind.ofName_str]
  dsimp only
  rw [show concatChunks ((pre ++ [putString name ByteArray.empty]) ++
      (putString strTypeName ByteArray.empty :: ([putString payload ByteArray.empty] ++ rest))) =
      concatChunks ((pre ++ [putString name ByteArray.empty, putString strTypeName ByteArray.empty]) ++
      (putString payload ByteArray.empty :: rest)) from by simp]
  rw [getString?_chunk (pre := pre ++ [putString name ByteArray.empty,
      putString strTypeName ByteArray.empty]) (s := payload) (post := rest) hp]
  simp only [Option.map_some]
  simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putString_size, putU32LE_size, putI32LE_size, putI64LE_size, putU64LE_size]
  omega

theorem MetaEntry.parseFromChunks_raw (pre : List Bytes) (name : Bytes) (hn : name.size < 2 ^ 32)
    (s : Bytes) (hb : s.size < 2 ^ 31) (htn : tn.size < 2 ^ 32)
    (hunk : MetaKind.ofName? tn = none) (rest : List Bytes) :
    MetaEntry.parseFrom
      (concatChunks (pre ++ (putString name ByteArray.empty :: (putString tn ByteArray.empty ::
        ([putU32LE (UInt32.ofNat s.size) ByteArray.empty, s] ++ rest)))))
      (concatChunks pre).size =
      some ((⟨name, tn, .raw s⟩ : MetaEntry), (concatChunks pre).size + ((⟨name, tn, .raw s⟩ : MetaEntry).chunks.map (·.size)).sum) := by
  unfold MetaEntry.parseFrom MetaEntry.chunks MetaEntry.valueChunks
  dsimp only
  rw [getString?_chunk (pre := pre) (s := name)
    (post := putString tn ByteArray.empty :: ([putU32LE (UInt32.ofNat s.size) ByteArray.empty, s] ++ rest)) hn]
  dsimp only
  have h1 : (concatChunks pre).size + 4 + name.size =
      (concatChunks (pre ++ [putString name ByteArray.empty])).size := by
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h1]
  rw [show concatChunks (pre ++ (putString name ByteArray.empty :: (putString tn ByteArray.empty ::
      ([putU32LE (UInt32.ofNat s.size) ByteArray.empty, s] ++ rest)))) =
      concatChunks ((pre ++ [putString name ByteArray.empty]) ++ (putString tn ByteArray.empty ::
      ([putU32LE (UInt32.ofNat s.size) ByteArray.empty, s] ++ rest))) from by simp]
  rw [getString?_chunk (pre := pre ++ [putString name ByteArray.empty]) (s := tn)
    (post := [putU32LE (UInt32.ofNat s.size) ByteArray.empty, s] ++ rest) htn]
  dsimp only
  have h2 : (concatChunks (pre ++ [putString name ByteArray.empty])).size + 4 + tn.size =
      (concatChunks (pre ++ [putString name ByteArray.empty,
        putString tn ByteArray.empty])).size := by
    rw [← h1]
    conv_rhs => rw [concatChunks_append_map]
    simp [putString_size]; omega
  rw [h2]
  rw [hunk]
  dsimp only
  rw [show concatChunks ((pre ++ [putString name ByteArray.empty]) ++
      (putString tn ByteArray.empty :: ([putU32LE (UInt32.ofNat s.size) ByteArray.empty, s] ++ rest))) =
      concatChunks (((pre ++ [putString name ByteArray.empty, putString tn ByteArray.empty]) ++
      [putU32LE (UInt32.ofNat s.size) ByteArray.empty, s]) ++ rest) from by simp]
  rw [pv_raw (hb := hb)]
  simp only [Option.map_some]
  simp [concatChunks_append_size, concatChunks_cons_size, concatChunks_singleton, concatChunks_nil_size, putString_size, putU32LE_size, putI32LE_size, putI64LE_size, putU64LE_size]
  omega

theorem MetaEntry.parseFromChunks (e : MetaEntry) (hwf : e.WellFormed)
    (pre rest : List Bytes) :
    MetaEntry.parseFrom (concatChunks (pre ++ e.chunks ++ rest)) (concatChunks pre).size =
      some (e, (concatChunks pre).size + (e.chunks.map (·.size)).sum) := by
  obtain ⟨hty, hsz⟩ := hwf
  obtain ⟨hn, htn, hsl⟩ := hsz
  rcases e with ⟨name, tn, val⟩
  cases val with
  | «str» s =>
    simp only [MetaEntry.TypeOK] at hty
    subst hty
    rw [show concatChunks (pre ++ (⟨name, strTypeName, .str s⟩ : MetaEntry).chunks ++ rest) =
        concatChunks (pre ++ (putString name ByteArray.empty :: (putString strTypeName ByteArray.empty ::
          ([putString s ByteArray.empty] ++ rest)))) from by simp [MetaEntry.chunks, MetaEntry.valueChunks]]
    exact MetaEntry.parseFromChunks_str pre name hn s hsl rest
  | boolean b =>
    simp only [MetaEntry.TypeOK] at hty
    subst hty
    rw [show concatChunks (pre ++ (⟨name, boolTypeName, .boolean b⟩ : MetaEntry).chunks ++ rest) =
        concatChunks (pre ++ (putString name ByteArray.empty :: (putString boolTypeName ByteArray.empty ::
          ([putU32LE 1 ByteArray.empty, putU8 (if b then 1 else 0) ByteArray.empty] ++ rest)))) from by simp [MetaEntry.chunks, MetaEntry.valueChunks]]
    exact MetaEntry.parseFromChunks_bool pre name hn b rest
  | int32 v =>
    simp only [MetaEntry.TypeOK] at hty
    subst hty
    rw [show concatChunks (pre ++ (⟨name, int32TypeName, .int32 v⟩ : MetaEntry).chunks ++ rest) =
        concatChunks (pre ++ (putString name ByteArray.empty :: (putString int32TypeName ByteArray.empty ::
          ([putU32LE 4 ByteArray.empty, putI32LE v ByteArray.empty] ++ rest)))) from by simp [MetaEntry.chunks, MetaEntry.valueChunks]]
    exact MetaEntry.parseFromChunks_int32 pre name hn v rest
  | int64 v =>
    simp only [MetaEntry.TypeOK] at hty
    subst hty
    rw [show concatChunks (pre ++ (⟨name, int64TypeName, .int64 v⟩ : MetaEntry).chunks ++ rest) =
        concatChunks (pre ++ (putString name ByteArray.empty :: (putString int64TypeName ByteArray.empty ::
          ([putU32LE 8 ByteArray.empty, putI64LE v ByteArray.empty] ++ rest)))) from by simp [MetaEntry.chunks, MetaEntry.valueChunks]]
    exact MetaEntry.parseFromChunks_int64 pre name hn v rest
  | f32 v =>
    simp only [MetaEntry.TypeOK] at hty
    subst hty
    rw [show concatChunks (pre ++ (⟨name, floatTypeName, .f32 v⟩ : MetaEntry).chunks ++ rest) =
        concatChunks (pre ++ (putString name ByteArray.empty :: (putString floatTypeName ByteArray.empty ::
          ([putU32LE 4 ByteArray.empty, putU32LE v ByteArray.empty] ++ rest)))) from by simp [MetaEntry.chunks, MetaEntry.valueChunks]]
    exact MetaEntry.parseFromChunks_f32 pre name hn v rest
  | f64 v =>
    simp only [MetaEntry.TypeOK] at hty
    subst hty
    rw [show concatChunks (pre ++ (⟨name, doubleTypeName, .f64 v⟩ : MetaEntry).chunks ++ rest) =
        concatChunks (pre ++ (putString name ByteArray.empty :: (putString doubleTypeName ByteArray.empty ::
          ([putU32LE 8 ByteArray.empty, putU64LE v ByteArray.empty] ++ rest)))) from by simp [MetaEntry.chunks, MetaEntry.valueChunks]]
    exact MetaEntry.parseFromChunks_f64 pre name hn v rest
  | vec3i x y z =>
    simp only [MetaEntry.TypeOK] at hty
    subst hty
    rw [show concatChunks (pre ++ (⟨name, vec3iTypeName, .vec3i x y z⟩ : MetaEntry).chunks ++ rest) =
        concatChunks (pre ++ (putString name ByteArray.empty :: (putString vec3iTypeName ByteArray.empty ::
          ([putU32LE 12 ByteArray.empty, putI32LE x ByteArray.empty, putI32LE y ByteArray.empty,
            putI32LE z ByteArray.empty] ++ rest)))) from by simp [MetaEntry.chunks, MetaEntry.valueChunks]]
    exact MetaEntry.parseFromChunks_vec3i pre name hn x y z rest
  | vec3f x y z =>
    simp only [MetaEntry.TypeOK] at hty
    subst hty
    rw [show concatChunks (pre ++ (⟨name, vec3sTypeName, .vec3f x y z⟩ : MetaEntry).chunks ++ rest) =
        concatChunks (pre ++ (putString name ByteArray.empty :: (putString vec3sTypeName ByteArray.empty ::
          ([putU32LE 12 ByteArray.empty, putU32LE x ByteArray.empty, putU32LE y ByteArray.empty,
            putU32LE z ByteArray.empty] ++ rest)))) from by simp [MetaEntry.chunks, MetaEntry.valueChunks]]
    exact MetaEntry.parseFromChunks_vec3f pre name hn x y z rest
  | vec3d x y z =>
    simp only [MetaEntry.TypeOK] at hty
    subst hty
    rw [show concatChunks (pre ++ (⟨name, vec3dTypeName, .vec3d x y z⟩ : MetaEntry).chunks ++ rest) =
        concatChunks (pre ++ (putString name ByteArray.empty :: (putString vec3dTypeName ByteArray.empty ::
          ([putU32LE 24 ByteArray.empty, putU64LE x ByteArray.empty, putU64LE y ByteArray.empty,
            putU64LE z ByteArray.empty] ++ rest)))) from by simp [MetaEntry.chunks, MetaEntry.valueChunks]]
    exact MetaEntry.parseFromChunks_vec3d pre name hn x y z rest
  | raw s =>
    simp only [MetaEntry.TypeOK] at hty
    obtain ⟨htyk, hstr⟩ := hty
    have hsl' : s.size < 2 ^ 31 := hsl
    rw [show concatChunks (pre ++ (⟨name, tn, .raw s⟩ : MetaEntry).chunks ++ rest) =
        concatChunks (pre ++ (putString name ByteArray.empty :: (putString tn ByteArray.empty ::
          ([putU32LE (UInt32.ofNat s.size) ByteArray.empty, s] ++ rest)))) from by simp [MetaEntry.chunks, MetaEntry.valueChunks]]
    exact MetaEntry.parseFromChunks_raw pre name hn s hsl' htn
      (MetaKind.ofName?_eq_none htyk hstr) rest

theorem parseEntries_emit (es : List MetaEntry)
    (hwf : ∀ e ∈ es, e.WellFormed) :
    ∀ (pre post : List Bytes),
      parseEntries es.length
        (concatChunks (pre ++ es.flatMap MetaEntry.chunks ++ post))
        (concatChunks pre).size =
      some (es, (concatChunks (pre ++ es.flatMap MetaEntry.chunks)).size) := by
  induction es with
  | nil =>
    intro pre post
    simp [parseEntries]
  | cons e es ih =>
    intro pre post
    have he := hwf e (by simp)
    have hes : ∀ x ∈ es, x.WellFormed := fun x hx => hwf x (by simp [hx])
    simp only [List.length_cons, List.flatMap_cons]
    rw [show concatChunks (pre ++ (e.chunks ++ es.flatMap MetaEntry.chunks) ++ post) =
        concatChunks (pre ++ e.chunks ++ (es.flatMap MetaEntry.chunks ++ post)) from by simp]
    simp only [parseEntries]
    rw [MetaEntry.parseFromChunks e he pre (es.flatMap MetaEntry.chunks ++ post)]
    dsimp only
    rw [show (concatChunks pre).size + (e.chunks.map (·.size)).sum =
        (concatChunks (pre ++ e.chunks)).size from (concatChunks_append_map pre e.chunks).symm]
    rw [show concatChunks (pre ++ e.chunks ++ (es.flatMap MetaEntry.chunks ++ post)) =
        concatChunks (pre ++ e.chunks ++ es.flatMap MetaEntry.chunks ++ post) from by simp]
    rw [ih hes (pre ++ e.chunks) post]
    simp

theorem MetaList.parseFrom_emitFrom (m : MetaList)
    (hcnt : m.entries.length ≤ 4096) (hwf : ∀ e ∈ m.entries, e.WellFormed) (acc : Bytes) :
    MetaList.parseFrom (m.emitFrom acc) acc.size =
      some (m, acc.size + (m.chunks.map (·.size)).sum) := by
  rcases m with ⟨es⟩
  have hcnt' : es.length ≤ 4096 := hcnt
  have hlen : es.length < 2 ^ 31 := by omega
  unfold MetaList.parseFrom MetaList.emitFrom MetaList.chunks
  dsimp only
  rw [acc_append_concatChunks]
  rw [show concatChunks (acc :: (putI32LE (Int32.ofNat es.length) ByteArray.empty ::
      es.flatMap MetaEntry.chunks)) =
      concatChunks ([acc] ++ putI32LE (Int32.ofNat es.length) ByteArray.empty ::
        es.flatMap MetaEntry.chunks) from by simp]
  rw [show acc.size = (concatChunks [acc]).size from by simp [concatChunks]]
  have hsz := getI32LE_chunk [acc] (Int32.ofNat es.length) (es.flatMap MetaEntry.chunks)
  rw [hsz]
  dsimp only
  rw [ite_eq_right (by
    rw [Int32.lt_iff_toInt_lt, Int32.toInt_ofNat_of_lt hlen, Int32.toInt_zero]
    omega)]
  rw [show (concatChunks [acc]).size + 4 =
      (concatChunks [acc, putI32LE (Int32.ofNat es.length) ByteArray.empty]).size from by
    rw [show ([acc, putI32LE (Int32.ofNat es.length) ByteArray.empty] : List Bytes) =
        [acc] ++ [putI32LE (Int32.ofNat es.length) ByteArray.empty] from rfl]
    rw [concatChunks_snoc_size]
    simp [putI32LE_size]]
  rw [Int32.toNatClampNeg_ofNat_of_lt hlen]
  rw [show concatChunks ([acc] ++ putI32LE (Int32.ofNat es.length) ByteArray.empty ::
      es.flatMap MetaEntry.chunks) =
      concatChunks ([acc, putI32LE (Int32.ofNat es.length) ByteArray.empty] ++
        es.flatMap MetaEntry.chunks) from by simp]
  rw [show concatChunks ([acc, putI32LE (Int32.ofNat es.length) ByteArray.empty] ++
      es.flatMap MetaEntry.chunks) =
      concatChunks ([acc, putI32LE (Int32.ofNat es.length) ByteArray.empty] ++
        es.flatMap MetaEntry.chunks ++ []) from by simp]
  rw [parseEntries_emit es hwf [acc, putI32LE (Int32.ofNat es.length) ByteArray.empty] []]
  simp [MetaList.chunks, concatChunks_size, concatChunks_append_size, concatChunks_cons_size,
    concatChunks_singleton, concatChunks_nil_size, putI32LE_size]

end Vdb
