/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Value-type algebra: the ten grid value types, their on-disk element sizes,
  half-precision grids' "components" rule, and the metadata type names.

  References (tinyvdbio):
  * `tvdb_value_type_t` / `tvdb_value_type_size` (`src/tinyvdb_io.h`).
  * `tvdb__read_grid_type` prefix table (`Tree_<prefix>_<log2dims...>`).
  * `tvdb__half_components` (components stored per element in half grids).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Bytes

namespace Vdb

/-! ### Grid value types -/

/-- The value type of a grid's tree (OpenVDB `Tree_<type>_...`). -/
inductive ValueType where
  | null
  | boolean
  | int32
  | int64
  | float
  | double
  | half
  | vec3i
  | vec3f
  | vec3d
  | string
  deriving Repr, DecidableEq, Inhabited

/-- On-disk element size in bytes (0 for `null`/`string`). -/
def ValueType.size : ValueType → Nat
  | .null => 0
  | .boolean => 1
  | .int32 => 4
  | .int64 => 8
  | .float => 4
  | .double => 8
  | .half => 2
  | .vec3i => 12
  | .vec3f => 12
  | .vec3d => 24
  | .string => 0

/-- Grid type name used in `Tree_<name>_...` (OpenVDB spelling). -/
def ValueType.treeName : ValueType → String
  | .boolean => "bool"
  | .int32 => "int32"
  | .int64 => "int64"
  | .float => "float"
  | .double => "double"
  | .half => "half"
  | .vec3i => "vec3i"
  | .vec3f => "vec3s"
  | .vec3d => "vec3d"
  | .string => "string"
  | .null => ""

/-- Metadata type name (OpenVDB spelling; `vec3s` is `Vec3f` on disk). -/
def ValueType.metaName : ValueType → String
  | .boolean => "bool"
  | .int32 => "int32"
  | .int64 => "int64"
  | .float => "float"
  | .double => "double"
  | .half => "half"
  | .vec3i => "vec3i"
  | .vec3f => "vec3s"
  | .vec3d => "vec3d"
  | .string => "string"
  | .null => ""

/-- The `Tree_` type-name prefixes accepted by `tvdb__read_grid_type`.
    `mask` is decoded as a bool tree; `ptidx32`/`ptdataidx32` as int32. -/
def treeTypePrefix : List (String × ValueType) :=
  [ ("float", .float), ("double", .double), ("int32", .int32),
    ("int64", .int64), ("bool", .boolean), ("mask", .boolean),
    ("vec3s", .vec3f), ("vec3d", .vec3d), ("vec3i", .vec3i),
    ("ptidx32", .int32), ("ptdataidx32", .int32) ]

/-- Metadata type names accepted by `tvdb__read_meta`. -/
def metaTypeName : List (String × ValueType) :=
  [ ("bool", .boolean), ("float", .float), ("double", .double),
    ("int32", .int32), ("int64", .int64), ("vec3i", .vec3i),
    ("vec3d", .vec3d), ("vec3s", .vec3f), ("string", .string) ]

/-- Lookup in a name table. -/
def lookupName (table : List (String × ValueType)) (s : String) : Option ValueType :=
  (table.find? (fun p => p.1 == s)).map (·.2)

/-- Grid-type prefix lookup (first match wins, like the C `strcmp` chain). -/
def ValueType.ofTreeName (s : String) : Option ValueType := lookupName treeTypePrefix s

/-- Metadata-type lookup. -/
def ValueType.ofMetaName (s : String) : Option ValueType := lookupName metaTypeName s

/-- Number of stored scalar components per element. Half grids store
    `2 * components` bytes per value: 2 for float/double, 6 for vec3f/vec3d,
    0 for every other type (no half encoding). -/
def ValueType.halfComponents : ValueType → Nat
  | .float => 1
  | .double => 1
  | .vec3f => 3
  | .vec3d => 3
  | _ => 0

/-- Element size in a half-precision grid (`tvdb__half_components`). -/
def ValueType.halfElemSize (vt : ValueType) : Nat :=
  if vt.halfComponents == 0 then 0 else 2 * vt.halfComponents

/-- Types whose values may be saved as half precision. -/
def ValueType.canBeHalf (vt : ValueType) : Bool := vt.halfComponents != 0


/-- Element size as stored in the file: half width when the grid is saved as
    half precision and the type has a half encoding, full width otherwise
    (the C `is_half ? 2 * half_comps : vsize`). -/
def ValueType.fileElemSize (vt : ValueType) (half : Bool) : Nat :=
  if half && vt.canBeHalf then vt.halfElemSize else vt.size

/-! ### Voxel values -/

/-- A voxel / tile value. Bit patterns are kept raw (no float semantics here):
    `f32`/`f64` hold the IEEE bits. Half grids widen to `f32` on read, exactly
    like `tvdb__read_value`. -/
inductive VoxelValue where
  | boolean : Bool → VoxelValue
  | int32 : Int32 → VoxelValue
  | int64 : Int64 → VoxelValue
  | f32 : UInt32 → VoxelValue
  | f64 : UInt64 → VoxelValue
  | vec3i : Int32 → Int32 → Int32 → VoxelValue
  | vec3f : UInt32 → UInt32 → UInt32 → VoxelValue
  | vec3d : UInt64 → UInt64 → UInt64 → VoxelValue
  deriving Repr, DecidableEq, Inhabited

/-- The type tag of a voxel value. -/
def VoxelValue.type : VoxelValue → ValueType
  | .boolean _ => .boolean
  | .int32 _ => .int32
  | .int64 _ => .int64
  | .f32 _ => .float
  | .f64 _ => .double
  | .vec3i _ _ _ => .vec3i
  | .vec3f _ _ _ => .vec3f
  | .vec3d _ _ _ => .vec3d

theorem VoxelValue.type_ne_string (v : VoxelValue) : v.type ≠ .string := by
  cases v <;> simp [VoxelValue.type]

theorem VoxelValue.type_ne_null (v : VoxelValue) : v.type ≠ .null := by
  cases v <;> simp [VoxelValue.type]

/-- A value of the given type (impossible for `null`/`string`). -/
def VoxelValue.isType (v : VoxelValue) (vt : ValueType) : Bool := v.type == vt

/-! ### Values of a given type, as raw little-endian bytes -/

/-- Number of whole bytes a voxel value occupies at full precision. -/
def VoxelValue.byteSize (v : VoxelValue) : Nat := v.type.size

theorem VoxelValue.byteSize_pos (v : VoxelValue) : 0 < v.byteSize := by
  cases v <;> simp [VoxelValue.byteSize, VoxelValue.type, ValueType.size]

/-! ### Metadata values -/

/-- A metadata entry's decoded value. `raw` keeps entries of unknown type. -/
inductive MetaValue where
  | boolean : Bool → MetaValue
  | int32 : Int32 → MetaValue
  | int64 : Int64 → MetaValue
  | f32 : UInt32 → MetaValue
  | f64 : UInt64 → MetaValue
  | vec3i : Int32 → Int32 → Int32 → MetaValue
  | vec3f : UInt32 → UInt32 → UInt32 → MetaValue
  | vec3d : UInt64 → UInt64 → UInt64 → MetaValue
  | str : Bytes → MetaValue
  | raw : Bytes → MetaValue
  deriving Repr, Inhabited

/-- The type tag of a metadata value; `none` for `raw`. -/
def MetaValue.type? : MetaValue → Option ValueType
  | .boolean _ => some .boolean
  | .int32 _ => some .int32
  | .int64 _ => some .int64
  | .f32 _ => some .float
  | .f64 _ => some .double
  | .vec3i _ _ _ => some .vec3i
  | .vec3f _ _ _ => some .vec3f
  | .vec3d _ _ _ => some .vec3d
  | .str _ => some .string
  | .raw _ => none

end Vdb
