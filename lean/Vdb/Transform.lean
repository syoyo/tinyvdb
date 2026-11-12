/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Grid transforms (`tvdb__read_transform` / `tvdb__write_transform`).

  Wire format: a map-name string followed by `f64` fields.

  | name                        | fields after the name                          |
  |-----------------------------|------------------------------------------------|
  | `UniformScaleMap`/`ScaleMap`| scale, voxelSize, scaleInv, invScaleSqr, invTwiceScale |
  | `UniformScaleTranslateMap`/`ScaleTranslateMap` | translation, scale, voxelSize, scaleInv, invScaleSqr, invTwiceScale |
  | `TranslationMap`            | translation                                    |
  | `AffineMap`                 | 16 `f64` (OpenVDB row-vector `Mat4d`)          |

  The reader stores only the primary fields (scale, voxel size, translation,
  matrix); the inverse fields are recomputed by the writer. The model keeps the
  primary fields as bit patterns and computes the derived fields from them, so
  the parse/emit round trip is exact on the stored fields.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Chunks

namespace Vdb

/-! ### 3-vectors of double bit patterns -/

/-- Three binary64 bit patterns. -/
structure Vec3d where
  x : UInt64
  y : UInt64
  z : UInt64
  deriving Repr, DecidableEq, Inhabited

namespace Vec3d

/-- The 24-byte wire encoding. -/
def toBytes (v : Vec3d) : Bytes :=
  putU64LE v.x ByteArray.empty ++
    (putU64LE v.y ByteArray.empty ++ putU64LE v.z ByteArray.empty)

/-- Decode a 24-byte blob (out-of-range reads become zero bits). -/
def ofBytes (b : Bytes) : Vec3d :=
  ⟨(getU64LE b 0).getD 0, (getU64LE b 8).getD 0, (getU64LE b 16).getD 0⟩

@[simp] theorem toBytes_size (v : Vec3d) : v.toBytes.size = 24 := by
  simp [toBytes]

theorem ofBytes_toBytes (v : Vec3d) : ofBytes v.toBytes = v := by
  unfold ofBytes toBytes
  have hx : getU64LE (putU64LE v.x ByteArray.empty ++
      (putU64LE v.y ByteArray.empty ++ putU64LE v.z ByteArray.empty)) 0 = some v.x := by
    rw [getU64LE_append_left (by simp)]
    rw [show (0 : Nat) = ByteArray.empty.size from rfl]
    exact getU64LE_putU64LE _ _
  have hy : getU64LE (putU64LE v.x ByteArray.empty ++
      (putU64LE v.y ByteArray.empty ++ putU64LE v.z ByteArray.empty)) 8 = some v.y := by
    rw [show (8 : Nat) = (putU64LE v.x ByteArray.empty).size + 0 by simp]
    rw [getU64LE_append_right' (j := 0)]
    rw [getU64LE_append_left (by simp)]
    rw [show (0 : Nat) = ByteArray.empty.size from rfl]
    exact getU64LE_putU64LE _ _
  have hz : getU64LE (putU64LE v.x ByteArray.empty ++
      (putU64LE v.y ByteArray.empty ++ putU64LE v.z ByteArray.empty)) 16 = some v.z := by
    rw [show (16 : Nat) = (putU64LE v.x ByteArray.empty).size + 8 by simp]
    rw [getU64LE_append_right' (j := 8)]
    rw [show (8 : Nat) = (putU64LE v.y ByteArray.empty).size + 0 by simp]
    rw [getU64LE_append_right' (j := 0)]
    rw [show (0 : Nat) = ByteArray.empty.size from rfl]
    exact getU64LE_putU64LE _ _
  rw [hx, hy, hz]
  rfl

/-- Read a 24-byte vector at `off`; returns it and the next offset. -/
def parseAt (b : Bytes) (off : Nat) : Option (Vec3d × Nat) :=
  (getBytes? b off 24).map fun raw => (ofBytes raw, off + 24)

end Vec3d

/-- A cross-product-free pass-through for the derived fields. -/
def Vec3d.zero : Vec3d := ⟨0, 0, 0⟩

/-- Floating-point reciprocal of the bit pattern (0 maps to 1 first, like the
    C writer's `scale != 0 ? scale : 1`). -/
def invBits (u : UInt64) : UInt64 :=
  let s : Float := if u = 0 then 1.0 else Float.ofBits u
  (1.0 / s).toBits

/-- First and second reciprocal fields derived from the scale. -/
def Vec3d.inv (v : Vec3d) : Vec3d :=
  ⟨invBits v.x, invBits v.y, invBits v.z⟩

def Vec3d.invSq (v : Vec3d) : Vec3d :=
  let w := v.inv
  ⟨bitsMul w.x w.x, bitsMul w.y w.y, bitsMul w.z w.z⟩
  where
    bitsMul (a b : UInt64) : UInt64 :=
      let sa : Float := if a = 0 then 1.0 else Float.ofBits a
      let sb : Float := if b = 0 then 1.0 else Float.ofBits b
      (sa * sb).toBits

def Vec3d.invTwice (v : Vec3d) : Vec3d :=
  let w := v.inv
  ⟨bitsHalf w.x, bitsHalf w.y, bitsHalf w.z⟩
  where
    bitsHalf (a : UInt64) : UInt64 :=
      let sa : Float := if a = 0 then 1.0 else Float.ofBits a
      (0.5 * sa).toBits

/-! ### Transform kinds -/

/-- The transform map kind. -/
inductive TransformKind where
  | uniformScale
  | scale
  | uniformScaleTranslate
  | scaleTranslate
  | translation
  | affine
  deriving Repr, DecidableEq

/-- OpenVDB map name. -/
def TransformKind.name : TransformKind → Bytes
  | .uniformScale => "UniformScaleMap".toUTF8
  | .scale => "ScaleMap".toUTF8
  | .uniformScaleTranslate => "UniformScaleTranslateMap".toUTF8
  | .scaleTranslate => "ScaleTranslateMap".toUTF8
  | .translation => "TranslationMap".toUTF8
  | .affine => "AffineMap".toUTF8

/-- A grid transform. `affine` holds the 128 raw bytes of the OpenVDB
    row-vector `Mat4d`; it is only meaningful for `.affine`. -/
structure Transform where
  kind : TransformKind
  translation : Vec3d
  scale : Vec3d
  voxelSize : Vec3d
  affine : Bytes
  deriving Repr

/-- The transform is well formed: the fields the reader does not store are
    canonical (zero vectors) and the affine block is exactly 128 bytes. -/
def Transform.WellFormed (t : Transform) : Prop :=
  (t.kind = .uniformScale ∨ t.kind = .scale → t.translation = Vec3d.zero) ∧
  (t.kind = .translation → t.scale = Vec3d.zero ∧ t.voxelSize = Vec3d.zero) ∧
  (t.kind = .affine → t.scale = Vec3d.zero ∧ t.voxelSize = Vec3d.zero ∧
    t.translation = Vec3d.zero) ∧
  (t.kind = .affine → t.affine.size = 128) ∧
  (t.kind ≠ .affine → t.affine.size = 0)

/-- The chunks after the map-name string. -/
def Transform.fieldChunks (t : Transform) : List Bytes :=
  match t.kind with
  | .uniformScale | .scale =>
    [t.scale.toBytes, t.voxelSize.toBytes, t.scale.inv.toBytes,
     t.scale.invSq.toBytes, t.scale.invTwice.toBytes]
  | .uniformScaleTranslate | .scaleTranslate =>
    [t.translation.toBytes, t.scale.toBytes, t.voxelSize.toBytes,
     t.scale.inv.toBytes, t.scale.invSq.toBytes, t.scale.invTwice.toBytes]
  | .translation => [t.translation.toBytes]
  | .affine => [t.affine]

/-- All chunks of the transform. -/
def Transform.chunks (t : Transform) : List Bytes :=
  putString t.kind.name ByteArray.empty :: t.fieldChunks

/-- Emit a transform after `acc`. -/
def Transform.emitFrom (t : Transform) (acc : Bytes) : Bytes :=
  acc ++ concatChunks t.chunks

/-- Emit a transform. -/
def Transform.emit (t : Transform) : Bytes := t.emitFrom ByteArray.empty

/-- Parse a chain of `n` 24-byte vectors. -/
def parseVecChain : Nat → Bytes → Nat → Option (List Vec3d × Nat)
  | 0, _, off => some ([], off)
  | n + 1, b, off =>
    match Vec3d.parseAt b off with
    | none => none
    | some (v, o) =>
      match parseVecChain n b o with
      | none => none
      | some (vs, o') => some (v :: vs, o')

/-- Parse a transform at `off`. Derived inverse fields are read and discarded
    (the writer recomputes them), matching the C reader. Values are taken by
    position from the parsed vector chain so the branches are non-dependent. -/
def Transform.parseFrom (b : Bytes) (off : Nat) : Option (Transform × Nat) :=
  match getString? b off with
  | none => none
  | some (tn, o1) =>
    if tn = TransformKind.uniformScale.name || tn = TransformKind.scale.name then
      match parseVecChain 5 b o1 with
      | some (vs, o) =>
        let k : TransformKind :=
          if tn = TransformKind.uniformScale.name then .uniformScale else .scale
        some (⟨k, Vec3d.zero, vs.getD 0 Vec3d.zero, vs.getD 1 Vec3d.zero,
          ByteArray.empty⟩, o)
      | none => none
    else if tn = TransformKind.uniformScaleTranslate.name ||
            tn = TransformKind.scaleTranslate.name then
      match parseVecChain 6 b o1 with
      | some (vs, o) =>
        let k : TransformKind :=
          if tn = TransformKind.uniformScaleTranslate.name then .uniformScaleTranslate
          else .scaleTranslate
        some (⟨k, vs.getD 0 Vec3d.zero, vs.getD 1 Vec3d.zero, vs.getD 2 Vec3d.zero,
          ByteArray.empty⟩, o)
      | none => none
    else if tn = TransformKind.translation.name then
      match parseVecChain 1 b o1 with
      | some (vs, o) => some (⟨.translation, vs.getD 0 Vec3d.zero, Vec3d.zero,
          Vec3d.zero, ByteArray.empty⟩, o)
      | none => none
    else if tn = TransformKind.affine.name then
      match getBytes? b o1 128 with
      | none => none
      | some raw => some (⟨.affine, Vec3d.zero, Vec3d.zero, Vec3d.zero, raw⟩, o1 + 128)
    else none

/-! ### Round trip -/

theorem Vec3d.parseAt_toBytes (v : Vec3d) (pre : List Bytes) (post : List Bytes) :
    Vec3d.parseAt (concatChunks (pre ++ v.toBytes :: post)) (concatChunks pre).size =
      some (v, (concatChunks pre).size + 24) := by
  unfold Vec3d.parseAt
  rw [show (24 : Nat) = v.toBytes.size from (Vec3d.toBytes_size v).symm]
  rw [getBytes?_chunk]
  simp [Vec3d.ofBytes_toBytes]

/-- Reading a chain of vectors back from its emitted chunks. -/
theorem parseVecChain_emit (vs : List Vec3d) :
    ∀ (pre post : List Bytes),
      parseVecChain vs.length
        (concatChunks (pre ++ vs.map Vec3d.toBytes ++ post)) (concatChunks pre).size =
        some (vs, (concatChunks (pre ++ vs.map Vec3d.toBytes)).size) := by
  induction vs with
  | nil =>
    intro pre post
    simp [parseVecChain]
  | cons v vs ih =>
    intro pre post
    rw [show pre ++ (v :: vs).map Vec3d.toBytes ++ post =
      pre ++ v.toBytes :: (vs.map Vec3d.toBytes ++ post) from by simp]
    simp only [List.length_cons, parseVecChain, List.map_cons]
    rw [Vec3d.parseAt_toBytes]
    dsimp only
    rw [show (concatChunks pre).size + 24 =
        (concatChunks (pre ++ [v.toBytes])).size by simp [concatChunks_size]]
    rw [show pre ++ v.toBytes :: (vs.map Vec3d.toBytes ++ post) =
        (pre ++ [v.toBytes]) ++ vs.map Vec3d.toBytes ++ post from by simp]
    rw [ih (pre ++ [v.toBytes]) post]
    simp [List.append_assoc]




/-- Translation maps: name + one 24-byte vector. -/
theorem Transform.parseFrom_emitFrom_translation (tr : Vec3d) (acc : Bytes) :
    ∃ out, Transform.parseFrom
        ((⟨.translation, tr, Vec3d.zero, Vec3d.zero, ByteArray.empty⟩ : Transform).emitFrom acc)
        acc.size =
      some (⟨.translation, tr, Vec3d.zero, Vec3d.zero, ByteArray.empty⟩, out) := by
  constructor
  unfold Transform.parseFrom Transform.emitFrom Transform.chunks Transform.fieldChunks
  rw [acc_append_concatChunks]
  rw [show (acc :: (putString (TransformKind.translation.name) ByteArray.empty :: [tr.toBytes])) =
      [acc] ++ putString (TransformKind.translation.name) ByteArray.empty :: [tr].map Vec3d.toBytes
      from rfl]
  rw [show acc.size = (concatChunks [acc]).size from by simp [concatChunks]]
  rw [getString?_chunk (pre := [acc]) (s := TransformKind.translation.name)
    (post := [tr].map Vec3d.toBytes) (by decide)]
  dsimp only
  split
  · rename_i h
    exact absurd h (by decide)
  · split
    · rename_i h
      exact absurd h (by decide)
    · split
      · rename_i h
        rw [show (concatChunks [acc]).size + 4 + (TransformKind.translation.name).size =
            (concatChunks [acc, putString (TransformKind.translation.name) ByteArray.empty]).size by
          simp [concatChunks_size, putString_size]; omega]
        have hchain := parseVecChain_emit [tr]
          [acc, putString (TransformKind.translation.name) ByteArray.empty] ([] : List Bytes)
        simp only [List.length_cons, List.length_nil] at hchain
        norm_num at hchain
        rw [show concatChunks ([acc] ++ putString (TransformKind.translation.name) ByteArray.empty ::
            [tr].map Vec3d.toBytes) = concatChunks
            [acc, putString (TransformKind.translation.name) ByteArray.empty, tr.toBytes] from by
          simp]
        rw [hchain]
        dsimp only
        simp
        rfl
      · rename_i h
        exact absurd h (by decide)

end Vdb
