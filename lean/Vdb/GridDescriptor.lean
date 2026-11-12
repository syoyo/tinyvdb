/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Grid descriptors (`tvdb__read_grid_descriptor`): the per-grid record that
  precedes the grid's payload.

  Wire format (file version 221 and later):

      unique name      VDB string
      grid type        VDB string
      instance parent  VDB string
      grid byte offset  u64
      block byte offset u64
      end byte offset   u64

  The writer always emits the instance-parent string; the reader only reads
  it for version 221 and later, so the round trip here assumes such a
  version. (For version 220 the writer's always-present string would be
  misread; noted in `plan-lean.md`/`VERIFICATION.md` as a C-side finding.)

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Chunks
import Vdb.Stable

set_option linter.unusedSimpArgs false

namespace Vdb

/-- A grid descriptor (the record before each grid's tree). The writer always
    emits the instance-parent name; the reader only reads it for file version
    221 and later, so the round trip below assumes such a version. -/
structure GridDescriptor where
  uniqueName : Bytes
  gridType : Bytes
  instanceParent : Bytes
  gridOffset : UInt64
  blockOffset : UInt64
  endOffset : UInt64
  deriving Repr, DecidableEq

/-- Descriptor strings fit their `u32` length words. -/
def GridDescriptor.Canonical (g : GridDescriptor) : Prop :=
  g.uniqueName.size < 2 ^ 32 ∧ g.gridType.size < 2 ^ 32 ∧
  g.instanceParent.size < 2 ^ 32

/-- The descriptor's wire chunks. -/
def GridDescriptor.chunks (g : GridDescriptor) : List Bytes :=
  [putString g.uniqueName ByteArray.empty, putString g.gridType ByteArray.empty,
   putString g.instanceParent ByteArray.empty,
   putU64LE g.gridOffset ByteArray.empty, putU64LE g.blockOffset ByteArray.empty,
   putU64LE g.endOffset ByteArray.empty]

/-- Emit a descriptor after `acc`. -/
def GridDescriptor.emitFrom (g : GridDescriptor) (acc : Bytes) : Bytes :=
  acc ++ concatChunks g.chunks

/-- Emit a descriptor. -/
def GridDescriptor.emit (g : GridDescriptor) : Bytes := g.emitFrom ByteArray.empty

/-- Parse a descriptor for a given file version at `off`. -/
def GridDescriptor.parseFrom (ver : UInt32) (b : Bytes) (off : Nat) :
    Option (GridDescriptor × Nat) :=
  match getString? b off with
  | none => none
  | some (u, o1) =>
    match getString? b o1 with
    | none => none
    | some (t, o2) =>
      if 221 ≤ ver then
        match getString? b o2 with
        | none => none
        | some (ip, o3) =>
          match getU64LE b o3 with
          | none => none
          | some go =>
            match getU64LE b (o3 + 8) with
            | none => none
            | some bo =>
              match getU64LE b (o3 + 16) with
              | none => none
              | some eo => some (⟨u, t, ip, go, bo, eo⟩, o3 + 24)
      else
        match getU64LE b o2 with
        | none => none
        | some go =>
          match getU64LE b (o2 + 8) with
          | none => none
          | some bo =>
            match getU64LE b (o2 + 16) with
            | none => none
            | some eo => some (⟨u, t, ByteArray.empty, go, bo, eo⟩, o2 + 24)

theorem GridDescriptor.parseFrom_emitFrom (ver : UInt32) (hver : 221 ≤ ver)
    (g : GridDescriptor) (hg : g.Canonical) (acc : Bytes) :
    GridDescriptor.parseFrom ver (g.emitFrom acc) acc.size =
      some (g, (concatChunks [acc, putString g.uniqueName ByteArray.empty,
        putString g.gridType ByteArray.empty,
        putString g.instanceParent ByteArray.empty]).size + 24) := by
  obtain ⟨hu, ht, hi⟩ := hg
  rcases g with ⟨u, t, ip, go, bo, eo⟩
  simp only at hu ht hi
  unfold GridDescriptor.parseFrom GridDescriptor.emitFrom GridDescriptor.chunks
  rw [acc_append_concatChunks]
  rw [show acc :: [putString u ByteArray.empty, putString t ByteArray.empty,
      putString ip ByteArray.empty, putU64LE go ByteArray.empty, putU64LE bo ByteArray.empty,
      putU64LE eo ByteArray.empty] =
      [acc] ++ putString u ByteArray.empty :: (putString t ByteArray.empty ::
        (putString ip ByteArray.empty :: (putU64LE go ByteArray.empty ::
          (putU64LE bo ByteArray.empty :: [putU64LE eo ByteArray.empty])))) from rfl]
  rw [show acc.size = (concatChunks [acc]).size from by simp [concatChunks]]
  rw [getString?_chunk (pre := [acc]) (s := u)
    (post := putString t ByteArray.empty :: (putString ip ByteArray.empty ::
      (putU64LE go ByteArray.empty :: (putU64LE bo ByteArray.empty ::
        [putU64LE eo ByteArray.empty])))) hu]
  dsimp only
  rw [show (concatChunks [acc]).size + 4 + u.size =
      (concatChunks [acc, putString u ByteArray.empty]).size from by
    conv_lhs => rw [concatChunks_size]
    conv_rhs => rw [concatChunks_size]
    simp [putString_size, putU64LE_size]
    omega]
  rw [show [acc] ++ (putString u ByteArray.empty :: (putString t ByteArray.empty ::
      (putString ip ByteArray.empty :: (putU64LE go ByteArray.empty ::
        (putU64LE bo ByteArray.empty :: [putU64LE eo ByteArray.empty]))))) =
      [acc, putString u ByteArray.empty] ++ (putString t ByteArray.empty ::
        (putString ip ByteArray.empty :: (putU64LE go ByteArray.empty ::
          (putU64LE bo ByteArray.empty :: [putU64LE eo ByteArray.empty])))) from rfl]
  rw [getString?_chunk (pre := [acc, putString u ByteArray.empty]) (s := t)
    (post := putString ip ByteArray.empty :: (putU64LE go ByteArray.empty ::
      (putU64LE bo ByteArray.empty :: [putU64LE eo ByteArray.empty]))) ht]
  dsimp only
  rw [show (concatChunks [acc, putString u ByteArray.empty]).size + 4 + t.size =
      (concatChunks [acc, putString u ByteArray.empty, putString t ByteArray.empty]).size from by
    conv_lhs => rw [concatChunks_size]
    conv_rhs => rw [concatChunks_size]
    simp [putString_size, putU64LE_size]
    omega]
  rw [show [acc, putString u ByteArray.empty] ++ (putString t ByteArray.empty ::
      (putString ip ByteArray.empty :: (putU64LE go ByteArray.empty ::
        (putU64LE bo ByteArray.empty :: [putU64LE eo ByteArray.empty])))) =
      [acc, putString u ByteArray.empty, putString t ByteArray.empty] ++
        (putString ip ByteArray.empty :: (putU64LE go ByteArray.empty ::
          (putU64LE bo ByteArray.empty :: [putU64LE eo ByteArray.empty]))) from rfl]
  rw [getString?_chunk (pre := [acc, putString u ByteArray.empty,
      putString t ByteArray.empty]) (s := ip)
    (post := putU64LE go ByteArray.empty :: (putU64LE bo ByteArray.empty ::
      [putU64LE eo ByteArray.empty])) hi]
  dsimp only
  rw [show (concatChunks [acc, putString u ByteArray.empty, putString t ByteArray.empty]).size + 4 + ip.size =
      (concatChunks [acc, putString u ByteArray.empty, putString t ByteArray.empty,
        putString ip ByteArray.empty]).size from by
    conv_lhs => rw [concatChunks_size]
    conv_rhs => rw [concatChunks_size]
    simp [putString_size, putU64LE_size]
    omega]
  rw [ite_eq_left hver]
  rw [show [acc, putString u ByteArray.empty, putString t ByteArray.empty] ++
      (putString ip ByteArray.empty :: (putU64LE go ByteArray.empty ::
        (putU64LE bo ByteArray.empty :: [putU64LE eo ByteArray.empty]))) =
      [acc, putString u ByteArray.empty, putString t ByteArray.empty,
        putString ip ByteArray.empty] ++
        (putU64LE go ByteArray.empty :: (putU64LE bo ByteArray.empty ::
          [putU64LE eo ByteArray.empty])) from rfl]
  rw [getU64LE_chunk]
  dsimp only
  rw [show (concatChunks [acc, putString u ByteArray.empty, putString t ByteArray.empty,
        putString ip ByteArray.empty]).size + 8 =
      (concatChunks [acc, putString u ByteArray.empty, putString t ByteArray.empty,
        putString ip ByteArray.empty, putU64LE go ByteArray.empty]).size from by
    conv_lhs => rw [concatChunks_size]
    conv_rhs => rw [concatChunks_size]
    simp [putString_size, putU64LE_size]
    omega]
  rw [show [acc, putString u ByteArray.empty, putString t ByteArray.empty,
        putString ip ByteArray.empty] ++
        (putU64LE go ByteArray.empty :: (putU64LE bo ByteArray.empty ::
          [putU64LE eo ByteArray.empty])) =
      [acc, putString u ByteArray.empty, putString t ByteArray.empty,
        putString ip ByteArray.empty, putU64LE go ByteArray.empty] ++
        (putU64LE bo ByteArray.empty :: [putU64LE eo ByteArray.empty]) from rfl]
  rw [getU64LE_chunk]
  dsimp only
  rw [show (concatChunks [acc, putString u ByteArray.empty, putString t ByteArray.empty,
        putString ip ByteArray.empty]).size + 16 =
      (concatChunks [acc, putString u ByteArray.empty, putString t ByteArray.empty,
        putString ip ByteArray.empty, putU64LE go ByteArray.empty,
        putU64LE bo ByteArray.empty]).size from by
    conv_lhs => rw [concatChunks_size]
    conv_rhs => rw [concatChunks_size]
    simp [putString_size, putU64LE_size]
    omega]
  rw [show [acc, putString u ByteArray.empty, putString t ByteArray.empty,
        putString ip ByteArray.empty, putU64LE go ByteArray.empty] ++
        [putU64LE bo ByteArray.empty, putU64LE eo ByteArray.empty] =
      [acc, putString u ByteArray.empty, putString t ByteArray.empty,
        putString ip ByteArray.empty, putU64LE go ByteArray.empty,
        putU64LE bo ByteArray.empty] ++ [putU64LE eo ByteArray.empty] from by simp]
  rw [getU64LE_chunk]


/-- A descriptor parse does not depend on trailing bytes. -/
theorem GridDescriptor.parseFrom_append (ver : UInt32) {b rest : Bytes} {off : Nat}
    {p : GridDescriptor × Nat}
    (h : GridDescriptor.parseFrom ver b off = some p) :
    GridDescriptor.parseFrom ver (b ++ rest) off = some p := by
  unfold GridDescriptor.parseFrom at h ⊢
  repeat' (first | split at h | split)
  all_goals simp_all [getString?_append_of_some, getU64LE_append_of_some]

end Vdb
