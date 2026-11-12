/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  The file prologue (`tvdb__file_parse`): the header, the file-level metadata
  list, and the grid count. Grid descriptors and grid data follow.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Header
import Vdb.Meta

set_option linter.unusedSimpArgs false

namespace Vdb

structure FilePrefix where
  header : Header
  fileMetadata : MetaList
  gridCount : Nat
  deriving Repr

def FilePrefix.Canonical (f : FilePrefix) : Prop :=
  f.header.Canonical ∧ f.fileMetadata.entries.length ≤ 4096 ∧
  (∀ e ∈ f.fileMetadata.entries, e.WellFormed) ∧ f.gridCount < 2 ^ 31

def FilePrefix.chunks (f : FilePrefix) : List Bytes :=
  f.header.chunks ++ f.fileMetadata.chunks ++
    [putI32LE (Int32.ofNat f.gridCount) ByteArray.empty]

def FilePrefix.emitFrom (f : FilePrefix) (acc : Bytes) : Bytes :=
  acc ++ concatChunks f.chunks

def FilePrefix.emit (f : FilePrefix) : Bytes := f.emitFrom ByteArray.empty

def FilePrefix.parseFrom (b : Bytes) (off : Nat) : Option (FilePrefix × Nat) :=
  match Header.parseFrom b off with
  | none => none
  | some (h, o1) =>
    match MetaList.parseFrom b o1 with
    | none => none
    | some (md, o2) =>
      match getI32LE b o2 with
      | none => none
      | some n =>
        if n < 0 then none
        else some (⟨h, md, n.toNatClampNeg⟩, o2 + 4)

theorem FilePrefix.parseFrom_emitFrom (f : FilePrefix) (hc : f.Canonical) (acc : Bytes) :
    FilePrefix.parseFrom (f.emitFrom acc) acc.size =
      some (f, acc.size + (f.chunks.map (·.size)).sum) := by
  obtain ⟨hh, hm, hwf, hcnt⟩ := hc
  rcases f with ⟨h, md, n⟩
  unfold FilePrefix.parseFrom FilePrefix.emitFrom FilePrefix.chunks
  dsimp only
  rw [acc_append_concatChunks]
  rw [show concatChunks (acc :: (h.chunks ++ md.chunks ++
      [putI32LE (Int32.ofNat n) ByteArray.empty])) =
      concatChunks ([acc] ++ h.chunks ++ (md.chunks ++
        [putI32LE (Int32.ofNat n) ByteArray.empty])) from by simp]
  rw [show acc.size = (concatChunks [acc]).size from by simp [concatChunks]]
  rw [Header.parseFromChunks h hh [acc] (md.chunks ++ [putI32LE (Int32.ofNat n) ByteArray.empty])]
  dsimp only
  rw [show (concatChunks ([acc] ++ h.chunks)).size =
      (concatChunks ([acc] ++ h.chunks)).size from rfl]
  rw [show concatChunks ([acc] ++ h.chunks ++ (md.chunks ++
      [putI32LE (Int32.ofNat n) ByteArray.empty])) =
      concatChunks (([acc] ++ h.chunks) ++ md.chunks ++
        [putI32LE (Int32.ofNat n) ByteArray.empty]) from by simp]
  rw [MetaList.parseFromChunks md hm hwf ([acc] ++ h.chunks)
    [putI32LE (Int32.ofNat n) ByteArray.empty]]
  dsimp only
  rw [show (concatChunks (([acc] ++ h.chunks) ++ md.chunks)).size =
      (concatChunks (([acc] ++ h.chunks) ++ md.chunks)).size from rfl]
  rw [show concatChunks ((([acc] ++ h.chunks) ++ md.chunks) ++
      [putI32LE (Int32.ofNat n) ByteArray.empty]) =
      concatChunks ((([acc] ++ h.chunks) ++ md.chunks) ++
        (putI32LE (Int32.ofNat n) ByteArray.empty :: [])) from by simp]
  rw [getI32LE_chunk]
  dsimp only
  rw [ite_eq_right (by
    rw [Int32.lt_iff_toInt_lt, Int32.toInt_ofNat_of_lt hcnt, Int32.toInt_zero]
    omega)]
  rw [Int32.toNatClampNeg_ofNat_of_lt hcnt]
  rw [show (concatChunks (([acc] ++ h.chunks) ++ md.chunks)).size + 4 =
      (concatChunks (([acc] ++ h.chunks) ++ md.chunks ++
        [putI32LE (Int32.ofNat n) ByteArray.empty])).size from by
    conv_lhs => rw [concatChunks_size]
    conv_rhs => rw [concatChunks_size]
    simp [putI32LE_size]
    omega]
  simp [FilePrefix.chunks, concatChunks_size, concatChunks_append_size, concatChunks_cons_size,
    concatChunks_singleton, concatChunks_nil_size, putI32LE_size]

end Vdb
