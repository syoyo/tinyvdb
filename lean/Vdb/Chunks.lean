/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Fixed-layout field chains. A record whose wire layout is a sequence of
  self-delimiting chunks (scalars and byte blobs) can be emitted as the
  concatenation of those chunks. Reading a field then happens at the size of
  the chunk prefix, which these lemmas turn into the scalar round trips.

  This is the plumbing used by the header and the transform.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Bytes

namespace Vdb

/-- Concatenate a list of byte chunks. -/
def concatChunks : List Bytes → Bytes
  | [] => ByteArray.empty
  | c :: cs => c ++ concatChunks cs

theorem concatChunks_append (l₁ l₂ : List Bytes) :
    concatChunks (l₁ ++ l₂) = concatChunks l₁ ++ concatChunks l₂ := by
  induction l₁ with
  | nil => simp [concatChunks]
  | cons c cs ih =>
    simp only [List.cons_append, concatChunks, ih, ByteArray.append_assoc]

theorem concatChunks_singleton (c : Bytes) : concatChunks [c] = c := by
  simp [concatChunks]

theorem concatChunks_size (l : List Bytes) :
    (concatChunks l).size = (l.map (·.size)).sum := by
  induction l with
  | nil => simp [concatChunks]
  | cons c cs ih =>
    simp only [concatChunks, ByteArray.size_append, ih, List.map_cons, List.sum_cons]

/-- Size of a concatenation of chunk lists. -/
theorem concatChunks_append_size (l₁ l₂ : List Bytes) :
    (concatChunks (l₁ ++ l₂)).size = (concatChunks l₁).size + (concatChunks l₂).size := by
  rw [concatChunks_append, ByteArray.size_append]

/-- Size of a chunk list starting with a chunk. -/
theorem concatChunks_cons_size (c : Bytes) (l : List Bytes) :
    (concatChunks (c :: l)).size = c.size + (concatChunks l).size := by
  simp [concatChunks, ByteArray.size_append]

/-- The size of a concatenation in terms of the sum of its chunk sizes. -/
theorem concatChunks_append_map (pre l : List Bytes) :
    (concatChunks (pre ++ l)).size = (concatChunks pre).size + (l.map (·.size)).sum := by
  rw [concatChunks_size, List.map_append, List.sum_append, ← concatChunks_size]

/-- Chunk concatenation distributes over a three-way list append. -/
theorem concatChunks_triple (a b c : List Bytes) :
    concatChunks (a ++ b ++ c) = concatChunks a ++ concatChunks b ++ concatChunks c := by
  rw [concatChunks_append, concatChunks_append, ByteArray.append_assoc]

/-- The empty chunk list has size zero. -/
theorem concatChunks_nil_size : (concatChunks ([] : List Bytes)).size = 0 := rfl

/-- Size of a chunk list with one chunk appended. -/
theorem concatChunks_snoc_size (l : List Bytes) (c : Bytes) :
    (concatChunks (l ++ [c])).size = (concatChunks l).size + c.size := by
  rw [concatChunks_append, concatChunks_singleton, ByteArray.size_append]

/-- Emitting a chunk list after `acc` is the same as concatenating `acc` as
    the first chunk. -/
theorem acc_append_concatChunks (acc : Bytes) (L : List Bytes) :
    acc ++ concatChunks L = concatChunks (acc :: L) := by
  rw [show acc :: L = [acc] ++ L from rfl]
  rw [concatChunks_append, concatChunks_singleton]

/-- Split a prefix/suffix chunk list so the next field is the first chunk of
    the right operand. -/
theorem concatChunks_split (pre : List Bytes) (f : Bytes) (post : List Bytes) :
    concatChunks (pre ++ f :: post) = concatChunks pre ++ (f ++ concatChunks post) := by
  have hsplit : pre ++ f :: post = (pre ++ [f]) ++ post := by simp
  rw [hsplit, concatChunks_append, concatChunks_append, concatChunks_singleton,
    ByteArray.append_assoc]

/-- Reading a 32-bit field that starts at the end of the chunk prefix. -/
theorem getU32LE_chunk (pre : List Bytes) (v : UInt32) (post : List Bytes) :
    getU32LE (concatChunks (pre ++ putU32LE v ByteArray.empty :: post))
        (concatChunks pre).size = some v := by
  rw [concatChunks_split]
  rw [show (concatChunks pre).size = (concatChunks pre).size + 0 by omega]
  rw [getU32LE_append_right']
  rw [getU32LE_append_left (by simp)]
  exact getU32LE_putU32LE _ _

/-- Reading a 16-bit field at the end of the chunk prefix. -/
theorem getU16LE_chunk (pre : List Bytes) (v : UInt16) (post : List Bytes) :
    getU16LE (concatChunks (pre ++ putU16LE v ByteArray.empty :: post))
        (concatChunks pre).size = some v := by
  rw [concatChunks_split]
  rw [show (concatChunks pre).size = (concatChunks pre).size + 0 by omega]
  rw [getU16LE_append_right']
  rw [getU16LE_append_left (by simp)]
  exact getU16LE_putU16LE _ _

/-- Reading a 64-bit field at the end of the chunk prefix. -/
theorem getU64LE_chunk (pre : List Bytes) (v : UInt64) (post : List Bytes) :
    getU64LE (concatChunks (pre ++ putU64LE v ByteArray.empty :: post))
        (concatChunks pre).size = some v := by
  rw [concatChunks_split]
  rw [show (concatChunks pre).size = (concatChunks pre).size + 0 by omega]
  rw [getU64LE_append_right']
  rw [getU64LE_append_left (by simp)]
  exact getU64LE_putU64LE _ _

/-- Reading a signed 64-bit field (the header magic) at the prefix end. -/
theorem getI64LE_chunk (pre : List Bytes) (v : Int64) (post : List Bytes) :
    getI64LE (concatChunks (pre ++ putI64LE v ByteArray.empty :: post))
        (concatChunks pre).size = some v := by
  unfold getI64LE putI64LE
  rw [concatChunks_split]
  rw [show (concatChunks pre).size = (concatChunks pre).size + 0 by omega]
  rw [getU64LE_append_right']
  rw [getU64LE_append_left (by simp)]
  rw [show (0 : Nat) = ByteArray.empty.size from rfl]
  rw [getU64LE_putU64LE]
  simp

/-- Reading an 8-bit field at the end of the chunk prefix. -/
theorem getU8?_chunk (pre : List Bytes) (v : UInt8) (post : List Bytes) :
    getU8? (concatChunks (pre ++ putU8 v ByteArray.empty :: post))
        (concatChunks pre).size = some v := by
  rw [concatChunks_split]
  rw [show (concatChunks pre).size = (concatChunks pre).size + 0 by omega]
  rw [getU8?_append_right']
  rw [getU8?_append_left (by simp)]
  exact getU8_putU8 ByteArray.empty v

/-- Reading a VDB string at the end of the chunk prefix. -/
theorem getString?_chunk (pre : List Bytes) (s : Bytes) (post : List Bytes)
    (hsize : s.size < 2 ^ 32) :
    getString? (concatChunks (pre ++ putString s ByteArray.empty :: post))
        (concatChunks pre).size = some (s, (concatChunks pre).size + 4 + s.size) := by
  rw [concatChunks_split]
  have hassoc : concatChunks pre ++ (putString s ByteArray.empty ++ concatChunks post) =
      putString s (concatChunks pre) ++ concatChunks post := by
    rw [putString, putString]
    have h1 : putU32LE (UInt32.ofNat s.size) (concatChunks pre) =
        concatChunks pre ++ putU32LE (UInt32.ofNat s.size) ByteArray.empty :=
      pushBytes_eq_append _ _
    rw [h1]
    simp only [ByteArray.append_assoc]
  rw [hassoc]
  exact getString?_putString_append s (concatChunks pre) (concatChunks post) hsize

/-- Reading a byte blob at the end of the chunk prefix. -/
theorem getBytes?_chunk (pre : List Bytes) (c : Bytes) (post : List Bytes) :
    getBytes? (concatChunks (pre ++ c :: post)) (concatChunks pre).size c.size = some c := by
  rw [concatChunks_split]
  unfold getBytes?
  have hb : (concatChunks pre).size + c.size ≤
      (concatChunks pre ++ (c ++ concatChunks post)).size := by
    rw [ByteArray.size_append, ByteArray.size_append]; omega
  rw [ite_eq_left hb]
  congr 1
  rw [extract_append_size_head (by simp)]
  exact ByteArray.extract_append_eq_left (i := c.size) rfl

end Vdb
