/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Parse stability under a trailing append: when a read succeeds on `b`, it
  succeeds with the same value on `b ++ rest`. These lemmas are what let a
  record parser be reused in the middle of a larger file, without redoing
  every round-trip proof over trailing bytes.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Bytes

set_option linter.unusedSimpArgs false

namespace Vdb

theorem getU8?_append_of_some {b r : Bytes} {i : Nat} {v : UInt8}
    (h : getU8? b i = some v) : getU8? (b ++ r) i = some v := by
  rw [getU8?_append_left (by
    by_contra hlt
    rw [getU8?_of_ge hlt] at h
    contradiction)]
  exact h

theorem getBytes?_append_of_some {b r : Bytes} {off n : Nat} {v : Bytes}
    (h : getBytes? b off n = some v) : getBytes? (b ++ r) off n = some v := by
  unfold getBytes? at h ⊢
  split at h
  · rename_i hle
    rw [ite_eq_left (by rw [ByteArray.size_append]; omega)]
    congr 1
    rw [ByteArray.extract_append]
    have h1 : off - b.size = 0 := by omega
    have h2 : off + n - b.size = 0 := by omega
    rw [h1, h2]
    simp
    simpa using h
  · contradiction

theorem getU32LE_append_of_some {b r : Bytes} {i : Nat} {v : UInt32}
    (h : getU32LE b i = some v) : getU32LE (b ++ r) i = some v := by
  rw [getU32LE_append_left (getU32LE_ibounds h)]
  exact h

theorem getU64LE_append_of_some {b r : Bytes} {i : Nat} {v : UInt64}
    (h : getU64LE b i = some v) : getU64LE (b ++ r) i = some v := by
  rw [getU64LE_append_left (getU64LE_ibounds h)]
  exact h

theorem getI32LE_append_of_some {b r : Bytes} {i : Nat} {v : Int32}
    (h : getI32LE b i = some v) : getI32LE (b ++ r) i = some v := by
  unfold getI32LE at h ⊢
  cases hx : getU32LE b i with
  | none =>
    rw [hx] at h
    simp at h
  | some x =>
    rw [hx] at h
    rw [getU32LE_append_of_some hx]
    exact h

theorem getI64LE_append_of_some {b r : Bytes} {i : Nat} {v : Int64}
    (h : getI64LE b i = some v) : getI64LE (b ++ r) i = some v := by
  unfold getI64LE at h ⊢
  cases hx : getU64LE b i with
  | none =>
    rw [hx] at h
    simp at h
  | some x =>
    rw [hx] at h
    rw [getU64LE_append_of_some hx]
    exact h

theorem getString?_append_of_some {b r : Bytes} {off : Nat} {p : Bytes × Nat}
    (h : getString? b off = some p) : getString? (b ++ r) off = some p := by
  unfold getString? at h ⊢
  split at h
  · contradiction
  · rename_i n hn
    rw [getU32LE_append_of_some hn]
    dsimp only
    split at h
    · contradiction
    · rename_i d hd
      rw [getBytes?_append_of_some hd]
      dsimp only
      simpa using h

end Vdb
