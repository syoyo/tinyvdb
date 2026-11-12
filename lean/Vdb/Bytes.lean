/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Byte-level layer: total little-endian readers, emitters ("difference lists")
  and the append/extract lemmas used by the parse/emit round trips.

  Design notes:
  * All readers are total; out-of-bounds reads return `none`, never panic.
  * Emitters are `ByteArray → ByteArray`, so concatenation is composition.
  * Scalars are bit patterns (`UInt16`/`UInt32`/`UInt64`); no float semantics
    are assumed here (see `Vdb/Half.lean` for binary16).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Std.Tactic.BVDecide

namespace Vdb

/-- File-format errors. `truncated` is the byte-layer failure; the format
    layers add the remaining kinds (see `Vdb/Header.lean`). -/
inductive BytesError where
  | truncated
  deriving Repr, DecidableEq, Inhabited

/-- A VDB file is a byte string. -/
abbrev Bytes := ByteArray

instance : Repr Bytes := ⟨fun _ _ => "⟨bytes⟩"⟩

/-! ### Total byte reads -/

/-- Total byte read. `none` past the end of the array; never out of bounds. -/
def getU8? (b : Bytes) (i : Nat) : Option UInt8 :=
  if h : i < b.size then some (b[i]'h) else none

@[simp] theorem getU8?_of_lt {b : Bytes} {i : Nat} (h : i < b.size) :
    getU8? b i = some (b[i]'h) := by simp [getU8?, h]

@[simp] theorem getU8?_of_ge {b : Bytes} {i : Nat} (h : ¬ i < b.size) :
    getU8? b i = none := by simp [getU8?, h]

@[simp] theorem getU8?_size (b : Bytes) : getU8? b b.size = none := by
  simp [getU8?]

theorem getU8?_isSome_lt {b : Bytes} {i : Nat} {v : UInt8} (h : getU8? b i = some v) :
    i < b.size := by
  by_cases hlt : i < b.size
  · exact hlt
  · rw [getU8?_of_ge hlt] at h; cases h

theorem getU8?_eq_some_iff {b : Bytes} {i : Nat} {v : UInt8} (h : i < b.size) :
    getU8? b i = some v ↔ b[i]'h = v := by simp [getU8?, h]

/-- Slice of `b` from `i` to `i + n` (as a fresh array). -/
def slice? (b : Bytes) (i n : Nat) : Option Bytes :=
  if i + n ≤ b.size then some (b.extract i (i + n)) else none

theorem slice?_self (b : Bytes) : slice? b 0 b.size = some b := by
  simp [slice?, ByteArray.extract_zero_size]

/-! ### Emitters (difference lists) -/

/-- An emitter extends a byte-array context by writing bytes. -/
abbrev Emit := Bytes → Bytes

namespace Emit

def seq' (e₁ : Emit) (e₂ : Emit) : Emit := e₂ ∘ e₁

@[simp] theorem seq'_def (e₁ e₂ : Emit) : seq' e₁ e₂ = e₂ ∘ e₁ := rfl

def empty : Emit := id

@[simp] theorem empty_def : empty = id := rfl

@[simp] theorem seq'_empty (e : Emit) : seq' e empty = e := rfl

@[simp] theorem empty_seq' (e : Emit) : seq' empty e = e := rfl

end Emit

/-- Append raw bytes (the "difference list" counterpart of `getBytes?`). -/
def putBytes (s : Bytes) : Emit := fun acc => acc ++ s

/-- Bounds-checked slice: `n` bytes at `off`. -/
def getBytes? (b : Bytes) (off n : Nat) : Option Bytes :=
  if off + n ≤ b.size then some (b.extract off (off + n)) else none

/-! ### Little-endian scalar writers/readers -/

/-- Append a list of bytes. Definitive form of every multi-byte writer, which
    keeps the round-trip proofs to one induction. -/
def pushBytes (bs : List UInt8) : Emit := fun acc => bs.foldl ByteArray.push acc

def putU8 (v : UInt8) : Emit := fun acc => acc.push v

def putU16LE (v : UInt16) : Emit := pushBytes (u16Bytes v)
  where u16Bytes (v : UInt16) : List UInt8 :=
    [ (v &&& 0xff).toUInt8, ((v >>> 8) &&& 0xff).toUInt8 ]

def putU32LE (v : UInt32) : Emit := pushBytes (u32Bytes v)
  where u32Bytes (v : UInt32) : List UInt8 :=
    [ (v &&& 0xff).toUInt8, ((v >>> 8) &&& 0xff).toUInt8,
      ((v >>> 16) &&& 0xff).toUInt8, ((v >>> 24) &&& 0xff).toUInt8 ]

def putU64LE (v : UInt64) : Emit := pushBytes (u64Bytes v)
  where u64Bytes (v : UInt64) : List UInt8 :=
    [ (v &&& 0xff).toUInt8, ((v >>> 8) &&& 0xff).toUInt8,
      ((v >>> 16) &&& 0xff).toUInt8, ((v >>> 24) &&& 0xff).toUInt8,
      ((v >>> 32) &&& 0xff).toUInt8, ((v >>> 40) &&& 0xff).toUInt8,
      ((v >>> 48) &&& 0xff).toUInt8, ((v >>> 56) &&& 0xff).toUInt8 ]

def putI32LE (v : Int32) : Emit := putU32LE v.toUInt32

def putI64LE (v : Int64) : Emit := putU64LE v.toUInt64

def putF32Bits (v : UInt32) : Emit := putU32LE v

def putF64Bits (v : UInt64) : Emit := putU64LE v

def getU8 (b : Bytes) (i : Nat) : Option UInt8 := getU8? b i

def getU16LE (b : Bytes) (i : Nat) : Option UInt16 := do
  let lo ← getU8 b i
  let hi ← getU8 b (i + 1)
  pure (lo.toUInt16 ||| (hi.toUInt16 <<< 8))

def getU32LE (b : Bytes) (i : Nat) : Option UInt32 := do
  let b0 ← getU8 b i
  let b1 ← getU8 b (i + 1)
  let b2 ← getU8 b (i + 2)
  let b3 ← getU8 b (i + 3)
  pure (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) |||
        (b3.toUInt32 <<< 24))

def getU64LE (b : Bytes) (i : Nat) : Option UInt64 := do
  let b0 ← getU8 b i
  let b1 ← getU8 b (i + 1)
  let b2 ← getU8 b (i + 2)
  let b3 ← getU8 b (i + 3)
  let b4 ← getU8 b (i + 4)
  let b5 ← getU8 b (i + 5)
  let b6 ← getU8 b (i + 6)
  let b7 ← getU8 b (i + 7)
  pure (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) |||
        (b3.toUInt64 <<< 24) ||| (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) |||
        (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56))

/-- Signed 32-bit little-endian read (two's complement). -/
def getI32LE (b : Bytes) (i : Nat) : Option Int32 := (getU32LE b i).map (·.toInt32)

/-- Signed 64-bit little-endian read (two's complement). -/
def getI64LE (b : Bytes) (i : Nat) : Option Int64 := (getU64LE b i).map (·.toInt64)

def getF32Bits (b : Bytes) (i : Nat) : Option UInt32 := getU32LE b i

def getF64Bits (b : Bytes) (i : Nat) : Option UInt64 := getU64LE b i

/-! ### Bounds of multi-byte reads -/

theorem getU32LE_ibounds {b : Bytes} {i : Nat} {v : UInt32}
    (h : getU32LE b i = some v) : i + 4 ≤ b.size := by
  by_cases hi : i + 4 ≤ b.size
  · exact hi
  · exfalso
    have hi' : ¬ i + 3 < b.size := by omega
    have hnone : getU8 b (i + 3) = none := getU8?_of_ge hi'
    simp [getU32LE, hnone] at h

theorem getU64LE_ibounds {b : Bytes} {i : Nat} {v : UInt64}
    (h : getU64LE b i = some v) : i + 8 ≤ b.size := by
  by_cases hi : i + 8 ≤ b.size
  · exact hi
  · exfalso
    have hi' : ¬ i + 7 < b.size := by omega
    have hnone : getU8 b (i + 7) = none := getU8?_of_ge hi'
    simp [getU64LE, hnone] at h

/-! ### Single-byte push lemmas (needed by the `pushBytes` read lemmas) -/

theorem getElem_push_byte (b : Bytes) (v : UInt8) :
    (b.push v)[b.size]'(by simp only [ByteArray.size_push]; omega) = v := by
  simp [ByteArray.getElem_eq_getElem_data, ← ByteArray.size_data, Array.getElem_push_eq]

theorem getElem_push_of_size_eq {b : Bytes} {v : UInt8} {i : Nat} (h : i = b.size) :
    (b.push v)[i]'(h.symm ▸ by simp only [ByteArray.size_push]; omega) = v := by
  subst h; exact getElem_push_byte b v

theorem getElem_push_lt_byte {b : Bytes} {v : UInt8} {i : Nat} (h : i < b.size) :
    (b.push v)[i]'(by simp only [ByteArray.size_push]; omega) = b[i]'h := by
  simp [ByteArray.getElem_eq_getElem_data, Array.getElem_push_lt h]

theorem getU8?_push_eq (b : Bytes) (v : UInt8) :
    getU8? (b.push v) b.size = some v := by
  have h' : b.size < (b.push v).size := by simp only [ByteArray.size_push]; omega
  rw [getU8?_of_lt h', getElem_push_byte]

theorem getU8?_push_lt {b : Bytes} {v : UInt8} {i : Nat} (h : i < b.size) :
    getU8? (b.push v) i = getU8? b i := by
  have h' : i < (b.push v).size := by simp only [ByteArray.size_push]; omega
  rw [getU8?_of_lt h', getU8?_of_lt h, getElem_push_lt_byte h]

theorem getU8?_push (b : Bytes) (v : UInt8) (i : Nat) :
    getU8? (b.push v) i = if i = b.size then some v else getU8? b i := by
  by_cases h : i = b.size
  · subst h; rw [ite_eq_left rfl]; exact getU8?_push_eq b v
  · by_cases hlt : i < b.size
    · have h' : i < (b.push v).size := by simp only [ByteArray.size_push]; omega
      simp [h, getU8?_of_lt h', getU8?_of_lt hlt, getElem_push_lt_byte hlt]
    · have hge : ¬ i < (b.push v).size := by simp only [ByteArray.size_push]; omega
      simp [h, getU8?_of_ge hge, getU8?_of_ge hlt]

/-! ### Reads out of `pushBytes` -/

theorem getU8?_pushBytes_lt (bs : List UInt8) (acc : Bytes) {i : Nat}
    (h : i < acc.size) :
    getU8? (pushBytes bs acc) i = getU8? acc i := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b rest ih =>
    show getU8? (pushBytes rest (acc.push b)) i = getU8? acc i
    have h' : i < (acc.push b).size := by simp only [ByteArray.size_push]; omega
    rw [ih (acc := acc.push b) h', getU8?_push_lt h]

theorem getU8?_pushBytes_ge (bs : List UInt8) (acc : Bytes) {i : Nat}
    (h : acc.size ≤ i) :
    getU8? (pushBytes bs acc) i = bs[i - acc.size]? := by
  induction bs generalizing acc i with
  | nil =>
    show getU8? acc i = none
    exact getU8?_of_ge (by omega)
  | cons b rest ih =>
    show getU8? (pushBytes rest (acc.push b)) i = (b :: rest)[i - acc.size]?
    by_cases hlt : i < (acc.push b).size
    · -- the read lands on the pushed byte `b`
      have hi : i = acc.size := by simp only [ByteArray.size_push] at hlt; omega
      subst hi
      rw [getU8?_pushBytes_lt rest (acc := acc.push b) (i := acc.size)
        (by simp only [ByteArray.size_push]; omega)]
      rw [getU8?_push]
      simp
    · -- the read lands in `rest`
      have hge : (acc.push b).size ≤ i := by omega
      rw [ih (acc := acc.push b) hge]
      have hpos : 0 < i - acc.size := by simp only [ByteArray.size_push] at hlt; omega
      cases j : i - acc.size with
      | zero => omega
      | succ j' =>
        rw [show i - (acc.push b).size = j' by simp only [ByteArray.size_push]; omega]
        rfl

theorem getU8?_pushBytes_add (bs : List UInt8) (acc : Bytes) (k : Nat) :
    getU8? (pushBytes bs acc) (acc.size + k) = bs[k]? := by
  rw [getU8?_pushBytes_ge bs acc (by omega)]
  rw [show acc.size + k - acc.size = k by omega]

/-- `pushBytes` is an append of the pushed bytes to the accumulator. -/
theorem pushBytes_eq_append (bs : List UInt8) (acc : Bytes) :
    pushBytes bs acc = acc ++ pushBytes bs ByteArray.empty := by
  induction bs generalizing acc with
  | nil => simp [pushBytes]
  | cons b t ih =>
    change pushBytes t (acc.push b) = acc ++ pushBytes (b :: t) ByteArray.empty
    rw [ih (acc.push b)]
    have hstep : pushBytes (b :: t) ByteArray.empty =
        (ByteArray.empty.push b) ++ pushBytes t ByteArray.empty := by
      change pushBytes t (ByteArray.empty.push b) = _
      rw [ih (ByteArray.empty.push b)]
    rw [hstep]
    rw [← ByteArray.append_toByteArray_singleton (as := acc) (a := b)]
    rw [← ByteArray.append_toByteArray_singleton (as := ByteArray.empty) (a := b)]
    simp only [ByteArray.empty_append]
    rw [ByteArray.append_assoc]

theorem pushBytes_size (bs : List UInt8) (acc : Bytes) :
    (pushBytes bs acc).size = acc.size + bs.length := by
  induction bs generalizing acc with
  | nil => simp [pushBytes]
  | cons b rest ih =>
    change (pushBytes rest (acc.push b)).size = acc.size + (rest.length + 1)
    rw [ih (acc := acc.push b)]
    simp only [ByteArray.size_push]
    omega

/-! ### Append / extract lemmas used by the parse-emit round trip -/

@[simp] theorem putU8_size (v : UInt8) (acc : Bytes) : (putU8 v acc).size = acc.size + 1 := by
  simp [putU8, ByteArray.size_push]

@[simp] theorem putU16LE_size (v : UInt16) (acc : Bytes) : (putU16LE v acc).size = acc.size + 2 := by
  unfold putU16LE
  rw [pushBytes_size]
  rfl

@[simp] theorem putU32LE_size (v : UInt32) (acc : Bytes) : (putU32LE v acc).size = acc.size + 4 := by
  unfold putU32LE
  rw [pushBytes_size]
  rfl

@[simp] theorem putU64LE_size (v : UInt64) (acc : Bytes) : (putU64LE v acc).size = acc.size + 8 := by
  unfold putU64LE
  rw [pushBytes_size]
  rfl

@[simp] theorem putI32LE_size (v : Int32) (acc : Bytes) : (putI32LE v acc).size = acc.size + 4 := by
  simp [putI32LE]

@[simp] theorem putI64LE_size (v : Int64) (acc : Bytes) : (putI64LE v acc).size = acc.size + 8 := by
  simp [putI64LE]

/-- A byte read entirely inside the left operand of an append. -/
theorem getU8?_append_left {a b : Bytes} {i : Nat} (h : i < a.size) :
    getU8? (a ++ b) i = getU8? a i := by
  have h' : i < (a ++ b).size := by rw [ByteArray.size_append]; omega
  rw [getU8?_of_lt h', getU8?_of_lt h]
  congr 1
  exact ByteArray.getElem_append_left (a := a) (b := b) (i := i) (by omega)

/-- A byte read that falls in the right operand of an append. -/
theorem getU8?_append_right {a b : Bytes} {i : Nat} (h : a.size ≤ i) :
    getU8? (a ++ b) i = getU8? b (i - a.size) := by
  by_cases hlt : i < (a ++ b).size
  · have hb : i - a.size < b.size := by
      rw [ByteArray.size_append] at hlt; omega
    rw [getU8?_of_lt hlt, getU8?_of_lt hb]
    congr 1
    exact ByteArray.getElem_append_right (a := a) (b := b) (i := i) (by omega)
  · have hb : ¬ i - a.size < b.size := by
      rw [ByteArray.size_append] at hlt; omega
    rw [getU8?_of_ge hlt, getU8?_of_ge hb]

/-- A byte read at an offset past the left operand of an append. -/
theorem getU8?_append_right' {a b : Bytes} (k : Nat) :
    getU8? (a ++ b) (a.size + k) = getU8? b k := by
  rw [getU8?_append_right (a := a) (b := b) (i := a.size + k) (by omega),
    show a.size + k - a.size = k by omega]

/-- A 32-bit read at an offset past the left operand of an append. -/
theorem getU32LE_append_right' {a b : Bytes} (j : Nat) :
    getU32LE (a ++ b) (a.size + j) = getU32LE b j := by
  have e : ∀ k, k < 4 → getU8? (a ++ b) (a.size + j + k) = getU8? b (j + k) := by
    intro k _
    rw [getU8?_append_right (a := a) (b := b) (i := a.size + j + k) (by omega)]
    rw [show a.size + j + k - a.size = j + k by omega]
  unfold getU32LE
  simp only [getU8]
  have h0 := e 0 (by omega)
  simp only [Nat.add_zero] at h0
  rw [h0, e 1 (by omega), e 2 (by omega), e 3 (by omega)]

/-- An 8-byte read at an offset past the left operand of an append. -/
theorem getU64LE_append_right' {a b : Bytes} (j : Nat) :
    getU64LE (a ++ b) (a.size + j) = getU64LE b j := by
  have e : ∀ k, k < 8 → getU8? (a ++ b) (a.size + j + k) = getU8? b (j + k) := by
    intro k _
    rw [getU8?_append_right (a := a) (b := b) (i := a.size + j + k) (by omega)]
    rw [show a.size + j + k - a.size = j + k by omega]
  unfold getU64LE
  simp only [getU8]
  have h0 := e 0 (by omega)
  simp only [Nat.add_zero] at h0
  rw [h0, e 1 (by omega), e 2 (by omega), e 3 (by omega),
      e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega)]

theorem getU32LE_append_left {a b : Bytes} {i : Nat} (h : i + 4 ≤ a.size) :
    getU32LE (a ++ b) i = getU32LE a i := by
  have e : ∀ k < 4, getU8? (a ++ b) (i + k) = getU8? a (i + k) := by
    intro k _
    exact getU8?_append_left (a := a) (b := b) (i := i + k) (by omega)
  unfold getU32LE
  simp only [getU8]
  have h0 := e 0 (by omega)
  simp only [Nat.add_zero] at h0
  rw [h0, e 1 (by omega), e 2 (by omega), e 3 (by omega)]

/-- An 8-byte read entirely inside the left operand of an append. -/
theorem getU64LE_append_left {a b : Bytes} {i : Nat} (h : i + 8 ≤ a.size) :
    getU64LE (a ++ b) i = getU64LE a i := by
  have e : ∀ k < 8, getU8? (a ++ b) (i + k) = getU8? a (i + k) := by
    intro k _
    exact getU8?_append_left (a := a) (b := b) (i := i + k) (by omega)
  unfold getU64LE
  simp only [getU8]
  have h0 := e 0 (by omega)
  simp only [Nat.add_zero] at h0
  rw [h0, e 1 (by omega), e 2 (by omega), e 3 (by omega),
      e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega)]

/-- A 16-bit read entirely inside the left operand of an append. -/
theorem getU16LE_append_left {a b : Bytes} {i : Nat} (h : i + 2 ≤ a.size) :
    getU16LE (a ++ b) i = getU16LE a i := by
  unfold getU16LE
  have e0 : getU8 (a ++ b) i = getU8 a i := by
    simp only [getU8]
    exact getU8?_append_left (by omega)
  have e1 : getU8 (a ++ b) (i + 1) = getU8 a (i + 1) := by
    simp only [getU8]
    exact getU8?_append_left (by omega)
  rw [e0, e1]

/-- A 16-bit read at an offset past the left operand of an append. -/
theorem getU16LE_append_right' {a b : Bytes} (j : Nat) :
    getU16LE (a ++ b) (a.size + j) = getU16LE b j := by
  unfold getU16LE
  have e0 : getU8 (a ++ b) (a.size + j) = getU8 b j := by
    simp only [getU8]
    exact getU8?_append_right' j
  have e1 : getU8 (a ++ b) (a.size + j + 1) = getU8 b (j + 1) := by
    simp only [getU8]
    rw [show a.size + j + 1 = a.size + (j + 1) by omega]
    exact getU8?_append_right' (j + 1)
  rw [e0, e1]

/-- A signed 64-bit read at an offset past the left operand of an append. -/
theorem getI64LE_append_right' {a b : Bytes} (j : Nat) :
    getI64LE (a ++ b) (a.size + j) = getI64LE b j := by
  unfold getI64LE
  rw [getU64LE_append_right']

/-- A 64-bit read entirely inside the left operand of an append. -/
theorem getI64LE_append_left {a b : Bytes} {i : Nat} (h : i + 8 ≤ a.size) :
    getI64LE (a ++ b) i = getI64LE a i := by
  unfold getI64LE
  rw [getU64LE_append_left h]

/-- A byte read at an offset past two nested left operands. -/
theorem getU8?_nested {p s rest : Bytes} (k : Nat) :
    getU8? (p ++ (s ++ rest)) (p.size + s.size + k) = getU8? rest k := by
  rw [show p.size + s.size + k = p.size + (s.size + k) by omega,
    getU8?_append_right' (a := p) (b := s ++ rest) (k := s.size + k),
    getU8?_append_right' (a := s) (b := rest) (k := k)]

/-- Extracting exactly the head of the appended array. -/
theorem extract_append_size_head {a b : Bytes} {k : Nat} (_hk : k ≤ b.size) :
    (a ++ b).extract a.size (a.size + k) = b.extract 0 k := by
  rw [show a.size = a.size + 0 from by omega,
      show a.size + 0 + k = a.size + k from by omega]
  rw [ByteArray.extract_append_size_add]

/-- Extracting a suffix that starts at `a.size` gives the right operand. -/
theorem extract_append_right_eq {a b : Bytes} :
    (a ++ b).extract a.size (a.size + b.size) = b :=
  ByteArray.extract_append_eq_right (i := a.size) (j := a.size + b.size)
    (by omega) (by omega)

/-- A left fold of appends equals the initial bytes followed by the right
    fold (associativity of `++`). -/
theorem foldl_append_eq_foldr {α : Type} (l : List α) (f : α → Bytes) (acc : Bytes) :
    l.foldl (fun acc' a => acc' ++ f a) acc =
      acc ++ l.foldr (fun a acc' => f a ++ acc') ByteArray.empty := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, ih, List.foldr_cons, ← ByteArray.append_assoc]

/-! ### Round-trip lemmas -/

theorem getU16LE_putU16LE (acc : Bytes) (v : UInt16) :
    getU16LE (putU16LE v acc) acc.size = some v := by
  have e0 : getU8 (putU16LE v acc) acc.size =
      some (v &&& 0xff).toUInt8 := by
    simp only [getU8, putU16LE]
    rw [show acc.size = acc.size + 0 by omega, getU8?_pushBytes_add (k := 0)]; rfl
  have e1 : getU8 (putU16LE v acc) (acc.size + 1) =
      some ((v >>> 8) &&& 0xff).toUInt8 := by
    simp only [getU8, putU16LE]
    rw [getU8?_pushBytes_add (k := 1)]; rfl
  simp [getU16LE, e0, e1]
  congr 1
  bv_decide

theorem getU32LE_putU32LE (acc : Bytes) (v : UInt32) :
    getU32LE (putU32LE v acc) acc.size = some v := by
  have e0 : getU8 (putU32LE v acc) acc.size =
      some (v &&& 0xff).toUInt8 := by
    simp only [getU8, putU32LE]
    rw [show acc.size = acc.size + 0 by omega, getU8?_pushBytes_add (k := 0)]; rfl
  have e1 : getU8 (putU32LE v acc) (acc.size + 1) =
      some ((v >>> 8) &&& 0xff).toUInt8 := by
    simp only [getU8, putU32LE]
    rw [getU8?_pushBytes_add (k := 1)]; rfl
  have e2 : getU8 (putU32LE v acc) (acc.size + 2) =
      some ((v >>> 16) &&& 0xff).toUInt8 := by
    simp only [getU8, putU32LE]
    rw [getU8?_pushBytes_add (k := 2)]; rfl
  have e3 : getU8 (putU32LE v acc) (acc.size + 3) =
      some ((v >>> 24) &&& 0xff).toUInt8 := by
    simp only [getU8, putU32LE]
    rw [getU8?_pushBytes_add (k := 3)]; rfl
  simp [getU32LE, e0, e1, e2, e3]
  congr 1
  bv_decide

theorem getU64LE_putU64LE (acc : Bytes) (v : UInt64) :
    getU64LE (putU64LE v acc) acc.size = some v := by
  have e0 : getU8 (putU64LE v acc) acc.size =
      some (v &&& 0xff).toUInt8 := by
    simp only [getU8, putU64LE]
    rw [show acc.size = acc.size + 0 by omega, getU8?_pushBytes_add (k := 0)]; rfl
  have e1 : getU8 (putU64LE v acc) (acc.size + 1) =
      some ((v >>> 8) &&& 0xff).toUInt8 := by
    simp only [getU8, putU64LE]
    rw [getU8?_pushBytes_add (k := 1)]; rfl
  have e2 : getU8 (putU64LE v acc) (acc.size + 2) =
      some ((v >>> 16) &&& 0xff).toUInt8 := by
    simp only [getU8, putU64LE]
    rw [getU8?_pushBytes_add (k := 2)]; rfl
  have e3 : getU8 (putU64LE v acc) (acc.size + 3) =
      some ((v >>> 24) &&& 0xff).toUInt8 := by
    simp only [getU8, putU64LE]
    rw [getU8?_pushBytes_add (k := 3)]; rfl
  have e4 : getU8 (putU64LE v acc) (acc.size + 4) =
      some ((v >>> 32) &&& 0xff).toUInt8 := by
    simp only [getU8, putU64LE]
    rw [getU8?_pushBytes_add (k := 4)]; rfl
  have e5 : getU8 (putU64LE v acc) (acc.size + 5) =
      some ((v >>> 40) &&& 0xff).toUInt8 := by
    simp only [getU8, putU64LE]
    rw [getU8?_pushBytes_add (k := 5)]; rfl
  have e6 : getU8 (putU64LE v acc) (acc.size + 6) =
      some ((v >>> 48) &&& 0xff).toUInt8 := by
    simp only [getU8, putU64LE]
    rw [getU8?_pushBytes_add (k := 6)]; rfl
  have e7 : getU8 (putU64LE v acc) (acc.size + 7) =
      some ((v >>> 56) &&& 0xff).toUInt8 := by
    simp only [getU8, putU64LE]
    rw [getU8?_pushBytes_add (k := 7)]; rfl
  simp [getU64LE, e0, e1, e2, e3, e4, e5, e6, e7]
  congr 1
  bv_decide

theorem getU8_putU8 (acc : Bytes) (v : UInt8) :
    getU8 (putU8 v acc) acc.size = some v := by
  simp only [getU8, putU8]
  rw [getU8?_push_eq]

theorem getI32LE_putI32LE (acc : Bytes) (v : Int32) :
    getI32LE (putI32LE v acc) acc.size = some v := by
  simp [getI32LE, putI32LE, getU32LE_putU32LE]

theorem getI64LE_putI64LE (acc : Bytes) (v : Int64) :
    getI64LE (putI64LE v acc) acc.size = some v := by
  simp [getI64LE, putI64LE, getU64LE_putU64LE]

theorem getF32Bits_putF32Bits (acc : Bytes) (v : UInt32) :
    getF32Bits (putF32Bits v acc) acc.size = some v := by
  simp [getF32Bits, putF32Bits, getU32LE_putU32LE]

theorem getF64Bits_putF64Bits (acc : Bytes) (v : UInt64) :
    getF64Bits (putF64Bits v acc) acc.size = some v := by
  simp [getF64Bits, putF64Bits, getU64LE_putU64LE]

/-! ### String and blob wire primitives -/

/-- A VDB string: `u32` length followed by that many bytes (no terminator). -/
def putString (s : Bytes) : Emit :=
  fun acc => (putU32LE (UInt32.ofNat s.size)) acc ++ s

/-- Parse a VDB string; returns the bytes and the next offset. -/
def getString? (b : Bytes) (off : Nat) : Option (Bytes × Nat) :=
  match getU32LE b off with
  | none => none
  | some n =>
    match getBytes? b (off + 4) n.toNat with
    | none => none
    | some payload => some (payload, off + 4 + n.toNat)

theorem getBytes?_append (s acc : Bytes) :
    getBytes? (acc ++ s) acc.size s.size = some s := by
  unfold getBytes?
  have h : acc.size + s.size ≤ (acc ++ s).size := by
    rw [ByteArray.size_append]; omega
  rw [ite_eq_left h]
  exact congrArg some extract_append_right_eq

/-- The same read with the `putBytes` spelling. -/
theorem getBytes?_putBytes (s acc : Bytes) :
    getBytes? (putBytes s acc) acc.size s.size = some s := getBytes?_append s acc

theorem putString_size (s acc : Bytes) :
    (putString s acc).size = acc.size + 4 + s.size := by
  unfold putString
  rw [ByteArray.size_append]
  have h : (putU32LE (UInt32.ofNat s.size) acc).size = acc.size + 4 := by
    unfold putU32LE
    rw [pushBytes_size]
    rfl
  rw [h]

theorem getString?_putString (s acc : Bytes) (hsize : s.size < 2 ^ 32) :
    getString? (putString s acc) acc.size = some (s, acc.size + 4 + s.size) := by
  unfold getString? putString
  have hoff : (putU32LE (UInt32.ofNat s.size) acc).size = acc.size + 4 := by
    unfold putU32LE
    rw [pushBytes_size]
    rfl
  rw [getU32LE_append_left (a := (putU32LE (UInt32.ofNat s.size)) acc) (b := s)
    (i := acc.size) (by rw [hoff]; omega)]
  rw [getU32LE_putU32LE]
  dsimp only
  have htoNat : (UInt32.ofNat s.size).toNat = s.size := by
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt hsize
  have hoff' : acc.size + 4 = (putU32LE (UInt32.ofNat s.size) acc).size := hoff.symm
  rw [htoNat, hoff', getBytes?_append]

/-- A byte blob read at a prefix boundary with trailing bytes. -/
theorem getBytes?_prefix (a s rest : Bytes) :
    getBytes? (a ++ (s ++ rest)) a.size s.size = some s := by
  unfold getBytes?
  rw [ite_eq_left (by simp [ByteArray.size_append])]
  congr 1
  rw [extract_append_size_head (by simp)]
  exact ByteArray.extract_append_eq_left (i := s.size) rfl

/-- Reading a VDB string at `acc.size` with trailing bytes after it. -/
theorem getString?_putString_append (s acc rest : Bytes) (hsize : s.size < 2 ^ 32) :
    getString? (putString s acc ++ rest) acc.size = some (s, acc.size + 4 + s.size) := by
  unfold getString? putString
  have hoff : (putU32LE (UInt32.ofNat s.size) acc).size = acc.size + 4 := by
    unfold putU32LE
    rw [pushBytes_size]
    rfl
  rw [ByteArray.append_assoc]
  rw [getU32LE_append_left (a := (putU32LE (UInt32.ofNat s.size) acc)) (b := s ++ rest)
    (i := acc.size) (by rw [hoff]; omega)]
  rw [getU32LE_putU32LE]
  dsimp only
  have htoNat : (UInt32.ofNat s.size).toNat = s.size := by
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt hsize
  rw [htoNat]
  rw [show acc.size + 4 = (putU32LE (UInt32.ofNat s.size) acc).size from hoff.symm]
  rw [getBytes?_prefix]

end Vdb
