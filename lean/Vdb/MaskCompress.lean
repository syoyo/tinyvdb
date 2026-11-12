/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Per-node value-mask compression (`tvdb__read_mask_values` /
  `tvdb__write_mask_values`): the seven `MaskCompress` codes, the stored-value
  compaction order, and the decoder used for both internal nodes and leaves.

  Codes (OpenVDB `MaskCompress`):

  | code | name                        | stored after the code byte        | inactive value |
  |------|-----------------------------|-----------------------------------|----------------|
  | 0    | NO_MASK_OR_INACTIVE_VALS    | nothing                           | `+bg`          |
  | 1    | NO_MASK_AND_MINUS_BG        | nothing                           | `-bg`          |
  | 2    | NO_MASK_AND_ONE_INACTIVE_VAL| `val0`                            | `val0`         |
  | 3    | MASK_AND_NO_INACTIVE_VALS   | selection mask                    | `-bg` / `+bg`  |
  | 4    | MASK_AND_ONE_INACTIVE_VAL   | `val0`, selection mask            | `val0` / `+bg` |
  | 5    | MASK_AND_TWO_INACTIVE_VALS  | `val0`, `val1`, selection mask    | `val0`/`val1`  |
  | 6    | NO_MASK_AND_ALL_VALS        | every value (no compaction)       | —              |

  Values are stored in increasing slot order (the k-th value belongs to the
  k-th set bit of the value mask). A half-precision grid stores inactive
  values at full width as well; that is a byte-layout fact handled by the
  value encoder, not by this layer.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Mask
import Vdb.Value

namespace Vdb

/-! ### Codes -/

/-- The seven mask-compression codes. -/
inductive MaskCode where
  | noMaskOrInactiveVals
  | noMaskAndMinusBg
  | noMaskAndOneInactiveVal
  | maskAndNoInactiveVals
  | maskAndOneInactiveVal
  | maskAndTwoInactiveVals
  | noMaskAndAllVals
  deriving Repr, DecidableEq

def MaskCode.toNat : MaskCode → Nat
  | .noMaskOrInactiveVals => 0
  | .noMaskAndMinusBg => 1
  | .noMaskAndOneInactiveVal => 2
  | .maskAndNoInactiveVals => 3
  | .maskAndOneInactiveVal => 4
  | .maskAndTwoInactiveVals => 5
  | .noMaskAndAllVals => 6

/-- Decode a code byte; anything above 6 is invalid (the C reader clamps by
    treating unknown codes as all-values in some paths, which the model makes
    explicit instead). -/
def MaskCode.ofNat? : Nat → Option MaskCode
  | 0 => some .noMaskOrInactiveVals
  | 1 => some .noMaskAndMinusBg
  | 2 => some .noMaskAndOneInactiveVal
  | 3 => some .maskAndNoInactiveVals
  | 4 => some .maskAndOneInactiveVal
  | 5 => some .maskAndTwoInactiveVals
  | 6 => some .noMaskAndAllVals
  | _ => none

theorem MaskCode.ofNat?_toNat (c : MaskCode) : MaskCode.ofNat? c.toNat = some c := by
  cases c <;> rfl

/-- How many values a reader consumes: `popcount(mask)` for the compacted
    codes (file version ≥ 222 with active-mask compression), or all slots. -/
def readCount (n valueMask : Nat) (code : MaskCode) : Nat :=
  match code with
  | .noMaskAndAllVals => n
  | _ => NodeMask.rank valueMask n

theorem readCount_le (n valueMask : Nat) (code : MaskCode) :
    readCount n valueMask code ≤ n := by
  cases code <;>
    simp only [readCount] <;>
    first
      | exact Nat.le_refl _
      | exact NodeMask.rank_le_index valueMask n

/-! ### Negation

`-bg` is a bit flip for floating-point values (so `-0` and NaN payloads are
preserved) and integer negation for the integral types; bool trees are
unaffected, like the C `tvdb__negate`. -/

/-- Negate a voxel value (`+bg → -bg`, used by codes 1 and 3). -/
def VoxelValue.negate : VoxelValue → VoxelValue
  | .boolean b => .boolean b
  | .int32 i => .int32 (-i)
  | .int64 i => .int64 (-i)
  | .f32 b => .f32 (b ^^^ 0x80000000)
  | .f64 b => .f64 (b ^^^ 0x8000000000000000)
  | .vec3i x y z => .vec3i (-x) (-y) (-z)
  | .vec3f x y z => .vec3f (x ^^^ 0x80000000) (y ^^^ 0x80000000) (z ^^^ 0x80000000)
  | .vec3d x y z =>
    .vec3d (x ^^^ 0x8000000000000000) (y ^^^ 0x8000000000000000)
      (z ^^^ 0x8000000000000000)

/-- The type is preserved by negation. -/
theorem VoxelValue.type_negate (v : VoxelValue) : v.negate.type = v.type := by
  cases v <;> rfl

/-- Negation is an involution for floating-point (bit flip), bool and
    single-component vector values. For signed integers it holds whenever the
    value is not the type minimum (`-min` saturates), which call sites
    guarantee for backgrounds; see `Vdb/Levelset` for that argument. -/
theorem VoxelValue.negate_negate_float (b : UInt32) :
    (VoxelValue.f32 b).negate.negate = VoxelValue.f32 b := by
  simp [VoxelValue.negate]
  bv_decide

theorem VoxelValue.negate_negate_double (b : UInt64) :
    (VoxelValue.f64 b).negate.negate = VoxelValue.f64 b := by
  simp [VoxelValue.negate]
  bv_decide

theorem VoxelValue.negate_negate_bool (b : Bool) :
    (VoxelValue.boolean b).negate.negate = VoxelValue.boolean b := rfl

/-! ### Decoding

The decoder needs only: the background, the code, the two inactive values,
the selection mask, the value mask and the compacted active values. Slots
that are active take values from `active` by rank; inactive slots take the
code's inactive value. -/

/-- Value at slot `i` given a decoded node. `active` holds the stored values
    in increasing slot order. -/
def decodeSlot (bg : VoxelValue) (code : MaskCode) (sel : Nat)
    (val0 val1 : VoxelValue) (valueMask : Nat) (active : List VoxelValue)
    (i : Nat) : VoxelValue :=
  if NodeMask.bit valueMask i then
    (active[NodeMask.rank valueMask i]?).getD bg
  else
    match code with
    | .noMaskOrInactiveVals => bg
    | .noMaskAndMinusBg => bg.negate
    | .noMaskAndOneInactiveVal => val0
    | .maskAndNoInactiveVals => if NodeMask.bit sel i then bg else bg.negate
    | .maskAndOneInactiveVal => if NodeMask.bit sel i then bg else val0
    | .maskAndTwoInactiveVals => if NodeMask.bit sel i then val1 else val0
    | .noMaskAndAllVals => (active[i]?).getD bg

/-- An active slot reads from the compacted value list. -/
theorem decodeSlot_active {bg : VoxelValue} {code : MaskCode} {sel : Nat}
    {val0 val1 : VoxelValue} {valueMask : Nat} {active : List VoxelValue} {i : Nat}
    (h : NodeMask.bit valueMask i = true) :
    decodeSlot bg code sel val0 val1 valueMask active i =
      (active[NodeMask.rank valueMask i]?).getD bg := by
  simp [decodeSlot, h]

/-- When the compacted list is the stored value image of the set bits, an
    active slot decodes to exactly its original value. This is the active
    half of the mask-compression round trip; the inactive half is the
    classification invariant proved in `classify`. -/
theorem decodeSlot_active_stored {bg : VoxelValue} {code : MaskCode} {sel : Nat}
    {val0 val1 : VoxelValue} {valueMask : Nat} {values : Nat → VoxelValue}
    {n i : Nat} (hn : i < n) (hb : valueMask.testBit i = true) :
    decodeSlot bg code sel val0 val1 valueMask
        ((setBits valueMask n).map values) i = values i := by
  rw [decodeSlot_active (by simpa [NodeMask.bit] using hb)]
  rw [List.getElem?_map, getElem?_setBits_rank hn hb]
  simp

/-! ### Classification (the encoder side)

`classify` mirrors `tvdb__write_mask_values`: scan the inactive values for at
most three distinct ones (seeded with the background), then pick the code that
reconstructs them from `{±bg, val0, val1}` plus a selection mask. -/

/-- Slots with no value (inactive), in increasing order. -/
def inactiveSlots (mask n : Nat) : List Nat :=
  (List.range n).filter (fun i => !mask.testBit i)

/-- Inactive stored values in slot order. -/
def inactiveValues (values : Nat → VoxelValue) (mask n : Nat) : List VoxelValue :=
  (inactiveSlots mask n).map values

/-- A node's classification: code plus the two inactive values and the
    selection mask choosing `val1` where set. -/
structure Compressed where
  code : MaskCode
  val0 : VoxelValue
  val1 : VoxelValue
  selection : Nat

/-- Selection mask: bits set for inactive slots whose value equals `v1`. -/
def selectionOf (values : Nat → VoxelValue) (mask n : Nat) (v1 : VoxelValue) : Nat :=
  (inactiveSlots mask n).foldl
    (fun acc i => if values i = v1 then acc ||| (1 <<< i) else acc) 0

/-- The C classifier's running state: two inactive values and a count that
    saturates at 3. -/
structure Scan where
  u0 : VoxelValue
  u1 : VoxelValue
  count : Nat

/-- One step of the unique-inactive-value scan (seeded with the background). -/
def Scan.step (s : Scan) (v : VoxelValue) : Scan :=
  if s.count > 0 ∧ v = s.u0 then s
  else if s.count > 1 ∧ v = s.u1 then s
  else if s.count < 2 then
    (if s.count = 0 then { s with u0 := v, count := 1 }
     else { s with u1 := v, count := 2 })
  else { s with count := 3 }

/-- Fold the scan over the inactive values. -/
def scanValues (vs : List VoxelValue) (bg : VoxelValue) : Scan :=
  vs.foldl Scan.step ⟨bg, bg, 0⟩

/-- Classify a node the way the writer does. -/
def classify (bg : VoxelValue) (values : Nat → VoxelValue) (mask n : Nat) : Compressed :=
  let sc := scanValues (inactiveValues values mask n) bg
  let negBg := bg.negate
  if sc.count = 0 then ⟨.noMaskOrInactiveVals, bg, bg, 0⟩
  else if sc.count = 1 then
    (if sc.u0 = bg then ⟨.noMaskOrInactiveVals, bg, bg, 0⟩
     else if sc.u0 = negBg then ⟨.noMaskAndMinusBg, bg, bg, 0⟩
     else ⟨.noMaskAndOneInactiveVal, sc.u0, bg, 0⟩)
  else if sc.count = 2 then
    (if sc.u1 = bg then
       (if sc.u0 = negBg then
          ⟨.maskAndNoInactiveVals, sc.u0, bg, selectionOf values mask n bg⟩
        else ⟨.maskAndOneInactiveVal, sc.u0, bg, selectionOf values mask n bg⟩)
     else if sc.u0 = bg then
       -- the background was seen first: swap so that `val1` is the background
       (if sc.u1 = negBg then
          ⟨.maskAndNoInactiveVals, sc.u1, bg, selectionOf values mask n bg⟩
        else ⟨.maskAndOneInactiveVal, sc.u1, bg, selectionOf values mask n bg⟩)
     else ⟨.maskAndTwoInactiveVals, sc.u0, sc.u1, selectionOf values mask n sc.u1⟩)
  else ⟨.noMaskAndAllVals, bg, bg, 0⟩

/-- The value list a reader reconstructs from: the compacted active values,
    or every slot for code 6. -/
def storedValues (values : Nat → VoxelValue) (mask n : Nat) (c : Compressed) :
    List VoxelValue :=
  match c.code with
  | .noMaskAndAllVals => (List.range n).map values
  | _ => (setBits mask n).map values

/-- Decode a full node from its classification. -/
def decodeAll (bg : VoxelValue) (values : Nat → VoxelValue) (mask n : Nat)
    (c : Compressed) (i : Nat) : VoxelValue :=
  decodeSlot bg c.code c.selection c.val0 c.val1 mask
    (storedValues values mask n c) i

/-! ### The uniform case: every inactive value is the background -/

/-- A step that sees the current `u0` again leaves the scan unchanged. -/
theorem Scan.step_of_eq_u0 (s : Scan) (v : VoxelValue) (hpos : s.count > 0)
    (hv : v = s.u0) : Scan.step s v = s := by
  unfold Scan.step
  rw [ite_eq_left ⟨hpos, hv⟩]

/-- A constant-background inactive list keeps the scan at count ≤ 1 and
    `u0 = bg`. -/
theorem fold_const_bg : ∀ (vs : List VoxelValue) (s : Scan) (bg : VoxelValue),
    s.count ≤ 1 → s.u0 = bg → (∀ v ∈ vs, v = bg) →
    (vs.foldl Scan.step s).count ≤ 1 ∧ (vs.foldl Scan.step s).u0 = bg
  | [], s, bg, hs, hu, _ => ⟨hs, hu⟩
  | v :: t, s, bg, hs, hu, hvs => by
    have hv : v = bg := hvs v (by simp)
    rw [hv]
    have ih := fold_const_bg t (Scan.step s bg) bg ?_ ?_
      (fun x hx => hvs x (by simp [hx]))
    · exact ih
    · by_cases h0 : s.count = 0
      · simp [Scan.step, h0]
      · have hpos : s.count > 0 := by omega
        rw [Scan.step_of_eq_u0 s bg hpos hu.symm]
        exact hs
    · by_cases h0 : s.count = 0
      · simp [Scan.step, h0]
      · have hpos : s.count > 0 := by omega
        rw [Scan.step_of_eq_u0 s bg hpos hu.symm]
        exact hu

/-- Slots in `inactiveSlots` are below `n` and inactive. -/
theorem mem_inactiveSlots {mask n i : Nat} (h : i ∈ inactiveSlots mask n) :
    i < n ∧ mask.testBit i = false := by
  unfold inactiveSlots at h
  rw [List.mem_filter] at h
  obtain ⟨hmem, hbit⟩ := h
  refine ⟨by simpa using hmem, ?_⟩
  simpa using hbit

/-- The inactive value list is constant when every inactive slot holds `bg`. -/
theorem inactiveValues_eq_bg {values : Nat → VoxelValue} {mask n : Nat} {bg : VoxelValue}
    (h : ∀ i < n, mask.testBit i = false → values i = bg) :
    ∀ v ∈ inactiveValues values mask n, v = bg := by
  intro v hv
  unfold inactiveValues at hv
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
  obtain ⟨hlt, hbit⟩ := mem_inactiveSlots hi
  exact h i hlt hbit

/-- The unique-value scan of a constant background list has count ≤ 1 and
    keeps `u0 = bg`. -/
theorem scan_uniform {values : Nat → VoxelValue} {mask n : Nat} {bg : VoxelValue}
    (h : ∀ i < n, mask.testBit i = false → values i = bg) :
    (scanValues (inactiveValues values mask n) bg).count ≤ 1 ∧
    (scanValues (inactiveValues values mask n) bg).u0 = bg :=
  fold_const_bg _ ⟨bg, bg, 0⟩ bg (by simp) rfl (inactiveValues_eq_bg h)

/-- A constant-background node classifies as `NO_MASK_OR_INACTIVE_VALS`. -/
theorem classify_uniform {values : Nat → VoxelValue} {mask n : Nat} {bg : VoxelValue}
    (h : ∀ i < n, mask.testBit i = false → values i = bg) :
    classify bg values mask n = ⟨.noMaskOrInactiveVals, bg, bg, 0⟩ := by
  have hc := scan_uniform h
  unfold classify
  by_cases h0 : (scanValues (inactiveValues values mask n) bg).count = 0
  · simp [h0]
  · have h1 : (scanValues (inactiveValues values mask n) bg).count = 1 := by omega
    have hu : (scanValues (inactiveValues values mask n) bg).u0 = bg := hc.2
    simp [h1, hu]

/-- **Mask-compression round trip, uniform case**: if every inactive slot holds
    the background, the classified node decodes to the original values on every
    slot inside the node. -/
theorem classify_uniform_decode {values : Nat → VoxelValue} {mask n i : Nat}
    {bg : VoxelValue}
    (h : ∀ i < n, mask.testBit i = false → values i = bg) (hn : i < n) :
    decodeAll bg values mask n (classify bg values mask n) i = values i := by
  rw [classify_uniform h]
  unfold decodeAll storedValues decodeSlot
  by_cases hb : NodeMask.bit mask i
  · simp only [hb]
    rw [List.getElem?_map,
      getElem?_setBits_rank hn (by simpa [NodeMask.bit] using hb)]
    simp
  · simp only [hb]
    have hoff : mask.testBit i = false := by simpa [NodeMask.bit] using hb
    exact (h i hn hoff).symm

end Vdb
