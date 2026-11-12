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

/-- Value at slot `i` of a compacted node (codes 0–5): active slots read the
    stored list by rank, inactive slots take the code's inactive value. -/
def decodeCompacted (bg : VoxelValue) (code : MaskCode) (sel : Nat)
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

/-- An active slot of a compacted code reads from the value list by rank. -/
theorem decodeCompacted_active {bg : VoxelValue} {code : MaskCode} {sel : Nat}
    {val0 val1 : VoxelValue} {valueMask : Nat} {active : List VoxelValue} {i : Nat}
    (h : NodeMask.bit valueMask i = true) :
    decodeCompacted bg code sel val0 val1 valueMask active i =
      (active[NodeMask.rank valueMask i]?).getD bg := by
  simp [decodeCompacted, h]

/-- When the compacted list is the stored value image of the set bits, an
    active slot decodes to exactly its original value. -/
theorem decodeCompacted_active_stored {bg : VoxelValue} {code : MaskCode} {sel : Nat}
    {val0 val1 : VoxelValue} {valueMask : Nat} {values : Nat → VoxelValue}
    {n i : Nat} (hn : i < n) (hb : valueMask.testBit i = true) :
    decodeCompacted bg code sel val0 val1 valueMask
        ((setBits valueMask n).map values) i = values i := by
  rw [decodeCompacted_active (by simpa [NodeMask.bit] using hb)]
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

theorem storedValues_of_ne {values : Nat → VoxelValue} {mask n : Nat} {c : Compressed}
    (h : c.code ≠ .noMaskAndAllVals) :
    storedValues values mask n c = (setBits mask n).map values := by
  unfold storedValues
  split
  · rename_i hc; exact absurd hc h
  · rfl

theorem getElem?_range_map (values : Nat → VoxelValue) {n i : Nat} (hi : i < n) :
    ((List.range n).map values)[i]? = some (values i) := by
  rw [List.getElem?_map, List.getElem?_range hi]
  rfl

/-- Decode a full node from its classification: code 6 stores every slot, so
    it reads the full list directly; the other codes reconstruct inactive
    slots from the code, `val0`, `val1` and the selection mask. -/
def decodeAll (bg : VoxelValue) (values : Nat → VoxelValue) (mask n : Nat)
    (c : Compressed) (i : Nat) : VoxelValue :=
  match c.code with
  | .noMaskAndAllVals => (storedValues values mask n c)[i]?.getD bg
  | _ => decodeCompacted bg c.code c.selection c.val0 c.val1 mask
      (storedValues values mask n c) i

/-- An active slot always decodes to its stored value, for every code. -/
theorem decodeAll_active {bg : VoxelValue} {values : Nat → VoxelValue} {mask n i : Nat}
    {c : Compressed} (hn : i < n) (hb : mask.testBit i = true) :
    decodeAll bg values mask n c i = values i := by
  unfold decodeAll
  cases hc : c.code <;> simp only [storedValues, hc]
  all_goals
    first
    | (rw [decodeCompacted_active (by simpa [NodeMask.bit] using hb)]
       rw [List.getElem?_map, getElem?_setBits_rank hn hb]
       simp)
    | (rw [getElem?_range_map values hn]; simp)

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
  unfold decodeAll decodeCompacted storedValues
  by_cases hb : NodeMask.bit mask i
  · simp only [hb]
    rw [List.getElem?_map,
      getElem?_setBits_rank hn (by simpa [NodeMask.bit] using hb)]
    simp
  · simp only [hb]
    have hoff : mask.testBit i = false := by simpa [NodeMask.bit] using hb
    exact (h i hn hoff).symm

/-! ### Selection-mask semantics -/

/-- A conditional OR-fold is the OR-fold over the filtered list. -/
theorem foldl_cond_eq_foldl_filter (l : List Nat) (p : Nat → Prop) [DecidablePred p]
    (acc : Nat) :
    l.foldl (fun a j => if p j then a ||| (1 <<< j) else a) acc =
      (l.filter (fun j => decide (p j))).foldl (fun a j => a ||| (1 <<< j)) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    rw [List.foldl_cons]
    by_cases hp : p a
    · simp [List.filter, hp, List.foldl_cons, ih]
    · simp [List.filter, hp, ih]

/-- Bit `i` of an OR-fold of single-bit shifts: it is set exactly when the
    initial accumulator has it set or some shifted position is `i`. -/
theorem testBit_foldl_lor (l : List Nat) (acc i : Nat) :
    (l.foldl (fun a j => a ||| (1 <<< j)) acc).testBit i =
      (acc.testBit i || decide (i ∈ l)) := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    have hcomm : decide (i = a) = decide (a = i) := by
      by_cases h : i = a
      · rw [h]
      · have h' : ¬ (a = i) := fun hh => h hh.symm
        simp [h, h']
    simp only [List.mem_cons, Bool.decide_or, hcomm]
    cases h1 : acc.testBit i <;> cases h2 : decide (a = i) <;>
      cases h3 : decide (i ∈ t) <;> simp_all

/-- Inactive slot membership from the coordinate bounds. -/
theorem mem_inactiveSlots_of {mask n i : Nat} (hi : i < n)
    (hoff : mask.testBit i = false) : i ∈ inactiveSlots mask n := by
  unfold inactiveSlots
  rw [List.mem_filter]
  exact ⟨by simpa using hi, by simpa using hoff⟩

/-- `selectionOf` sets bit `i` exactly for inactive slots holding `v1`. -/
theorem selectionOf_bit {values : Nat → VoxelValue} {mask n i : Nat} {v1 : VoxelValue}
    (hi : i < n) (hoff : mask.testBit i = false) :
    (selectionOf values mask n v1).testBit i = decide (values i = v1) := by
  unfold selectionOf
  rw [foldl_cond_eq_foldl_filter, testBit_foldl_lor]
  have hiff : i ∈ (inactiveSlots mask n).filter (fun j => decide (values j = v1)) ↔
      values i = v1 := by
    constructor
    · intro hm
      unfold inactiveSlots at hm
      rw [List.mem_filter] at hm
      exact of_decide_eq_true hm.2
    · intro h
      unfold inactiveSlots
      rw [List.mem_filter]
      exact ⟨mem_inactiveSlots_of hi hoff, decide_eq_true h⟩
  have hdec : decide (i ∈ (inactiveSlots mask n).filter
      (fun j => decide (values j = v1))) = decide (values i = v1) :=
    decide_eq_decide.mpr hiff
  rw [hdec]
  simp

/-- `selectionOf` marks the `val1` slots for a decode. -/
theorem selectionOf_bit_of_eq {values : Nat → VoxelValue} {mask n i : Nat} {v1 : VoxelValue}
    (hi : i < n) (hoff : mask.testBit i = false) (heq : values i = v1) :
    NodeMask.bit (selectionOf values mask n v1) i = true := by
  simp [NodeMask.bit, selectionOf_bit hi hoff, heq]

theorem selectionOf_bit_of_ne {values : Nat → VoxelValue} {mask n i : Nat} {v1 : VoxelValue}
    (hi : i < n) (hoff : mask.testBit i = false) (hne : values i ≠ v1) :
    NodeMask.bit (selectionOf values mask n v1) i = false := by
  simp [NodeMask.bit, selectionOf_bit hi hoff, hne]

/-! ### The unique-value scan invariant -/

/-- Every value seen so far is one of the stored inactive values (as long as
    the scan has not saturated at three distinct values). -/
def Scan.Inv (s : Scan) (seen : List VoxelValue) : Prop :=
  (s.count = 0 → seen = []) ∧
  (s.count = 1 → ∀ v ∈ seen, v = s.u0) ∧
  (s.count = 2 → ∀ v ∈ seen, v = s.u0 ∨ v = s.u1) ∧
  (s.count = 2 → s.u0 ≠ s.u1)

theorem Scan.inv_zero (v0 v1 : VoxelValue) : (⟨v0, v1, 0⟩ : Scan).Inv [] := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_⟩ <;> (intro h; simp at h)

/-- One scan step preserves the invariant. -/
theorem Scan.step_inv {u0 u1 : VoxelValue} {c : Nat} {seen : List VoxelValue}
    (h : (⟨u0, u1, c⟩ : Scan).Inv seen) (v : VoxelValue) :
    (Scan.step ⟨u0, u1, c⟩ v).Inv (v :: seen) := by
  rcases c with _ | _ | _ | k
  · -- count 0: the value becomes `u0`
    have hstep : Scan.step ⟨u0, u1, 0⟩ v = ⟨v, u1, 1⟩ := by simp [Scan.step]
    rw [hstep]
    refine ⟨by simp, ?_, by simp, by simp⟩
    intro _ x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · rfl
    · have hempty : seen = [] := h.1 rfl
      subst hempty
      cases hx
  · -- count 1
    by_cases hv : v = u0
    · have hstep : Scan.step ⟨u0, u1, 1⟩ v = ⟨u0, u1, 1⟩ := by simp [Scan.step, hv]
      rw [hstep]
      refine ⟨by simp, ?_, by simp, by simp⟩
      intro _ x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hv
      · exact h.2.1 (by rfl) x hx
    · have hstep : Scan.step ⟨u0, u1, 1⟩ v = ⟨u0, v, 2⟩ := by simp [Scan.step, hv]
      rw [hstep]
      refine ⟨by simp, by simp, ?_, ?_⟩
      · intro _ x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact Or.inr rfl
        · exact Or.inl (h.2.1 (by rfl) x hx)
      · intro _ hh
        exact hv hh.symm
  · -- count 2
    by_cases hv : v = u0
    · have hstep : Scan.step ⟨u0, u1, 2⟩ v = ⟨u0, u1, 2⟩ := by simp [Scan.step, hv]
      rw [hstep]
      refine ⟨by simp, by simp, ?_, ?_⟩
      · intro _ x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact Or.inl hv
        · exact h.2.2.1 (by rfl) x hx
      · exact h.2.2.2
    · by_cases hv1 : v = u1
      · have hstep : Scan.step ⟨u0, u1, 2⟩ v = ⟨u0, u1, 2⟩ := by simp [Scan.step, hv1]
        rw [hstep]
        refine ⟨by simp, by simp, ?_, ?_⟩
        · intro _ x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact Or.inr hv1
          · exact h.2.2.1 (by rfl) x hx
        · exact h.2.2.2
      · -- saturated: count 3, no constraint
        have hstep : Scan.step ⟨u0, u1, 2⟩ v = ⟨u0, u1, 3⟩ := by simp [Scan.step, hv, hv1]
        rw [hstep]
        exact ⟨by simp, by simp, by simp, by simp⟩
  · -- count ≥ 3: no constraint
    have hge : 3 ≤ (Scan.step ⟨u0, u1, k + 1 + 1 + 1⟩ v).count := by
      unfold Scan.step
      by_cases hv0 : v = u0
      · simp [hv0]
      · by_cases hv1 : v = u1
        · simp [hv1]
        · by_cases hlt : k + 3 < 2
          · omega
          · simp [hv0, hv1, hlt]
    refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩ <;> omega

/-- Folding the step preserves the invariant over the reversed prefix. -/
theorem Scan.fold_inv (l : List VoxelValue) (s : Scan) (seen : List VoxelValue)
    (h : s.Inv seen) : (l.foldl Scan.step s).Inv (l.reverse ++ seen) := by
  induction l generalizing s seen with
  | nil => simpa using h
  | cons a t ih =>
    rw [List.foldl_cons, List.reverse_cons, List.append_assoc]
    exact ih (Scan.step s a) (a :: seen) (Scan.step_inv h a)

theorem Scan.Inv.of_reverse {s : Scan} {l : List VoxelValue} (h : s.Inv l.reverse) :
    s.Inv l := by
  have mem : ∀ x, x ∈ l ↔ x ∈ l.reverse := fun x => List.mem_reverse.symm
  refine ⟨fun h0 => ?_, fun h1 v hv => h.2.1 h1 v ((mem v).1 hv),
    fun h2 v hv => h.2.2.1 h2 v ((mem v).1 hv), fun h2 => h.2.2.2 h2⟩
  rw [← List.reverse_reverse l, h.1 h0]
  simp

/-- The scan of the inactive values satisfies the invariant. -/
theorem scanValues_inv (vs : List VoxelValue) (bg : VoxelValue) :
    (scanValues vs bg).Inv vs := by
  have h := Scan.fold_inv vs ⟨bg, bg, 0⟩ [] (Scan.inv_zero bg bg)
  rw [List.append_nil] at h
  exact h.of_reverse

/-! ### General mask-compression round trip -/

/-- An inactive slot's value is a member of the inactive value list. -/
theorem inactiveValues_mem {values : Nat → VoxelValue} {mask n i : Nat}
    (hi : i < n) (hoff : mask.testBit i = false) :
    values i ∈ inactiveValues values mask n := by
  unfold inactiveValues
  exact List.mem_map.mpr ⟨i, mem_inactiveSlots_of hi hoff, rfl⟩

/-- **Mask-compression round trip**: decoding a classified node returns the
    original value on every slot inside the node, for every combination of
    inactive values. This covers all seven codes: the scan invariant bounds
    the inactive values by `{u0, u1}`, the selection mask separates them, and
    code 6 stores the full per-slot list. -/
theorem classify_decode {bg : VoxelValue} {values : Nat → VoxelValue} {mask n i : Nat}
    (hn : i < n) :
    decodeAll bg values mask n (classify bg values mask n) i = values i := by
  by_cases hb : mask.testBit i = true
  · exact decodeAll_active hn hb
  · have hoff : mask.testBit i = false := by simpa using hb
    have hbit : NodeMask.bit mask i = false := by simpa [NodeMask.bit] using hoff
    have hmem : values i ∈ inactiveValues values mask n := inactiveValues_mem hn hoff
    have hinv := scanValues_inv (inactiveValues values mask n) bg
    rcases hscan : scanValues (inactiveValues values mask n) bg with ⟨u0, u1, c⟩
    rw [hscan] at hinv
    rcases c with _ | _ | _ | k
    · -- count 0: there are no inactive values
      have hempty : inactiveValues values mask n = [] := hinv.1 rfl
      rw [hempty] at hmem
      simp at hmem
    · -- count 1: every inactive value is `u0`
      have hval : values i = u0 := hinv.2.1 rfl (values i) hmem
      by_cases hu : u0 = bg
      · -- code 0
        have hcls : classify bg values mask n = ⟨.noMaskOrInactiveVals, bg, bg, 0⟩ := by
          unfold classify; rw [hscan]; simp [hu]
        rw [hcls]
        simp [decodeAll, decodeCompacted, hbit]
        rw [hval, hu]
      · by_cases hneg : u0 = bg.negate
        · -- code 1
          have hne' : bg.negate ≠ bg := fun hh => hu (hneg.trans hh)
          have hcls : classify bg values mask n = ⟨.noMaskAndMinusBg, bg, bg, 0⟩ := by
            unfold classify; rw [hscan]; simp [hneg, hne']
          rw [hcls]
          simp [decodeAll, decodeCompacted, hbit]
          rw [hval, ← hneg]
        · -- code 2
          have hcls : classify bg values mask n =
              ⟨.noMaskAndOneInactiveVal, u0, bg, 0⟩ := by
            unfold classify; rw [hscan]; simp [hu, hneg]
          rw [hcls]
          simp [decodeAll, decodeCompacted, hbit, hval]
    · -- count 2: inactive values are `u0` or `u1`, and they differ
      have hval : values i = u0 ∨ values i = u1 := hinv.2.2.1 rfl (values i) hmem
      have hne : u0 ≠ u1 := hinv.2.2.2 rfl
      by_cases hu1 : u1 = bg
      · by_cases hneg : u0 = bg.negate
        · -- code 3 (selection marks `bg`)
          have hne' : bg.negate ≠ bg := fun hh => hne (hneg.trans (hh.trans hu1.symm))
          have hcls : classify bg values mask n =
              ⟨.maskAndNoInactiveVals, u0, bg, selectionOf values mask n bg⟩ := by
            unfold classify; rw [hscan]; simp [hu1, hneg]
          rw [hcls]
          simp [decodeAll, decodeCompacted, hbit]
          by_cases heq : values i = bg
          · simp [selectionOf_bit_of_eq hn hoff heq, heq]
          · have hu0 : values i = u0 := by
              rcases hval with h | h
              · exact h
              · exact absurd (h.trans hu1) heq
            simp [selectionOf_bit_of_ne hn hoff heq, hu0, hneg]
        · -- code 4 (`u0` and `bg`)
          have hcls : classify bg values mask n =
              ⟨.maskAndOneInactiveVal, u0, bg, selectionOf values mask n bg⟩ := by
            unfold classify; rw [hscan]; simp [hu1, hneg]
          rw [hcls]
          simp [decodeAll, decodeCompacted, hbit]
          by_cases heq : values i = bg
          · simp [selectionOf_bit_of_eq hn hoff heq, heq]
          · have hu0 : values i = u0 := by
              rcases hval with h | h
              · exact h
              · exact absurd (h.trans hu1) heq
            simp [selectionOf_bit_of_ne hn hoff heq, hu0]
      · by_cases hu0 : u0 = bg
        · -- the background was seen first: codes 3/4 with `val0 = u1`
          by_cases hneg : u1 = bg.negate
          · have hne' : bg.negate ≠ bg := fun hh => hu1 (hneg.trans hh)
            have hcls : classify bg values mask n =
                ⟨.maskAndNoInactiveVals, u1, bg, selectionOf values mask n bg⟩ := by
              unfold classify; rw [hscan]; simp [hu0, hneg, hne']
            rw [hcls]
            simp [decodeAll, decodeCompacted, hbit]
            by_cases heq : values i = bg
            · simp [selectionOf_bit_of_eq hn hoff heq, heq]
            · have hu1' : values i = u1 := by
                rcases hval with h | h
                · exact absurd (h.trans hu0) heq
                · exact h
              simp [selectionOf_bit_of_ne hn hoff heq, hu1', hneg]
          · have hcls : classify bg values mask n =
                ⟨.maskAndOneInactiveVal, u1, bg, selectionOf values mask n bg⟩ := by
              unfold classify; rw [hscan]; simp [hu1, hu0, hneg]
            rw [hcls]
            simp [decodeAll, decodeCompacted, hbit]
            by_cases heq : values i = bg
            · simp [selectionOf_bit_of_eq hn hoff heq, heq]
            · have hu1' : values i = u1 := by
                rcases hval with h | h
                · exact absurd (h.trans hu0) heq
                · exact h
              simp [selectionOf_bit_of_ne hn hoff heq, hu1']
        · -- code 5: `u0` and `u1`, neither is the background
          have hcls : classify bg values mask n =
              ⟨.maskAndTwoInactiveVals, u0, u1, selectionOf values mask n u1⟩ := by
            unfold classify; rw [hscan]; simp [hu1, hu0]
          rw [hcls]
          simp [decodeAll, decodeCompacted, hbit]
          by_cases heq : values i = u1
          · simp [selectionOf_bit_of_eq hn hoff heq, heq]
          · have hu0' : values i = u0 := by
              rcases hval with h | h
              · exact h
              · exact absurd h heq
            simp [selectionOf_bit_of_ne hn hoff heq, hu0']
    · -- saturated: code 6 stores every slot
      have hcls : classify bg values mask n = ⟨.noMaskAndAllVals, bg, bg, 0⟩ := by
        unfold classify; rw [hscan]; simp
      rw [hcls]
      simp [decodeAll, storedValues, getElem?_range_map values hn]

end Vdb
