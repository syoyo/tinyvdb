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
    | .maskAndNoInactiveVals => if NodeMask.bit sel i then bg.negate else bg
    | .maskAndOneInactiveVal => if NodeMask.bit sel i then bg else val0
    | .maskAndTwoInactiveVals => if NodeMask.bit sel i then val1 else val0
    | .noMaskAndAllVals => bg

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

end Vdb
