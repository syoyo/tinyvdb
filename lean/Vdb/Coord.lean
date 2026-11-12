/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Integer coordinates, tree layouts, node spans, child origins and the
  coordinate-to-slot mapping used by the VDB tree.

  Conventions (mirroring `src/tinyvdb_tree.c`):
  * A layout is `[0, L1, ..., Ln]`: level 0 is the root (`L = 0`), the last
    entry is the leaf.
  * `spanShift i = Σ_{j ≥ i} L_j` and `span i = 2^(spanShift i)` is the
    edge length in voxels of the box owned by a level-`i` node. `span 0` is
    the root box size, `span n` the leaf size (`3` ⇒ 8).
  * A coordinate `c` belongs to node box `[o, o + span i)`; its local index
    below level `i` is `(c - o) / 2^(spanShift (i+1))` (arithmetic shift).
  * The slot of a (x, y, z) local index is `(x << 2L) | (y << L) | z`.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Bytes

namespace Vdb

/-! ### Coordinates -/

/-- An integer index-space coordinate. -/
structure Coord where
  x : Int
  y : Int
  z : Int
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Coord

def zero : Coord := ⟨0, 0, 0⟩

instance : Zero Coord := ⟨zero⟩

def add (a b : Coord) : Coord := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def sub (a b : Coord) : Coord := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩

def smul (k : Int) (a : Coord) : Coord := ⟨k * a.x, k * a.y, k * a.z⟩

@[simp] theorem add_x (a b : Coord) : (add a b).x = a.x + b.x := rfl
@[simp] theorem add_y (a b : Coord) : (add a b).y = a.y + b.y := rfl
@[simp] theorem add_z (a b : Coord) : (add a b).z = a.z + b.z := rfl

theorem add_comm (a b : Coord) : add a b = add b a := by
  cases a; cases b; simp only [add, Coord.mk.injEq]
  exact ⟨Int.add_comm _ _, Int.add_comm _ _, Int.add_comm _ _⟩

theorem sub_eq_add_smul_neg (a b : Coord) :
    sub a b = add a (smul (-1) b) := by
  cases a; cases b; simp only [sub, add, smul, Coord.mk.injEq]
  exact ⟨by omega, by omega, by omega⟩

/-- Axis projection. -/
def axis (i : Fin 3) (c : Coord) : Int :=
  match i with
  | ⟨0, _⟩ => c.x
  | ⟨1, _⟩ => c.y
  | _ => c.z

end Coord

/-- Componentwise box membership, `o ≤ c < o + span`. -/
def InBox (o : Coord) (span : Int) (c : Coord) : Prop :=
  o.x ≤ c.x ∧ c.x < o.x + span ∧
  o.y ≤ c.y ∧ c.y < o.y + span ∧
  o.z ≤ c.z ∧ c.z < o.z + span

/-! ### Layouts -/

/-- A tree layout: level 0 is the root with `log2dim = 0`, followed by the
    internal levels and finally the leaf level. -/
structure Layout where
  levels : List Nat
  deriving Repr, DecidableEq

/-- Structural well-formedness of a layout. `maxLog2` is the largest
    per-level `log2dim` the implementation accepts (5 for `tvdb_tree_index`,
    10 for the lenient file parser). -/
def Layout.WellFormed (l : Layout) (maxLog2 : Nat) : Prop :=
  l.levels.head? = some 0 ∧
  l.levels.length ≥ 3 ∧
  l.levels.length ≤ 8 ∧
  (∀ L ∈ l.levels, L ≤ maxLog2) ∧
  (l.levels.drop 1).sum ≤ 31

/-- The standard `5_4_3` layout. -/
def Layout.standard : Layout := ⟨[0, 5, 4, 3]⟩

theorem Layout.standard_wf : Layout.standard.WellFormed 5 := by
  unfold Layout.WellFormed Layout.standard
  decide

/-- `log2dim` of a level (0 outside the layout). -/
def Layout.log2dim (l : Layout) (i : Nat) : Nat := l.levels.getD i 0

/-- Sum of the `log2dim`s at and below level `i`: `span i = 2^(spanShift i)`. -/
def Layout.spanShift (l : Layout) (i : Nat) : Nat := (l.levels.drop i).sum

theorem Layout.spanShift_zero (l : Layout) : l.spanShift 0 = l.levels.sum := by
  simp [Layout.spanShift]

/-- Edge length in voxels of a level-`i` node's box. -/
def Layout.span (l : Layout) (i : Nat) : Int := 2 ^ (l.spanShift i)

/-- Local index of `c` inside a node at `o` whose child voxels are spaced
    `2^(shiftBelow)` voxels apart (arithmetic shift, floor division). -/
def localIndex (c o : Int) (shiftBelow : Nat) : Int := (c - o) / (2 ^ shiftBelow : Int)

/-- Local index is non-negative inside the node box. -/
theorem localIndex_nonneg {c o : Int} {shiftBelow : Nat} (h : o ≤ c) :
    0 ≤ localIndex c o shiftBelow := by
  unfold localIndex
  have h2 : (0 : Int) ≤ (2 : Int) ^ shiftBelow := by positivity
  exact Int.ediv_nonneg (by omega) h2

/-- The local index is below the node's edge length `2^L`. -/
theorem localIndex_lt {c o : Int} {shiftBelow L : Nat}
    (h : c - o < (2 ^ shiftBelow : Int) * 2 ^ L) :
    localIndex c o shiftBelow < 2 ^ L := by
  unfold localIndex
  have hpos : (0 : Int) < 2 ^ shiftBelow := by positivity
  rw [Int.ediv_lt_iff_lt_mul hpos]
  simpa [mul_comm] using h

/-- Reassembling a local index: the coordinate is recovered from the node
    origin, the index and the spacing. -/
theorem origin_add_localIndex {c o : Int} {shiftBelow : Nat} :
    o + 2 ^ shiftBelow * localIndex c o shiftBelow ≤ c := by
  unfold localIndex
  have hpos : (0 : Int) < 2 ^ shiftBelow := by positivity
  have h := Int.ediv_mul_le (c - o) hpos.ne'
  have hb : o + 2 ^ shiftBelow * ((c - o) / 2 ^ shiftBelow) = o + ((c - o) / 2 ^ shiftBelow) * 2 ^ shiftBelow := by
    rw [mul_comm]
  rw [hb]
  omega

/-- Flatten a (x, y, z) local index into a node slot, `x` most significant.

    This is the arithmetic form of the C bit expression
    `(x << 2L) | (y << L) | z`; the bit expression only coincides with it when
    `x, y, z < 2^L`, which every call site guarantees. -/
def slotOf (L x y z : Nat) : Nat :=
  x * 2 ^ (2 * L) + y * 2 ^ L + z

/-- `x` component of a slot. -/
def slotX (L s : Nat) : Nat := s / 2 ^ (2 * L)

/-- `y` component of a slot. -/
def slotY (L s : Nat) : Nat := (s / 2 ^ L) % 2 ^ L

/-- `z` component of a slot. -/
def slotZ (L s : Nat) : Nat := s % 2 ^ L

/-- Inverse of `slotOf` on the node's slot range. -/
def localOfSlot (L s : Nat) : Nat × Nat × Nat :=
  (slotX L s, slotY L s, slotZ L s)

/-- A slot with in-range components fits in the node's `2^(3L)` slots. -/
theorem slotOf_lt {L x y z : Nat}
    (hx : x < 2 ^ L) (hy : y < 2 ^ L) (hz : z < 2 ^ L) :
    slotOf L x y z < 2 ^ (3 * L) := by
  set a : Nat := 2 ^ L with ha_def
  have ha : 0 < a := Nat.two_pow_pos L
  have h2L : 2 ^ (2 * L) = a * a := by
    rw [ha_def, ← pow_add]; ring_nf
  have h3L : 2 ^ (3 * L) = a * a * a := by
    rw [ha_def, ← pow_add, ← pow_add]; ring_nf
  have hyz : y * a + z < a * a := by
    have hy' : y + 1 ≤ a := by omega
    have hz' : z + 1 ≤ a := by omega
    have hmul : y * a ≤ (a - 1) * a := Nat.mul_le_mul_right _ (by omega)
    have hsub : (a - 1) * a = a * a - a := by rw [Nat.sub_mul, one_mul]
    have hmul' : y * a ≤ a * a - a := hsub ▸ hmul
    have hle : a ≤ a * a := Nat.le_mul_of_pos_left a ha
    omega
  have hx1 : x + 1 ≤ a := by omega
  have hstep : x * (a * a) + y * a + z < x * (a * a) + a * a := by omega
  have hnext : x * (a * a) + a * a = (x + 1) * (a * a) := by
    rw [Nat.succ_mul]
  have hle : (x + 1) * (a * a) ≤ a * (a * a) := Nat.mul_le_mul_right _ hx1
  rw [slotOf, h2L, h3L]
  calc x * (a * a) + y * a + z
      < x * (a * a) + a * a := hstep
    _ = (x + 1) * (a * a) := hnext
    _ ≤ a * (a * a) := hle
    _ = a * a * a := by ring

/-- `slotOf` is injective on the node box. -/
theorem slotOf_inj {L x y z x' y' z' : Nat}
    (_hx : x < 2 ^ L) (hy : y < 2 ^ L) (hz : z < 2 ^ L)
    (_hx' : x' < 2 ^ L) (hy' : y' < 2 ^ L) (hz' : z' < 2 ^ L)
    (h : slotOf L x y z = slotOf L x' y' z') :
    x = x' ∧ y = y' ∧ z = z' := by
  set a : Nat := 2 ^ L with ha_def
  have ha : 0 < a := Nat.two_pow_pos L
  have h2L : 2 ^ (2 * L) = a * a := by
    rw [ha_def, ← pow_add]; ring_nf
  have hzmod : z = z' := by
    have hmod : (slotOf L x y z) % a = (slotOf L x' y' z') % a := by rw [h]
    unfold slotOf at hmod
    rw [h2L] at hmod
    have e1 : (x * (a * a) + y * a + z) % a = z % a := by
      rw [show x * (a * a) + y * a + z = (x * a + y) * a + z by ring]
      exact Nat.mul_add_mod_self_right _ _ _
    have e2 : (x' * (a * a) + y' * a + z') % a = z' % a := by
      rw [show x' * (a * a) + y' * a + z' = (x' * a + y') * a + z' by ring]
      exact Nat.mul_add_mod_self_right _ _ _
    rw [e1, e2] at hmod
    have hzlt : z < a := by omega
    have hzlt' : z' < a := by omega
    rw [Nat.mod_eq_of_lt hzlt, Nat.mod_eq_of_lt hzlt'] at hmod
    exact hmod
  have hxy : x * (a * a) + y * a = x' * (a * a) + y' * a := by
    unfold slotOf at h
    rw [h2L, ← ha_def] at h
    omega
  have hyz : y * a < a * a := by
    have hmul : y * a ≤ (a - 1) * a := Nat.mul_le_mul_right _ (by omega)
    have hsub : (a - 1) * a = a * a - a := by rw [Nat.sub_mul, one_mul]
    have hmul' : y * a ≤ a * a - a := hsub ▸ hmul
    have hle : a ≤ a * a := Nat.le_mul_of_pos_left a ha
    omega
  have hyz' : y' * a < a * a := by
    have hmul : y' * a ≤ (a - 1) * a := Nat.mul_le_mul_right _ (by omega)
    have hsub : (a - 1) * a = a * a - a := by rw [Nat.sub_mul, one_mul]
    have hmul' : y' * a ≤ a * a - a := hsub ▸ hmul
    have hle : a ≤ a * a := Nat.le_mul_of_pos_left a ha
    omega
  have hy : y = y' := by
    have hm : (x * (a * a) + y * a) % (a * a) = (x' * (a * a) + y' * a) % (a * a) := by
      rw [hxy]
    rw [mul_comm x (a * a), mul_comm x' (a * a)] at hm
    rw [Nat.mul_add_mod_self_left, Nat.mul_add_mod_self_left,
        Nat.mod_eq_of_lt hyz, Nat.mod_eq_of_lt hyz'] at hm
    exact Nat.mul_right_cancel ha hm
  have hx : x = x' := by
    have hmul : x * (a * a) = x' * (a * a) := by
      have hh := hxy
      rw [hy] at hh
      omega
    exact Nat.mul_right_cancel (by positivity) hmul
  exact ⟨hx, hy, hzmod⟩

/-- Rebuilding a slot's components returns the slot. -/
theorem slotOf_localOfSlot {L s : Nat} (_hs : s < 2 ^ (3 * L)) :
    slotOf L (slotX L s) (slotY L s) (slotZ L s) = s := by
  set a : Nat := 2 ^ L with ha_def
  have h2L : 2 ^ (2 * L) = a * a := by rw [ha_def, ← pow_add]; ring_nf
  unfold slotX slotY slotZ slotOf
  rw [h2L, ← ha_def]
  have hdecomp : s = s / (a * a) * (a * a) + s % (a * a) := by
    rw [mul_comm]; exact (Nat.div_add_mod s (a * a)).symm
  have hdecomp2 : s % (a * a) = (s / a % a) * a + s % a := by
    have h1 : s % (a * a) = (s % (a * a) / a) * a + s % (a * a) % a := by
      have := Nat.div_add_mod (s % (a * a)) a
      rw [Nat.mul_comm] at this
      exact this.symm
    have h2 : s % (a * a) / a = s / a % a := Nat.mod_mul_right_div_self s a a
    have h3 : s % (a * a) % a = s % a := Nat.mod_mul_right_mod s a a
    rw [h1, h2, h3]
  omega

/-- Splitting a slot into components and reassembling is the identity. -/
theorem localOfSlot_slotOf {L x y z : Nat}
    (hx : x < 2 ^ L) (hy : y < 2 ^ L) (hz : z < 2 ^ L) :
    localOfSlot L (slotOf L x y z) = (x, y, z) := by
  set a : Nat := 2 ^ L with ha_def
  have ha : 0 < a := Nat.two_pow_pos L
  have h2L : 2 ^ (2 * L) = a * a := by rw [ha_def, ← pow_add]; ring_nf
  have h3L : 2 ^ (3 * L) = a * a * a := by
    rw [ha_def, ← pow_add, ← pow_add]; ring_nf
  have hs : slotOf L x y z < 2 ^ (3 * L) := slotOf_lt hx hy hz
  have hb1 : slotX L (slotOf L x y z) < a := by
    unfold slotX
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    have hgoal : slotOf L x y z < a * (a * a) := by
      rw [h3L] at hs
      calc slotOf L x y z < a * a * a := hs
        _ = a * (a * a) := by ring
    rw [h2L]
    exact hgoal
  have hb2 : slotY L (slotOf L x y z) < a := by
    unfold slotY; rw [← ha_def]; exact Nat.mod_lt _ ha
  have hb3 : slotZ L (slotOf L x y z) < a := by
    unfold slotZ; rw [← ha_def]; exact Nat.mod_lt _ ha
  have hre : slotOf L (slotX L (slotOf L x y z)) (slotY L (slotOf L x y z))
      (slotZ L (slotOf L x y z)) = slotOf L x y z := slotOf_localOfSlot (L := L) hs
  obtain ⟨e1, e2, e3⟩ := slotOf_inj hb1 hb2 hb3 hx hy hz hre
  unfold localOfSlot
  rw [e1, e2, e3]

/-- Child origin of local index `(x, y, z)` at a node origin. -/
def childOrigin (o : Coord) (childSpan : Int) (x y z : Int) : Coord :=
  ⟨o.x + x * childSpan, o.y + y * childSpan, o.z + z * childSpan⟩

theorem childOrigin_at_zero (o : Coord) (h : Int) :
    childOrigin o h 0 0 0 = o := by
  simp [childOrigin]

/-- Root key of a coordinate: the origin of the level-1 box containing it.
    This is `floorDiv c span1 * span1`, matching the C code's
    `(v >= 0 ? v >> sh : -1 - ((-1 - v) >> sh)) * span`. -/
def rootKey (span1 : Int) (c : Coord) : Coord :=
  ⟨c.x / span1 * span1, c.y / span1 * span1, c.z / span1 * span1⟩

theorem rootKey_le {span1 : Int} (hpos : 0 < span1) (c : Coord) :
    (rootKey span1 c).x ≤ c.x ∧ (rootKey span1 c).y ≤ c.y ∧
    (rootKey span1 c).z ≤ c.z := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold rootKey <;> simp <;>
    exact Int.ediv_mul_le _ hpos.ne'

theorem lt_rootKey_add {span1 : Int} (hpos : 0 < span1) (c : Coord) :
    c.x < (rootKey span1 c).x + span1 ∧
    c.y < (rootKey span1 c).y + span1 ∧
    c.z < (rootKey span1 c).z + span1 := by
  have key : ∀ a : Int, a < a / span1 * span1 + span1 := by
    intro a
    have hmod := Int.emod_lt_of_pos a hpos
    have hdecomp : a / span1 * span1 + a % span1 = a := by
      have := Int.mul_ediv_add_emod a span1
      rwa [mul_comm] at this
    omega
  refine ⟨?_, ?_, ?_⟩
  · have := key c.x; simpa [rootKey] using this
  · have := key c.y; simpa [rootKey] using this
  · have := key c.z; simpa [rootKey] using this

/-- The root key is a multiple of the root box span. -/
theorem rootKey_dvd {span1 : Int} (c : Coord) :
    ∃ k : Int, (rootKey span1 c).x = k * span1 :=
  ⟨_, rfl⟩

end Vdb
