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
  deriving Repr, DecidableEq, Inhabited

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

/-- Flatten a (x, y, z) local index into a node slot, `x` most significant. -/
def slotOf (L : Nat) (x y z : Nat) : Nat :=
  (x <<< (2 * L)) ||| (y <<< L) ||| z

/-- Child origin of local index `(x, y, z)` at a node origin. -/
def childOrigin (o : Coord) (childSpan : Int) (x y z : Int) : Coord :=
  ⟨o.x + x * childSpan, o.y + y * childSpan, o.z + z * childSpan⟩

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
