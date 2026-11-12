/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  The sparse tree model: root (background, tiles, children), internal nodes
  (child mask, value mask, tile values, children) and leaves (value mask and
  values), plus the lookup semantics and the well-formedness predicate that
  mirrors `validate_node` / `tvdb_tree_index_create`.

  Levels are numbered like the layout: 0 is the root, `depth - 1` the leaf.
  A node at level `l` owns the box `[origin, origin + span l)`; its child
  slots are `spanShift (l+1)` voxels wide, and a slot's value lives at
  `slotOf (log2dim l) x y z`.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Coord
import Vdb.Mask
import Vdb.Value

namespace Vdb

/-! ### Coordinate to slot -/

/-- Grid coordinate of a node slot along one axis, before flattening. -/
def slotComponent (c o : Int) (shift : Nat) : Nat := (localIndex c o shift).toNat

/-- Slot of coordinate `c` inside a node of level `lg` whose children are
    `2^shift` voxels apart. -/
def nodeSlot (lg shift : Nat) (o c : Coord) : Nat :=
  slotOf lg (slotComponent c.x o.x shift) (slotComponent c.y o.y shift)
    (slotComponent c.z o.z shift)

theorem slotComponent_lt {c o : Int} {shift lg : Nat}
    (hlo : o ≤ c) (hhi : c - o < (2 ^ shift : Int) * 2 ^ lg) :
    slotComponent c o shift < 2 ^ lg := by
  unfold slotComponent
  have h0 : (0 : Int) ≤ localIndex c o shift := localIndex_nonneg hlo
  have h1 : localIndex c o shift < (2 : Int) ^ lg := localIndex_lt hhi
  have hcast : ((localIndex c o shift).toNat : Int) = localIndex c o shift :=
    Int.toNat_of_nonneg h0
  have hpow : ((2 : Int) ^ lg).toNat = 2 ^ lg := by
    have : (2 : Int) ^ lg = ((2 ^ lg : Nat) : Int) := by simp
    rw [this, Int.toNat_natCast]
  omega

/-- A coordinate inside the node's box maps to a slot below `2^(3L)`. -/
theorem nodeSlot_lt {lg shift : Nat} {o c : Coord}
    (hx0 : o.x ≤ c.x) (hx1 : c.x - o.x < (2 ^ shift : Int) * 2 ^ lg)
    (hy0 : o.y ≤ c.y) (hy1 : c.y - o.y < (2 ^ shift : Int) * 2 ^ lg)
    (hz0 : o.z ≤ c.z) (hz1 : c.z - o.z < (2 ^ shift : Int) * 2 ^ lg) :
    nodeSlot lg shift o c < 2 ^ (3 * lg) := by
  unfold nodeSlot
  exact slotOf_lt (slotComponent_lt hx0 hx1) (slotComponent_lt hy0 hy1)
    (slotComponent_lt hz0 hz1)

/-- Origin of the child at slot `s` of a node at `origin`, whose children are
    `childSpan` voxels apart. `s` is decomposed into (x, y, z) fields. -/
def slotOrigin (lg : Nat) (o : Coord) (childSpan : Int) (s : Nat) : Coord :=
  childOrigin o childSpan
    ((slotX lg s : Nat) : Int) ((slotY lg s : Nat) : Int) ((slotZ lg s : Nat) : Int)

/-! ### Nodes -/

/-- A tree node. `values` is total in the slot index; slots that hold a child
    keep their tile value there, matching the C `values` array. -/
inductive Node where
  | leaf (origin : Coord) (valueMask : Nat) (values : Nat → VoxelValue)
  | internal (origin : Coord) (childMask : Nat) (valueMask : Nat)
      (values : Nat → VoxelValue) (children : Nat → Option Node)

namespace Node

/-- Node origin. -/
def origin : Node → Coord
  | .leaf o _ _ => o
  | .internal o _ _ _ _ => o

/-- Slots that own a child (all zero for a leaf). -/
def childMask : Node → Nat
  | .leaf _ _ _ => 0
  | .internal _ cm _ _ _ => cm

/-- Active-tile mask. -/
def valueMask : Node → Nat
  | .leaf _ vm _ => vm
  | .internal _ _ vm _ _ => vm

/-- Tile / stored value by slot. -/
def tileValue : Node → Nat → VoxelValue
  | .leaf _ _ v => v
  | .internal _ _ _ v _ => v

/-- Child by slot (`none` for leaves). -/
def child? : Node → Nat → Option Node
  | .leaf _ _ _ => fun _ => none
  | .internal _ _ _ _ ch => ch

/-- Children and value masks never overlap. -/
def MasksDisjoint (n : Node) : Prop :=
  ∀ s, NodeMask.bit n.childMask s = true → NodeMask.bit n.valueMask s = false

/-- A child exists exactly where the child mask says so. -/
def ChildrenMatch (n : Node) : Prop :=
  ∀ s, (n.child? s).isSome = NodeMask.bit n.childMask s

/-- A leaf has no children; an internal node has at least one. -/
def IsLeaf : Node → Bool
  | .leaf _ _ _ => true
  | .internal _ _ _ _ _ => false

end Node

/-! ### Root -/

/-- A root-level tile. -/
structure Tile where
  origin : Coord
  value : VoxelValue
  active : Bool
  deriving Repr, Inhabited

/-- The root node: background value plus tiles and child subtrees. -/
structure Root where
  background : VoxelValue
  tiles : List Tile
  children : List (Coord × Node)

namespace Root

/-- Root tile at a key, if any. -/
def tileAt (r : Root) (key : Coord) : Option Tile :=
  r.tiles.find? (fun t => t.origin == key)

/-- Root child at a key, if any. -/
def childAt (r : Root) (key : Coord) : Option Node :=
  (r.children.find? (fun p => p.1 == key)).map (·.2)

/-- Keys are unique across tiles and children (the C hash-map check). -/
def KeysUnique (r : Root) : Prop :=
  (r.tiles.map (·.origin)).Nodup ∧
  (r.children.map (·.1)).Nodup ∧
  ∀ t, t ∈ r.tiles → ∀ c, c ∈ r.children → t.origin ≠ c.1

end Root

/-! ### Trees -/

/-- A sparse VDB grid tree. -/
structure Tree where
  layout : Layout
  root : Root

namespace Tree

/-- Number of levels, root included. -/
def depth (t : Tree) : Nat := t.layout.levels.length

/-- `log2dim` of a level. -/
def log2dim (t : Tree) (l : Nat) : Nat := t.layout.log2dim l

/-- Spacing of a level's child slots in voxels. -/
def childShift (t : Tree) (l : Nat) : Nat := t.layout.spanShift (l + 1)

/-- Root box edge length in voxels. -/
def rootSpan (t : Tree) : Int := t.layout.span 1

/-- Slot of a coordinate in a node at level `l`. -/
def slotAt (t : Tree) (l : Nat) (o c : Coord) : Nat :=
  nodeSlot (t.log2dim l) (t.childShift l) o c

/-- Child origin for a slot at level `l`. -/
def childOriginAt (t : Tree) (l : Nat) (o : Coord) (s : Nat) : Coord :=
  slotOrigin (t.log2dim l) o (t.layout.span (l + 1)) s

/-- Descend from a node at level `l`, with an explicit fuel bound (at most
    one unit per level). Well-formed trees never exhaust it. -/
def lookupNode (t : Tree) : Nat → Nat → Node → Coord → VoxelValue × Bool
  | 0, _, _, _ => (t.root.background, false)
  | fuel + 1, l, n, c =>
    match n with
    | .leaf _ mask values =>
      let s := t.slotAt l n.origin c
      (values s, NodeMask.bit mask s)
    | .internal _ _ mask values children =>
      let s := t.slotAt l n.origin c
      match children s with
      | some ch => t.lookupNode fuel (l + 1) ch c
      | none => (values s, NodeMask.bit mask s)

/-- Value and active flag at a coordinate: root tiles/children by key, then a
    descent through the nodes, finally the background (inactive). -/
def lookup (t : Tree) (c : Coord) : VoxelValue × Bool :=
  let key := rootKey t.rootSpan c
  match t.root.childAt key with
  | some n => t.lookupNode t.depth 1 n c
  | none =>
    match t.root.tileAt key with
    | some tile => (tile.value, tile.active)
    | none => (t.root.background, false)

/-- The value at a coordinate. -/
def get (t : Tree) (c : Coord) : VoxelValue := (t.lookup c).1

/-- The active flag at a coordinate. -/
def active (t : Tree) (c : Coord) : Bool := (t.lookup c).2

/-- Two trees are equivalent when they agree on every coordinate. -/
def Equiv (a b : Tree) : Prop := ∀ c, a.lookup c = b.lookup c

theorem equiv_refl (t : Tree) : t.Equiv t := fun _ => rfl

theorem equiv_symm {a b : Tree} (h : a.Equiv b) : b.Equiv a := fun c => (h c).symm

theorem equiv_trans {a b c : Tree} (h₁ : a.Equiv b) (h₂ : b.Equiv c) : a.Equiv c :=
  fun x => (h₁ x).trans (h₂ x)

/-! ### Well-formedness -/

/-- Fuel-bounded well-formedness of a node at level `l`. The fuel is the
    number of levels that may still be inspected; `t.depth` always suffices
    for a well-formed tree. -/
def NodeWFuel (t : Tree) : Nat → Nat → Node → Prop
  | 0, _, _ => True
  | fuel + 1, l, n =>
    l < t.depth ∧
    (∀ a : Fin 3, ∃ k : Int, Coord.axis a n.origin = k * t.layout.span l) ∧
    Node.MasksDisjoint n ∧
    Node.ChildrenMatch n ∧
    (l + 1 = t.depth → n.IsLeaf = true) ∧
    (n.IsLeaf = false → l + 1 < t.depth) ∧
    (∀ s, NodeMask.bit n.childMask s = true →
      ∃ ch, n.child? s = some ch ∧
        ch.origin = t.childOriginAt l n.origin s ∧ NodeWFuel t fuel (l + 1) ch)

/-- A node at level `l` is well formed with the tree's full depth as fuel. -/
def NodeWF (t : Tree) (l : Nat) (n : Node) : Prop := NodeWFuel t t.depth l n

/-- The tree is well formed: layout bounds, aligned unique root keys, root
    tiles and children valid, every subtree well formed, one value type. -/
def WellFormed (t : Tree) : Prop :=
  t.layout.WellFormed 5 ∧
  t.depth ≥ 3 ∧
  Root.KeysUnique t.root ∧
  (∀ tile ∈ t.root.tiles,
    (∀ a : Fin 3, ∃ k : Int, Coord.axis a tile.origin = k * t.rootSpan) ∧
    tile.value.type = t.root.background.type) ∧
  (∀ p ∈ t.root.children,
    (∀ a : Fin 3, ∃ k : Int, Coord.axis a p.1 = k * t.rootSpan) ∧
    NodeWF t 1 p.2) ∧
  (∀ tile ∈ t.root.tiles, tile.value.type = t.root.background.type)

/-- The lookup agrees with the root key box. -/
theorem lookup_outside_children {t : Tree} {c : Coord}
    (h : t.root.childAt (rootKey t.rootSpan c) = none) :
    (t.root.tileAt (rootKey t.rootSpan c)).isSome = false →
    t.lookup c = (t.root.background, false) := by
  intro htile
  unfold lookup
  dsimp only
  rw [h]
  cases ht : t.root.tileAt (rootKey t.rootSpan c) with
  | none => rfl
  | some tile =>
    rw [ht] at htile
    cases htile

end Tree

/-! ### A worked example: one active voxel at the origin -/

/-- Value function of the example leaf: slot 0 holds `1`, everything else `0`. -/
def exampleValue (s : Nat) : VoxelValue :=
  if s = 0 then .int32 1 else .int32 0

/-- Leaf with only slot 0 active. -/
def exampleLeaf : Node :=
  .leaf Coord.zero 1 exampleValue

/-- Level-2 internal node (log2dim 4) with a single child at slot 0. -/
def exampleInner4 : Node :=
  .internal Coord.zero 1 0 (fun _ => .int32 0)
    (fun s => if s = 0 then some exampleLeaf else none)

/-- Level-1 internal node (log2dim 5) with a single child at slot 0. -/
def exampleInner5 : Node :=
  .internal Coord.zero 1 0 (fun _ => .int32 0)
    (fun s => if s = 0 then some exampleInner4 else none)

/-- A `5_4_3` tree whose single active voxel is at the origin, background `0`. -/
def exampleTree : Tree :=
  { layout := Layout.standard
    root :=
      { background := .int32 0
        tiles := []
        children := [(Coord.zero, exampleInner5)] } }

/-- The active voxel reads back its value. -/
theorem exampleTree_lookup_origin :
    exampleTree.lookup Coord.zero = (.int32 1, true) := by
  decide

/-- An inactive voxel reads its stored value with the inactive flag. -/
theorem exampleTree_lookup_inactive :
    exampleTree.lookup ⟨1, 0, 0⟩ = (.int32 0, false) := by
  decide

/-- A coordinate outside the root child's box falls back to the background. -/
theorem exampleTree_lookup_background :
    exampleTree.lookup ⟨4096, 0, 0⟩ = (.int32 0, false) := by
  decide

end Vdb
