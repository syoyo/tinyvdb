/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  The indexed lookup — the model of the C `tree_find` descent
  (`src/tinyvdb_tree.c`). The spec model (`Tree.lookup`, `Tree.lookupNode`)
  stores an internal node's children as a slot-indexed function; the C index
  stores them compactly, in rank order, and finds a child at

    `child_indices[tree_child_rank(p, node, &child_mask, slot)]`

  where `tree_child_rank` counts the set bits strictly below `slot` — the
  `NodeMask.rank` of the spec model. The root hash map (open addressing,
  linear probing) is modelled in set form: a single combined tile/child
  table whose probe returns the unique matching item; the probing order is
  irrelevant once keys are unique.

  Contents:

  * `rank_lt_popCount`: a set child-mask bit's rank is strictly below the
    population count (for an in-node slot), which is why the C reads the
    compact array in bounds.
  * `IndexedNode` / `descend` / `toNode` and **`descend_eq_lookupNode`**:
    the rank-compacted C-style descent agrees with the spec descent on every
    coordinate, for every (finite) tree. No well-formedness is needed for
    the equality — both sides match on the same `Option`.
  * `IndexedTree` / `IndexedRoot.probe` and
    **`lookup_eq_toTree_lookup`**: under key uniqueness
    (`IndexedRoot.KeysNodup`), the combined root table agrees with the
    spec root stage, so the whole C-style lookup equals the spec lookup.

  The `tvdb_tree_accessor` node cache is a memo of this same descent; it is
  not modelled here (see `lean/VERIFICATION.md`).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Tree

namespace Vdb

theorem Coord.beq_iff_eq {a b : Coord} : (a == b) = true ↔ a = b := by
  cases a with
  | mk x y z =>
    cases b with
    | mk x' y' z' =>
      show (x == x' && (y == y' && z == z')) = true ↔ Coord.mk x y z = Coord.mk x' y' z'
      simp [Bool.and_eq_true]

/-! ### The C `tree_child_rank` bound -/

/-- A set bit strictly inside the node's slot range has its rank strictly
    below the population count: the compact children array is indexed in
    bounds (the C `child_indices[tree_child_rank(...)]`). -/
theorem rank_lt_popCount {L : Nat} (m : Nat) {s : Nat}
    (hs : s < nodeSlots L) (hb : NodeMask.bit m s = true) :
    NodeMask.rank m s < NodeMask.popCount (L := L) m := by
  unfold NodeMask.bit at hb
  have h1 : NodeMask.rank m s < NodeMask.rank m (s + 1) := by
    rw [NodeMask.rank_succ]
    simp only [NodeMask.bit, hb, ite_true]
    omega
  have h2 : NodeMask.rank m (s + 1) ≤ NodeMask.rank m (nodeSlots L) :=
    NodeMask.rank_mono m (by omega)
  rw [NodeMask.rank_full] at h2
  omega

/-! ### Rank-compacted nodes (the C `child_indices` form) -/

/-- An internal node in the compact form the C index uses: children are
    stored as a list in rank order and indexed by `rank childMask slot`. The
    spec model (`Node`) stores a slot-indexed function instead; `toNode`
    erases the compaction. -/
inductive IndexedNode where
  | leaf (origin : Coord) (valueMask : Nat) (values : Nat → VoxelValue)
  | internal (origin : Coord) (childMask valueMask : Nat)
      (values : Nat → VoxelValue) (children : List IndexedNode)

namespace IndexedNode

/-- Node origin. -/
def origin : IndexedNode → Coord
  | .leaf o _ _ => o
  | .internal o _ _ _ _ => o

mutual
/-- Erase the compaction, turning a rank-indexed children list into the
    slot-indexed function used by the spec model. The list recursion lives in
    `toNodeList` so both functions are structurally recursive. -/
def toNode : IndexedNode → Node
  | .leaf o vm v => .leaf o vm v
  | .internal o cm vm v children =>
      .internal o cm vm v fun s =>
        if NodeMask.bit cm s then (toNodeList children)[NodeMask.rank cm s]? else none

/-- Pointwise `toNode` on a children list. -/
def toNodeList : List IndexedNode → List Node
  | [] => []
  | ch :: cs => toNode ch :: toNodeList cs
end

theorem toNodeList_eq_map (cs : List IndexedNode) :
    toNodeList cs = cs.map toNode := by
  induction cs with
  | nil => rfl
  | cons ch cs ih => simp [toNodeList, ih]

end IndexedNode

/-! ### The C-style descent -/

/-- The C `tree_find` descent below the root, on rank-compacted nodes. The
    slot computation is shared with the spec lookup (`Tree.slotAt`); internal
    children go through the compact array; a missing child reads the tile
    value and flag, like `mask_on(child_mask, slot) == 0` in the C code.
    Well-formed trees never exhaust the fuel. -/
def Tree.descend (t : Tree) : Nat → Nat → IndexedNode → Coord → VoxelValue × Bool
  | 0, _, _, _ => (t.root.background, false)
  | fuel + 1, l, n, c =>
    match n with
    | .leaf o mask values =>
        (values (t.slotAt l o c), NodeMask.bit mask (t.slotAt l o c))
    | .internal o cm mask values children =>
        match (if NodeMask.bit cm (t.slotAt l o c)
               then children[NodeMask.rank cm (t.slotAt l o c)]?
               else none) with
        | some ch => t.descend fuel (l + 1) ch c
        | none => (values (t.slotAt l o c), NodeMask.bit mask (t.slotAt l o c))

/-- **The rank-compacted descent agrees with the spec descent**: on every
    coordinate, the C-style rank descent returns the same value and active
    flag as the spec lookup on the erased node. No well-formedness
    hypotheses are needed: both sides case-split on the same `Option`. -/
theorem Tree.descend_eq_lookupNode (t : Tree) :
    ∀ fuel l n c, t.descend fuel l n c = t.lookupNode fuel l n.toNode c := by
  intro fuel
  induction fuel with
  | zero =>
      intro l n c
      simp only [Tree.descend, Tree.lookupNode]
  | succ fuel ih =>
      intro l n c
      cases n with
      | leaf o vm v =>
          simp only [Tree.descend, Tree.lookupNode, IndexedNode.toNode, Node.origin]
      | internal o cm vm v children =>
          simp only [Tree.descend, Tree.lookupNode, IndexedNode.toNode, Node.origin]
          have hget : ∀ i : Nat, (IndexedNode.toNodeList children)[i]?
              = (children[i]?).map IndexedNode.toNode := by
            intro i
            rw [IndexedNode.toNodeList_eq_map, List.getElem?_map]
          by_cases hb : NodeMask.bit cm (t.slotAt l o c) = true
          · simp only [hb]
            cases hc : children[NodeMask.rank cm (t.slotAt l o c)]? with
            | none => simp [hget, hc]
            | some ch =>
              rw [hget, hc]; simp only [Option.map_some]
              exact ih (l + 1) ch c
          · simp [hb]

/-! ### The combined root table (the C hash map) -/

/-- A `find?` result is a member of the list. -/
theorem List.mem_of_find?_eq_some {α : Type} {p : α → Bool} {a : α} {l : List α}
    (h : l.find? p = some a) : a ∈ l := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.find?_cons] at h
    split at h
    · rename_i hpx
      simp only [Option.some.injEq] at h
      subst h
      exact List.mem_cons_self

    · rename_i hpx
      exact List.mem_cons_of_mem x (ih h)

/-- A root item: either a tile (value plus flag) or a child subtree
    (origin plus rank-compacted node). -/
inductive RootItem where
  | tile (t : Tile)
  | child (origin : Coord) (node : IndexedNode)

namespace RootItem

/-- The key a root item hashes under (the C hash-map key). -/
def key : RootItem → Coord
  | .tile t => t.origin
  | .child o _ => o

def asTile? : RootItem → Option Tile
  | .tile t => some t
  | .child _ _ => none

def asChild? : RootItem → Option (Coord × IndexedNode)
  | .tile _ => none
  | .child o n => some (o, n)

end RootItem

/-- The root in the compact form the C index uses: background plus **one
    combined tile/child table** (the C `tvdb_tree_index` hash map). The probe
    returns the unique matching item; open addressing and probing order are
    modelled away, which is sound once keys are unique
    (`IndexedRoot.KeysNodup`). -/
structure IndexedRoot where
  background : VoxelValue
  items : List RootItem

/-- The root probe: the first item whose key matches. -/
def IndexedRoot.probe (r : IndexedRoot) (key : Coord) : Option RootItem :=
  r.items.find? (fun i => i.key == key)

theorem IndexedRoot.probe_some {r : IndexedRoot} {key : Coord} {i : RootItem}
    (h : r.probe key = some i) : i ∈ r.items ∧ (i.key == key) = true := by
  have hf : r.items.find? (fun j => j.key == key) = some i := by
    unfold IndexedRoot.probe at h; exact h
  exact ⟨List.mem_of_find?_eq_some hf,
    List.find?_some (p := fun (j : RootItem) => j.key == key) hf⟩

/-- Equal keys under the table match imply equal items (the C hash-map
    uniqueness check): the two keys both equal the probe key, so,
    transitivity through `Coord.beq_iff_eq`, they are equal to each other. -/
def IndexedRoot.KeysNodup (r : IndexedRoot) : Prop :=
  ∀ i ∈ r.items, ∀ j ∈ r.items, (i.key == j.key) = true → i = j

theorem IndexedRoot.eq_of_same_key {r : IndexedRoot} (hk : r.KeysNodup)
    {i j : RootItem} (hi : i ∈ r.items) (hj : j ∈ r.items)
    {k : Coord} (hik : (i.key == k) = true) (hjk : (j.key == k) = true) :
    i = j :=
  hk i hi j hj (by
    have h1 : i.key = k := Coord.beq_iff_eq.mp hik
    have h2 : j.key = k := Coord.beq_iff_eq.mp hjk
    exact Coord.beq_iff_eq.mpr (h1.trans h2.symm))

/-- A sparse VDB grid tree with compact nodes and a combined root table. -/
structure IndexedTree where
  layout : Layout
  root : IndexedRoot

namespace IndexedTree

/-- Root span, mirroring `Tree.rootSpan`. -/
def rootSpan (t : IndexedTree) : Int := t.layout.span 1

/-- Number of levels, mirroring `Tree.depth`. -/
def depth (t : IndexedTree) : Nat := t.layout.levels.length

/-- Erase the compaction: rebuild the spec tree (tiles and children lists
    via `filterMap`; the child nodes are erased with `IndexedNode.toNode`). -/
def toTree (t : IndexedTree) : Tree :=
  { layout := t.layout
    root :=
      { background := t.root.background
        tiles := t.root.items.filterMap RootItem.asTile?
        children := (t.root.items.filterMap RootItem.asChild?).map
          (fun (o, n) => (o, n.toNode)) } }

theorem toTree_rootSpan (t : IndexedTree) :
    t.toTree.rootSpan = t.rootSpan := rfl

theorem toTree_depth (t : IndexedTree) :
    t.toTree.depth = t.depth := rfl

theorem tiles_eq (t : IndexedTree) :
    t.toTree.root.tiles = t.root.items.filterMap RootItem.asTile? := rfl

theorem children_eq (t : IndexedTree) :
    t.toTree.root.children
      = ((t.root.items.filterMap RootItem.asChild?).map
          (fun (o, n) => (o, n.toNode))) := rfl

/-- A tile item witnesses membership of its tile in the erased tree. -/
theorem mem_tiles_of_mem_items {t : IndexedTree} {i : RootItem} (hi : i ∈ t.root.items)
    {tile : Tile} (hkey : RootItem.asTile? i = some tile) :
    tile ∈ t.toTree.root.tiles :=
  tiles_eq t ▸ List.mem_filterMap.mpr ⟨i, hi, hkey⟩

/-- A child item witnesses membership of its erased subtree. -/
theorem mem_children_of_mem_items {t : IndexedTree} {i : RootItem} (hi : i ∈ t.root.items)
    {o : Coord} {n : IndexedNode} (hkey : RootItem.asChild? i = some (o, n)) :
    (o, n.toNode) ∈ t.toTree.root.children :=
  children_eq t ▸ List.mem_map.mpr ⟨(o, n), List.mem_filterMap.mpr ⟨i, hi, hkey⟩, rfl⟩

/-- C-style lookup: probe the root table, then descend through the compact
    nodes. (The spec tree supplies the layout, the background and the slot
    geometry; `descend` only reads those and the raw node.) -/
def lookup (t : IndexedTree) (c : Coord) : VoxelValue × Bool :=
  match t.root.probe (rootKey t.rootSpan c) with
  | some (.tile tile) => (tile.value, tile.active)
  | some (.child _ node) => t.toTree.descend t.depth 1 node c
  | none => (t.root.background, false)

/-- **The combined root probe agrees with the spec root stage**: under
    key uniqueness, the C-style lookup (combined table, rank-compacted
    descent) equals the spec lookup on the erased tree. -/
theorem lookup_eq_toTree_lookup (t : IndexedTree) (hk : t.root.KeysNodup)
    (c : Coord) : t.lookup c = t.toTree.lookup c := by
  cases hp : t.root.probe (rootKey t.rootSpan c) with
  | none =>
      have hf : t.root.items.find? (fun (j : RootItem) => j.key == rootKey t.rootSpan c) = none := by
        unfold IndexedRoot.probe at hp; exact hp
      have hno : ∀ i ∈ t.root.items, ¬ ((i.key == rootKey t.rootSpan c) = true) :=
        List.find?_eq_none.mp hf
      have hnone_tiles :
          t.toTree.root.tiles.find? (fun tt => tt.origin == rootKey t.rootSpan c) = none := by
        rw [List.find?_eq_none]
        intro tt htt htk
        rw [tiles_eq, List.mem_filterMap] at htt
        obtain ⟨i, hi, hit⟩ := htt
        cases i with
        | tile t0 =>
            simp only [RootItem.asTile?, Option.some.injEq] at hit
            subst hit
            exact hno (.tile t0) hi htk
        | child _ _ => simp [RootItem.asTile?] at hit
      have hnone_children :
          t.toTree.root.children.find? (fun p => p.1 == rootKey t.rootSpan c) = none := by
        rw [List.find?_eq_none]
        intro p hpmem hpk
        rw [children_eq, List.mem_map] at hpmem
        obtain ⟨⟨o, n⟩, hqmem, rfl⟩ := hpmem
        rw [List.mem_filterMap] at hqmem
        obtain ⟨i, hi, hqi⟩ := hqmem
        cases i with
        | tile t0 => simp [RootItem.asChild?] at hqi
        | child o' n' =>
            simp only [RootItem.asChild?, Option.some.injEq] at hqi
            obtain ⟨rfl, rfl⟩ := hqi
            exact hno (.child o n) hi hpk
      have hca : Root.childAt t.toTree.root (rootKey t.rootSpan c) = none := by
        simp [Root.childAt, hnone_children]
      have hta : Root.tileAt t.toTree.root (rootKey t.rootSpan c) = none :=
        hnone_tiles
      show (match t.root.probe (rootKey t.rootSpan c) with
            | some (.tile tile) => (tile.value, tile.active)
            | some (.child _ node) => t.toTree.descend t.depth 1 node c
            | none => (t.root.background, false))
          = (match Root.childAt t.toTree.root (rootKey t.rootSpan c) with
             | some n => Tree.lookupNode t.toTree t.toTree.depth 1 n c
             | none => match Root.tileAt t.toTree.root (rootKey t.rootSpan c) with
                       | some tile => (tile.value, tile.active)
                       | none => (t.toTree.root.background, false))
      rw [hp, hca, hta]
      rfl
  | some item =>
    cases item with
    | tile t0 =>
        have hpb := IndexedRoot.probe_some hp
        have hmem := hpb.1
        have hkey := hpb.2
        have hcnone : t.toTree.root.children.find? (fun p => p.1 == rootKey t.rootSpan c) = none := by
          rw [List.find?_eq_none]
          intro p hpmem hpk
          rw [children_eq, List.mem_map] at hpmem
          obtain ⟨⟨o, n⟩, hqmem, rfl⟩ := hpmem
          rw [List.mem_filterMap] at hqmem
          obtain ⟨i, hi, hqi⟩ := hqmem
          cases i with
          | tile t0' => simp [RootItem.asChild?] at hqi
          | child o n =>
              simp only [RootItem.asChild?, Option.some.injEq] at hqi
              obtain ⟨rfl, rfl⟩ := hqi
              have hik : (RootItem.key (.child o n) == rootKey t.rootSpan c) = true := hpk
              have heq : (.child o n : RootItem) = .tile t0 :=
                IndexedRoot.eq_of_same_key hk hi hmem hik hkey
              exact RootItem.noConfusion heq
        have hca : Root.childAt t.toTree.root (rootKey t.rootSpan c) = none := by
          simp [Root.childAt, hcnone]
        have hta : Root.tileAt t.toTree.root (rootKey t.rootSpan c) = some t0 := by
          have hf0 : t.toTree.root.tiles.find? (fun tt => tt.origin == rootKey t.rootSpan c) = some t0 := by
            cases hf : t.toTree.root.tiles.find? (fun tt => tt.origin == rootKey t.rootSpan c) with
            | none =>
              exfalso
              have htmem : t0 ∈ t.toTree.root.tiles :=
                mem_tiles_of_mem_items hmem (by simp [RootItem.asTile?])
              rw [List.find?_eq_none] at hf
              exact hf t0 htmem (by simpa [RootItem.key] using hkey)
            | some t' =>
              have ht'mem : t' ∈ t.toTree.root.tiles := List.mem_of_find?_eq_some hf
              have ht'key : (t'.origin == rootKey t.rootSpan c) = true := by
                simpa using List.find?_some hf
              rw [tiles_eq, List.mem_filterMap] at ht'mem
              obtain ⟨j, hj, hjt⟩ := ht'mem
              cases j with
              | tile tj =>
                  simp only [RootItem.asTile?, Option.some.injEq] at hjt
                  subst hjt
                  have hjk : (RootItem.key (.tile tj) == rootKey t.rootSpan c) = true := by
                    simpa [RootItem.key] using ht'key
                  have heq : (.tile tj : RootItem) = .tile t0 :=
                    IndexedRoot.eq_of_same_key hk hj hmem hjk hkey
                  simp only [RootItem.tile.injEq] at heq
                  subst heq
                  rfl
              | child _ _ => simp [RootItem.asTile?] at hjt
          exact hf0
        show (match t.root.probe (rootKey t.rootSpan c) with
              | some (.tile tile) => (tile.value, tile.active)
              | some (.child _ node) => t.toTree.descend t.depth 1 node c
              | none => (t.root.background, false))
            = (match Root.childAt t.toTree.root (rootKey t.rootSpan c) with
               | some n => Tree.lookupNode t.toTree t.toTree.depth 1 n c
               | none => match Root.tileAt t.toTree.root (rootKey t.rootSpan c) with
                         | some tile => (tile.value, tile.active)
                         | none => (t.toTree.root.background, false))
        rw [hp, hca, hta]
    | child o n =>
        have hpb := IndexedRoot.probe_some hp
        have hmem := hpb.1
        have hkey := hpb.2
        have hcsome : t.toTree.root.children.find? (fun p => p.1 == rootKey t.rootSpan c)
            = some (o, n.toNode) := by
          cases hf : t.toTree.root.children.find? (fun p => p.1 == rootKey t.rootSpan c) with
          | none =>
              exfalso
              have hmemc : (o, n.toNode) ∈ t.toTree.root.children :=
                mem_children_of_mem_items hmem (by rfl)
              rw [List.find?_eq_none] at hf
              exact hf _ hmemc (by simpa [RootItem.key] using hkey)
          | some p =>
              have hpmem : p ∈ t.toTree.root.children := List.mem_of_find?_eq_some hf
              have hpk : (p.1 == rootKey t.rootSpan c) = true := by
                simpa using List.find?_some hf
              rw [children_eq, List.mem_map] at hpmem
              obtain ⟨⟨o', n'⟩, hqmem, rfl⟩ := hpmem
              rw [List.mem_filterMap] at hqmem
              obtain ⟨i, hi, hqi⟩ := hqmem
              cases i with
              | tile t0' => simp [RootItem.asChild?] at hqi
              | child o' n' =>
                  simp only [RootItem.asChild?, Option.some.injEq] at hqi
                  obtain ⟨rfl, rfl⟩ := hqi
                  have hik : (RootItem.key (.child o' n') == rootKey t.rootSpan c) = true := by
                    simpa [RootItem.key] using hpk
                  have heq : (.child o' n' : RootItem) = .child o n :=
                    IndexedRoot.eq_of_same_key hk hi hmem hik hkey
                  simp only [RootItem.child.injEq] at heq
                  obtain ⟨rfl, rfl⟩ := heq
                  rfl
        have hca : Root.childAt t.toTree.root (rootKey t.rootSpan c) = some (n.toNode) := by
          simp [Root.childAt, hcsome]
        have hd := Tree.descend_eq_lookupNode t.toTree t.depth 1 n c
        show (match t.root.probe (rootKey t.rootSpan c) with
              | some (.tile tile) => (tile.value, tile.active)
              | some (.child _ node) => t.toTree.descend t.depth 1 node c
              | none => (t.root.background, false))
            = (match Root.childAt t.toTree.root (rootKey t.rootSpan c) with
               | some n' => Tree.lookupNode t.toTree t.toTree.depth 1 n' c
               | none => match Root.tileAt t.toTree.root (rootKey t.rootSpan c) with
                         | some tile => (tile.value, tile.active)
                         | none => (t.toTree.root.background, false))
        rw [hp, hca]
        exact hd

end IndexedTree

end Vdb
