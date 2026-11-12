/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Node topology for the standard `Tree_float_5_4_3` layout, one level at a
  time (the tree-base/root layer is in `Vdb/Topology.lean`):

  * leaf node (log2dim 3): the value mask;
  * level-4 child slot: an `i32 x3` origin plus the leaf subtree;
  * level-4 internal node: child mask, value mask, the compressed value
    record (`Vdb/NodeRecord.lean`) and its children.

  The value-chunk size (`expected`) is a parameter, because it depends on the
  grid's compression flags, the value size and the per-node active count; the
  round trips are stated with `record.stored.size = expected`.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Meta
import Vdb.NodeRecord
import Vdb.Topology

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
open Vdb

namespace Vdb

/-- A leaf node's topology pass: its `2^9`-bit value mask (file version 222
    and later; older versions also store the origin). -/
structure LeafNode where
  valueMask : NodeMask 3
  deriving Repr

def LeafNode.chunks (l : LeafNode) : List Bytes :=
  [@NodeMask.serialize 3 l.valueMask]

def LeafNode.WellFormed (l : LeafNode) : Prop :=
  l.valueMask < nodeSlots 3

def LeafNode.parseFrom (b : Bytes) (off : Nat) : Option (LeafNode × Nat) :=
  some (⟨parseNat b off (nodeMaskBytes 3)⟩, off + nodeMaskBytes 3)

theorem LeafNode.parseFrom_emitFrom (l : LeafNode) (h : l.WellFormed)
    (pre post : List Bytes) :
    LeafNode.parseFrom (concatChunks (pre ++ l.chunks ++ post)) (concatChunks pre).size =
      some (l, (concatChunks (pre ++ l.chunks)).size) := by
  rcases l with ⟨m⟩
  simp only [LeafNode.WellFormed] at h
  unfold LeafNode.parseFrom LeafNode.chunks
  rw [show concatChunks (pre ++ [@NodeMask.serialize 3 m] ++ post) =
      concatChunks (pre ++ (@NodeMask.serialize 3 m :: post)) from by simp]
  rw [parseNat_chunk_serialize m h pre post]
  dsimp only
  rw [show (concatChunks pre).size + nodeMaskBytes 3 =
      (concatChunks (pre ++ [@NodeMask.serialize 3 m])).size from by
    conv_rhs => rw [concatChunks_snoc_size]
    rw [@NodeMask.serialize_size 3 m h]]

theorem peel1 (pre : List Bytes) (c : Bytes) (tail : List Bytes) :
    concatChunks (pre ++ (c :: tail)) = concatChunks ((pre ++ [c]) ++ tail) := by simp

/-- A level-4 child slot: its origin and the leaf subtree. -/
structure Child4 where
  ox : Int32
  oy : Int32
  oz : Int32
  leaf : LeafNode
  deriving Repr

def Child4.chunks (c : Child4) : List Bytes :=
  [putI32LE c.ox ByteArray.empty, putI32LE c.oy ByteArray.empty,
   putI32LE c.oz ByteArray.empty] ++ c.leaf.chunks

def Child4.WellFormed (c : Child4) : Prop := c.leaf.WellFormed

def Child4.parseFrom (b : Bytes) (off : Nat) : Option (Child4 × Nat) :=
  match getI32LE b off with
  | none => none
  | some ox =>
    match getI32LE b (off + 4) with
    | none => none
    | some oy =>
      match getI32LE b (off + 8) with
      | none => none
      | some oz =>
        match LeafNode.parseFrom b (off + 12) with
        | none => none
        | some (l, o) => some (⟨ox, oy, oz, l⟩, o)

theorem Child4.parseFrom_emitFrom (c : Child4) (h : c.WellFormed)
    (pre post : List Bytes) :
    Child4.parseFrom (concatChunks (pre ++ c.chunks ++ post)) (concatChunks pre).size =
      some (c, (concatChunks (pre ++ c.chunks)).size) := by
  rcases c with ⟨ox, oy, oz, l⟩
  simp only [Child4.WellFormed] at h
  unfold Child4.parseFrom Child4.chunks
  rw [show pre ++ ([putI32LE ox ByteArray.empty, putI32LE oy ByteArray.empty,
      putI32LE oz ByteArray.empty] ++ l.chunks) ++ post =
      pre ++ (putI32LE ox ByteArray.empty :: (putI32LE oy ByteArray.empty ::
        (putI32LE oz ByteArray.empty :: (l.chunks ++ post)))) from by simp]
  rw [getI32LE_chunk]
  dsimp only
  rw [show (concatChunks pre).size + 4 =
      (concatChunks (pre ++ [putI32LE ox ByteArray.empty])).size from by
    conv_rhs => rw [concatChunks_snoc_size]
    simp [putI32LE_size]]
  rw [peel1 pre (putI32LE ox ByteArray.empty) (putI32LE oy ByteArray.empty ::
    (putI32LE oz ByteArray.empty :: (l.chunks ++ post)))]
  rw [getI32LE_chunk]
  dsimp only
  rw [show (concatChunks pre).size + 8 =
      (concatChunks ((pre ++ [putI32LE ox ByteArray.empty]) ++
        [putI32LE oy ByteArray.empty])).size from by
    conv_rhs => rw [concatChunks_snoc_size]
    conv_rhs => rw [concatChunks_snoc_size]
    simp [putI32LE_size]]
  rw [peel1 (pre ++ [putI32LE ox ByteArray.empty]) (putI32LE oy ByteArray.empty)
    (putI32LE oz ByteArray.empty :: (l.chunks ++ post))]
  rw [getI32LE_chunk]
  dsimp only
  rw [show (concatChunks pre).size + 12 =
      (concatChunks (((pre ++ [putI32LE ox ByteArray.empty]) ++
        [putI32LE oy ByteArray.empty]) ++ [putI32LE oz ByteArray.empty])).size from by
    conv_rhs => rw [concatChunks_snoc_size]
    conv_rhs => rw [concatChunks_snoc_size]
    conv_rhs => rw [concatChunks_snoc_size]
    simp [putI32LE_size]]
  rw [peel1 ((pre ++ [putI32LE ox ByteArray.empty]) ++ [putI32LE oy ByteArray.empty])
    (putI32LE oz ByteArray.empty) (l.chunks ++ post)]
  rw [show concatChunks ((((pre ++ [putI32LE ox ByteArray.empty]) ++ [putI32LE oy ByteArray.empty]) ++
      [putI32LE oz ByteArray.empty]) ++ (l.chunks ++ post)) =
      concatChunks ((((pre ++ [putI32LE ox ByteArray.empty]) ++ [putI32LE oy ByteArray.empty]) ++
        [putI32LE oz ByteArray.empty]) ++ l.chunks ++ post) from by simp]
  rw [LeafNode.parseFrom_emitFrom l h (((pre ++ [putI32LE ox ByteArray.empty]) ++
    [putI32LE oy ByteArray.empty]) ++ [putI32LE oz ByteArray.empty]) post]
  simp [Child4.chunks, List.append_assoc]

end Vdb

namespace Vdb

def Child4.parseMany (b : Bytes) : Nat → Nat → Option (List Child4 × Nat)
  | 0, off => some ([], off)
  | n + 1, off =>
    match Child4.parseFrom b off with
    | none => none
    | some (c, o) =>
      match Child4.parseMany b n o with
      | none => none
      | some (cs, o') => some (c :: cs, o')

theorem Child4.parseMany_emit (cs : List Child4) (hwf : ∀ c ∈ cs, c.WellFormed) :
    ∀ (pre post : List Bytes),
      Child4.parseMany (concatChunks (pre ++ cs.flatMap Child4.chunks ++ post))
        cs.length (concatChunks pre).size =
      some (cs, (concatChunks (pre ++ cs.flatMap Child4.chunks)).size) := by
  induction cs with
  | nil =>
    intro pre post
    simp [Child4.parseMany, concatChunks]
  | cons c cs ih =>
    intro pre post
    have hc := hwf c (by simp)
    have hcs : ∀ x ∈ cs, x.WellFormed := fun x hx => hwf x (by simp [hx])
    simp only [List.length_cons, List.flatMap_cons]
    rw [show pre ++ (c.chunks ++ cs.flatMap Child4.chunks) ++ post =
        pre ++ c.chunks ++ (cs.flatMap Child4.chunks ++ post) from by simp]
    rw [Child4.parseMany]
    rw [Child4.parseFrom_emitFrom c hc pre (cs.flatMap Child4.chunks ++ post)]
    dsimp only
    rw [show concatChunks (pre ++ c.chunks ++ (cs.flatMap Child4.chunks ++ post)) =
        concatChunks ((pre ++ c.chunks) ++ cs.flatMap Child4.chunks ++ post) from by simp]
    rw [ih hcs (pre ++ c.chunks) post]
    simp [List.append_assoc]

/-- A standard level-4 internal node's topology: child mask, value mask, its
    compressed value record, then the child slots. -/
structure Node4 where
  childMask : NodeMask 4
  valueMask : NodeMask 4
  record : ValueRecord 4
  children : List Child4

def Node4.chunks (n : Node4) : List Bytes :=
  [@NodeMask.serialize 4 n.childMask, @NodeMask.serialize 4 n.valueMask] ++
    n.record.chunks ++ n.children.flatMap Child4.chunks

def Node4.childCount (n : Node4) : Nat := (setBits n.childMask (nodeSlots 4)).length

def Node4.WellFormed (vsize expected : Nat) (n : Node4) : Prop :=
  n.childMask < nodeSlots 4 ∧ n.valueMask < nodeSlots 4 ∧
  n.children.length = n.childCount ∧
  n.record.WellFormed vsize expected ∧
  (∀ c ∈ n.children, c.WellFormed)

def Node4.parseFrom (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (b : Bytes) (off : Nat) : Option (Node4 × Nat) :=
  let cm : NodeMask 4 := parseNat b off (nodeMaskBytes 4)
  let vm : NodeMask 4 := parseNat b (off + nodeMaskBytes 4) (nodeMaskBytes 4)
  match ValueRecord.parseFrom vsize expected decompress b
      (off + nodeMaskBytes 4 + nodeMaskBytes 4) with
  | none => none
  | some (r, o1) =>
    match Child4.parseMany b (setBits cm (nodeSlots 4)).length o1 with
    | none => none
    | some (cs, o2) => some (⟨cm, vm, r, cs⟩, o2)

theorem Node4.parseFrom_emitFrom (n : Node4) (vsize expected : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : n.WellFormed vsize expected) (pre post : List Bytes) :
    Node4.parseFrom vsize expected decompress
        (concatChunks (pre ++ n.chunks ++ post)) (concatChunks pre).size =
      some (n, (concatChunks (pre ++ n.chunks)).size) := by
  obtain ⟨hcm, hvm, hcnt, hrec, hch⟩ := h
  rcases n with ⟨cm, vm, r, cs⟩
  simp only [Node4.WellFormed] at hcm hvm hcnt hrec hch
  unfold Node4.parseFrom Node4.chunks Node4.childCount at *
  rw [show pre ++ ([@NodeMask.serialize 4 cm, @NodeMask.serialize 4 vm] ++ r.chunks ++
      cs.flatMap Child4.chunks) ++ post =
      pre ++ ((@NodeMask.serialize 4 cm) :: ((@NodeMask.serialize 4 vm) ::
        (r.chunks ++ (cs.flatMap Child4.chunks ++ post)))) from by simp]
  -- first mask
  rw [parseNat_chunk_serialize cm hcm pre ((@NodeMask.serialize 4 vm) ::
    (r.chunks ++ (cs.flatMap Child4.chunks ++ post)))]
  have e1 : (concatChunks (pre ++ [@NodeMask.serialize 4 cm])).size =
      (concatChunks pre).size + nodeMaskBytes 4 := by
    rw [concatChunks_append_map]
    simp [@NodeMask.serialize_size 4 cm hcm]
  rw [show (concatChunks pre).size + nodeMaskBytes 4 =
      (concatChunks (pre ++ [@NodeMask.serialize 4 cm])).size from e1.symm]
  rw [peel1 pre (@NodeMask.serialize 4 cm) ((@NodeMask.serialize 4 vm) ::
    (r.chunks ++ (cs.flatMap Child4.chunks ++ post)))]
  -- second mask
  rw [parseNat_chunk_serialize vm hvm (pre ++ [@NodeMask.serialize 4 cm])
    (r.chunks ++ (cs.flatMap Child4.chunks ++ post))]
  have e2 : (concatChunks ((pre ++ [@NodeMask.serialize 4 cm]) ++
      [@NodeMask.serialize 4 vm])).size =
      (concatChunks (pre ++ [@NodeMask.serialize 4 cm])).size + nodeMaskBytes 4 := by
    rw [concatChunks_snoc_size]
    rw [@NodeMask.serialize_size 4 vm hvm]
  rw [show (concatChunks (pre ++ [@NodeMask.serialize 4 cm])).size + nodeMaskBytes 4 =
      (concatChunks ((pre ++ [@NodeMask.serialize 4 cm]) ++
        [@NodeMask.serialize 4 vm])).size from e2.symm]
  rw [peel1 (pre ++ [@NodeMask.serialize 4 cm]) (@NodeMask.serialize 4 vm)
    (r.chunks ++ (cs.flatMap Child4.chunks ++ post))]
  -- value record
  rw [show concatChunks (((pre ++ [@NodeMask.serialize 4 cm]) ++ [@NodeMask.serialize 4 vm]) ++
      (r.chunks ++ (cs.flatMap Child4.chunks ++ post))) =
      concatChunks (((pre ++ [@NodeMask.serialize 4 cm]) ++ [@NodeMask.serialize 4 vm]) ++
        r.chunks ++ (cs.flatMap Child4.chunks ++ post)) from by simp]
  rw [ValueRecord.parseFrom_emitFrom r vsize expected decompress hrec
    (((pre ++ [@NodeMask.serialize 4 cm]) ++ [@NodeMask.serialize 4 vm])) (cs.flatMap Child4.chunks ++ post)]
  dsimp only
  -- children
  rw [show (concatChunks (((pre ++ [@NodeMask.serialize 4 cm]) ++ [@NodeMask.serialize 4 vm]) ++
      r.chunks)).size = (concatChunks ((((pre ++ [@NodeMask.serialize 4 cm]) ++
      [@NodeMask.serialize 4 vm]) ++ r.chunks))).size from rfl]
  rw [show concatChunks ((((pre ++ [@NodeMask.serialize 4 cm]) ++ [@NodeMask.serialize 4 vm]) ++
      r.chunks) ++ (cs.flatMap Child4.chunks ++ post)) =
      concatChunks ((((pre ++ [@NodeMask.serialize 4 cm]) ++ [@NodeMask.serialize 4 vm]) ++
        r.chunks) ++ cs.flatMap Child4.chunks ++ post) from by simp]
  rw [← hcnt]
  rw [Child4.parseMany_emit cs hch (((pre ++ [@NodeMask.serialize 4 cm]) ++
    [@NodeMask.serialize 4 vm]) ++ r.chunks) post]
  simp [Node4.chunks, List.append_assoc]

end Vdb

namespace Vdb

/-- A level-5 child slot: its origin and the level-4 subtree. -/
structure Child5 where
  ox : Int32
  oy : Int32
  oz : Int32
  node : Node4

def Child5.chunks (c : Child5) : List Bytes :=
  [putI32LE c.ox ByteArray.empty, putI32LE c.oy ByteArray.empty,
   putI32LE c.oz ByteArray.empty] ++ c.node.chunks

def Child5.WellFormed (vsize expected : Nat) (c : Child5) : Prop :=
  c.node.WellFormed vsize expected

def Child5.parseFrom (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (b : Bytes) (off : Nat) : Option (Child5 × Nat) :=
  match getI32LE b off with
  | none => none
  | some ox =>
    match getI32LE b (off + 4) with
    | none => none
    | some oy =>
      match getI32LE b (off + 8) with
      | none => none
      | some oz =>
        match Node4.parseFrom vsize expected decompress b (off + 12) with
        | none => none
        | some (n, o) => some (⟨ox, oy, oz, n⟩, o)

theorem Child5.parseFrom_emitFrom (c : Child5) (vsize expected : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : c.WellFormed vsize expected) (pre post : List Bytes) :
    Child5.parseFrom vsize expected decompress
        (concatChunks (pre ++ c.chunks ++ post)) (concatChunks pre).size =
      some (c, (concatChunks (pre ++ c.chunks)).size) := by
  rcases c with ⟨ox, oy, oz, n⟩
  simp only [Child5.WellFormed] at h
  unfold Child5.parseFrom Child5.chunks
  rw [show pre ++ ([putI32LE ox ByteArray.empty, putI32LE oy ByteArray.empty,
      putI32LE oz ByteArray.empty] ++ n.chunks) ++ post =
      pre ++ (putI32LE ox ByteArray.empty :: (putI32LE oy ByteArray.empty ::
        (putI32LE oz ByteArray.empty :: (n.chunks ++ post)))) from by simp]
  rw [getI32LE_chunk]
  dsimp only
  rw [show (concatChunks pre).size + 4 =
      (concatChunks (pre ++ [putI32LE ox ByteArray.empty])).size from by
    conv_rhs => rw [concatChunks_snoc_size]
    simp [putI32LE_size]]
  rw [peel1 pre (putI32LE ox ByteArray.empty) (putI32LE oy ByteArray.empty ::
    (putI32LE oz ByteArray.empty :: (n.chunks ++ post)))]
  rw [getI32LE_chunk]
  dsimp only
  rw [show (concatChunks pre).size + 8 =
      (concatChunks ((pre ++ [putI32LE ox ByteArray.empty]) ++
        [putI32LE oy ByteArray.empty])).size from by
    conv_rhs => rw [concatChunks_snoc_size]
    conv_rhs => rw [concatChunks_snoc_size]
    simp [putI32LE_size]]
  rw [peel1 (pre ++ [putI32LE ox ByteArray.empty]) (putI32LE oy ByteArray.empty)
    (putI32LE oz ByteArray.empty :: (n.chunks ++ post))]
  rw [getI32LE_chunk]
  dsimp only
  rw [show (concatChunks pre).size + 12 =
      (concatChunks (((pre ++ [putI32LE ox ByteArray.empty]) ++
        [putI32LE oy ByteArray.empty]) ++ [putI32LE oz ByteArray.empty])).size from by
    conv_rhs => rw [concatChunks_snoc_size]
    conv_rhs => rw [concatChunks_snoc_size]
    conv_rhs => rw [concatChunks_snoc_size]
    simp [putI32LE_size]]
  rw [peel1 ((pre ++ [putI32LE ox ByteArray.empty]) ++ [putI32LE oy ByteArray.empty])
    (putI32LE oz ByteArray.empty) (n.chunks ++ post)]
  rw [show concatChunks ((((pre ++ [putI32LE ox ByteArray.empty]) ++ [putI32LE oy ByteArray.empty]) ++
      [putI32LE oz ByteArray.empty]) ++ (n.chunks ++ post)) =
      concatChunks ((((pre ++ [putI32LE ox ByteArray.empty]) ++ [putI32LE oy ByteArray.empty]) ++
        [putI32LE oz ByteArray.empty]) ++ n.chunks ++ post) from by simp]
  rw [Node4.parseFrom_emitFrom n vsize expected decompress h
    (((pre ++ [putI32LE ox ByteArray.empty]) ++ [putI32LE oy ByteArray.empty]) ++
      [putI32LE oz ByteArray.empty]) post]
  simp [Child5.chunks, List.append_assoc]



def Child5.parseMany (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (b : Bytes) : Nat → Nat → Option (List Child5 × Nat)
  | 0, off => some ([], off)
  | n + 1, off =>
    match Child5.parseFrom vsize expected decompress b off with
    | none => none
    | some (c, o) =>
      match Child5.parseMany vsize expected decompress b n o with
      | none => none
      | some (cs, o') => some (c :: cs, o')

theorem Child5.parseMany_emit (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (cs : List Child5) (hwf : ∀ c ∈ cs, c.WellFormed vsize expected) :
    ∀ (pre post : List Bytes),
      Child5.parseMany vsize expected decompress
        (concatChunks (pre ++ cs.flatMap Child5.chunks ++ post)) cs.length (concatChunks pre).size =
      some (cs, (concatChunks (pre ++ cs.flatMap Child5.chunks)).size) := by
  induction cs with
  | nil =>
    intro pre post
    simp [Child5.parseMany, concatChunks]
  | cons c cs ih =>
    intro pre post
    have hc := hwf c (by simp)
    have hcs : ∀ x ∈ cs, x.WellFormed vsize expected := fun x hx => hwf x (by simp [hx])
    simp only [List.length_cons, List.flatMap_cons]
    rw [show pre ++ (c.chunks ++ cs.flatMap Child5.chunks) ++ post =
        pre ++ c.chunks ++ (cs.flatMap Child5.chunks ++ post) from by simp]
    rw [Child5.parseMany]
    rw [Child5.parseFrom_emitFrom c vsize expected decompress hc pre (cs.flatMap Child5.chunks ++ post)]
    dsimp only
    rw [show concatChunks (pre ++ c.chunks ++ (cs.flatMap Child5.chunks ++ post)) =
        concatChunks ((pre ++ c.chunks) ++ cs.flatMap Child5.chunks ++ post) from by simp]
    rw [ih hcs (pre ++ c.chunks) post]
    simp [List.append_assoc]

/-- A root node with tiles and level-5 child subtrees. -/
structure RootNode where
  background : Bytes
  tiles : List RootTile
  children : List Child5

def RootNode.chunks (r : RootNode) : List Bytes :=
  [r.background, putU32LE (UInt32.ofNat r.tiles.length) ByteArray.empty,
   putU32LE (UInt32.ofNat r.children.length) ByteArray.empty] ++
    r.tiles.flatMap RootTile.chunks ++ r.children.flatMap Child5.chunks

def RootNode.WellFormed (vsize expected : Nat) (r : RootNode) : Prop :=
  r.background.size = vsize ∧
  (∀ t ∈ r.tiles, t.value.size = vsize) ∧
  r.tiles.length < 2 ^ 32 ∧ r.children.length < 2 ^ 32 ∧
  (∀ c ∈ r.children, c.WellFormed vsize expected)

def RootNode.parseFrom (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (b : Bytes) (off : Nat) : Option (RootNode × Nat) :=
  match getBytes? b off vsize with
  | none => none
  | some bg =>
    match getU32LE b (off + vsize) with
    | none => none
    | some nt =>
      match getU32LE b (off + vsize + 4) with
      | none => none
      | some nc =>
        match parseTiles vsize b nt.toNat (off + vsize + 8) with
        | none => none
        | some (ts, o1) =>
          match Child5.parseMany vsize expected decompress b nc.toNat o1 with
          | none => none
          | some (cs, o2) => some (⟨bg, ts, cs⟩, o2)



theorem RootNode.parseFrom_emitFrom (r : RootNode) (vsize expected : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : r.WellFormed vsize expected) (pre post : List Bytes) :
    RootNode.parseFrom vsize expected decompress
        (concatChunks (pre ++ r.chunks ++ post)) (concatChunks pre).size =
      some (r, (concatChunks (pre ++ r.chunks)).size) := by
  obtain ⟨hbg, htv, htl, hcl, hch⟩ := h
  rcases r with ⟨bg, ts, cs⟩
  simp only [RootNode.WellFormed] at hbg htv htl hcl hch
  unfold RootNode.parseFrom RootNode.chunks
  rw [show pre ++ ([bg, putU32LE (UInt32.ofNat ts.length) ByteArray.empty,
      putU32LE (UInt32.ofNat cs.length) ByteArray.empty] ++
      ts.flatMap RootTile.chunks ++ cs.flatMap Child5.chunks) ++ post =
      pre ++ (bg :: (putU32LE (UInt32.ofNat ts.length) ByteArray.empty ::
        (putU32LE (UInt32.ofNat cs.length) ByteArray.empty ::
          (ts.flatMap RootTile.chunks ++ (cs.flatMap Child5.chunks ++ post))))) from by simp]
  -- background
  rw [show vsize = bg.size from hbg.symm]
  rw [getBytes?_chunk pre bg (putU32LE (UInt32.ofNat ts.length) ByteArray.empty ::
    (putU32LE (UInt32.ofNat cs.length) ByteArray.empty ::
      (ts.flatMap RootTile.chunks ++ (cs.flatMap Child5.chunks ++ post))))]
  dsimp only
  have e1 : (concatChunks (pre ++ [bg])).size = (concatChunks pre).size + bg.size := by
    rw [concatChunks_append_map]
    simp
  rw [show (concatChunks pre).size + bg.size =
      (concatChunks (pre ++ [bg])).size from e1.symm]
  rw [peel1 pre bg (putU32LE (UInt32.ofNat ts.length) ByteArray.empty ::
    (putU32LE (UInt32.ofNat cs.length) ByteArray.empty ::
      (ts.flatMap RootTile.chunks ++ (cs.flatMap Child5.chunks ++ post))))]
  -- tile count
  rw [getU32LE_chunk]
  dsimp only
  have e2 : (concatChunks ((pre ++ [bg]) ++
      [putU32LE (UInt32.ofNat ts.length) ByteArray.empty])).size =
      (concatChunks (pre ++ [bg])).size + 4 := by
    rw [concatChunks_snoc_size]
    simp [putU32LE_size]
  rw [show (concatChunks (pre ++ [bg])).size + 4 =
      (concatChunks ((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty])).size
      from e2.symm]
  rw [peel1 (pre ++ [bg]) (putU32LE (UInt32.ofNat ts.length) ByteArray.empty)
    (putU32LE (UInt32.ofNat cs.length) ByteArray.empty ::
      (ts.flatMap RootTile.chunks ++ (cs.flatMap Child5.chunks ++ post)))]
  -- child count
  rw [getU32LE_chunk]
  dsimp only
  rw [peel1 ((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty])
    (putU32LE (UInt32.ofNat cs.length) ByteArray.empty)
    (ts.flatMap RootTile.chunks ++ (cs.flatMap Child5.chunks ++ post))]
  -- counts to Nat
  rw [show (UInt32.ofNat ts.length).toNat = ts.length from by
    rw [show (UInt32.ofNat ts.length).toNat = ts.length % UInt32.size from rfl]
    exact Nat.mod_eq_of_lt htl]
  rw [show (UInt32.ofNat cs.length).toNat = cs.length from by
    rw [show (UInt32.ofNat cs.length).toNat = cs.length % UInt32.size from rfl]
    exact Nat.mod_eq_of_lt hcl]
  -- tiles
  have e4 : (concatChunks (((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty]) ++
      [putU32LE (UInt32.ofNat cs.length) ByteArray.empty])).size =
      (concatChunks (pre ++ [bg])).size + 8 := by
    rw [concatChunks_snoc_size, concatChunks_snoc_size]
    simp [putU32LE_size]
  rw [show (concatChunks (pre ++ [bg])).size + 8 =
      (concatChunks (((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty]) ++
        [putU32LE (UInt32.ofNat cs.length) ByteArray.empty])).size from e4.symm]
  rw [show concatChunks ((((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty]) ++
        [putU32LE (UInt32.ofNat cs.length) ByteArray.empty]) ++
        (ts.flatMap RootTile.chunks ++ (cs.flatMap Child5.chunks ++ post))) =
      concatChunks (((((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty]) ++
        [putU32LE (UInt32.ofNat cs.length) ByteArray.empty]) ++ ts.flatMap RootTile.chunks) ++
        (cs.flatMap Child5.chunks ++ post)) from by simp]
  have htv' : ∀ t ∈ ts, t.value.size = bg.size := by
    intro t ht
    rw [htv t ht, hbg]
  rw [parseTiles_emit (bg.size) ts htv'
    (((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty]) ++
      [putU32LE (UInt32.ofNat cs.length) ByteArray.empty]) (cs.flatMap Child5.chunks ++ post)]
  dsimp only
  -- children
  have hch' : ∀ c ∈ cs, c.WellFormed bg.size expected := by
    intro c hc
    rw [show bg.size = vsize from hbg]
    exact hch c hc
  rw [show concatChunks (((((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty]) ++
        [putU32LE (UInt32.ofNat cs.length) ByteArray.empty]) ++ ts.flatMap RootTile.chunks) ++
        (cs.flatMap Child5.chunks ++ post)) =
      concatChunks ((((((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty]) ++
        [putU32LE (UInt32.ofNat cs.length) ByteArray.empty]) ++ ts.flatMap RootTile.chunks) ++
        cs.flatMap Child5.chunks) ++ post) from by simp]
  rw [Child5.parseMany_emit (bg.size) expected decompress cs hch'
    ((((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty]) ++
      [putU32LE (UInt32.ofNat cs.length) ByteArray.empty]) ++ ts.flatMap RootTile.chunks) post]
  simp [RootNode.chunks, List.append_assoc]



/-- The tree data of a grid: the tree-base buffer count (`i32` = 1) followed
    by the root node (tiles + child subtrees). -/
structure TreeData5 where
  root : RootNode

def TreeData5.chunks (t : TreeData5) : List Bytes :=
  putI32LE 1 ByteArray.empty :: t.root.chunks

def TreeData5.WellFormed (vsize expected : Nat) (t : TreeData5) : Prop :=
  t.root.WellFormed vsize expected

def TreeData5.parseFrom (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (b : Bytes) (off : Nat) : Option (TreeData5 × Nat) :=
  match getI32LE b off with
  | none => none
  | some n =>
    if n = 1 then
      match RootNode.parseFrom vsize expected decompress b (off + 4) with
      | none => none
      | some (r, o) => some (⟨r⟩, o)
    else none

theorem TreeData5.parseFrom_emitFrom (t : TreeData5) (vsize expected : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : t.WellFormed vsize expected) (pre post : List Bytes) :
    TreeData5.parseFrom vsize expected decompress
        (concatChunks (pre ++ t.chunks ++ post)) (concatChunks pre).size =
      some (t, (concatChunks (pre ++ t.chunks)).size) := by
  rcases t with ⟨r⟩
  simp only [TreeData5.WellFormed] at h
  unfold TreeData5.parseFrom TreeData5.chunks
  rw [show pre ++ (putI32LE 1 ByteArray.empty :: r.chunks) ++ post =
      pre ++ (putI32LE 1 ByteArray.empty :: (r.chunks ++ post)) from by simp]
  rw [getI32LE_chunk]
  dsimp only
  rw [ite_eq_left (show ((1 : Int32) = 1) from rfl)]
  have e1 : (concatChunks (pre ++ [putI32LE (1 : Int32) ByteArray.empty])).size =
      (concatChunks pre).size + 4 := by
    rw [concatChunks_append_map]
    simp [putI32LE_size]
  rw [show (concatChunks pre).size + 4 =
      (concatChunks (pre ++ [putI32LE (1 : Int32) ByteArray.empty])).size from e1.symm]
  rw [peel1 pre (putI32LE (1 : Int32) ByteArray.empty) (r.chunks ++ post)]
  rw [show concatChunks ((pre ++ [putI32LE (1 : Int32) ByteArray.empty]) ++ (r.chunks ++ post)) =
      concatChunks ((pre ++ [putI32LE (1 : Int32) ByteArray.empty]) ++ r.chunks ++ post) from by simp]
  rw [RootNode.parseFrom_emitFrom r vsize expected decompress h
    (pre ++ [putI32LE (1 : Int32) ByteArray.empty]) post]
  simp [TreeData5.chunks, List.append_assoc]

end Vdb
