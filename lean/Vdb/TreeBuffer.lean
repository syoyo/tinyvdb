/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  The tree buffer pass (`tvdb__read_node_buffer` / `tvdb__write_node_buffer`):
  after the topology pass, the same tree is traversed again and every leaf
  writes its value mask plus the compressed value record. Internal nodes
  carry no buffer of their own; the traversal order is the child order, so
  the buffer blob is a flattening of the leaf buffers in depth-first order.

  The value-chunk size is a parameter, as in `Vdb/NodeRecord.lean`.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.TreeNode

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Vdb

/-- A leaf's buffer pass: the value mask again, then the compressed value
    record (`tvdb__read_leaf_buffer` / `tvdb__write_leaf_buffer`). -/
structure LeafBuffer where
  valueMask : NodeMask 3
  record : ValueRecord 3

def LeafBuffer.chunks (b : LeafBuffer) : List Bytes :=
  [@NodeMask.serialize 3 b.valueMask] ++ b.record.chunks

def LeafBuffer.WellFormed (vsize expected : Nat) (b : LeafBuffer) : Prop :=
  b.valueMask < nodeSlots 3 ∧ b.record.WellFormed vsize expected

def LeafBuffer.parseFrom (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (b : Bytes) (off : Nat) : Option (LeafBuffer × Nat) :=
  let vm : NodeMask 3 := parseNat b off (nodeMaskBytes 3)
  match ValueRecord.parseFrom vsize expected decompress b (off + nodeMaskBytes 3) with
  | none => none
  | some (r, o) => some (⟨vm, r⟩, o)

theorem LeafBuffer.parseFrom_emitFrom (b : LeafBuffer) (vsize expected : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : b.WellFormed vsize expected) (pre post : List Bytes) :
    LeafBuffer.parseFrom vsize expected decompress
        (concatChunks (pre ++ b.chunks ++ post)) (concatChunks pre).size =
      some (b, (concatChunks (pre ++ b.chunks)).size) := by
  obtain ⟨hvm, hrec⟩ := h
  rcases b with ⟨vm, r⟩
  simp only [LeafBuffer.WellFormed] at hvm hrec
  unfold LeafBuffer.parseFrom LeafBuffer.chunks
  dsimp only
  rw [show pre ++ ([@NodeMask.serialize 3 vm] ++ r.chunks) ++ post =
      pre ++ (@NodeMask.serialize 3 vm :: (r.chunks ++ post)) from by simp]
  rw [parseNat_chunk_serialize vm hvm pre (r.chunks ++ post)]
  have e1 : (concatChunks (pre ++ [@NodeMask.serialize 3 vm])).size =
      (concatChunks pre).size + nodeMaskBytes 3 := by
    rw [concatChunks_append_map]
    simp [@NodeMask.serialize_size 3 vm hvm]
  rw [show (concatChunks pre).size + nodeMaskBytes 3 =
      (concatChunks (pre ++ [@NodeMask.serialize 3 vm])).size from e1.symm]
  rw [peel1 pre (@NodeMask.serialize 3 vm) (r.chunks ++ post)]
  rw [show concatChunks ((pre ++ [@NodeMask.serialize 3 vm]) ++ (r.chunks ++ post)) =
      concatChunks ((pre ++ [@NodeMask.serialize 3 vm]) ++ r.chunks ++ post) from by simp]
  rw [ValueRecord.parseFrom_emitFrom r vsize expected decompress hrec
    (pre ++ [@NodeMask.serialize 3 vm]) post]
  simp [LeafBuffer.chunks, List.append_assoc]

end Vdb

namespace Vdb

def parseLeafBuffers (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (b : Bytes) : Nat → Nat → Option (List LeafBuffer × Nat)
  | 0, off => some ([], off)
  | n + 1, off =>
    match LeafBuffer.parseFrom vsize expected decompress b off with
    | none => none
    | some (lb, o) =>
      match parseLeafBuffers vsize expected decompress b n o with
      | none => none
      | some (lbs, o') => some (lb :: lbs, o')

theorem parseLeafBuffers_emit (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (lbs : List LeafBuffer) (hwf : ∀ b ∈ lbs, b.WellFormed vsize expected) :
    ∀ (pre post : List Bytes),
      parseLeafBuffers vsize expected decompress
        (concatChunks (pre ++ lbs.flatMap LeafBuffer.chunks ++ post)) lbs.length
        (concatChunks pre).size =
      some (lbs, (concatChunks (pre ++ lbs.flatMap LeafBuffer.chunks)).size) := by
  induction lbs with
  | nil =>
    intro pre post
    simp [parseLeafBuffers, concatChunks]
  | cons lb lbs ih =>
    intro pre post
    have hlb := hwf lb (by simp)
    have hlbs : ∀ b ∈ lbs, b.WellFormed vsize expected := fun b hb => hwf b (by simp [hb])
    simp only [List.length_cons, List.flatMap_cons]
    rw [show pre ++ (lb.chunks ++ lbs.flatMap LeafBuffer.chunks) ++ post =
        pre ++ lb.chunks ++ (lbs.flatMap LeafBuffer.chunks ++ post) from by simp]
    rw [parseLeafBuffers]
    rw [LeafBuffer.parseFrom_emitFrom lb vsize expected decompress hlb pre
      (lbs.flatMap LeafBuffer.chunks ++ post)]
    dsimp only
    rw [show concatChunks (pre ++ lb.chunks ++ (lbs.flatMap LeafBuffer.chunks ++ post)) =
        concatChunks ((pre ++ lb.chunks) ++ lbs.flatMap LeafBuffer.chunks ++ post) from by simp]
    rw [ih hlbs (pre ++ lb.chunks) post]
    simp [List.append_assoc]

/-- The buffer pass of a level-4 internal node: one leaf buffer per child, in
    child order (internal nodes carry no buffer of their own). -/
def Node4.bufferChunks (bs : List LeafBuffer) : List Bytes :=
  bs.flatMap LeafBuffer.chunks

def Node4.parseBuffers (n : Node4) (vsize expected : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) :
    Option (List LeafBuffer × Nat) :=
  parseLeafBuffers vsize expected decompress b n.children.length off

theorem Node4.parseBuffers_emit (n : Node4) (bs : List LeafBuffer)
    (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (hlen : bs.length = n.children.length)
    (hwf : ∀ b ∈ bs, b.WellFormed vsize expected) (pre post : List Bytes) :
    Node4.parseBuffers n vsize expected decompress
        (concatChunks (pre ++ Node4.bufferChunks bs ++ post)) (concatChunks pre).size =
      some (bs, (concatChunks (pre ++ Node4.bufferChunks bs)).size) := by
  unfold Node4.parseBuffers Node4.bufferChunks
  rw [← hlen]
  exact parseLeafBuffers_emit vsize expected decompress bs hwf pre post

end Vdb

namespace Vdb

/-- The buffer chunks of the level-5 child slots, in child order. -/
def Child5Buffers.chunks (bss : List (List LeafBuffer)) : List Bytes :=
  bss.flatMap (fun bs => bs.flatMap LeafBuffer.chunks)

/-- The outer list matches the child slots and each inner list matches that
    child's leaves. -/
def BufMatch : List Child5 → List (List LeafBuffer) → Prop
  | [], [] => True
  | c :: cs, bs :: bss => bs.length = c.node.children.length ∧ BufMatch cs bss
  | _, _ => False

def parseChild5Buffers (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (b : Bytes) : List Child5 → Nat → Option (List (List LeafBuffer) × Nat)
  | [], off => some ([], off)
  | c :: cs, off =>
    match Node4.parseBuffers c.node vsize expected decompress b off with
    | none => none
    | some (lbs, o) =>
      match parseChild5Buffers vsize expected decompress b cs o with
      | none => none
      | some (bss, o') => some (lbs :: bss, o')

theorem parseChild5Buffers_emit (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (cs : List Child5) (bss : List (List LeafBuffer))
    (hm : BufMatch cs bss)
    (hwf : ∀ bs ∈ bss, ∀ b ∈ bs, b.WellFormed vsize expected) :
    ∀ (pre post : List Bytes),
      parseChild5Buffers vsize expected decompress
        (concatChunks (pre ++ Child5Buffers.chunks bss ++ post)) cs
        (concatChunks pre).size =
      some (bss, (concatChunks (pre ++ Child5Buffers.chunks bss)).size) := by
  induction cs generalizing bss with
  | nil =>
    intro pre post
    cases bss with
    | nil => simp [parseChild5Buffers, concatChunks, Child5Buffers.chunks]
    | cons bs bss => simp [BufMatch] at hm
  | cons c cs ih =>
    cases bss with
    | nil => simp [BufMatch] at hm
    | cons bs bss =>
      simp only [BufMatch] at hm
      obtain ⟨hlen, hm'⟩ := hm
      intro pre post
      have hbs : ∀ b ∈ bs, b.WellFormed vsize expected := hwf bs (by simp)
      have hbss : ∀ bs' ∈ bss, ∀ b ∈ bs', b.WellFormed vsize expected :=
        fun bs' hbs' => hwf bs' (by simp [hbs'])
      rw [show Child5Buffers.chunks (bs :: bss) =
          bs.flatMap LeafBuffer.chunks ++ Child5Buffers.chunks bss from rfl]
      rw [show pre ++ (bs.flatMap LeafBuffer.chunks ++ Child5Buffers.chunks bss) ++ post =
          pre ++ Node4.bufferChunks bs ++ (Child5Buffers.chunks bss ++ post) from by
        simp [Node4.bufferChunks]]
      rw [parseChild5Buffers]
      rw [Node4.parseBuffers_emit c.node bs vsize expected decompress hlen hbs pre
        (Child5Buffers.chunks bss ++ post)]
      dsimp only
      rw [show concatChunks (pre ++ Node4.bufferChunks bs ++ (Child5Buffers.chunks bss ++ post)) =
          concatChunks ((pre ++ Node4.bufferChunks bs) ++ Child5Buffers.chunks bss ++ post) from by simp]
      rw [ih bss hm' hbss (pre ++ Node4.bufferChunks bs) post]
      simp [Child5Buffers.chunks, Node4.bufferChunks, List.append_assoc]

/-- The buffer pass of a level-5 node: the buffers of its level-4 children. -/
def Node5.bufferChunks (bss : List (List LeafBuffer)) : List Bytes :=
  Child5Buffers.chunks bss

def Node5.parseBuffers (n : Node5) (vsize expected : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) :
    Option (List (List LeafBuffer) × Nat) :=
  parseChild5Buffers vsize expected decompress b n.children off

theorem Node5.parseBuffers_emit (n : Node5) (bss : List (List LeafBuffer))
    (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (hm : BufMatch n.children bss)
    (hwf : ∀ bs ∈ bss, ∀ b ∈ bs, b.WellFormed vsize expected)
    (pre post : List Bytes) :
    Node5.parseBuffers n vsize expected decompress
        (concatChunks (pre ++ Node5.bufferChunks bss ++ post)) (concatChunks pre).size =
      some (bss, (concatChunks (pre ++ Node5.bufferChunks bss)).size) := by
  unfold Node5.parseBuffers Node5.bufferChunks
  exact parseChild5Buffers_emit vsize expected decompress n.children bss hm hwf pre post

/-- The buffer chunks of the root's child subtrees. -/
def RootBuffers.chunks (bsss : List (List (List LeafBuffer))) : List Bytes :=
  bsss.flatMap Child5Buffers.chunks

/-- The nested buffer lists match the root's child subtrees and their
    level-4 children. -/
def BufMatchRoot : List ChildRoot → List (List (List LeafBuffer)) → Prop
  | [], [] => True
  | c :: cs, bss :: bsss => BufMatch c.node.children bss ∧ BufMatchRoot cs bsss
  | _, _ => False

def parseChildRootBuffers (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (b : Bytes) : List ChildRoot → Nat → Option (List (List (List LeafBuffer)) × Nat)
  | [], off => some ([], off)
  | c :: cs, off =>
    match Node5.parseBuffers c.node vsize expected decompress b off with
    | none => none
    | some (bss, o) =>
      match parseChildRootBuffers vsize expected decompress b cs o with
      | none => none
      | some (bsss, o') => some (bss :: bsss, o')

theorem parseChildRootBuffers_emit (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (cs : List ChildRoot) (bsss : List (List (List LeafBuffer)))
    (hm : BufMatchRoot cs bsss)
    (hwf : ∀ bss ∈ bsss, ∀ bs ∈ bss, ∀ b ∈ bs, b.WellFormed vsize expected) :
    ∀ (pre post : List Bytes),
      parseChildRootBuffers vsize expected decompress
        (concatChunks (pre ++ RootBuffers.chunks bsss ++ post)) cs
        (concatChunks pre).size =
      some (bsss, (concatChunks (pre ++ RootBuffers.chunks bsss)).size) := by
  induction cs generalizing bsss with
  | nil =>
    intro pre post
    cases bsss with
    | nil => simp [parseChildRootBuffers, concatChunks, RootBuffers.chunks]
    | cons bss bsss => simp [BufMatchRoot] at hm
  | cons c cs ih =>
    cases bsss with
    | nil => simp [BufMatchRoot] at hm
    | cons bss bsss =>
      simp only [BufMatchRoot] at hm
      obtain ⟨hm1, hm2⟩ := hm
      intro pre post
      have hbss : ∀ bs ∈ bss, ∀ b ∈ bs, b.WellFormed vsize expected := hwf bss (by simp)
      have hbsss : ∀ bss' ∈ bsss, ∀ bs ∈ bss', ∀ b ∈ bs, b.WellFormed vsize expected :=
        fun bss' hb' => hwf bss' (by simp [hb'])
      rw [show RootBuffers.chunks (bss :: bsss) =
          Child5Buffers.chunks bss ++ RootBuffers.chunks bsss from rfl]
      rw [show pre ++ (Child5Buffers.chunks bss ++ RootBuffers.chunks bsss) ++ post =
          pre ++ Node5.bufferChunks bss ++ (RootBuffers.chunks bsss ++ post) from by
        simp [Node5.bufferChunks]]
      rw [parseChildRootBuffers]
      rw [Node5.parseBuffers_emit c.node bss vsize expected decompress hm1 hbss pre
        (RootBuffers.chunks bsss ++ post)]
      dsimp only
      rw [show concatChunks (pre ++ Node5.bufferChunks bss ++ (RootBuffers.chunks bsss ++ post)) =
          concatChunks ((pre ++ Node5.bufferChunks bss) ++ RootBuffers.chunks bsss ++ post) from by simp]
      rw [ih bsss hm2 hbsss (pre ++ Node5.bufferChunks bss) post]
      simp [RootBuffers.chunks, Node5.bufferChunks, Child5Buffers.chunks, List.append_assoc]

/-- The buffer pass of a root node: the buffers of its child subtrees. -/
def RootNode.bufferChunks (_r : RootNode) (bsss : List (List (List LeafBuffer))) : List Bytes :=
  RootBuffers.chunks bsss

def RootNode.parseBuffers (r : RootNode) (vsize expected : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) :
    Option (List (List (List LeafBuffer)) × Nat) :=
  parseChildRootBuffers vsize expected decompress b r.children off

theorem RootNode.parseBuffers_emit (r : RootNode) (bsss : List (List (List LeafBuffer)))
    (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (hm : BufMatchRoot r.children bsss)
    (hwf : ∀ bss ∈ bsss, ∀ bs ∈ bss, ∀ b ∈ bs, b.WellFormed vsize expected)
    (pre post : List Bytes) :
    RootNode.parseBuffers r vsize expected decompress
        (concatChunks (pre ++ r.bufferChunks bsss ++ post)) (concatChunks pre).size =
      some (bsss, (concatChunks (pre ++ r.bufferChunks bsss)).size) := by
  unfold RootNode.parseBuffers RootNode.bufferChunks
  exact parseChildRootBuffers_emit vsize expected decompress r.children bsss hm hwf pre post

/-- The tree data as stored: topology chunks followed by the buffer chunks. -/
def TreeData5.fullChunks (t : TreeData5) (bsss : List (List (List LeafBuffer))) : List Bytes :=
  t.chunks ++ RootNode.bufferChunks t.root bsss

def TreeData5.parseFull (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (b : Bytes) (off : Nat) : Option (TreeData5 × List (List (List LeafBuffer)) × Nat) :=
  match TreeData5.parseFrom vsize expected decompress b off with
  | none => none
  | some (t, o) =>
    match RootNode.parseBuffers t.root vsize expected decompress b o with
    | none => none
    | some (bsss, o') => some (t, bsss, o')

theorem TreeData5.parseFull_emit (t : TreeData5) (bsss : List (List (List LeafBuffer)))
    (vsize expected : Nat) (decompress : Bytes → Nat → Option Bytes)
    (h : t.WellFormed vsize expected)
    (hm : BufMatchRoot t.root.children bsss)
    (hwf : ∀ bss ∈ bsss, ∀ bs ∈ bss, ∀ b ∈ bs, b.WellFormed vsize expected)
    (pre post : List Bytes) :
    TreeData5.parseFull vsize expected decompress
        (concatChunks (pre ++ t.fullChunks bsss ++ post)) (concatChunks pre).size =
      some (t, bsss, (concatChunks (pre ++ t.fullChunks bsss)).size) := by
  unfold TreeData5.parseFull TreeData5.fullChunks
  rw [show concatChunks (pre ++ (t.chunks ++ RootNode.bufferChunks t.root bsss) ++ post) =
      concatChunks (pre ++ t.chunks ++ (RootNode.bufferChunks t.root bsss ++ post)) from by simp]
  rw [TreeData5.parseFrom_emitFrom t vsize expected decompress h pre
    (RootNode.bufferChunks t.root bsss ++ post)]
  dsimp only
  rw [show concatChunks (pre ++ t.chunks ++ (RootNode.bufferChunks t.root bsss ++ post)) =
      concatChunks ((pre ++ t.chunks) ++ RootNode.bufferChunks t.root bsss ++ post) from by simp]
  rw [RootNode.parseBuffers_emit t.root bsss vsize expected decompress hm hwf (pre ++ t.chunks) post]
  simp [TreeData5.fullChunks, List.append_assoc]

end Vdb
