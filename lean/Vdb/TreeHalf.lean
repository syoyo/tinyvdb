/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  The count-derived tree cascade with the half-grid chunk omission (F6)
  threaded through it. This is a copy of `Vdb/TreeDerived.lean` in which the
  value-record parser/emitter is the mode-aware `ValueRecord.parseFromCountM`
  / `ValueRecord.chunksM`: when `half` is set and a node's stored count is
  zero, no chunk header is read or written.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.TreeDerived

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace Vdb

/-! ### Mode-aware emit side -/

/-- Level-4 node topology with the mode-aware value record. -/
def Node4.chunksH (n : Node4) (half : Bool) : List Bytes :=
  [@NodeMask.serialize 4 n.childMask, @NodeMask.serialize 4 n.valueMask] ++
    n.record.chunksM half ++ n.children.flatMap Child4.chunks

def Child5.chunksH (c : Child5) (half : Bool) : List Bytes := c.node.chunksH half

def Node5.chunksH (n : Node5) (half : Bool) : List Bytes :=
  [@NodeMask.serialize 5 n.childMask, @NodeMask.serialize 5 n.valueMask] ++
    n.record.chunksM half ++ n.children.flatMap (Child5.chunksH · half)

def ChildRoot.chunksH (c : ChildRoot) (half : Bool) : List Bytes :=
  [putI32LE c.ox ByteArray.empty, putI32LE c.oy ByteArray.empty,
   putI32LE c.oz ByteArray.empty] ++ c.node.chunksH half

def RootNode.chunksH (r : RootNode) (half : Bool) : List Bytes :=
  [r.background, putU32LE (UInt32.ofNat r.tiles.length) ByteArray.empty,
   putU32LE (UInt32.ofNat r.children.length) ByteArray.empty] ++
    r.tiles.flatMap RootTile.chunks ++ r.children.flatMap (ChildRoot.chunksH · half)

def TreeData5.chunksH (t : TreeData5) (half : Bool) : List Bytes :=
  putI32LE 1 ByteArray.empty :: t.root.chunksH half

def LeafBuffer.chunksH (b : LeafBuffer) (half : Bool) : List Bytes :=
  [@NodeMask.serialize 3 b.valueMask] ++ b.record.chunksM half

def Node4.bufferChunksH (bs : List LeafBuffer) (half : Bool) : List Bytes :=
  bs.flatMap (LeafBuffer.chunksH · half)

def Child5Buffers.chunksH (bss : List (List LeafBuffer)) (half : Bool) : List Bytes :=
  bss.flatMap (fun bs => bs.flatMap (LeafBuffer.chunksH · half))

def Node5.bufferChunksH (bss : List (List LeafBuffer)) (half : Bool) : List Bytes :=
  Child5Buffers.chunksH bss half

def RootBuffers.chunksH (bsss : List (List (List LeafBuffer))) (half : Bool) : List Bytes :=
  bsss.flatMap (Child5Buffers.chunksH · half)

def RootNode.bufferChunksH (_r : RootNode) (bsss : List (List (List LeafBuffer)))
    (half : Bool) : List Bytes :=
  RootBuffers.chunksH bsss half

def TreeData5.fullChunksH (t : TreeData5) (half : Bool)
    (bsss : List (List (List LeafBuffer))) : List Bytes :=
  t.chunksH half ++ RootNode.bufferChunksH t.root bsss half





def Node4.parseFromCountH (half : Bool) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) : Option (Node4 × Nat) :=
  let cm : NodeMask 4 := parseNat b off (nodeMaskBytes 4)
  let vm : NodeMask 4 := parseNat b (off + nodeMaskBytes 4) (nodeMaskBytes 4)
  match ValueRecord.parseFromCountM vsize elemSize (storedCount (L := 4) compressed ver vm) decompress b
      (off + nodeMaskBytes 4 + nodeMaskBytes 4) (half := half) with
  | none => none
  | some (r, o1) =>
    match Child4.parseMany b (setBits cm (nodeSlots 4)).length o1 with
    | none => none
    | some (cs, o2) => some (⟨cm, vm, r, cs⟩, o2)

theorem Node4.parseFromCountH_emit {half : Bool} (n : Node4) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : n.WellFormedCount vsize elemSize compressed ver) (pre post : List Bytes) :
    Node4.parseFromCountH half vsize elemSize compressed ver decompress
        (concatChunks (pre ++ n.chunksH half ++ post)) (concatChunks pre).size =
      some (n, (concatChunks (pre ++ n.chunksH half)).size) := by
  obtain ⟨hcm, hvm, hcnt, hrec, hch⟩ := h
  rcases n with ⟨cm, vm, r, cs⟩
  simp only [Node4.WellFormedCount] at hcm hvm hcnt hrec hch
  unfold Node4.parseFromCountH Node4.chunksH Node4.childCount at *
  dsimp only
  rw [show pre ++ ([@NodeMask.serialize 4 cm, @NodeMask.serialize 4 vm] ++ r.chunksM half ++
      cs.flatMap Child4.chunks) ++ post =
      pre ++ ((@NodeMask.serialize 4 cm) :: ((@NodeMask.serialize 4 vm) ::
        (r.chunksM half ++ (cs.flatMap Child4.chunks ++ post)))) from by simp]
  -- first mask
  rw [parseNat_chunk_serialize cm hcm pre ((@NodeMask.serialize 4 vm) ::
    (r.chunksM half ++ (cs.flatMap Child4.chunks ++ post)))]
  have e1 : (concatChunks (pre ++ [@NodeMask.serialize 4 cm])).size =
      (concatChunks pre).size + nodeMaskBytes 4 := by
    rw [concatChunks_append_map]
    simp [@NodeMask.serialize_size 4 cm hcm]
  rw [show (concatChunks pre).size + nodeMaskBytes 4 =
      (concatChunks (pre ++ [@NodeMask.serialize 4 cm])).size from e1.symm]
  rw [peel1 pre (@NodeMask.serialize 4 cm) ((@NodeMask.serialize 4 vm) ::
    (r.chunksM half ++ (cs.flatMap Child4.chunks ++ post)))]
  -- second mask
  rw [parseNat_chunk_serialize vm hvm (pre ++ [@NodeMask.serialize 4 cm])
    (r.chunksM half ++ (cs.flatMap Child4.chunks ++ post))]
  have e2 : (concatChunks ((pre ++ [@NodeMask.serialize 4 cm]) ++
      [@NodeMask.serialize 4 vm])).size =
      (concatChunks (pre ++ [@NodeMask.serialize 4 cm])).size + nodeMaskBytes 4 := by
    rw [concatChunks_snoc_size]
    rw [@NodeMask.serialize_size 4 vm hvm]
  rw [show (concatChunks (pre ++ [@NodeMask.serialize 4 cm])).size + nodeMaskBytes 4 =
      (concatChunks ((pre ++ [@NodeMask.serialize 4 cm]) ++
        [@NodeMask.serialize 4 vm])).size from e2.symm]
  rw [peel1 (pre ++ [@NodeMask.serialize 4 cm]) (@NodeMask.serialize 4 vm)
    (r.chunksM half ++ (cs.flatMap Child4.chunks ++ post))]
  -- value record
  rw [show concatChunks (((pre ++ [@NodeMask.serialize 4 cm]) ++ [@NodeMask.serialize 4 vm]) ++
      (r.chunksM half ++ (cs.flatMap Child4.chunks ++ post))) =
      concatChunks (((pre ++ [@NodeMask.serialize 4 cm]) ++ [@NodeMask.serialize 4 vm]) ++
        r.chunksM half ++ (cs.flatMap Child4.chunks ++ post)) from by simp]
  rw [ValueRecord.parseFromCountM_emit r vsize elemSize (storedCount (L := 4) compressed ver vm) decompress hrec
    (((pre ++ [@NodeMask.serialize 4 cm]) ++ [@NodeMask.serialize 4 vm])) (cs.flatMap Child4.chunks ++ post) (half := half)]
  dsimp only
  -- children
  rw [show (concatChunks (((pre ++ [@NodeMask.serialize 4 cm]) ++ [@NodeMask.serialize 4 vm]) ++
      r.chunksM half)).size = (concatChunks ((((pre ++ [@NodeMask.serialize 4 cm]) ++
      [@NodeMask.serialize 4 vm]) ++ r.chunksM half))).size from rfl]
  rw [show concatChunks ((((pre ++ [@NodeMask.serialize 4 cm]) ++ [@NodeMask.serialize 4 vm]) ++
      r.chunksM half) ++ (cs.flatMap Child4.chunks ++ post)) =
      concatChunks ((((pre ++ [@NodeMask.serialize 4 cm]) ++ [@NodeMask.serialize 4 vm]) ++
        r.chunksM half) ++ cs.flatMap Child4.chunks ++ post) from by simp]
  rw [← hcnt]
  rw [Child4.parseMany_emit cs hch (((pre ++ [@NodeMask.serialize 4 cm]) ++
    [@NodeMask.serialize 4 vm]) ++ r.chunksM half) post]
  simp [Node4.chunksH, List.append_assoc]

def Child5.parseFromCountH (half : Bool) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) : Option (Child5 × Nat) :=
  match Node4.parseFromCountH half vsize elemSize compressed ver decompress b off with
  | none => none
  | some (n, o) => some (⟨n⟩, o)

theorem Child5.parseFromCountH_emit {half : Bool} (c : Child5) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : c.WellFormedCount vsize elemSize compressed ver) (pre post : List Bytes) :
    Child5.parseFromCountH half vsize elemSize compressed ver decompress
        (concatChunks (pre ++ c.chunksH half ++ post)) (concatChunks pre).size =
      some (c, (concatChunks (pre ++ c.chunksH half)).size) := by
  rcases c with ⟨n⟩
  simp only [Child5.WellFormedCount] at h
  unfold Child5.parseFromCountH Child5.chunksH
  rw [Node4.parseFromCountH_emit n vsize elemSize compressed ver decompress h pre post]

def Child5.parseManyCountH (half : Bool) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) : Nat → Nat → Option (List Child5 × Nat)
  | 0, off => some ([], off)
  | n + 1, off =>
    match Child5.parseFromCountH half vsize elemSize compressed ver decompress b off with
    | none => none
    | some (c, o) =>
      match Child5.parseManyCountH half vsize elemSize compressed ver decompress b n o with
      | none => none
      | some (cs, o') => some (c :: cs, o')

theorem Child5.parseManyCountH_emit {half : Bool} (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (cs : List Child5) (hwf : ∀ c ∈ cs, c.WellFormedCount vsize elemSize compressed ver) :
    ∀ (pre post : List Bytes),
      Child5.parseManyCountH half vsize elemSize compressed ver decompress
        (concatChunks (pre ++ cs.flatMap (Child5.chunksH · half) ++ post)) cs.length (concatChunks pre).size =
      some (cs, (concatChunks (pre ++ cs.flatMap (Child5.chunksH · half))).size) := by
  induction cs with
  | nil =>
    intro pre post
    simp [Child5.parseManyCountH, concatChunks]
  | cons c cs ih =>
    intro pre post
    have hc := hwf c (by simp)
    have hcs : ∀ x ∈ cs, x.WellFormedCount vsize elemSize compressed ver := fun x hx => hwf x (by simp [hx])
    simp only [List.length_cons, List.flatMap_cons]
    rw [show pre ++ (c.chunksH half ++ cs.flatMap (Child5.chunksH · half)) ++ post =
        pre ++ c.chunksH half ++ (cs.flatMap (Child5.chunksH · half) ++ post) from by simp]
    rw [Child5.parseManyCountH]
    rw [Child5.parseFromCountH_emit c vsize elemSize compressed ver decompress hc pre (cs.flatMap (Child5.chunksH · half) ++ post) (half := half)]
    dsimp only
    rw [show concatChunks (pre ++ c.chunksH half ++ (cs.flatMap (Child5.chunksH · half) ++ post)) =
        concatChunks ((pre ++ c.chunksH half) ++ cs.flatMap (Child5.chunksH · half) ++ post) from by simp]
    rw [ih hcs (pre ++ c.chunksH half) post]
    simp [List.append_assoc]

def Node5.parseFromCountH (half : Bool) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) : Option (Node5 × Nat) :=
  let cm : NodeMask 5 := parseNat b off (nodeMaskBytes 5)
  let vm : NodeMask 5 := parseNat b (off + nodeMaskBytes 5) (nodeMaskBytes 5)
  match ValueRecord.parseFromCountM vsize elemSize (storedCount (L := 5) compressed ver vm) decompress b
      (off + nodeMaskBytes 5 + nodeMaskBytes 5) (half := half) with
  | none => none
  | some (r, o1) =>
    match Child5.parseManyCountH half vsize elemSize compressed ver decompress b (setBits cm (nodeSlots 5)).length o1 with
    | none => none
    | some (cs, o2) => some (⟨cm, vm, r, cs⟩, o2)

theorem Node5.parseFromCountH_emit {half : Bool} (n : Node5) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : n.WellFormedCount vsize elemSize compressed ver) (pre post : List Bytes) :
    Node5.parseFromCountH half vsize elemSize compressed ver decompress
        (concatChunks (pre ++ n.chunksH half ++ post)) (concatChunks pre).size =
      some (n, (concatChunks (pre ++ n.chunksH half)).size) := by
  obtain ⟨hcm, hvm, hcnt, hrec, hch⟩ := h
  rcases n with ⟨cm, vm, r, cs⟩
  simp only [Node5.WellFormedCount] at hcm hvm hcnt hrec hch
  unfold Node5.parseFromCountH Node5.chunksH Node5.childCount at *
  dsimp only
  rw [show pre ++ ([@NodeMask.serialize 5 cm, @NodeMask.serialize 5 vm] ++ r.chunksM half ++
      cs.flatMap (Child5.chunksH · half)) ++ post =
      pre ++ ((@NodeMask.serialize 5 cm) :: ((@NodeMask.serialize 5 vm) ::
        (r.chunksM half ++ (cs.flatMap (Child5.chunksH · half) ++ post)))) from by simp]
  -- first mask
  rw [parseNat_chunk_serialize (L := 5) cm hcm pre ((@NodeMask.serialize 5 vm) ::
    (r.chunksM half ++ (cs.flatMap (Child5.chunksH · half) ++ post)))]
  have e1 : (concatChunks (pre ++ [@NodeMask.serialize 5 cm])).size =
      (concatChunks pre).size + nodeMaskBytes 5 := by
    rw [concatChunks_append_map]
    simp [@NodeMask.serialize_size 5 cm hcm]
  rw [show (concatChunks pre).size + nodeMaskBytes 5 =
      (concatChunks (pre ++ [@NodeMask.serialize 5 cm])).size from e1.symm]
  rw [peel1 pre (@NodeMask.serialize 5 cm) ((@NodeMask.serialize 5 vm) ::
    (r.chunksM half ++ (cs.flatMap (Child5.chunksH · half) ++ post)))]
  -- second mask
  rw [parseNat_chunk_serialize (L := 5) vm hvm (pre ++ [@NodeMask.serialize 5 cm])
    (r.chunksM half ++ (cs.flatMap (Child5.chunksH · half) ++ post))]
  have e2 : (concatChunks ((pre ++ [@NodeMask.serialize 5 cm]) ++
      [@NodeMask.serialize 5 vm])).size =
      (concatChunks (pre ++ [@NodeMask.serialize 5 cm])).size + nodeMaskBytes 5 := by
    rw [concatChunks_snoc_size]
    rw [@NodeMask.serialize_size 5 vm hvm]
  rw [show (concatChunks (pre ++ [@NodeMask.serialize 5 cm])).size + nodeMaskBytes 5 =
      (concatChunks ((pre ++ [@NodeMask.serialize 5 cm]) ++
        [@NodeMask.serialize 5 vm])).size from e2.symm]
  rw [peel1 (pre ++ [@NodeMask.serialize 5 cm]) (@NodeMask.serialize 5 vm)
    (r.chunksM half ++ (cs.flatMap (Child5.chunksH · half) ++ post))]
  -- value record
  rw [show concatChunks (((pre ++ [@NodeMask.serialize 5 cm]) ++ [@NodeMask.serialize 5 vm]) ++
      (r.chunksM half ++ (cs.flatMap (Child5.chunksH · half) ++ post))) =
      concatChunks (((pre ++ [@NodeMask.serialize 5 cm]) ++ [@NodeMask.serialize 5 vm]) ++
        r.chunksM half ++ (cs.flatMap (Child5.chunksH · half) ++ post)) from by simp]
  rw [ValueRecord.parseFromCountM_emit r vsize elemSize (storedCount (L := 5) compressed ver vm) decompress hrec
    (((pre ++ [@NodeMask.serialize 5 cm]) ++ [@NodeMask.serialize 5 vm])) (cs.flatMap (Child5.chunksH · half) ++ post) (half := half)]
  dsimp only
  -- children
  rw [show (concatChunks (((pre ++ [@NodeMask.serialize 5 cm]) ++ [@NodeMask.serialize 5 vm]) ++
      r.chunksM half)).size = (concatChunks ((((pre ++ [@NodeMask.serialize 5 cm]) ++
      [@NodeMask.serialize 5 vm]) ++ r.chunksM half))).size from rfl]
  rw [show concatChunks ((((pre ++ [@NodeMask.serialize 5 cm]) ++ [@NodeMask.serialize 5 vm]) ++
      r.chunksM half) ++ (cs.flatMap (Child5.chunksH · half) ++ post)) =
      concatChunks ((((pre ++ [@NodeMask.serialize 5 cm]) ++ [@NodeMask.serialize 5 vm]) ++
        r.chunksM half) ++ cs.flatMap (Child5.chunksH · half) ++ post) from by simp]
  rw [← hcnt]
  rw [Child5.parseManyCountH_emit vsize elemSize compressed ver decompress cs hch (((pre ++ [@NodeMask.serialize 5 cm]) ++
    [@NodeMask.serialize 5 vm]) ++ r.chunksM half) post]
  simp [Node5.chunksH, List.append_assoc]

def ChildRoot.parseFromCountH (half : Bool) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) : Option (ChildRoot × Nat) :=
  match getI32LE b off with
  | none => none
  | some ox =>
    match getI32LE b (off + 4) with
    | none => none
    | some oy =>
      match getI32LE b (off + 8) with
      | none => none
      | some oz =>
        match Node5.parseFromCountH half vsize elemSize compressed ver decompress b (off + 12) with
        | none => none
        | some (n, o) => some (⟨ox, oy, oz, n⟩, o)

theorem ChildRoot.parseFromCountH_emit {half : Bool} (c : ChildRoot) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : c.WellFormedCount vsize elemSize compressed ver) (pre post : List Bytes) :
    ChildRoot.parseFromCountH half vsize elemSize compressed ver decompress
        (concatChunks (pre ++ c.chunksH half ++ post)) (concatChunks pre).size =
      some (c, (concatChunks (pre ++ c.chunksH half)).size) := by
  rcases c with ⟨ox, oy, oz, n⟩
  simp only [ChildRoot.WellFormedCount] at h
  unfold ChildRoot.parseFromCountH ChildRoot.chunksH
  rw [show pre ++ ([putI32LE ox ByteArray.empty, putI32LE oy ByteArray.empty,
      putI32LE oz ByteArray.empty] ++ n.chunksH half) ++ post =
      pre ++ (putI32LE ox ByteArray.empty :: (putI32LE oy ByteArray.empty ::
        (putI32LE oz ByteArray.empty :: (n.chunksH half ++ post)))) from by simp]
  rw [getI32LE_chunk]
  dsimp only
  rw [show (concatChunks pre).size + 4 =
      (concatChunks (pre ++ [putI32LE ox ByteArray.empty])).size from by
    conv_rhs => rw [concatChunks_snoc_size]
    simp [putI32LE_size]]
  rw [peel1 pre (putI32LE ox ByteArray.empty) (putI32LE oy ByteArray.empty ::
    (putI32LE oz ByteArray.empty :: (n.chunksH half ++ post)))]
  rw [getI32LE_chunk]
  dsimp only
  rw [show (concatChunks pre).size + 8 =
      (concatChunks ((pre ++ [putI32LE ox ByteArray.empty]) ++
        [putI32LE oy ByteArray.empty])).size from by
    conv_rhs => rw [concatChunks_snoc_size]
    conv_rhs => rw [concatChunks_snoc_size]
    simp [putI32LE_size]]
  rw [peel1 (pre ++ [putI32LE ox ByteArray.empty]) (putI32LE oy ByteArray.empty)
    (putI32LE oz ByteArray.empty :: (n.chunksH half ++ post))]
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
    (putI32LE oz ByteArray.empty) (n.chunksH half ++ post)]
  rw [show concatChunks ((((pre ++ [putI32LE ox ByteArray.empty]) ++ [putI32LE oy ByteArray.empty]) ++
      [putI32LE oz ByteArray.empty]) ++ (n.chunksH half ++ post)) =
      concatChunks ((((pre ++ [putI32LE ox ByteArray.empty]) ++ [putI32LE oy ByteArray.empty]) ++
        [putI32LE oz ByteArray.empty]) ++ n.chunksH half ++ post) from by simp]
  rw [Node5.parseFromCountH_emit n vsize elemSize compressed ver decompress h
    (((pre ++ [putI32LE ox ByteArray.empty]) ++ [putI32LE oy ByteArray.empty]) ++
      [putI32LE oz ByteArray.empty]) post]
  simp [ChildRoot.chunksH, List.append_assoc]

def ChildRoot.parseManyCountH (half : Bool) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) : Nat → Nat → Option (List ChildRoot × Nat)
  | 0, off => some ([], off)
  | n + 1, off =>
    match ChildRoot.parseFromCountH half vsize elemSize compressed ver decompress b off with
    | none => none
    | some (c, o) =>
      match ChildRoot.parseManyCountH half vsize elemSize compressed ver decompress b n o with
      | none => none
      | some (cs, o') => some (c :: cs, o')

theorem ChildRoot.parseManyCountH_emit {half : Bool} (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (cs : List ChildRoot) (hwf : ∀ c ∈ cs, c.WellFormedCount vsize elemSize compressed ver) :
    ∀ (pre post : List Bytes),
      ChildRoot.parseManyCountH half vsize elemSize compressed ver decompress
        (concatChunks (pre ++ cs.flatMap (ChildRoot.chunksH · half) ++ post)) cs.length (concatChunks pre).size =
      some (cs, (concatChunks (pre ++ cs.flatMap (ChildRoot.chunksH · half))).size) := by
  induction cs with
  | nil =>
    intro pre post
    simp [ChildRoot.parseManyCountH, concatChunks]
  | cons c cs ih =>
    intro pre post
    have hc := hwf c (by simp)
    have hcs : ∀ x ∈ cs, x.WellFormedCount vsize elemSize compressed ver := fun x hx => hwf x (by simp [hx])
    simp only [List.length_cons, List.flatMap_cons]
    rw [show pre ++ (c.chunksH half ++ cs.flatMap (ChildRoot.chunksH · half)) ++ post =
        pre ++ c.chunksH half ++ (cs.flatMap (ChildRoot.chunksH · half) ++ post) from by simp]
    rw [ChildRoot.parseManyCountH]
    rw [ChildRoot.parseFromCountH_emit c vsize elemSize compressed ver decompress hc pre (cs.flatMap (ChildRoot.chunksH · half) ++ post)]
    dsimp only
    rw [show concatChunks (pre ++ c.chunksH half ++ (cs.flatMap (ChildRoot.chunksH · half) ++ post)) =
        concatChunks ((pre ++ c.chunksH half) ++ cs.flatMap (ChildRoot.chunksH · half) ++ post) from by simp]
    rw [ih hcs (pre ++ c.chunksH half) post]
    simp [List.append_assoc]

def RootNode.parseFromCountH (half : Bool) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) : Option (RootNode × Nat) :=
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
          match ChildRoot.parseManyCountH half vsize elemSize compressed ver decompress b nc.toNat o1 with
          | none => none
          | some (cs, o2) => some (⟨bg, ts, cs⟩, o2)

theorem RootNode.parseFromCountH_emit {half : Bool} (r : RootNode) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : r.WellFormedCount vsize elemSize compressed ver) (pre post : List Bytes) :
    RootNode.parseFromCountH half vsize elemSize compressed ver decompress
        (concatChunks (pre ++ r.chunksH half ++ post)) (concatChunks pre).size =
      some (r, (concatChunks (pre ++ r.chunksH half)).size) := by
  obtain ⟨hbg, htv, htl, hcl, hch⟩ := h
  rcases r with ⟨bg, ts, cs⟩
  simp only [RootNode.WellFormedCount] at hbg htv htl hcl hch
  unfold RootNode.parseFromCountH RootNode.chunksH
  rw [show pre ++ ([bg, putU32LE (UInt32.ofNat ts.length) ByteArray.empty,
      putU32LE (UInt32.ofNat cs.length) ByteArray.empty] ++
      ts.flatMap RootTile.chunks ++ cs.flatMap (ChildRoot.chunksH · half)) ++ post =
      pre ++ (bg :: (putU32LE (UInt32.ofNat ts.length) ByteArray.empty ::
        (putU32LE (UInt32.ofNat cs.length) ByteArray.empty ::
          (ts.flatMap RootTile.chunks ++ (cs.flatMap (ChildRoot.chunksH · half) ++ post))))) from by simp]
  -- background
  rw [show vsize = bg.size from hbg.symm]
  rw [getBytes?_chunk pre bg (putU32LE (UInt32.ofNat ts.length) ByteArray.empty ::
    (putU32LE (UInt32.ofNat cs.length) ByteArray.empty ::
      (ts.flatMap RootTile.chunks ++ (cs.flatMap (ChildRoot.chunksH · half) ++ post))))]
  dsimp only
  have e1 : (concatChunks (pre ++ [bg])).size = (concatChunks pre).size + bg.size := by
    rw [concatChunks_append_map]
    simp
  rw [show (concatChunks pre).size + bg.size =
      (concatChunks (pre ++ [bg])).size from e1.symm]
  rw [peel1 pre bg (putU32LE (UInt32.ofNat ts.length) ByteArray.empty ::
    (putU32LE (UInt32.ofNat cs.length) ByteArray.empty ::
      (ts.flatMap RootTile.chunks ++ (cs.flatMap (ChildRoot.chunksH · half) ++ post))))]
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
      (ts.flatMap RootTile.chunks ++ (cs.flatMap (ChildRoot.chunksH · half) ++ post)))]
  -- child count
  rw [getU32LE_chunk]
  dsimp only
  rw [peel1 ((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty])
    (putU32LE (UInt32.ofNat cs.length) ByteArray.empty)
    (ts.flatMap RootTile.chunks ++ (cs.flatMap (ChildRoot.chunksH · half) ++ post))]
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
        (ts.flatMap RootTile.chunks ++ (cs.flatMap (ChildRoot.chunksH · half) ++ post))) =
      concatChunks (((((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty]) ++
        [putU32LE (UInt32.ofNat cs.length) ByteArray.empty]) ++ ts.flatMap RootTile.chunks) ++
        (cs.flatMap (ChildRoot.chunksH · half) ++ post)) from by simp]
  have htv' : ∀ t ∈ ts, t.value.size = bg.size := by
    intro t ht
    rw [htv t ht, hbg]
  rw [parseTiles_emit (bg.size) ts htv'
    (((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty]) ++
      [putU32LE (UInt32.ofNat cs.length) ByteArray.empty]) (cs.flatMap (ChildRoot.chunksH · half) ++ post)]
  dsimp only
  -- children
  have hch' : ∀ c ∈ cs, c.WellFormedCount bg.size elemSize compressed ver := by
    intro c hc
    rw [show bg.size = vsize from hbg]
    exact hch c hc
  rw [show concatChunks (((((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty]) ++
        [putU32LE (UInt32.ofNat cs.length) ByteArray.empty]) ++ ts.flatMap RootTile.chunks) ++
        (cs.flatMap (ChildRoot.chunksH · half) ++ post)) =
      concatChunks ((((((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty]) ++
        [putU32LE (UInt32.ofNat cs.length) ByteArray.empty]) ++ ts.flatMap RootTile.chunks) ++
        cs.flatMap (ChildRoot.chunksH · half)) ++ post) from by simp]
  rw [ChildRoot.parseManyCountH_emit (bg.size) elemSize compressed ver decompress cs hch'
    ((((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty]) ++
      [putU32LE (UInt32.ofNat cs.length) ByteArray.empty]) ++ ts.flatMap RootTile.chunks) post]
  simp [RootNode.chunksH, List.append_assoc]

def TreeData5.parseFromCountH (half : Bool) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) : Option (TreeData5 × Nat) :=
  match getI32LE b off with
  | none => none
  | some n =>
    if n = 1 then
      match RootNode.parseFromCountH half vsize elemSize compressed ver decompress b (off + 4) with
      | none => none
      | some (r, o) => some (⟨r⟩, o)
    else none

theorem TreeData5.parseFromCountH_emit {half : Bool} (t : TreeData5) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : t.WellFormedCount vsize elemSize compressed ver) (pre post : List Bytes) :
    TreeData5.parseFromCountH half vsize elemSize compressed ver decompress
        (concatChunks (pre ++ t.chunksH half ++ post)) (concatChunks pre).size =
      some (t, (concatChunks (pre ++ t.chunksH half)).size) := by
  rcases t with ⟨r⟩
  simp only [TreeData5.WellFormedCount] at h
  unfold TreeData5.parseFromCountH TreeData5.chunksH
  rw [show pre ++ (putI32LE 1 ByteArray.empty :: r.chunksH half) ++ post =
      pre ++ (putI32LE 1 ByteArray.empty :: (r.chunksH half ++ post)) from by simp]
  rw [getI32LE_chunk]
  dsimp only
  rw [ite_eq_left (show ((1 : Int32) = 1) from rfl)]
  have e1 : (concatChunks (pre ++ [putI32LE (1 : Int32) ByteArray.empty])).size =
      (concatChunks pre).size + 4 := by
    rw [concatChunks_append_map]
    simp [putI32LE_size]
  rw [show (concatChunks pre).size + 4 =
      (concatChunks (pre ++ [putI32LE (1 : Int32) ByteArray.empty])).size from e1.symm]
  rw [peel1 pre (putI32LE (1 : Int32) ByteArray.empty) (r.chunksH half ++ post)]
  rw [show concatChunks ((pre ++ [putI32LE (1 : Int32) ByteArray.empty]) ++ (r.chunksH half ++ post)) =
      concatChunks ((pre ++ [putI32LE (1 : Int32) ByteArray.empty]) ++ r.chunksH half ++ post) from by simp]
  rw [RootNode.parseFromCountH_emit r vsize elemSize compressed ver decompress h
    (pre ++ [putI32LE (1 : Int32) ByteArray.empty]) post]
  simp [TreeData5.chunksH, List.append_assoc]

def LeafBuffer.parseFromCountH (half : Bool) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) : Option (LeafBuffer × Nat) :=
  let vm : NodeMask 3 := parseNat b off (nodeMaskBytes 3)
  match ValueRecord.parseFromCountM vsize elemSize (storedCount (L := 3) compressed ver vm) decompress b (off + nodeMaskBytes 3) (half := half) with
  | none => none
  | some (r, o) => some (⟨vm, r⟩, o)

theorem LeafBuffer.parseFromCountH_emit {half : Bool} (b : LeafBuffer) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : b.WellFormedCount vsize elemSize compressed ver) (pre post : List Bytes) :
    LeafBuffer.parseFromCountH half vsize elemSize compressed ver decompress
        (concatChunks (pre ++ b.chunksH half ++ post)) (concatChunks pre).size =
      some (b, (concatChunks (pre ++ b.chunksH half)).size) := by
  obtain ⟨hvm, hrec⟩ := h
  rcases b with ⟨vm, r⟩
  simp only [LeafBuffer.WellFormedCount] at hvm hrec
  unfold LeafBuffer.parseFromCountH LeafBuffer.chunksH
  dsimp only
  rw [show pre ++ ([@NodeMask.serialize 3 vm] ++ r.chunksM half) ++ post =
      pre ++ (@NodeMask.serialize 3 vm :: (r.chunksM half ++ post)) from by simp]
  rw [parseNat_chunk_serialize vm hvm pre (r.chunksM half ++ post)]
  have e1 : (concatChunks (pre ++ [@NodeMask.serialize 3 vm])).size =
      (concatChunks pre).size + nodeMaskBytes 3 := by
    rw [concatChunks_append_map]
    simp [@NodeMask.serialize_size 3 vm hvm]
  rw [show (concatChunks pre).size + nodeMaskBytes 3 =
      (concatChunks (pre ++ [@NodeMask.serialize 3 vm])).size from e1.symm]
  rw [peel1 pre (@NodeMask.serialize 3 vm) (r.chunksM half ++ post)]
  rw [show concatChunks ((pre ++ [@NodeMask.serialize 3 vm]) ++ (r.chunksM half ++ post)) =
      concatChunks ((pre ++ [@NodeMask.serialize 3 vm]) ++ r.chunksM half ++ post) from by simp]
  rw [ValueRecord.parseFromCountM_emit r vsize elemSize (storedCount (L := 3) compressed ver vm) decompress hrec
    (pre ++ [@NodeMask.serialize 3 vm]) post (half := half)]
  simp [LeafBuffer.chunksH, List.append_assoc]

def parseLeafBuffersCountH (half : Bool) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) : Nat → Nat → Option (List LeafBuffer × Nat)
  | 0, off => some ([], off)
  | n + 1, off =>
    match LeafBuffer.parseFromCountH half vsize elemSize compressed ver decompress b off with
    | none => none
    | some (lb, o) =>
      match parseLeafBuffersCountH half vsize elemSize compressed ver decompress b n o with
      | none => none
      | some (lbs, o') => some (lb :: lbs, o')

theorem parseLeafBuffersCountH_emit {half : Bool} (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (lbs : List LeafBuffer) (hwf : ∀ b ∈ lbs, b.WellFormedCount vsize elemSize compressed ver) :
    ∀ (pre post : List Bytes),
      parseLeafBuffersCountH half vsize elemSize compressed ver decompress
        (concatChunks (pre ++ lbs.flatMap (LeafBuffer.chunksH · half) ++ post)) lbs.length
        (concatChunks pre).size =
      some (lbs, (concatChunks (pre ++ lbs.flatMap (LeafBuffer.chunksH · half))).size) := by
  induction lbs with
  | nil =>
    intro pre post
    simp [parseLeafBuffersCountH, concatChunks]
  | cons lb lbs ih =>
    intro pre post
    have hlb := hwf lb (by simp)
    have hlbs : ∀ b ∈ lbs, b.WellFormedCount vsize elemSize compressed ver := fun b hb => hwf b (by simp [hb])
    simp only [List.length_cons, List.flatMap_cons]
    rw [show pre ++ (lb.chunksH half ++ lbs.flatMap (LeafBuffer.chunksH · half)) ++ post =
        pre ++ lb.chunksH half ++ (lbs.flatMap (LeafBuffer.chunksH · half) ++ post) from by simp]
    rw [parseLeafBuffersCountH]
    rw [LeafBuffer.parseFromCountH_emit lb vsize elemSize compressed ver decompress hlb pre
      (lbs.flatMap (LeafBuffer.chunksH · half) ++ post)]
    dsimp only
    rw [show concatChunks (pre ++ lb.chunksH half ++ (lbs.flatMap (LeafBuffer.chunksH · half) ++ post)) =
        concatChunks ((pre ++ lb.chunksH half) ++ lbs.flatMap (LeafBuffer.chunksH · half) ++ post) from by simp]
    rw [ih hlbs (pre ++ lb.chunksH half) post]
    simp [List.append_assoc]

def Node4.parseBuffersCountH (half : Bool) (n : Node4) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) :
    Option (List LeafBuffer × Nat) :=
  parseLeafBuffersCountH half vsize elemSize compressed ver decompress b n.children.length off

theorem Node4.parseBuffersCountH_emit {half : Bool} (n : Node4) (bs : List LeafBuffer)
    (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (decompress : Bytes → Nat → Option Bytes)
    (hlen : bs.length = n.children.length)
    (hwf : ∀ b ∈ bs, b.WellFormedCount vsize elemSize compressed ver) (pre post : List Bytes) :
    Node4.parseBuffersCountH half n vsize elemSize compressed ver decompress
        (concatChunks (pre ++ Node4.bufferChunksH bs half ++ post)) (concatChunks pre).size =
      some (bs, (concatChunks (pre ++ Node4.bufferChunksH bs half)).size) := by
  unfold Node4.parseBuffersCountH Node4.bufferChunksH
  rw [← hlen]
  exact parseLeafBuffersCountH_emit vsize elemSize compressed ver decompress bs hwf pre post

def parseChild5BuffersCountH (half : Bool) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) : List Child5 → Nat → Option (List (List LeafBuffer) × Nat)
  | [], off => some ([], off)
  | c :: cs, off =>
    match Node4.parseBuffersCountH half c.node vsize elemSize compressed ver decompress b off with
    | none => none
    | some (lbs, o) =>
      match parseChild5BuffersCountH half vsize elemSize compressed ver decompress b cs o with
      | none => none
      | some (bss, o') => some (lbs :: bss, o')

theorem parseChild5BuffersCountH_emit {half : Bool} (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (cs : List Child5) (bss : List (List LeafBuffer))
    (hm : BufMatch cs bss)
    (hwf : ∀ bs ∈ bss, ∀ b ∈ bs, b.WellFormedCount vsize elemSize compressed ver) :
    ∀ (pre post : List Bytes),
      parseChild5BuffersCountH half vsize elemSize compressed ver decompress
        (concatChunks (pre ++ Child5Buffers.chunksH bss half ++ post)) cs
        (concatChunks pre).size =
      some (bss, (concatChunks (pre ++ Child5Buffers.chunksH bss half)).size) := by
  induction cs generalizing bss with
  | nil =>
    intro pre post
    cases bss with
    | nil => simp [parseChild5BuffersCountH, concatChunks, Child5Buffers.chunksH]
    | cons bs bss => simp [BufMatch] at hm
  | cons c cs ih =>
    cases bss with
    | nil => simp [BufMatch] at hm
    | cons bs bss =>
      simp only [BufMatch] at hm
      obtain ⟨hlen, hm'⟩ := hm
      intro pre post
      have hbs : ∀ b ∈ bs, b.WellFormedCount vsize elemSize compressed ver := hwf bs (by simp)
      have hbss : ∀ bs' ∈ bss, ∀ b ∈ bs', b.WellFormedCount vsize elemSize compressed ver :=
        fun bs' hbs' => hwf bs' (by simp [hbs'])
      rw [show Child5Buffers.chunksH (bs :: bss) half =
          bs.flatMap (LeafBuffer.chunksH · half) ++ Child5Buffers.chunksH bss half from rfl]
      rw [show pre ++ (bs.flatMap (LeafBuffer.chunksH · half) ++ Child5Buffers.chunksH bss half) ++ post =
          pre ++ Node4.bufferChunksH bs half ++ (Child5Buffers.chunksH bss half ++ post) from by
        simp [Node4.bufferChunksH]]
      rw [parseChild5BuffersCountH]
      rw [Node4.parseBuffersCountH_emit c.node bs vsize elemSize compressed ver decompress hlen hbs pre
        (Child5Buffers.chunksH bss half ++ post)]
      dsimp only
      rw [show concatChunks (pre ++ Node4.bufferChunksH bs half ++ (Child5Buffers.chunksH bss half ++ post)) =
          concatChunks ((pre ++ Node4.bufferChunksH bs half) ++ Child5Buffers.chunksH bss half ++ post) from by simp]
      rw [ih bss hm' hbss (pre ++ Node4.bufferChunksH bs half) post]
      simp [Child5Buffers.chunksH, Node4.bufferChunksH, List.append_assoc]

def Node5.parseBuffersCountH (half : Bool) (n : Node5) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) :
    Option (List (List LeafBuffer) × Nat) :=
  parseChild5BuffersCountH half vsize elemSize compressed ver decompress b n.children off

theorem Node5.parseBuffersCountH_emit {half : Bool} (n : Node5) (bss : List (List LeafBuffer))
    (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (decompress : Bytes → Nat → Option Bytes)
    (hm : BufMatch n.children bss)
    (hwf : ∀ bs ∈ bss, ∀ b ∈ bs, b.WellFormedCount vsize elemSize compressed ver)
    (pre post : List Bytes) :
    Node5.parseBuffersCountH half n vsize elemSize compressed ver decompress
        (concatChunks (pre ++ Node5.bufferChunksH bss half ++ post)) (concatChunks pre).size =
      some (bss, (concatChunks (pre ++ Node5.bufferChunksH bss half)).size) := by
  unfold Node5.parseBuffersCountH Node5.bufferChunksH
  exact parseChild5BuffersCountH_emit vsize elemSize compressed ver decompress n.children bss hm hwf pre post

def parseChildRootBuffersCountH (half : Bool) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) : List ChildRoot → Nat → Option (List (List (List LeafBuffer)) × Nat)
  | [], off => some ([], off)
  | c :: cs, off =>
    match Node5.parseBuffersCountH half c.node vsize elemSize compressed ver decompress b off with
    | none => none
    | some (bss, o) =>
      match parseChildRootBuffersCountH half vsize elemSize compressed ver decompress b cs o with
      | none => none
      | some (bsss, o') => some (bss :: bsss, o')

theorem parseChildRootBuffersCountH_emit {half : Bool} (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (cs : List ChildRoot) (bsss : List (List (List LeafBuffer)))
    (hm : BufMatchRoot cs bsss)
    (hwf : ∀ bss ∈ bsss, ∀ bs ∈ bss, ∀ b ∈ bs, b.WellFormedCount vsize elemSize compressed ver) :
    ∀ (pre post : List Bytes),
      parseChildRootBuffersCountH half vsize elemSize compressed ver decompress
        (concatChunks (pre ++ RootBuffers.chunksH bsss half ++ post)) cs
        (concatChunks pre).size =
      some (bsss, (concatChunks (pre ++ RootBuffers.chunksH bsss half)).size) := by
  induction cs generalizing bsss with
  | nil =>
    intro pre post
    cases bsss with
    | nil => simp [parseChildRootBuffersCountH, concatChunks, RootBuffers.chunksH]
    | cons bss bsss => simp [BufMatchRoot] at hm
  | cons c cs ih =>
    cases bsss with
    | nil => simp [BufMatchRoot] at hm
    | cons bss bsss =>
      simp only [BufMatchRoot] at hm
      obtain ⟨hm1, hm2⟩ := hm
      intro pre post
      have hbss : ∀ bs ∈ bss, ∀ b ∈ bs, b.WellFormedCount vsize elemSize compressed ver := hwf bss (by simp)
      have hbsss : ∀ bss' ∈ bsss, ∀ bs ∈ bss', ∀ b ∈ bs, b.WellFormedCount vsize elemSize compressed ver :=
        fun bss' hb' => hwf bss' (by simp [hb'])
      rw [show RootBuffers.chunksH (bss :: bsss) half =
          Child5Buffers.chunksH bss half ++ RootBuffers.chunksH bsss half from rfl]
      rw [show pre ++ (Child5Buffers.chunksH bss half ++ RootBuffers.chunksH bsss half) ++ post =
          pre ++ Node5.bufferChunksH bss half ++ (RootBuffers.chunksH bsss half ++ post) from by
        simp [Node5.bufferChunksH]]
      rw [parseChildRootBuffersCountH]
      rw [Node5.parseBuffersCountH_emit c.node bss vsize elemSize compressed ver decompress hm1 hbss pre
        (RootBuffers.chunksH bsss half ++ post)]
      dsimp only
      rw [show concatChunks (pre ++ Node5.bufferChunksH bss half ++ (RootBuffers.chunksH bsss half ++ post)) =
          concatChunks ((pre ++ Node5.bufferChunksH bss half) ++ RootBuffers.chunksH bsss half ++ post) from by simp]
      rw [ih bsss hm2 hbsss (pre ++ Node5.bufferChunksH bss half) post]
      simp [RootBuffers.chunksH, Node5.bufferChunksH, Child5Buffers.chunksH, List.append_assoc]

def RootNode.parseBuffersCountH (half : Bool) (r : RootNode) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) :
    Option (List (List (List LeafBuffer)) × Nat) :=
  parseChildRootBuffersCountH half vsize elemSize compressed ver decompress b r.children off

theorem RootNode.parseBuffersCountH_emit {half : Bool} (r : RootNode) (bsss : List (List (List LeafBuffer)))
    (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (decompress : Bytes → Nat → Option Bytes)
    (hm : BufMatchRoot r.children bsss)
    (hwf : ∀ bss ∈ bsss, ∀ bs ∈ bss, ∀ b ∈ bs, b.WellFormedCount vsize elemSize compressed ver)
    (pre post : List Bytes) :
    RootNode.parseBuffersCountH half r vsize elemSize compressed ver decompress
        (concatChunks (pre ++ r.bufferChunksH bsss half ++ post)) (concatChunks pre).size =
      some (bsss, (concatChunks (pre ++ r.bufferChunksH bsss half)).size) := by
  unfold RootNode.parseBuffersCountH RootNode.bufferChunksH
  exact parseChildRootBuffersCountH_emit vsize elemSize compressed ver decompress r.children bsss hm hwf pre post

def TreeData5.parseFullCountH (half : Bool) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) :
    Option (TreeData5 × List (List (List LeafBuffer)) × Nat) :=
  match TreeData5.parseFromCountH half vsize elemSize compressed ver decompress b off with
  | none => none
  | some (t, o) =>
    match RootNode.parseBuffersCountH half t.root vsize elemSize compressed ver decompress b o with
    | none => none
    | some (bsss, o') => some (t, bsss, o')

theorem TreeData5.parseFullCountH_emit {half : Bool} (t : TreeData5) (bsss : List (List (List LeafBuffer)))
    (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (decompress : Bytes → Nat → Option Bytes)
    (h : t.WellFormedCount vsize elemSize compressed ver)
    (hm : BufMatchRoot t.root.children bsss)
    (hwf : ∀ bss ∈ bsss, ∀ bs ∈ bss, ∀ b ∈ bs, b.WellFormedCount vsize elemSize compressed ver)
    (pre post : List Bytes) :
    TreeData5.parseFullCountH half vsize elemSize compressed ver decompress
        (concatChunks (pre ++ t.fullChunksH half bsss ++ post)) (concatChunks pre).size =
      some (t, bsss, (concatChunks (pre ++ t.fullChunksH half bsss)).size) := by
  unfold TreeData5.parseFullCountH TreeData5.fullChunksH
  rw [show concatChunks (pre ++ (t.chunksH half ++ RootNode.bufferChunksH t.root bsss half) ++ post) =
      concatChunks (pre ++ t.chunksH half ++ (RootNode.bufferChunksH t.root bsss half ++ post)) from by simp]
  rw [TreeData5.parseFromCountH_emit t vsize elemSize compressed ver decompress h pre
    (RootNode.bufferChunksH t.root bsss half ++ post)]
  dsimp only
  rw [show concatChunks (pre ++ t.chunksH half ++ (RootNode.bufferChunksH t.root bsss half ++ post)) =
      concatChunks ((pre ++ t.chunksH half) ++ RootNode.bufferChunksH t.root bsss half ++ post) from by simp]
  rw [RootNode.parseBuffersCountH_emit t.root bsss vsize elemSize compressed ver decompress hm hwf (pre ++ t.chunksH half) post]
  simp [TreeData5.fullChunksH, List.append_assoc]

end Vdb