/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  The tree parsers with the value-chunk size *derived* from the mask and the
  compression code (instead of supplied). `Vdb.ValueCount.storedCount` models
  the C reader's `read_count`; these variants thread it through the node
  cascade, the buffer pass and the grid body, so `GridBody5` can be parsed
  from a real descriptor/header (`elemSize`, the grid's active-mask
  compression flag and the file version are all that is needed) with no
  external `expected`.

  Everything else is identical to `Vdb/TreeNode.lean`, `Vdb/TreeBuffer.lean`
  and `Vdb/GridBody5.lean`; only the record parser and its well-formedness
  condition change.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.ValueCount
import Vdb.TreeNode
import Vdb.TreeBuffer
import Vdb.GridBody5

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace Vdb

def Node4.WellFormedCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (n : Node4) : Prop :=
  n.childMask < nodeSlots 4 ∧ n.valueMask < nodeSlots 4 ∧
  n.children.length = n.childCount ∧
  n.record.WellFormed vsize (storedCount (L := 4) compressed ver n.valueMask n.record.code * elemSize) ∧
  (∀ c ∈ n.children, c.WellFormed)

def Node4.parseFromCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) : Option (Node4 × Nat) :=
  let cm : NodeMask 4 := parseNat b off (nodeMaskBytes 4)
  let vm : NodeMask 4 := parseNat b (off + nodeMaskBytes 4) (nodeMaskBytes 4)
  match ValueRecord.parseFromCount vsize elemSize (storedCount (L := 4) compressed ver vm) decompress b
      (off + nodeMaskBytes 4 + nodeMaskBytes 4) with
  | none => none
  | some (r, o1) =>
    match Child4.parseMany b (setBits cm (nodeSlots 4)).length o1 with
    | none => none
    | some (cs, o2) => some (⟨cm, vm, r, cs⟩, o2)

theorem Node4.parseFromCount_emit (n : Node4) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : n.WellFormedCount vsize elemSize compressed ver) (pre post : List Bytes) :
    Node4.parseFromCount vsize elemSize compressed ver decompress
        (concatChunks (pre ++ n.chunks ++ post)) (concatChunks pre).size =
      some (n, (concatChunks (pre ++ n.chunks)).size) := by
  obtain ⟨hcm, hvm, hcnt, hrec, hch⟩ := h
  rcases n with ⟨cm, vm, r, cs⟩
  simp only [Node4.WellFormedCount] at hcm hvm hcnt hrec hch
  unfold Node4.parseFromCount Node4.chunks Node4.childCount at *
  dsimp only
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
  rw [ValueRecord.parseFromCount_emit r vsize elemSize (storedCount (L := 4) compressed ver vm) decompress hrec
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


def Child5.WellFormedCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (c : Child5) : Prop :=
  c.node.WellFormedCount vsize elemSize compressed ver

def Child5.parseFromCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) : Option (Child5 × Nat) :=
  match Node4.parseFromCount vsize elemSize compressed ver decompress b off with
  | none => none
  | some (n, o) => some (⟨n⟩, o)

theorem Child5.parseFromCount_emit (c : Child5) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : c.WellFormedCount vsize elemSize compressed ver) (pre post : List Bytes) :
    Child5.parseFromCount vsize elemSize compressed ver decompress
        (concatChunks (pre ++ c.chunks ++ post)) (concatChunks pre).size =
      some (c, (concatChunks (pre ++ c.chunks)).size) := by
  rcases c with ⟨n⟩
  simp only [Child5.WellFormedCount] at h
  unfold Child5.parseFromCount Child5.chunks
  rw [Node4.parseFromCount_emit n vsize elemSize compressed ver decompress h pre post]

def Child5.parseManyCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) : Nat → Nat → Option (List Child5 × Nat)
  | 0, off => some ([], off)
  | n + 1, off =>
    match Child5.parseFromCount vsize elemSize compressed ver decompress b off with
    | none => none
    | some (c, o) =>
      match Child5.parseManyCount vsize elemSize compressed ver decompress b n o with
      | none => none
      | some (cs, o') => some (c :: cs, o')

theorem Child5.parseManyCount_emit (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (cs : List Child5) (hwf : ∀ c ∈ cs, c.WellFormedCount vsize elemSize compressed ver) :
    ∀ (pre post : List Bytes),
      Child5.parseManyCount vsize elemSize compressed ver decompress
        (concatChunks (pre ++ cs.flatMap Child5.chunks ++ post)) cs.length (concatChunks pre).size =
      some (cs, (concatChunks (pre ++ cs.flatMap Child5.chunks)).size) := by
  induction cs with
  | nil =>
    intro pre post
    simp [Child5.parseManyCount, concatChunks]
  | cons c cs ih =>
    intro pre post
    have hc := hwf c (by simp)
    have hcs : ∀ x ∈ cs, x.WellFormedCount vsize elemSize compressed ver := fun x hx => hwf x (by simp [hx])
    simp only [List.length_cons, List.flatMap_cons]
    rw [show pre ++ (c.chunks ++ cs.flatMap Child5.chunks) ++ post =
        pre ++ c.chunks ++ (cs.flatMap Child5.chunks ++ post) from by simp]
    rw [Child5.parseManyCount]
    rw [Child5.parseFromCount_emit c vsize elemSize compressed ver decompress hc pre (cs.flatMap Child5.chunks ++ post)]
    dsimp only
    rw [show concatChunks (pre ++ c.chunks ++ (cs.flatMap Child5.chunks ++ post)) =
        concatChunks ((pre ++ c.chunks) ++ cs.flatMap Child5.chunks ++ post) from by simp]
    rw [ih hcs (pre ++ c.chunks) post]
    simp [List.append_assoc]


def Node5.WellFormedCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (n : Node5) : Prop :=
  n.childMask < nodeSlots 5 ∧ n.valueMask < nodeSlots 5 ∧
  n.children.length = n.childCount ∧
  n.record.WellFormed vsize (storedCount (L := 5) compressed ver n.valueMask n.record.code * elemSize) ∧
  (∀ c ∈ n.children, c.WellFormedCount vsize elemSize compressed ver)

def Node5.parseFromCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) : Option (Node5 × Nat) :=
  let cm : NodeMask 5 := parseNat b off (nodeMaskBytes 5)
  let vm : NodeMask 5 := parseNat b (off + nodeMaskBytes 5) (nodeMaskBytes 5)
  match ValueRecord.parseFromCount vsize elemSize (storedCount (L := 5) compressed ver vm) decompress b
      (off + nodeMaskBytes 5 + nodeMaskBytes 5) with
  | none => none
  | some (r, o1) =>
    match Child5.parseManyCount vsize elemSize compressed ver decompress b (setBits cm (nodeSlots 5)).length o1 with
    | none => none
    | some (cs, o2) => some (⟨cm, vm, r, cs⟩, o2)

theorem Node5.parseFromCount_emit (n : Node5) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : n.WellFormedCount vsize elemSize compressed ver) (pre post : List Bytes) :
    Node5.parseFromCount vsize elemSize compressed ver decompress
        (concatChunks (pre ++ n.chunks ++ post)) (concatChunks pre).size =
      some (n, (concatChunks (pre ++ n.chunks)).size) := by
  obtain ⟨hcm, hvm, hcnt, hrec, hch⟩ := h
  rcases n with ⟨cm, vm, r, cs⟩
  simp only [Node5.WellFormedCount] at hcm hvm hcnt hrec hch
  unfold Node5.parseFromCount Node5.chunks Node5.childCount at *
  dsimp only
  rw [show pre ++ ([@NodeMask.serialize 5 cm, @NodeMask.serialize 5 vm] ++ r.chunks ++
      cs.flatMap Child5.chunks) ++ post =
      pre ++ ((@NodeMask.serialize 5 cm) :: ((@NodeMask.serialize 5 vm) ::
        (r.chunks ++ (cs.flatMap Child5.chunks ++ post)))) from by simp]
  -- first mask
  rw [parseNat_chunk_serialize (L := 5) cm hcm pre ((@NodeMask.serialize 5 vm) ::
    (r.chunks ++ (cs.flatMap Child5.chunks ++ post)))]
  have e1 : (concatChunks (pre ++ [@NodeMask.serialize 5 cm])).size =
      (concatChunks pre).size + nodeMaskBytes 5 := by
    rw [concatChunks_append_map]
    simp [@NodeMask.serialize_size 5 cm hcm]
  rw [show (concatChunks pre).size + nodeMaskBytes 5 =
      (concatChunks (pre ++ [@NodeMask.serialize 5 cm])).size from e1.symm]
  rw [peel1 pre (@NodeMask.serialize 5 cm) ((@NodeMask.serialize 5 vm) ::
    (r.chunks ++ (cs.flatMap Child5.chunks ++ post)))]
  -- second mask
  rw [parseNat_chunk_serialize (L := 5) vm hvm (pre ++ [@NodeMask.serialize 5 cm])
    (r.chunks ++ (cs.flatMap Child5.chunks ++ post))]
  have e2 : (concatChunks ((pre ++ [@NodeMask.serialize 5 cm]) ++
      [@NodeMask.serialize 5 vm])).size =
      (concatChunks (pre ++ [@NodeMask.serialize 5 cm])).size + nodeMaskBytes 5 := by
    rw [concatChunks_snoc_size]
    rw [@NodeMask.serialize_size 5 vm hvm]
  rw [show (concatChunks (pre ++ [@NodeMask.serialize 5 cm])).size + nodeMaskBytes 5 =
      (concatChunks ((pre ++ [@NodeMask.serialize 5 cm]) ++
        [@NodeMask.serialize 5 vm])).size from e2.symm]
  rw [peel1 (pre ++ [@NodeMask.serialize 5 cm]) (@NodeMask.serialize 5 vm)
    (r.chunks ++ (cs.flatMap Child5.chunks ++ post))]
  -- value record
  rw [show concatChunks (((pre ++ [@NodeMask.serialize 5 cm]) ++ [@NodeMask.serialize 5 vm]) ++
      (r.chunks ++ (cs.flatMap Child5.chunks ++ post))) =
      concatChunks (((pre ++ [@NodeMask.serialize 5 cm]) ++ [@NodeMask.serialize 5 vm]) ++
        r.chunks ++ (cs.flatMap Child5.chunks ++ post)) from by simp]
  rw [ValueRecord.parseFromCount_emit r vsize elemSize (storedCount (L := 5) compressed ver vm) decompress hrec
    (((pre ++ [@NodeMask.serialize 5 cm]) ++ [@NodeMask.serialize 5 vm])) (cs.flatMap Child5.chunks ++ post)]
  dsimp only
  -- children
  rw [show (concatChunks (((pre ++ [@NodeMask.serialize 5 cm]) ++ [@NodeMask.serialize 5 vm]) ++
      r.chunks)).size = (concatChunks ((((pre ++ [@NodeMask.serialize 5 cm]) ++
      [@NodeMask.serialize 5 vm]) ++ r.chunks))).size from rfl]
  rw [show concatChunks ((((pre ++ [@NodeMask.serialize 5 cm]) ++ [@NodeMask.serialize 5 vm]) ++
      r.chunks) ++ (cs.flatMap Child5.chunks ++ post)) =
      concatChunks ((((pre ++ [@NodeMask.serialize 5 cm]) ++ [@NodeMask.serialize 5 vm]) ++
        r.chunks) ++ cs.flatMap Child5.chunks ++ post) from by simp]
  rw [← hcnt]
  rw [Child5.parseManyCount_emit vsize elemSize compressed ver decompress cs hch (((pre ++ [@NodeMask.serialize 5 cm]) ++
    [@NodeMask.serialize 5 vm]) ++ r.chunks) post]
  simp [Node5.chunks, List.append_assoc]


def ChildRoot.WellFormedCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (c : ChildRoot) : Prop :=
  c.node.WellFormedCount vsize elemSize compressed ver

def ChildRoot.parseFromCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
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
        match Node5.parseFromCount vsize elemSize compressed ver decompress b (off + 12) with
        | none => none
        | some (n, o) => some (⟨ox, oy, oz, n⟩, o)

theorem ChildRoot.parseFromCount_emit (c : ChildRoot) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : c.WellFormedCount vsize elemSize compressed ver) (pre post : List Bytes) :
    ChildRoot.parseFromCount vsize elemSize compressed ver decompress
        (concatChunks (pre ++ c.chunks ++ post)) (concatChunks pre).size =
      some (c, (concatChunks (pre ++ c.chunks)).size) := by
  rcases c with ⟨ox, oy, oz, n⟩
  simp only [ChildRoot.WellFormedCount] at h
  unfold ChildRoot.parseFromCount ChildRoot.chunks
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
  rw [Node5.parseFromCount_emit n vsize elemSize compressed ver decompress h
    (((pre ++ [putI32LE ox ByteArray.empty]) ++ [putI32LE oy ByteArray.empty]) ++
      [putI32LE oz ByteArray.empty]) post]
  simp [ChildRoot.chunks, List.append_assoc]

def ChildRoot.parseManyCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) : Nat → Nat → Option (List ChildRoot × Nat)
  | 0, off => some ([], off)
  | n + 1, off =>
    match ChildRoot.parseFromCount vsize elemSize compressed ver decompress b off with
    | none => none
    | some (c, o) =>
      match ChildRoot.parseManyCount vsize elemSize compressed ver decompress b n o with
      | none => none
      | some (cs, o') => some (c :: cs, o')

theorem ChildRoot.parseManyCount_emit (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (cs : List ChildRoot) (hwf : ∀ c ∈ cs, c.WellFormedCount vsize elemSize compressed ver) :
    ∀ (pre post : List Bytes),
      ChildRoot.parseManyCount vsize elemSize compressed ver decompress
        (concatChunks (pre ++ cs.flatMap ChildRoot.chunks ++ post)) cs.length (concatChunks pre).size =
      some (cs, (concatChunks (pre ++ cs.flatMap ChildRoot.chunks)).size) := by
  induction cs with
  | nil =>
    intro pre post
    simp [ChildRoot.parseManyCount, concatChunks]
  | cons c cs ih =>
    intro pre post
    have hc := hwf c (by simp)
    have hcs : ∀ x ∈ cs, x.WellFormedCount vsize elemSize compressed ver := fun x hx => hwf x (by simp [hx])
    simp only [List.length_cons, List.flatMap_cons]
    rw [show pre ++ (c.chunks ++ cs.flatMap ChildRoot.chunks) ++ post =
        pre ++ c.chunks ++ (cs.flatMap ChildRoot.chunks ++ post) from by simp]
    rw [ChildRoot.parseManyCount]
    rw [ChildRoot.parseFromCount_emit c vsize elemSize compressed ver decompress hc pre (cs.flatMap ChildRoot.chunks ++ post)]
    dsimp only
    rw [show concatChunks (pre ++ c.chunks ++ (cs.flatMap ChildRoot.chunks ++ post)) =
        concatChunks ((pre ++ c.chunks) ++ cs.flatMap ChildRoot.chunks ++ post) from by simp]
    rw [ih hcs (pre ++ c.chunks) post]
    simp [List.append_assoc]


def RootNode.WellFormedCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (r : RootNode) : Prop :=
  r.background.size = vsize ∧
  (∀ t ∈ r.tiles, t.value.size = vsize) ∧
  r.tiles.length < 2 ^ 32 ∧ r.children.length < 2 ^ 32 ∧
  (∀ c ∈ r.children, c.WellFormedCount vsize elemSize compressed ver)

def RootNode.parseFromCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
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
          match ChildRoot.parseManyCount vsize elemSize compressed ver decompress b nc.toNat o1 with
          | none => none
          | some (cs, o2) => some (⟨bg, ts, cs⟩, o2)



theorem RootNode.parseFromCount_emit (r : RootNode) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : r.WellFormedCount vsize elemSize compressed ver) (pre post : List Bytes) :
    RootNode.parseFromCount vsize elemSize compressed ver decompress
        (concatChunks (pre ++ r.chunks ++ post)) (concatChunks pre).size =
      some (r, (concatChunks (pre ++ r.chunks)).size) := by
  obtain ⟨hbg, htv, htl, hcl, hch⟩ := h
  rcases r with ⟨bg, ts, cs⟩
  simp only [RootNode.WellFormedCount] at hbg htv htl hcl hch
  unfold RootNode.parseFromCount RootNode.chunks
  rw [show pre ++ ([bg, putU32LE (UInt32.ofNat ts.length) ByteArray.empty,
      putU32LE (UInt32.ofNat cs.length) ByteArray.empty] ++
      ts.flatMap RootTile.chunks ++ cs.flatMap ChildRoot.chunks) ++ post =
      pre ++ (bg :: (putU32LE (UInt32.ofNat ts.length) ByteArray.empty ::
        (putU32LE (UInt32.ofNat cs.length) ByteArray.empty ::
          (ts.flatMap RootTile.chunks ++ (cs.flatMap ChildRoot.chunks ++ post))))) from by simp]
  -- background
  rw [show vsize = bg.size from hbg.symm]
  rw [getBytes?_chunk pre bg (putU32LE (UInt32.ofNat ts.length) ByteArray.empty ::
    (putU32LE (UInt32.ofNat cs.length) ByteArray.empty ::
      (ts.flatMap RootTile.chunks ++ (cs.flatMap ChildRoot.chunks ++ post))))]
  dsimp only
  have e1 : (concatChunks (pre ++ [bg])).size = (concatChunks pre).size + bg.size := by
    rw [concatChunks_append_map]
    simp
  rw [show (concatChunks pre).size + bg.size =
      (concatChunks (pre ++ [bg])).size from e1.symm]
  rw [peel1 pre bg (putU32LE (UInt32.ofNat ts.length) ByteArray.empty ::
    (putU32LE (UInt32.ofNat cs.length) ByteArray.empty ::
      (ts.flatMap RootTile.chunks ++ (cs.flatMap ChildRoot.chunks ++ post))))]
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
      (ts.flatMap RootTile.chunks ++ (cs.flatMap ChildRoot.chunks ++ post)))]
  -- child count
  rw [getU32LE_chunk]
  dsimp only
  rw [peel1 ((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty])
    (putU32LE (UInt32.ofNat cs.length) ByteArray.empty)
    (ts.flatMap RootTile.chunks ++ (cs.flatMap ChildRoot.chunks ++ post))]
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
        (ts.flatMap RootTile.chunks ++ (cs.flatMap ChildRoot.chunks ++ post))) =
      concatChunks (((((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty]) ++
        [putU32LE (UInt32.ofNat cs.length) ByteArray.empty]) ++ ts.flatMap RootTile.chunks) ++
        (cs.flatMap ChildRoot.chunks ++ post)) from by simp]
  have htv' : ∀ t ∈ ts, t.value.size = bg.size := by
    intro t ht
    rw [htv t ht, hbg]
  rw [parseTiles_emit (bg.size) ts htv'
    (((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty]) ++
      [putU32LE (UInt32.ofNat cs.length) ByteArray.empty]) (cs.flatMap ChildRoot.chunks ++ post)]
  dsimp only
  -- children
  have hch' : ∀ c ∈ cs, c.WellFormedCount bg.size elemSize compressed ver := by
    intro c hc
    rw [show bg.size = vsize from hbg]
    exact hch c hc
  rw [show concatChunks (((((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty]) ++
        [putU32LE (UInt32.ofNat cs.length) ByteArray.empty]) ++ ts.flatMap RootTile.chunks) ++
        (cs.flatMap ChildRoot.chunks ++ post)) =
      concatChunks ((((((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty]) ++
        [putU32LE (UInt32.ofNat cs.length) ByteArray.empty]) ++ ts.flatMap RootTile.chunks) ++
        cs.flatMap ChildRoot.chunks) ++ post) from by simp]
  rw [ChildRoot.parseManyCount_emit (bg.size) elemSize compressed ver decompress cs hch'
    ((((pre ++ [bg]) ++ [putU32LE (UInt32.ofNat ts.length) ByteArray.empty]) ++
      [putU32LE (UInt32.ofNat cs.length) ByteArray.empty]) ++ ts.flatMap RootTile.chunks) post]
  simp [RootNode.chunks, List.append_assoc]


def TreeData5.WellFormedCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (t : TreeData5) : Prop :=
  t.root.WellFormedCount vsize elemSize compressed ver

def TreeData5.parseFromCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) : Option (TreeData5 × Nat) :=
  match getI32LE b off with
  | none => none
  | some n =>
    if n = 1 then
      match RootNode.parseFromCount vsize elemSize compressed ver decompress b (off + 4) with
      | none => none
      | some (r, o) => some (⟨r⟩, o)
    else none

theorem TreeData5.parseFromCount_emit (t : TreeData5) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : t.WellFormedCount vsize elemSize compressed ver) (pre post : List Bytes) :
    TreeData5.parseFromCount vsize elemSize compressed ver decompress
        (concatChunks (pre ++ t.chunks ++ post)) (concatChunks pre).size =
      some (t, (concatChunks (pre ++ t.chunks)).size) := by
  rcases t with ⟨r⟩
  simp only [TreeData5.WellFormedCount] at h
  unfold TreeData5.parseFromCount TreeData5.chunks
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
  rw [RootNode.parseFromCount_emit r vsize elemSize compressed ver decompress h
    (pre ++ [putI32LE (1 : Int32) ByteArray.empty]) post]
  simp [TreeData5.chunks, List.append_assoc]


def LeafBuffer.WellFormedCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (b : LeafBuffer) : Prop :=
  b.valueMask < nodeSlots 3 ∧
  b.record.WellFormed vsize (storedCount (L := 3) compressed ver b.valueMask b.record.code * elemSize)

def LeafBuffer.parseFromCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) : Option (LeafBuffer × Nat) :=
  let vm : NodeMask 3 := parseNat b off (nodeMaskBytes 3)
  match ValueRecord.parseFromCount vsize elemSize (storedCount (L := 3) compressed ver vm) decompress b (off + nodeMaskBytes 3) with
  | none => none
  | some (r, o) => some (⟨vm, r⟩, o)

theorem LeafBuffer.parseFromCount_emit (b : LeafBuffer) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (h : b.WellFormedCount vsize elemSize compressed ver) (pre post : List Bytes) :
    LeafBuffer.parseFromCount vsize elemSize compressed ver decompress
        (concatChunks (pre ++ b.chunks ++ post)) (concatChunks pre).size =
      some (b, (concatChunks (pre ++ b.chunks)).size) := by
  obtain ⟨hvm, hrec⟩ := h
  rcases b with ⟨vm, r⟩
  simp only [LeafBuffer.WellFormedCount] at hvm hrec
  unfold LeafBuffer.parseFromCount LeafBuffer.chunks
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
  rw [ValueRecord.parseFromCount_emit r vsize elemSize (storedCount (L := 3) compressed ver vm) decompress hrec
    (pre ++ [@NodeMask.serialize 3 vm]) post]
  simp [LeafBuffer.chunks, List.append_assoc]

def parseLeafBuffersCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) : Nat → Nat → Option (List LeafBuffer × Nat)
  | 0, off => some ([], off)
  | n + 1, off =>
    match LeafBuffer.parseFromCount vsize elemSize compressed ver decompress b off with
    | none => none
    | some (lb, o) =>
      match parseLeafBuffersCount vsize elemSize compressed ver decompress b n o with
      | none => none
      | some (lbs, o') => some (lb :: lbs, o')

theorem parseLeafBuffersCount_emit (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (lbs : List LeafBuffer) (hwf : ∀ b ∈ lbs, b.WellFormedCount vsize elemSize compressed ver) :
    ∀ (pre post : List Bytes),
      parseLeafBuffersCount vsize elemSize compressed ver decompress
        (concatChunks (pre ++ lbs.flatMap LeafBuffer.chunks ++ post)) lbs.length
        (concatChunks pre).size =
      some (lbs, (concatChunks (pre ++ lbs.flatMap LeafBuffer.chunks)).size) := by
  induction lbs with
  | nil =>
    intro pre post
    simp [parseLeafBuffersCount, concatChunks]
  | cons lb lbs ih =>
    intro pre post
    have hlb := hwf lb (by simp)
    have hlbs : ∀ b ∈ lbs, b.WellFormedCount vsize elemSize compressed ver := fun b hb => hwf b (by simp [hb])
    simp only [List.length_cons, List.flatMap_cons]
    rw [show pre ++ (lb.chunks ++ lbs.flatMap LeafBuffer.chunks) ++ post =
        pre ++ lb.chunks ++ (lbs.flatMap LeafBuffer.chunks ++ post) from by simp]
    rw [parseLeafBuffersCount]
    rw [LeafBuffer.parseFromCount_emit lb vsize elemSize compressed ver decompress hlb pre
      (lbs.flatMap LeafBuffer.chunks ++ post)]
    dsimp only
    rw [show concatChunks (pre ++ lb.chunks ++ (lbs.flatMap LeafBuffer.chunks ++ post)) =
        concatChunks ((pre ++ lb.chunks) ++ lbs.flatMap LeafBuffer.chunks ++ post) from by simp]
    rw [ih hlbs (pre ++ lb.chunks) post]
    simp [List.append_assoc]

def Node4.parseBuffersCount (n : Node4) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) :
    Option (List LeafBuffer × Nat) :=
  parseLeafBuffersCount vsize elemSize compressed ver decompress b n.children.length off

theorem Node4.parseBuffersCount_emit (n : Node4) (bs : List LeafBuffer)
    (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (decompress : Bytes → Nat → Option Bytes)
    (hlen : bs.length = n.children.length)
    (hwf : ∀ b ∈ bs, b.WellFormedCount vsize elemSize compressed ver) (pre post : List Bytes) :
    Node4.parseBuffersCount n vsize elemSize compressed ver decompress
        (concatChunks (pre ++ Node4.bufferChunks bs ++ post)) (concatChunks pre).size =
      some (bs, (concatChunks (pre ++ Node4.bufferChunks bs)).size) := by
  unfold Node4.parseBuffersCount Node4.bufferChunks
  rw [← hlen]
  exact parseLeafBuffersCount_emit vsize elemSize compressed ver decompress bs hwf pre post

def parseChild5BuffersCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) : List Child5 → Nat → Option (List (List LeafBuffer) × Nat)
  | [], off => some ([], off)
  | c :: cs, off =>
    match Node4.parseBuffersCount c.node vsize elemSize compressed ver decompress b off with
    | none => none
    | some (lbs, o) =>
      match parseChild5BuffersCount vsize elemSize compressed ver decompress b cs o with
      | none => none
      | some (bss, o') => some (lbs :: bss, o')

theorem parseChild5BuffersCount_emit (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (cs : List Child5) (bss : List (List LeafBuffer))
    (hm : BufMatch cs bss)
    (hwf : ∀ bs ∈ bss, ∀ b ∈ bs, b.WellFormedCount vsize elemSize compressed ver) :
    ∀ (pre post : List Bytes),
      parseChild5BuffersCount vsize elemSize compressed ver decompress
        (concatChunks (pre ++ Child5Buffers.chunks bss ++ post)) cs
        (concatChunks pre).size =
      some (bss, (concatChunks (pre ++ Child5Buffers.chunks bss)).size) := by
  induction cs generalizing bss with
  | nil =>
    intro pre post
    cases bss with
    | nil => simp [parseChild5BuffersCount, concatChunks, Child5Buffers.chunks]
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
      rw [show Child5Buffers.chunks (bs :: bss) =
          bs.flatMap LeafBuffer.chunks ++ Child5Buffers.chunks bss from rfl]
      rw [show pre ++ (bs.flatMap LeafBuffer.chunks ++ Child5Buffers.chunks bss) ++ post =
          pre ++ Node4.bufferChunks bs ++ (Child5Buffers.chunks bss ++ post) from by
        simp [Node4.bufferChunks]]
      rw [parseChild5BuffersCount]
      rw [Node4.parseBuffersCount_emit c.node bs vsize elemSize compressed ver decompress hlen hbs pre
        (Child5Buffers.chunks bss ++ post)]
      dsimp only
      rw [show concatChunks (pre ++ Node4.bufferChunks bs ++ (Child5Buffers.chunks bss ++ post)) =
          concatChunks ((pre ++ Node4.bufferChunks bs) ++ Child5Buffers.chunks bss ++ post) from by simp]
      rw [ih bss hm' hbss (pre ++ Node4.bufferChunks bs) post]
      simp [Child5Buffers.chunks, Node4.bufferChunks, List.append_assoc]

def Node5.parseBuffersCount (n : Node5) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) :
    Option (List (List LeafBuffer) × Nat) :=
  parseChild5BuffersCount vsize elemSize compressed ver decompress b n.children off

theorem Node5.parseBuffersCount_emit (n : Node5) (bss : List (List LeafBuffer))
    (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (decompress : Bytes → Nat → Option Bytes)
    (hm : BufMatch n.children bss)
    (hwf : ∀ bs ∈ bss, ∀ b ∈ bs, b.WellFormedCount vsize elemSize compressed ver)
    (pre post : List Bytes) :
    Node5.parseBuffersCount n vsize elemSize compressed ver decompress
        (concatChunks (pre ++ Node5.bufferChunks bss ++ post)) (concatChunks pre).size =
      some (bss, (concatChunks (pre ++ Node5.bufferChunks bss)).size) := by
  unfold Node5.parseBuffersCount Node5.bufferChunks
  exact parseChild5BuffersCount_emit vsize elemSize compressed ver decompress n.children bss hm hwf pre post

def parseChildRootBuffersCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) : List ChildRoot → Nat → Option (List (List (List LeafBuffer)) × Nat)
  | [], off => some ([], off)
  | c :: cs, off =>
    match Node5.parseBuffersCount c.node vsize elemSize compressed ver decompress b off with
    | none => none
    | some (bss, o) =>
      match parseChildRootBuffersCount vsize elemSize compressed ver decompress b cs o with
      | none => none
      | some (bsss, o') => some (bss :: bsss, o')

theorem parseChildRootBuffersCount_emit (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (cs : List ChildRoot) (bsss : List (List (List LeafBuffer)))
    (hm : BufMatchRoot cs bsss)
    (hwf : ∀ bss ∈ bsss, ∀ bs ∈ bss, ∀ b ∈ bs, b.WellFormedCount vsize elemSize compressed ver) :
    ∀ (pre post : List Bytes),
      parseChildRootBuffersCount vsize elemSize compressed ver decompress
        (concatChunks (pre ++ RootBuffers.chunks bsss ++ post)) cs
        (concatChunks pre).size =
      some (bsss, (concatChunks (pre ++ RootBuffers.chunks bsss)).size) := by
  induction cs generalizing bsss with
  | nil =>
    intro pre post
    cases bsss with
    | nil => simp [parseChildRootBuffersCount, concatChunks, RootBuffers.chunks]
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
      rw [show RootBuffers.chunks (bss :: bsss) =
          Child5Buffers.chunks bss ++ RootBuffers.chunks bsss from rfl]
      rw [show pre ++ (Child5Buffers.chunks bss ++ RootBuffers.chunks bsss) ++ post =
          pre ++ Node5.bufferChunks bss ++ (RootBuffers.chunks bsss ++ post) from by
        simp [Node5.bufferChunks]]
      rw [parseChildRootBuffersCount]
      rw [Node5.parseBuffersCount_emit c.node bss vsize elemSize compressed ver decompress hm1 hbss pre
        (RootBuffers.chunks bsss ++ post)]
      dsimp only
      rw [show concatChunks (pre ++ Node5.bufferChunks bss ++ (RootBuffers.chunks bsss ++ post)) =
          concatChunks ((pre ++ Node5.bufferChunks bss) ++ RootBuffers.chunks bsss ++ post) from by simp]
      rw [ih bsss hm2 hbsss (pre ++ Node5.bufferChunks bss) post]
      simp [RootBuffers.chunks, Node5.bufferChunks, Child5Buffers.chunks, List.append_assoc]

def RootNode.parseBuffersCount (r : RootNode) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) :
    Option (List (List (List LeafBuffer)) × Nat) :=
  parseChildRootBuffersCount vsize elemSize compressed ver decompress b r.children off

theorem RootNode.parseBuffersCount_emit (r : RootNode) (bsss : List (List (List LeafBuffer)))
    (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (decompress : Bytes → Nat → Option Bytes)
    (hm : BufMatchRoot r.children bsss)
    (hwf : ∀ bss ∈ bsss, ∀ bs ∈ bss, ∀ b ∈ bs, b.WellFormedCount vsize elemSize compressed ver)
    (pre post : List Bytes) :
    RootNode.parseBuffersCount r vsize elemSize compressed ver decompress
        (concatChunks (pre ++ r.bufferChunks bsss ++ post)) (concatChunks pre).size =
      some (bsss, (concatChunks (pre ++ r.bufferChunks bsss)).size) := by
  unfold RootNode.parseBuffersCount RootNode.bufferChunks
  exact parseChildRootBuffersCount_emit vsize elemSize compressed ver decompress r.children bsss hm hwf pre post

def TreeData5.parseFullCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) :
    Option (TreeData5 × List (List (List LeafBuffer)) × Nat) :=
  match TreeData5.parseFromCount vsize elemSize compressed ver decompress b off with
  | none => none
  | some (t, o) =>
    match RootNode.parseBuffersCount t.root vsize elemSize compressed ver decompress b o with
    | none => none
    | some (bsss, o') => some (t, bsss, o')

theorem TreeData5.parseFullCount_emit (t : TreeData5) (bsss : List (List (List LeafBuffer)))
    (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (decompress : Bytes → Nat → Option Bytes)
    (h : t.WellFormedCount vsize elemSize compressed ver)
    (hm : BufMatchRoot t.root.children bsss)
    (hwf : ∀ bss ∈ bsss, ∀ bs ∈ bss, ∀ b ∈ bs, b.WellFormedCount vsize elemSize compressed ver)
    (pre post : List Bytes) :
    TreeData5.parseFullCount vsize elemSize compressed ver decompress
        (concatChunks (pre ++ t.fullChunks bsss ++ post)) (concatChunks pre).size =
      some (t, bsss, (concatChunks (pre ++ t.fullChunks bsss)).size) := by
  unfold TreeData5.parseFullCount TreeData5.fullChunks
  rw [show concatChunks (pre ++ (t.chunks ++ RootNode.bufferChunks t.root bsss) ++ post) =
      concatChunks (pre ++ t.chunks ++ (RootNode.bufferChunks t.root bsss ++ post)) from by simp]
  rw [TreeData5.parseFromCount_emit t vsize elemSize compressed ver decompress h pre
    (RootNode.bufferChunks t.root bsss ++ post)]
  dsimp only
  rw [show concatChunks (pre ++ t.chunks ++ (RootNode.bufferChunks t.root bsss ++ post)) =
      concatChunks ((pre ++ t.chunks) ++ RootNode.bufferChunks t.root bsss ++ post) from by simp]
  rw [RootNode.parseBuffersCount_emit t.root bsss vsize elemSize compressed ver decompress hm hwf (pre ++ t.chunks) post]
  simp [TreeData5.fullChunks, List.append_assoc]


def GridBody5.CanonicalCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (g : GridBody5) : Prop :=
  g.header.Canonical ∧ g.tree.WellFormedCount vsize elemSize compressed ver ∧
  BufMatchRoot g.tree.root.children g.buffers ∧
  (∀ bss ∈ g.buffers, ∀ bs ∈ bss, ∀ b ∈ bs, b.WellFormedCount vsize elemSize compressed ver)

def GridBody5.parseFromCount (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes) (b : Bytes) (off : Nat) : Option (GridBody5 × Nat) :=
  match GridHeader.parseFrom b off with
  | none => none
  | some (h, o1) =>
    match TreeData5.parseFullCount vsize elemSize compressed ver decompress b o1 with
    | none => none
    | some (t, bss, o2) => some (⟨h, t, bss⟩, o2)

theorem GridBody5.parseFromCount_emit (g : GridBody5) (vsize elemSize : Nat) (compressed : Bool) (ver : Nat)
    (decompress : Bytes → Nat → Option Bytes)
    (hc : g.CanonicalCount vsize elemSize compressed ver) (pre post : List Bytes) :
    GridBody5.parseFromCount vsize elemSize compressed ver decompress
        (concatChunks (pre ++ g.chunks ++ post)) (concatChunks pre).size =
      some (g, (concatChunks (pre ++ g.chunks)).size) := by
  obtain ⟨hh, ht, hm, hwf⟩ := hc
  rcases g with ⟨h, t, bss⟩
  unfold GridBody5.parseFromCount GridBody5.chunks
  rw [show pre ++ (h.chunks ++ t.fullChunks bss) ++ post =
      pre ++ h.chunks ++ (t.fullChunks bss ++ post) from by simp]
  rw [GridHeader.parseFromChunks_exact h hh pre (t.fullChunks bss ++ post)]
  dsimp only
  rw [show concatChunks (pre ++ h.chunks ++ (t.fullChunks bss ++ post)) =
      concatChunks ((pre ++ h.chunks) ++ t.fullChunks bss ++ post) from by simp]
  rw [TreeData5.parseFullCount_emit t bss vsize elemSize compressed ver decompress ht hm hwf (pre ++ h.chunks) post]
  simp [GridBody5.chunks, List.append_assoc]

end Vdb
