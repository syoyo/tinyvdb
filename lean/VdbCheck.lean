/-
  TinyVDB - `vdbcheck`: parse a `.vdb` file with the Lean model and print the
  file header, file metadata names, grid descriptors, and (for the standard
  non-half `5_4_3` layout) the structured tree counts.

  This is the Lean half of the model-versus-C differential harness: the C
  `vdb_dump_prologue` tool prints the same fields from the C reader, and a
  script compares the two outputs.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import VdbSpec

open Vdb

/-- C-reader style name for a transform kind. -/
def transformKindName : TransformKind → String
  | .uniformScale => "UniformScaleMap"
  | .scale => "ScaleMap"
  | .uniformScaleTranslate => "UniformScaleTranslateMap"
  | .scaleTranslate => "ScaleTranslateMap"
  | .translation => "TranslationMap"
  | .affine => "AffineMap"

/-- Printable form of a wire string (names are ASCII in practice). -/
def byteString (b : Bytes) : String :=
  String.fromUTF8? b |>.getD s!"<{b.size} bytes>"


/-- Strip a literal suffix (UTF-8 suffix handling is unnecessary: all type
    suffixes are ASCII). -/
def trimSuffix (s suf : String) : Option String :=
  if s.endsWith suf then some ((s.take (s.length - suf.length)).toString) else none

/-- Value type and half flag of a `Tree_...` grid type with the standard
    `5_4_3` layout (the layout the structured tree model covers). -/
def gridTypeOfWire (s0 : String) : Option (ValueType × Bool) := do
  let (s, half) ←
    match trimSuffix s0 "_HalfFloat" with
    | some s => some (s, true)
    | none => some (s0, false)
  let gt ← Vdb.parseGridType s
  if gt.layout.levels == [0, 5, 4, 3] then pure (gt.valueType, half) else none

/-- Node counts of a structured tree. -/
structure TreeStats where
  internal : Nat
  leaves : Nat
  active : Nat

def TreeStats.zero : TreeStats := ⟨0, 0, 0⟩

def TreeStats.add (a b : TreeStats) : TreeStats :=
  ⟨a.internal + b.internal, a.leaves + b.leaves, a.active + b.active⟩

def leafStats (l : LeafNode) : TreeStats :=
  ⟨0, 1, (setBits l.valueMask (nodeSlots 3)).length⟩

def node4Stats (n : Node4) : TreeStats :=
  n.children.foldl (fun acc c => acc.add (leafStats c.leaf)) TreeStats.zero

def node5Stats (n : Node5) : TreeStats :=
  let s := n.children.foldl (fun acc c => acc.add (node4Stats c.node)) TreeStats.zero
  { s with internal := s.internal + 1 + n.children.length }

def treeStats (t : TreeData5) : TreeStats :=
  t.root.children.foldl (fun acc c => acc.add (node5Stats c.node)) TreeStats.zero

/-- Codec stub for the structural pass: the tree layout (masks, chunk framing
    and the buffer order) does not depend on the decoded bytes. -/
def skipDecompress : Bytes → Nat → Option Bytes := fun _ _ => some ByteArray.empty

/-- Print the structured tree pass, when the grid type is covered. -/
def printTree (b : Bytes) (ver : UInt32) (gd : GridDescriptor) :
    IO Unit := do
  let ty := byteString gd.gridType
  match gridTypeOfWire ty with
  | none => IO.println "  tree unsupported"
  | some (vt, half) =>
    match GridHeader.parseFrom b gd.gridOffset.toNat with
    | none => IO.println "  tree invalid header"
    | some (h, ho) =>
      let compressed := (h.compressionFlags &&& 2) != 0
      match TreeData5.parseFullCount vt.size (vt.fileElemSize half) compressed ver.toNat
          skipDecompress b ho with
      | none => IO.println s!"  tree invalid (vsize={vt.size} elem={vt.fileElemSize half})"
      | some (t, _, endOff) =>
        let s := treeStats t
        IO.println s!"  tree tiles={t.root.tiles.length} children={t.root.children.length}"
        IO.println s!"  tree nodes internal={s.internal} leaf={s.leaves} active={s.active}"
        IO.println s!"  tree end={endOff} expected={gd.endOffset.toNat} \
          ok={endOff == gd.endOffset.toNat}"

def main (args : List String) : IO UInt32 := do
  let path := args.headD "sphere.vdb"
  let data ← IO.FS.readBinFile path
  let b : Bytes := data
  match FilePrefix.parseFrom b 0 with
  | none =>
    IO.println s!"vdbcheck: {path}: invalid file prefix"
    return 1
  | some (fp, off) =>
    IO.println s!"header version={fp.header.fileVersion} major={fp.header.majorVersion} \
      minor={fp.header.minorVersion} legacy={fp.header.legacyCompressed} \
      uuid={byteString fp.header.uuid}"
    IO.println s!"file-metadata {fp.fileMetadata.entries.length}"
    for e in fp.fileMetadata.entries do
      IO.println s!"  meta {byteString e.name} {byteString e.typeName}"
    IO.println s!"grids {fp.gridCount}"
    let mut o := off
    for i in List.range fp.gridCount do
      match GridDescriptor.parseFrom fp.header.fileVersion b o with
      | none =>
        IO.println s!"grid {i}: invalid descriptor"
        return 1
      | some (gd, _) =>
        IO.println s!"grid {i} {byteString gd.uniqueName} {byteString gd.gridType} \
          instance={byteString gd.instanceParent} \
          offsets={gd.gridOffset} {gd.blockOffset} {gd.endOffset}"
        match GridBody.parseFrom b gd.gridOffset.toNat gd.endOffset.toNat with
        | none => IO.println s!"  body {i}: invalid"
        | some (gb, _) =>
          IO.println s!"  body {i} compression={gb.header.compressionFlags} \
            transform={transformKindName gb.header.transform.kind} \
            metadata={gb.header.metadata.entries.length} treebase={gb.bufferCount}"
        printTree b fp.header.fileVersion gd
        o := gd.endOffset.toNat
    match VdbFile.parseFrom b 0 with
    | none => IO.println "file: invalid grid sequence"
    | some (vf, fin) =>
      IO.println s!"file grids={vf.grids.length} end={fin} size={b.size} \
        complete={fin == b.size}"
    return 0
