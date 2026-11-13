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

/-- Does the wire grid type contain a literal substring? -/
def containsSub (s sub : String) : Bool :=
  let subL := sub.toList
  let rec go : List Char → Bool
    | [] => subL.isEmpty
    | c :: cs => subL.isPrefixOf (c :: cs) || go cs
  go s.toList

/-- Strip a literal UTF-8/ASCII suffix. -/
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

/-- `log2dim` of the tree level (0 is the root). -/
def log2dimOfLevel : Nat → Nat
  | 1 => 5
  | 2 => 4
  | _ => 3

/-- Root tile count, for the half-grid printout. -/
def treeTiles (b : Bytes) (ho vsize : Nat) : Nat :=
  match getU32LE b (ho + 4 + vsize) with
  | some n => n.toNat
  | none => 0

/-- Root child count, for the half-grid printout. -/
def treeChildren (b : Bytes) (ho vsize : Nat) : Nat :=
  match getU32LE b (ho + 4 + vsize + 4) with
  | some n => n.toNat
  | none => 0

/-- Print the structured tree pass, when the grid type is covered. -/
def printTree (b : Bytes) (ver : UInt32) (gd : GridDescriptor) : IO Unit := do
  let ty := byteString gd.gridType
  match gridTypeOfWire ty with
  | none => IO.println "  tree unsupported"
  | some (vt, half) =>
    match GridHeader.parseFrom b gd.gridOffset.toNat with
    | none => IO.println "  tree invalid header"
    | some (h, ho) =>
      let compressed := (h.compressionFlags &&& 2) != 0
      let vsize := vt.size
      let elemSize := vt.fileElemSize half
      if containsSub ty "ptdataidx" then
        -- PointDataGrid: the C reader parses topology only, then jumps to the
        -- grid's end marker (leaf buffers are AttributeSet blobs).
        match TreeData5.parseFromCount vsize elemSize compressed ver.toNat
            skipDecompress b ho with
        | none => IO.println s!"  tree invalid (point-data topology, vsize={vsize} elem={elemSize})"
        | some (t, topEnd) =>
          let s := treeStats t
          IO.println s!"  tree tiles={t.root.tiles.length} children={t.root.children.length}"
          IO.println s!"  tree nodes internal={s.internal} leaf={s.leaves} active={s.active}"
          IO.println s!"  tree end-ok={decide (topEnd <= gd.endOffset.toNat)}"
      else if half then
        let framed := (h.compressionFlags &&& 5) != 0
        -- F6/F14: the proven half-aware count cascade, in the grid's framing
        -- mode (BLOSC/ZIP chunks vs raw payloads).
        match TreeData5.parseFullCountH true framed vsize elemSize compressed ver.toNat
            skipDecompress b ho with
        | none => IO.println s!"  tree invalid (half cascade, vsize={vsize} elem={elemSize})"
        | some (t, _, endOff) =>
          let s := treeStats t
          IO.println s!"  tree mode=proven-half framed={framed}"
          IO.println s!"  tree tiles={t.root.tiles.length} children={t.root.children.length}"
          IO.println s!"  tree nodes internal={s.internal} leaf={s.leaves} active={s.active}"
          IO.println s!"  tree end={endOff} expected={gd.endOffset.toNat} \
            ok={endOff == gd.endOffset.toNat}"
      else
        match TreeData5.parseFullCount vsize elemSize compressed ver.toNat
            skipDecompress b ho with
        | none => IO.println s!"  tree invalid (vsize={vsize} elem={elemSize})"
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
