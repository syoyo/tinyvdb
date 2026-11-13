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

/-- Skip an *uncompressed* record payload: the extras (flag, inactive values,
    selection mask) followed by `expected` raw bytes with no chunk header
    (`read_and_decompress`'s no-compression branch). The extras parser is the
    proven `ValueRecord.parseNoChunk`. -/
def skipRawRecord (L : Nat) (vsize expected : Nat) (b : Bytes) (off : Nat) : Option Nat := do
  let (_, o1) ← ValueRecord.parseNoChunk (L := L) vsize b off
  let _ ← getBytes? b o1 expected
  pure (o1 + expected)

/-- The per-node compression code byte. -/
def codeAt (b : Bytes) (off : Nat) : MaskCode :=
  (MaskCode.ofNat? (readByteOrZero b off 0)).getD .noMaskAndAllVals

/-- `log2dim` of the tree level (0 is the root). -/
def log2dimOfLevel : Nat → Nat
  | 1 => 5
  | 2 => 4
  | _ => 3

/- Half-grid structural pass (F6). The `read_count == 0` nodes of a half grid
    carry no chunk header, which the proven tree cascade does not branch on
    yet; this walk mirrors the layout but delegates every value record to the
    proven `ValueRecord.parseFromCountM`. Returns the node counts, the leaf
    value masks in depth-first order, and the end offset. -/
mutual
partial def halfTopo (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (framed : Bool)
    (b : Bytes) (level : Nat) (off : Nat) :
    Option (TreeStats × List Nat × Nat) := do
  let L := log2dimOfLevel level
  let mb := nodeMaskBytes L
  let cm := parseNat b off mb
  if level = 3 then
    pure (⟨0, 1, (setBits cm (nodeSlots 3)).length⟩, [cm], off + mb)
  else
    let vm := parseNat b (off + mb) mb
    let countOf := fun code => storedCount (L := L) compressed ver vm code
    let o1 ←
      if framed then do
        let (_, o) ← ValueRecord.parseFromCountM (L := L) vsize elemSize countOf
          skipDecompress b (off + mb + mb) (half := true)
        pure o
      else
        skipRawRecord L vsize (countOf (codeAt b (off + mb + mb)) * elemSize)
          b (off + mb + mb)
    let nc := (setBits cm (nodeSlots L)).length
    let (s, ms, o2) ← halfChildren vsize elemSize compressed ver framed b (level + 1) nc o1
    pure ({ s with internal := s.internal + 1 }, ms, o2)

partial def halfChildren (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (framed : Bool)
    (b : Bytes) (level : Nat) : Nat → Nat → Option (TreeStats × List Nat × Nat)
  | 0, off => some (TreeStats.zero, [], off)
  | k + 1, off => do
    let (s, ms, o1) ← halfTopo vsize elemSize compressed ver framed b level off
    let (s', ms', o2) ← halfChildren vsize elemSize compressed ver framed b level k o1
    pure (s.add s', ms ++ ms', o2)
end

/-- The root's children carry explicit `i32 x3` origins. -/
partial def halfRoots (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (framed : Bool)
    (b : Bytes) : Nat → Nat → Option (TreeStats × List Nat × Nat)
  | 0, off => some (TreeStats.zero, [], off)
  | k + 1, off => do
    let (s, ms, o1) ← halfTopo vsize elemSize compressed ver framed b 1 (off + 12)
    let (s', ms', o2) ← halfRoots vsize elemSize compressed ver framed b k o1
    pure (s.add s', ms ++ ms', o2)

/-- Consume the leaf buffers: value mask, then the (possibly chunk-less)
    mask-compression record. -/
def halfBuffers (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (framed : Bool)
    (b : Bytes) (masks : List Nat) (off : Nat) : Option Nat :=
  match masks with
  | [] => some off
  | vm :: rest => do
    let countOf := fun code => storedCount (L := 3) compressed ver vm code
    let o1 ←
      if framed then do
        let (_, o) ← ValueRecord.parseFromCountM (L := 3) vsize elemSize countOf
          skipDecompress b (off + nodeMaskBytes 3) (half := true)
        pure o
      else
        skipRawRecord 3 vsize
          (countOf (codeAt b (off + nodeMaskBytes 3)) * elemSize)
          b (off + nodeMaskBytes 3)
    halfBuffers vsize elemSize compressed ver framed b rest o1

/-- Parse the half-grid tree and check it ends at `endOff`. -/
def halfParse (vsize elemSize : Nat) (compressed : Bool) (ver : Nat) (framed : Bool)
    (b : Bytes) (ho endOff : Nat) : Option (TreeStats × Bool) := do
  let _bc ← getI32LE b ho
  let bgOff := ho + 4
  let nt ← getU32LE b (bgOff + vsize)
  let nc ← getU32LE b (bgOff + vsize + 4)
  let o := bgOff + vsize + 8 + nt.toNat * (12 + vsize + 1)
  let (s, ms, oTop) ← halfRoots vsize elemSize compressed ver framed b nc.toNat o
  let oEnd ← halfBuffers vsize elemSize compressed ver framed b ms oTop
  pure (s, oEnd == endOff)

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
        if framed then
          -- F6: the proven half-aware count cascade (BLOSC/ZIP framing).
          match TreeData5.parseFullCountH true vsize elemSize compressed ver.toNat
              skipDecompress b ho with
          | none => IO.println s!"  tree invalid (half cascade, vsize={vsize} elem={elemSize})"
          | some (t, _, endOff) =>
            let s := treeStats t
            IO.println s!"  tree mode=proven-half"
            IO.println s!"  tree tiles={t.root.tiles.length} children={t.root.children.length}"
            IO.println s!"  tree nodes internal={s.internal} leaf={s.leaves} active={s.active}"
            IO.println s!"  tree end={endOff} expected={gd.endOffset.toNat} \
              ok={endOff == gd.endOffset.toNat}"
        else
          -- F14: grids without BLOSC/ZIP store raw payloads (no size word), which
          -- the proven cascade does not model yet; walk the layout instead.
          match halfParse vsize elemSize compressed ver.toNat framed b ho gd.endOffset.toNat with
          | none => IO.println s!"  tree invalid (half walk, vsize={vsize} elem={elemSize})"
          | some (s, ok) =>
            IO.println s!"  tree tiles={treeTiles b ho vsize} children={treeChildren b ho vsize}"
            IO.println s!"  tree nodes internal={s.internal} leaf={s.leaves} active={s.active}"
            IO.println s!"  tree end-ok={ok}"
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
