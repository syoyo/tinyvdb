import VdbSpec
import Vdb.Half
import Vdb.TreeHalf

/-! Seeded generator for well-formed `.vdb` files (the generator half of the
oracle harness).

Usage: `vdbgen <out.vdb> <seed> <kind> [<kind> ...]`

Kinds: `empty`, `tiles`, `sparse`, `half`, `multi`. Each kind produces one
grid (`multi` produces three: a tile grid, a sparse float tree and a sparse
half tree in one file). Every generated file is self-checked twice:

* the emitted bytes reparse through the model's structured parsers
  (`TreeData5.parseFullCountH`, per grid) consuming every byte of the tree
  region;
* the emitted file reparses through the opaque full-file parser
  (`VdbFile.parse`), consuming every byte.

The grids use the standard `Tree_float_5_4_3` layout, file version 224, BLOSC
compression with the `-Int64(inBytes)` sentinel for payloads that do not
shrink (exactly what the C writer emits for small nodes) and `ACTIVE_MASK`
set, so stored counts are the mask popcounts. Half grids carry the
`_HalfFloat` grid-type suffix and an `is_saved_as_half_float` boolean
metadata entry, matching the C writer.
-/

open Vdb

/-! ### splitmix64 PRNG -/

structure Rng where
  s : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.s + UInt64.ofNat 0x9E3779B97F4A7C15
  let z0 := s
  let z1 := (z0 ^^^ (z0 >>> 30)) * UInt64.ofNat 0xBF58476D1CE4E5B9
  let z2 := (z1 ^^^ (z1 >>> 27)) * UInt64.ofNat 0x94D049BB133111EB
  (z2 ^^^ (z2 >>> 31), ⟨s⟩)

/-- Uniform bounded pick. -/
def Rng.pick (r : Rng) (n : Nat) : Nat × Rng :=
  let (z, r') := r.next
  (z.toNat % n, r')

/-- Up to `k` distinct indices in `[0, n)`. -/
def Rng.pickSet (r : Rng) (n k : Nat) : List Nat × Rng :=
  let rec go (acc : List Nat) (r : Rng) (fuel : Nat) : List Nat × Rng :=
    match fuel with
    | 0 => (acc, r)
    | fuel + 1 =>
      if acc.length >= k then (acc, r)
      else
        let (i, r') := r.pick n
        if acc.contains i then go acc r' fuel
        else go (i :: acc) r' fuel
  go [] r (k * 8 + 4)

/-- Parse a seed (decimal). -/
def parseSeed (s : String) : UInt64 :=
  s.toList.foldl (fun acc c =>
    if '0' ≤ c && c ≤ '9' then acc * (10 : UInt64) + UInt64.ofNat (c.toNat - '0'.toNat)
    else acc) 0

/-- Hex digit for `n` (0-15). -/
def hexChar (d : Nat) : Char :=
  if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- `w` hex digits of `n`, most significant first. -/
def hexW (w : Nat) (n : Nat) : String :=
  String.ofList ((List.range w).reverse.map fun i => hexChar ((n / 16 ^ i) % 16))

/-! ### float symbols -/

def BG : UInt32 := 0x40200000          --  2.5f
def NEG_BG : UInt32 := 0xC0200000      -- -2.5f
def FA : UInt32 := 0x3FC00000          --  1.5f
def FB : UInt32 := 0x40600000          --  3.5f
def FC : UInt32 := 0x40800000          --  4.5f

/-- The five-symbol alphabet used for generated voxel values. -/
def alphabet (i : Nat) : UInt32 :=
  match i with
  | 0 => BG | 1 => NEG_BG | 2 => FA | 3 => FB | 4 => FC | _ => BG

def symVal (i : Nat) : VoxelValue := .f32 (alphabet (i % 5))

/-! ### small byte helpers -/

def u16BytesLE (v : UInt16) : List UInt8 :=
  [ (v &&& 0xff).toUInt8, ((v >>> 8) &&& 0xff).toUInt8 ]

def u32BytesLE (v : UInt32) : List UInt8 :=
  [ (v &&& 0xff).toUInt8, ((v >>> 8) &&& 0xff).toUInt8,
    ((v >>> 16) &&& 0xff).toUInt8, ((v >>> 24) &&& 0xff).toUInt8 ]

/-- Full-width bytes of a stored value: half grids demote to 2 bytes,
    float grids store 4. -/
def activeBytes (half : Bool) (v : VoxelValue) : List UInt8 :=
  match v with
  | .f32 b => if half then u16BytesLE (floatToHalfRNE b) else u32BytesLE b
  | _ => u32BytesLE 0

/-- Bytes of an inactive value stored for codes 2/4/5: full width,
    truncated to half and widened again in half mode (as the writer does). -/
def inactiveBytes (half : Bool) (v : VoxelValue) : Bytes :=
  match v with
  | .f32 b =>
    if half then (u32BytesLE (halfToFloatBits (floatToHalfRNE b)) : List UInt8).toByteArray
    else (u32BytesLE b : List UInt8).toByteArray
  | _ => ByteArray.empty

/-! ### record construction -/

/-- Build the value record from the model's own classifier, exactly the way
    the writer computes it: inactive-value scan, code selection, selection
    mask; payload = values at active slots (full width, or demoted to half in
    half grids); code 6 stores every slot. -/
def buildRecord (L : Nat) (half : Bool)
    (values : Nat → VoxelValue) (mask n : Nat) : ValueRecord L :=
  let c := classify (.f32 BG) values mask n
  let idxs := if c.code = .noMaskAndAllVals then List.range n else setBits mask n
  let stored : Bytes := ((idxs.map values).flatMap (activeBytes half)).toByteArray
  let val0 :=
    if c.code = .noMaskAndOneInactiveVal || c.code = .maskAndOneInactiveVal
        || c.code = .maskAndTwoInactiveVals
    then inactiveBytes half c.val0 else ByteArray.empty
  let val1 := if c.code = .maskAndTwoInactiveVals then inactiveBytes half c.val1 else ByteArray.empty
  { code := c.code, val0 := val0, val1 := val1, selection := c.selection, stored := stored }

/-! ### random node construction -/

structure GenSt where
  half : Bool
  rng : Rng

/-- A mask with few set bits, for sparse trees. -/
def randomSmallMask (st : GenSt) (slots maxBits : Nat) : Nat × GenSt :=
  let (z, rng) := st.rng.next
  let nbits := z.toNat % (maxBits + 1)
  let rec go (fuel : Nat) (remaining : Nat) (acc : Nat) (st : GenSt) : Nat × GenSt :=
    match remaining with
    | 0 => (acc, st)
    | remaining + 1 =>
      match fuel with
      | 0 => (acc, st)
      | fuel + 1 =>
        let (i, rng') := st.rng.pick slots
        let bit := 1 <<< i
        if (acc &&& bit) != 0 then go fuel (remaining + 1) acc { st with rng := rng' }
        else go fuel remaining (acc ||| bit) { st with rng := rng' }
  go (nbits * 32 + 32) nbits 0 { st with rng := rng }

/-- Random voxel values, mostly from the five-symbol alphabet. -/
def randomValues (st : GenSt) (slots : Nat) : Array VoxelValue × GenSt :=
  let rec go (fuel : Nat) (i : Nat) (acc : Array VoxelValue) (st : GenSt) : Array VoxelValue × GenSt :=
    match fuel with
    | 0 => (acc, st)
    | fuel + 1 =>
      let (z, rng) := st.rng.next
      let v := z.toNat % 10
      let v' := if v < 8 then symVal ((z >>> 8).toNat) else .f32 (UInt32.ofNat z.toNat)
      go fuel (i + 1) (acc.push v') { st with rng := rng }
  go slots 0 (Array.mkEmpty slots) st

/-- Leaf generation at level 3 (512 slots). -/
def genLeaf (st : GenSt) : LeafNode × LeafBuffer × GenSt :=
  let slots := nodeSlots 3
  let (mask, st) := randomSmallMask st slots 4
  let (vals, st) := randomValues st slots
  let values : Nat → VoxelValue := fun i => vals.getD i (.f32 BG)
  let record := buildRecord 3 st.half values mask slots
  (⟨mask⟩, ⟨mask, record⟩, st)

/-- Level-4 internal node generation: up to two leaf children. -/
def genNode4 (st : GenSt) : Node4 × List LeafBuffer × GenSt :=
  let slots := nodeSlots 4
  let (childIdxs, rng) := st.rng.pickSet slots 2
  let childMask := childIdxs.foldl (fun a i => a ||| (1 <<< i)) 0
  let (valueMask, st1) := randomSmallMask { st with rng := rng } slots 4
  let (vals, st2) := randomValues st1 slots
  let values : Nat → VoxelValue := fun i => vals.getD i (.f32 BG)
  let record := buildRecord 4 st2.half values valueMask slots
  let rec go (st : GenSt) (idxs : List Nat) : List Child4 × List LeafBuffer × GenSt :=
    match idxs with
    | [] => ([], [], st)
    | _ :: rest =>
      let (leaf, buf, st') := genLeaf st
      let (cs, bss, st'') := go st' rest
      (⟨leaf⟩ :: cs, buf :: bss, st'')
  let (children, buffers, st3) := go st2 (setBits childMask slots)
  (⟨childMask, valueMask, record, children⟩, buffers, st3)

/-- Level-5 child (level-4 subtree). -/
def genChild5 (st : GenSt) : Child5 × List LeafBuffer × GenSt :=
  let (n4, bss, st') := genNode4 st
  (⟨n4⟩, bss, st')

/-- Root child (level-5 subtree) with an origin. -/
def genChildRoot (st : GenSt) (origin : Int32 × Int32 × Int32) :
    ChildRoot × List (List LeafBuffer) × GenSt :=
  let slots := nodeSlots 5
  let (childIdxs, rng) := st.rng.pickSet slots 2
  let childMask := childIdxs.foldl (fun a i => a ||| (1 <<< i)) 0
  let (valueMask, st1) := randomSmallMask { st with rng := rng } slots 4
  let (vals, st2) := randomValues st1 slots
  let values : Nat → VoxelValue := fun i => vals.getD i (.f32 BG)
  let record := buildRecord 5 st2.half values valueMask slots
  let rec go (st : GenSt) (idxs : List Nat) : List Child5 × List (List LeafBuffer) × GenSt :=
    match idxs with
    | [] => ([], [], st)
    | _ :: rest =>
      let (c5, bss, st') := genChild5 st
      let (cs, bsss, st'') := go st' rest
      (c5 :: cs, bss :: bsss, st'')
  let (children, bsss, st3) := go st2 (setBits childMask slots)
  (⟨origin.1, origin.2.1, origin.2.2, ⟨childMask, valueMask, record, children⟩⟩, bsss, st3)

/-- Build a tree with `nChildren` level-5 children. -/
def buildTree (st : GenSt) (nChildren : Nat) : TreeData5 × List (List (List LeafBuffer)) × GenSt :=
  let rec go (st : GenSt) (left : Nat) (acc : List ChildRoot) (all : List (List (List LeafBuffer))) :
      List ChildRoot × List (List (List LeafBuffer)) × GenSt :=
    match left with
    | 0 => (acc.reverse, all.reverse, st)
    | left + 1 =>
      let (z, rng) := st.rng.next
      let origin : Int32 × Int32 × Int32 :=
        (Int32.ofNat (z.toNat % 4) * 4096,
         Int32.ofNat ((z >>> 8).toNat % 4) * 4096,
         Int32.ofNat ((z >>> 16).toNat % 4) * 4096)
      let (cr, bsss, st') := genChildRoot { st with rng := rng } origin
      go st' left (cr :: acc) (bsss :: all)
  let (children, all, st') := go st nChildren [] []
  (⟨⟨(u32BytesLE BG : List UInt8).toByteArray, [], children⟩⟩, all, st')

/-- Random root tiles. -/
def randomTiles (st : GenSt) (n : Nat) : List RootTile × GenSt :=
  let rec go (st : GenSt) (left : Nat) (acc : List RootTile) : List RootTile × GenSt :=
    match left with
    | 0 => (acc.reverse, st)
    | left + 1 =>
      let (z1, rng) := st.rng.next
      let (z2, rng2) := rng.next
      let o := fun k => Int32.ofNat ((z1 >>> (k * 8)).toNat % 256) * 16 - 2048
      let t : RootTile :=
        { ox := o 0, oy := o 1, oz := o 2
        , value := (u32BytesLE (alphabet (z2.toNat % 5)) : List UInt8).toByteArray
        , active := UInt8.ofNat ((z2.toNat >>> 16) &&& 1) }
      go { st with rng := rng2 } left (t :: acc)
  go st n []

/-! ### file assembly -/

def uuid36 (r : Rng) : Bytes :=
  let (z1, r1) := r.next
  let (z2, _) := r1.next
  let s := hexW 16 z1.toNat ++ hexW 16 z2.toNat   -- 32 hex digits
  let part (a b : Nat) : String := String.ofList ((s.toList.take b).drop a)
  (part 0 8 ++ "-" ++ part 8 12 ++ "-" ++ part 12 16
   ++ "-" ++ part 16 20 ++ "-" ++ part 20 32).toUTF8

def prologue (gridCount : Nat) (uuid : Bytes) : FilePrefix :=
  { header := { fileVersion := 224, majorVersion := 21, minorVersion := 2
              , hasGridOffsets := true, uuid := uuid }
  , fileMetadata := { entries := [] }
  , gridCount := gridCount }

def gridHeader (half : Bool) : GridHeader :=
  { compressionFlags := 0x6
  , metadata :=
      if half then
        { entries := [{ name := "is_saved_as_half_float".toUTF8
                      , typeName := "bool".toUTF8
                      , value := .boolean true }] }
      else { entries := [] }
  , transform :=
      { kind := .scaleTranslate
      , translation := Vec3d.mk 0x0 0x0 0x0                      -- +0.0d
      , scale := Vec3d.mk 0x3FB999999999999A 0x3FB999999999999A 0x3FB999999999999A  -- 0.1d
      , voxelSize := Vec3d.mk 0x3FF0000000000000 0x3FF0000000000000 0x3FF0000000000000  -- 1.0d
      , affine := ByteArray.empty } }

def gridBody (half : Bool) (tree : Bytes) : GridBody :=
  { header := gridHeader half, bufferCount := 1, tree := tree }

def makeFileGrid (uniqueName gridType : Bytes) (g : GridBody) : FileGrid :=
  { uniqueName := uniqueName, gridType := gridType, instanceParent := ByteArray.empty, body := g }

/-- Build the full tree byte list (with the tree-base `i32 1`), and the body
    bytes for the opaque `GridBody` (without it: `GridBody.bufferCount` is
    the tree-base word the C reader consumes). -/
def treeInner (half : Bool) (tree : TreeData5) (bsss : List (List (List LeafBuffer))) : List Bytes :=
  TreeData5.chunksH tree half true ++ RootNode.bufferChunksH tree.root bsss half true

/-- Build one grid from a kind; returns the grid and the advanced state. -/
def buildGrid (st : GenSt) (kind : String) : FileGrid × GenSt :=
  if kind == "empty" then
    let tree : TreeData5 := ⟨⟨(u32BytesLE BG : List UInt8).toByteArray, [], []⟩⟩
    let bodyBytes := concatChunks (treeInner false tree []).tail
    (makeFileGrid "gen_empty".toUTF8 "Tree_float_5_4_3".toUTF8 (gridBody false bodyBytes), st)
  else if kind == "tiles" then
    let (z, rng) := st.rng.next
    let (tiles, st') := randomTiles { st with rng := rng } (1 + z.toNat % 5)
    let tree : TreeData5 := ⟨⟨(u32BytesLE BG : List UInt8).toByteArray, tiles, []⟩⟩
    let bodyBytes := concatChunks (treeInner false tree []).tail
    (makeFileGrid "gen_tiles".toUTF8 "Tree_float_5_4_3".toUTF8 (gridBody false bodyBytes), st')
  else if kind == "sparse" || kind == "half" then
    let half := kind == "half"
    let st' : GenSt := { st with half := half }
    let (tree, bsss, st'') := buildTree st' 1
    let bodyBytes := concatChunks (treeInner half tree bsss).tail
    (makeFileGrid (if half then "gen_half" else "gen_sparse").toUTF8
       (if half then "Tree_float_5_4_3_HalfFloat" else "Tree_float_5_4_3").toUTF8
       (gridBody half bodyBytes), st'')
  else
    let tree : TreeData5 := ⟨⟨(u32BytesLE BG : List UInt8).toByteArray, [], []⟩⟩
    let bodyBytes := concatChunks (treeInner false tree []).tail
    (makeFileGrid "gen_empty".toUTF8 "Tree_float_5_4_3".toUTF8 (gridBody false bodyBytes), st)

def buildFile (seed : UInt64) (kinds : List String) : IO VdbFile := do
  let mut st : GenSt := { half := false, rng := ⟨seed⟩ }
  let mut grids : List FileGrid := []
  for kind in kinds do
    let eff := if kind == "multi" then ["tiles", "sparse", "half"] else [kind]
    for k in eff do
      let (g, st') := buildGrid st k
      grids := g :: grids
      st := st'
  let uuid := uuid36 ⟨seed + UInt64.ofNat 0x1234⟩
  pure { prologue := prologue grids.length uuid, grids := grids.reverse }

/-! ### self-checks -/

/-- The emitted tree bytes reparse through the count-derived structured
    parsers, consuming every byte. The opaque `GridBody.tree` carries no
    tree-base word, so the check prepends the `i32 1` the structured model
    (and the C reader) expect. -/
def selfCheckTree (half : Bool) (bodyTree : Bytes) : Bool :=
  let elemSize := if half then 2 else 4
  let bytes := concatChunks ([putI32LE 1 ByteArray.empty] ++ [bodyTree])
  match TreeData5.parseFullCountH half true 4 elemSize true 224 (fun _ _ => none) bytes 0 with
  | some (_, _, endOff) => endOff == bytes.size
  | none => false

/-- Emit a file, run both self-checks, write it. Returns false on any
    failure. -/
def generate (outPath : String) (seed : UInt64) (kinds : List String) : IO Unit := do
  let file ← buildFile seed kinds
  for g in file.grids do
    let half := g.gridType == "Tree_float_5_4_3_HalfFloat".toUTF8
    if !selfCheckTree half g.body.tree then
      IO.eprintln s!"vdbgen: structured self-check failed for grid {g.uniqueName}"
      IO.Process.exit 2
  let bytes := VdbFile.emit file
  match VdbFile.parse bytes with
  | some (_, endOff) =>
    if endOff != bytes.size then
      IO.eprintln "vdbgen: full-file self-check consumed the wrong number of bytes"
      IO.Process.exit 2
  | none =>
    IO.eprintln "vdbgen: full-file self-check failed to reparse the emitted file"
    IO.Process.exit 2
  IO.FS.writeBinFile outPath bytes

def main (args : List String) : IO Unit := do
  match args with
  | out :: seed :: kinds@(_ :: _) => generate out (parseSeed seed) kinds
  | _ => do
    IO.eprintln "usage: vdbgen <out.vdb> <seed> <kind> [<kind> ...]"
    IO.eprintln "kinds: empty tiles sparse half multi"
    IO.Process.exit 2
