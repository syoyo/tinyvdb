/-
  TinyVDB - `vdbcheck`: parse a `.vdb` file with the Lean model and print the
  file header, file metadata names and grid descriptors.

  This is the Lean half of the model-versus-C differential harness: the C
  `vdb_dump_prologue` tool prints the same fields from the C reader, and a
  script compares the two outputs.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import VdbSpec

open Vdb

/-- Printable form of a wire string (names are ASCII in practice). -/
def byteString (b : Bytes) : String :=
  String.fromUTF8? b |>.getD s!"<{b.size} bytes>"

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
        o := gd.endOffset.toNat
    return 0
