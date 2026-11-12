/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  A full `.vdb` file: the prologue (header, file metadata, grid count) and
  the interleaved grid entries. Each grid's descriptor byte offsets are
  derived from its position in the emitted stream; the parser follows the
  descriptor's `gridOffset`/`endOffset` like the C reader.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.FilePrefix
import Vdb.GridBody
import Vdb.GridDescriptor

set_option linter.unusedSimpArgs false

namespace Vdb

structure FileGrid where
  uniqueName : Bytes
  gridType : Bytes
  instanceParent : Bytes
  body : GridBody
  deriving Repr

/-- Chunks of a descriptor-like record, used for its size. -/
def descChunkSizes (u t ip : Bytes) : Nat :=
  ([putString u ByteArray.empty, putString t ByteArray.empty,
    putString ip ByteArray.empty, putU64LE 0 ByteArray.empty,
    putU64LE 0 ByteArray.empty, putU64LE 0 ByteArray.empty].map (·.size)).sum

/-- The descriptor for a grid whose record starts at byte position `pos`.
    The body follows the descriptor and runs to `endOffset`. -/
def FileGrid.descriptorAt (g : FileGrid) (pos : Nat) : GridDescriptor :=
  let bodyPos := pos + descChunkSizes g.uniqueName g.gridType g.instanceParent
  let endPos := bodyPos + (g.body.chunks.map (·.size)).sum
  { uniqueName := g.uniqueName
    gridType := g.gridType
    instanceParent := g.instanceParent
    gridOffset := UInt64.ofNat bodyPos
    blockOffset := UInt64.ofNat bodyPos
    endOffset := UInt64.ofNat endPos }

/-- Emit a grid (descriptor + body) after `acc`. -/
def FileGrid.emitInto (g : FileGrid) (acc : Bytes) : Bytes :=
  g.body.emitFrom ((g.descriptorAt acc.size).emitFrom acc)

def emitGrids (gs : List FileGrid) (acc : Bytes) : Bytes :=
  match gs with
  | [] => acc
  | g :: rest => emitGrids rest (g.emitInto acc)

/-- A full `.vdb` file: the prologue and the interleaved grids. -/
structure VdbFile where
  prologue : FilePrefix
  grids : List FileGrid
  deriving Repr

def VdbFile.Canonical (f : VdbFile) : Prop :=
  f.prologue.Canonical ∧ f.prologue.gridCount = f.grids.length ∧
  221 ≤ f.prologue.header.fileVersion ∧
  (∀ g ∈ f.grids, g.body.Canonical)

def VdbFile.emitFrom (f : VdbFile) (acc : Bytes) : Bytes :=
  emitGrids f.grids (f.prologue.emitFrom acc)

def VdbFile.emit (f : VdbFile) : Bytes := f.emitFrom ByteArray.empty

/-- Parse `n` grids starting at `off`; returns them and the next offset. -/
def parseGrids (ver : UInt32) (b : Bytes) : Nat → Nat → Option (List FileGrid × Nat)
  | 0, off => some ([], off)
  | n + 1, off =>
    match GridDescriptor.parseFrom ver b off with
    | none => none
    | some (gd, _) =>
      match GridBody.parseFrom b gd.gridOffset.toNat gd.endOffset.toNat with
      | none => none
      | some (gb, _) =>
        match parseGrids ver b n gd.endOffset.toNat with
        | none => none
        | some (gs, lastOff) =>
          some (⟨gd.uniqueName, gd.gridType, gd.instanceParent, gb⟩ :: gs, lastOff)

/-- Parse a `.vdb` file at `off`. -/
def VdbFile.parseFrom (b : Bytes) (off : Nat) : Option (VdbFile × Nat) :=
  match FilePrefix.parseFrom b off with
  | none => none
  | some (pf, o) =>
    match parseGrids pf.header.fileVersion b pf.gridCount o with
    | none => none
    | some (gs, lastOff) => some (⟨pf, gs⟩, lastOff)

def VdbFile.parse (b : Bytes) : Option (VdbFile × Nat) := VdbFile.parseFrom b 0

end Vdb
