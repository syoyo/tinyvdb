/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Tree data inside a grid body: the tree-base buffer count and the root
  node's topology (background value, tile/child counts, tiles). Child
  subtrees and the internal/leaf records are the next layer; the model
  rejects roots with children for now.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Meta

set_option linter.unusedSimpArgs false

namespace Vdb

/-- A root-node tile: origin, value (full value width) and active flag. -/
structure RootTile where
  ox : Int32
  oy : Int32
  oz : Int32
  value : Bytes
  active : UInt8
  deriving Repr

def RootTile.chunks (t : RootTile) : List Bytes :=
  [putI32LE t.ox ByteArray.empty, putI32LE t.oy ByteArray.empty,
   putI32LE t.oz ByteArray.empty, t.value, putU8 t.active ByteArray.empty]

/-- A root node topology: background, tile/child counts, tiles. Children are
    not modelled yet, so a well-formed root has no children. -/
structure RootTopo where
  background : Bytes
  tiles : List RootTile
  deriving Repr

def RootTopo.chunks (r : RootTopo) : List Bytes :=
  [r.background, putU32LE (UInt32.ofNat r.tiles.length) ByteArray.empty,
   putU32LE 0 ByteArray.empty] ++ r.tiles.flatMap RootTile.chunks

def RootTopo.WellFormed (vsize : Nat) (r : RootTopo) : Prop :=
  r.background.size = vsize ∧ (∀ t ∈ r.tiles, t.value.size = vsize) ∧
  r.tiles.length < 2 ^ 32

def parseTiles (vsize : Nat) (b : Bytes) : Nat → Nat → Option (List RootTile × Nat)
  | 0, off => some ([], off)
  | n + 1, off =>
    match getI32LE b off with
    | none => none
    | some ox =>
      match getI32LE b (off + 4) with
      | none => none
      | some oy =>
        match getI32LE b (off + 8) with
        | none => none
        | some oz =>
          match getBytes? b (off + 12) vsize with
          | none => none
          | some v =>
            match getU8? b (off + 12 + vsize) with
            | none => none
            | some a =>
              match parseTiles vsize b n (off + 13 + vsize) with
              | none => none
              | some (ts, o) => some (⟨ox, oy, oz, v, a⟩ :: ts, o)

def RootTopo.parseFrom (vsize : Nat) (b : Bytes) (off : Nat) :
    Option (RootTopo × Nat) :=
  match getBytes? b off vsize with
  | none => none
  | some bg =>
    match getU32LE b (off + vsize) with
    | none => none
    | some nt =>
      match getU32LE b (off + vsize + 4) with
      | none => none
      | some nc =>
        if nc = 0 then
          match parseTiles vsize b nt.toNat (off + vsize + 8) with
          | none => none
          | some (ts, o) => some (⟨bg, ts⟩, o)
        else none

/-- The tree base: buffer count 1, then the root topology. -/
structure TreeData where
  root : RootTopo
  deriving Repr

def TreeData.chunks (t : TreeData) : List Bytes :=
  putI32LE 1 ByteArray.empty :: t.root.chunks

def TreeData.WellFormed (vsize : Nat) (t : TreeData) : Prop :=
  t.root.WellFormed vsize

def TreeData.parseFrom (vsize : Nat) (b : Bytes) (off : Nat) :
    Option (TreeData × Nat) :=
  match getI32LE b off with
  | none => none
  | some n =>
    if n = 1 then
      match RootTopo.parseFrom vsize b (off + 4) with
      | none => none
      | some (r, o) => some (⟨r⟩, o)
    else none


theorem RootTopo.parseFrom_emitFrom_empty (vsize : Nat) (bg : Bytes)
    (hb : bg.size = vsize) (pre : List Bytes) :
    RootTopo.parseFrom vsize
      (concatChunks (pre ++ RootTopo.chunks ⟨bg, []⟩)) (concatChunks pre).size =
    some (⟨bg, []⟩, (concatChunks (pre ++ RootTopo.chunks ⟨bg, []⟩)).size) := by
  have h1 : (concatChunks (pre ++ [bg])).size = (concatChunks pre).size + vsize := by
    rw [concatChunks_append_map]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [hb]
    omega
  have h1' : (concatChunks (pre ++ [bg])).size = (concatChunks pre).size + bg.size := by
    rw [h1, hb]
  have h2 : (concatChunks (pre ++ [bg, putU32LE (UInt32.ofNat 0) ByteArray.empty])).size =
      (concatChunks (pre ++ [bg])).size + 4 := by
    rw [show pre ++ [bg, putU32LE (UInt32.ofNat 0) ByteArray.empty] =
        (pre ++ [bg]) ++ [putU32LE (UInt32.ofNat 0) ByteArray.empty] from by simp]
    rw [concatChunks_snoc_size]; simp [putU32LE_size]
  have h3 : (concatChunks (pre ++ [bg, putU32LE (UInt32.ofNat 0) ByteArray.empty,
        putU32LE 0 ByteArray.empty])).size =
      (concatChunks (pre ++ [bg, putU32LE (UInt32.ofNat 0) ByteArray.empty])).size + 4 := by
    rw [show pre ++ [bg, putU32LE (UInt32.ofNat 0) ByteArray.empty, putU32LE 0 ByteArray.empty] =
        (pre ++ [bg, putU32LE (UInt32.ofNat 0) ByteArray.empty]) ++ [putU32LE 0 ByteArray.empty] from by simp]
    rw [concatChunks_snoc_size]; simp [putU32LE_size]
  unfold RootTopo.parseFrom RootTopo.chunks
  simp only [List.flatMap_nil, List.append_nil, List.length_nil]
  rw [show pre ++ [bg, putU32LE (UInt32.ofNat 0) ByteArray.empty, putU32LE 0 ByteArray.empty] =
      pre ++ (bg :: (putU32LE (UInt32.ofNat 0) ByteArray.empty :: (putU32LE 0 ByteArray.empty :: []))) from by simp]
  rw [show vsize = bg.size from hb.symm]
  rw [getBytes?_chunk]
  dsimp only
  rw [show (concatChunks pre).size + bg.size = (concatChunks (pre ++ [bg])).size from h1'.symm]
  rw [show concatChunks (pre ++ (bg :: (putU32LE (UInt32.ofNat 0) ByteArray.empty ::
      (putU32LE 0 ByteArray.empty :: [])))) =
      concatChunks ((pre ++ [bg]) ++ (putU32LE (UInt32.ofNat 0) ByteArray.empty ::
        (putU32LE 0 ByteArray.empty :: []))) from by simp]
  rw [getU32LE_chunk]
  dsimp only
  rw [show (concatChunks (pre ++ [bg])).size + 4 =
      (concatChunks (pre ++ [bg, putU32LE (UInt32.ofNat 0) ByteArray.empty])).size from h2.symm]
  rw [show concatChunks ((pre ++ [bg]) ++ (putU32LE (UInt32.ofNat 0) ByteArray.empty ::
      (putU32LE 0 ByteArray.empty :: []))) =
      concatChunks ((pre ++ [bg, putU32LE (UInt32.ofNat 0) ByteArray.empty]) ++
        (putU32LE 0 ByteArray.empty :: [])) from by simp]
  rw [getU32LE_chunk]
  dsimp only
  rw [show ((UInt32.ofNat 0).toNat) = 0 from rfl]
  rw [ite_eq_left rfl]
  rw [show (concatChunks (pre ++ [bg])).size + 8 =
      (concatChunks (pre ++ [bg, putU32LE (UInt32.ofNat 0) ByteArray.empty,
        putU32LE 0 ByteArray.empty])).size from by
    rw [h3, h2]]
  simp [parseTiles, concatChunks_append]
end Vdb
