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

/-- Read one tile record at `off`: origin, full-width value, active byte. -/
def parseTile (vsize : Nat) (b : Bytes) (off : Nat) : Option (RootTile × Nat) :=
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
          | some a => some (⟨ox, oy, oz, v, a⟩, off + 13 + vsize)

/-- Read `n` tile records in sequence. -/
def parseTiles (vsize : Nat) (b : Bytes) : Nat → Nat → Option (List RootTile × Nat)
  | 0, off => some ([], off)
  | n + 1, off =>
    match parseTile vsize b off with
    | none => none
    | some (t, o) =>
      match parseTiles vsize b n o with
      | none => none
      | some (ts, o') => some (t :: ts, o')

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
theorem parseTile_emit (vsize : Nat) (t : RootTile) (ht : t.value.size = vsize)
    (pre post : List Bytes) :
    parseTile vsize (concatChunks (pre ++ t.chunks ++ post)) (concatChunks pre).size =
      some (t, (concatChunks (pre ++ t.chunks)).size) := by
  have h0 : (concatChunks (pre ++ [putI32LE t.ox ByteArray.empty])).size =
      (concatChunks pre).size + 4 := by
    rw [concatChunks_snoc_size]; simp [putI32LE_size]
  have h1 : (concatChunks (pre ++ [putI32LE t.ox ByteArray.empty,
      putI32LE t.oy ByteArray.empty])).size = (concatChunks pre).size + 8 := by
    rw [show pre ++ [putI32LE t.ox ByteArray.empty, putI32LE t.oy ByteArray.empty] =
        (pre ++ [putI32LE t.ox ByteArray.empty]) ++ [putI32LE t.oy ByteArray.empty] from by simp]
    rw [concatChunks_snoc_size, h0]
    simp [putI32LE_size]
  have h2 : (concatChunks (pre ++ [putI32LE t.ox ByteArray.empty,
      putI32LE t.oy ByteArray.empty, putI32LE t.oz ByteArray.empty])).size =
      (concatChunks pre).size + 12 := by
    rw [show pre ++ [putI32LE t.ox ByteArray.empty, putI32LE t.oy ByteArray.empty,
        putI32LE t.oz ByteArray.empty] =
        (pre ++ [putI32LE t.ox ByteArray.empty, putI32LE t.oy ByteArray.empty]) ++
          [putI32LE t.oz ByteArray.empty] from by simp]
    rw [concatChunks_snoc_size, h1]
    simp [putI32LE_size]
  have h3 : (concatChunks (pre ++ [putI32LE t.ox ByteArray.empty,
      putI32LE t.oy ByteArray.empty, putI32LE t.oz ByteArray.empty, t.value])).size =
      (concatChunks pre).size + 12 + t.value.size := by
    rw [show pre ++ [putI32LE t.ox ByteArray.empty, putI32LE t.oy ByteArray.empty,
        putI32LE t.oz ByteArray.empty, t.value] =
        (pre ++ [putI32LE t.ox ByteArray.empty, putI32LE t.oy ByteArray.empty,
          putI32LE t.oz ByteArray.empty]) ++ [t.value] from by simp]
    rw [concatChunks_snoc_size, h2]
  have h4 : (concatChunks (pre ++ [putI32LE t.ox ByteArray.empty,
      putI32LE t.oy ByteArray.empty, putI32LE t.oz ByteArray.empty, t.value,
      putU8 t.active ByteArray.empty])).size =
      (concatChunks pre).size + 12 + t.value.size + 1 := by
    rw [show pre ++ [putI32LE t.ox ByteArray.empty, putI32LE t.oy ByteArray.empty,
        putI32LE t.oz ByteArray.empty, t.value, putU8 t.active ByteArray.empty] =
        (pre ++ [putI32LE t.ox ByteArray.empty, putI32LE t.oy ByteArray.empty,
          putI32LE t.oz ByteArray.empty, t.value]) ++ [putU8 t.active ByteArray.empty] from by simp]
    rw [concatChunks_snoc_size, h3]
    simp [putU8_size]
  unfold parseTile RootTile.chunks
  rw [show pre ++ [putI32LE t.ox ByteArray.empty, putI32LE t.oy ByteArray.empty,
      putI32LE t.oz ByteArray.empty, t.value, putU8 t.active ByteArray.empty] ++ post =
      pre ++ (putI32LE t.ox ByteArray.empty :: (putI32LE t.oy ByteArray.empty ::
        (putI32LE t.oz ByteArray.empty :: (t.value ::
          (putU8 t.active ByteArray.empty :: post))))) from by simp]
  rw [getI32LE_chunk]
  dsimp only
  rw [show (concatChunks pre).size + 4 =
      (concatChunks (pre ++ [putI32LE t.ox ByteArray.empty])).size from h0.symm]
  rw [show concatChunks (pre ++ (putI32LE t.ox ByteArray.empty ::
      (putI32LE t.oy ByteArray.empty :: (putI32LE t.oz ByteArray.empty ::
        (t.value :: (putU8 t.active ByteArray.empty :: post)))))) =
      concatChunks ((pre ++ [putI32LE t.ox ByteArray.empty]) ++
        (putI32LE t.oy ByteArray.empty :: (putI32LE t.oz ByteArray.empty ::
          (t.value :: (putU8 t.active ByteArray.empty :: post))))) from by simp]
  rw [getI32LE_chunk]
  dsimp only
  rw [show (concatChunks pre).size + 8 =
      (concatChunks (pre ++ [putI32LE t.ox ByteArray.empty,
        putI32LE t.oy ByteArray.empty])).size from h1.symm]
  rw [show concatChunks ((pre ++ [putI32LE t.ox ByteArray.empty]) ++
      (putI32LE t.oy ByteArray.empty :: (putI32LE t.oz ByteArray.empty ::
        (t.value :: (putU8 t.active ByteArray.empty :: post))))) =
      concatChunks ((pre ++ [putI32LE t.ox ByteArray.empty,
        putI32LE t.oy ByteArray.empty]) ++ (putI32LE t.oz ByteArray.empty ::
          (t.value :: (putU8 t.active ByteArray.empty :: post)))) from by simp]
  rw [getI32LE_chunk]
  dsimp only
  rw [show (concatChunks pre).size + 12 =
      (concatChunks (pre ++ [putI32LE t.ox ByteArray.empty,
        putI32LE t.oy ByteArray.empty, putI32LE t.oz ByteArray.empty])).size from h2.symm]
  rw [show concatChunks ((pre ++ [putI32LE t.ox ByteArray.empty,
        putI32LE t.oy ByteArray.empty]) ++ (putI32LE t.oz ByteArray.empty ::
          (t.value :: (putU8 t.active ByteArray.empty :: post)))) =
      concatChunks ((pre ++ [putI32LE t.ox ByteArray.empty,
        putI32LE t.oy ByteArray.empty, putI32LE t.oz ByteArray.empty]) ++
        (t.value :: (putU8 t.active ByteArray.empty :: post))) from by simp]
  rw [show vsize = t.value.size from ht.symm]
  rw [getBytes?_chunk]
  dsimp only
  rw [show (concatChunks (pre ++ [putI32LE t.ox ByteArray.empty,
        putI32LE t.oy ByteArray.empty, putI32LE t.oz ByteArray.empty])).size +
        t.value.size =
      (concatChunks (pre ++ [putI32LE t.ox ByteArray.empty,
        putI32LE t.oy ByteArray.empty, putI32LE t.oz ByteArray.empty,
        t.value])).size from by rw [h3, h2]]
  rw [show concatChunks ((pre ++ [putI32LE t.ox ByteArray.empty,
        putI32LE t.oy ByteArray.empty, putI32LE t.oz ByteArray.empty]) ++
        (t.value :: (putU8 t.active ByteArray.empty :: post))) =
      concatChunks ((pre ++ [putI32LE t.ox ByteArray.empty,
        putI32LE t.oy ByteArray.empty, putI32LE t.oz ByteArray.empty,
        t.value]) ++ (putU8 t.active ByteArray.empty :: post)) from by simp]
  rw [getU8?_chunk]
  dsimp only
  rw [show (concatChunks pre).size + 13 + t.value.size =
      (concatChunks (pre ++ [putI32LE t.ox ByteArray.empty,
        putI32LE t.oy ByteArray.empty, putI32LE t.oz ByteArray.empty,
        t.value, putU8 t.active ByteArray.empty])).size from by
    rw [h4]; omega]


theorem parseTiles_emit (vsize : Nat) (ts : List RootTile)
    (hwf : ∀ t ∈ ts, t.value.size = vsize) :
    ∀ (pre post : List Bytes),
      parseTiles vsize (concatChunks (pre ++ ts.flatMap RootTile.chunks ++ post))
        ts.length (concatChunks pre).size =
      some (ts, (concatChunks (pre ++ ts.flatMap RootTile.chunks)).size) := by
  induction ts with
  | nil =>
    intro pre post
    simp [parseTiles, concatChunks]
  | cons t ts ih =>
    intro pre post
    have ht : t.value.size = vsize := hwf t (by simp)
    have hts : ∀ x ∈ ts, x.value.size = vsize := fun x hx => hwf x (by simp [hx])
    simp only [List.length_cons, List.flatMap_cons]
    rw [show pre ++ (t.chunks ++ ts.flatMap RootTile.chunks) ++ post =
        pre ++ t.chunks ++ (ts.flatMap RootTile.chunks ++ post) from by simp]
    rw [parseTiles]
    rw [parseTile_emit vsize t ht pre (ts.flatMap RootTile.chunks ++ post)]
    dsimp only
    rw [show concatChunks (pre ++ t.chunks ++ (ts.flatMap RootTile.chunks ++ post)) =
        concatChunks ((pre ++ t.chunks) ++ ts.flatMap RootTile.chunks ++ post) from by simp]
    rw [ih hts (pre ++ t.chunks) post]
    simp [List.append_assoc]

theorem RootTopo.parseFrom_emitFrom (vsize : Nat) (r : RootTopo)
    (hwf : r.WellFormed vsize) (pre post : List Bytes) :
    RootTopo.parseFrom vsize (concatChunks (pre ++ r.chunks ++ post)) (concatChunks pre).size =
      some (r, (concatChunks (pre ++ r.chunks)).size) := by
  obtain ⟨hbg, htiles, hlen⟩ := hwf
  rcases r with ⟨bg, tiles⟩
  simp only at hbg htiles
  unfold RootTopo.parseFrom RootTopo.chunks
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [show pre ++ ([bg, putU32LE (UInt32.ofNat tiles.length) ByteArray.empty,
      putU32LE 0 ByteArray.empty] ++ tiles.flatMap RootTile.chunks) ++ post =
      pre ++ (bg :: (putU32LE (UInt32.ofNat tiles.length) ByteArray.empty ::
        (putU32LE 0 ByteArray.empty :: (tiles.flatMap RootTile.chunks ++ post)))) from by simp]
  rw [show vsize = bg.size from hbg.symm]
  rw [getBytes?_chunk]
  dsimp only
  have h1 : (concatChunks (pre ++ [bg])).size = (concatChunks pre).size + bg.size := by
    rw [concatChunks_snoc_size]
  rw [show (concatChunks pre).size + bg.size = (concatChunks (pre ++ [bg])).size from h1.symm]
  rw [show concatChunks (pre ++ (bg :: (putU32LE (UInt32.ofNat tiles.length) ByteArray.empty ::
      (putU32LE 0 ByteArray.empty :: (tiles.flatMap RootTile.chunks ++ post))))) =
      concatChunks ((pre ++ [bg]) ++ (putU32LE (UInt32.ofNat tiles.length) ByteArray.empty ::
        (putU32LE 0 ByteArray.empty :: (tiles.flatMap RootTile.chunks ++ post)))) from by simp]
  rw [getU32LE_chunk]
  dsimp only
  have h2 : (concatChunks (pre ++ [bg, putU32LE (UInt32.ofNat tiles.length) ByteArray.empty])).size =
      (concatChunks pre).size + bg.size + 4 := by
    rw [show pre ++ [bg, putU32LE (UInt32.ofNat tiles.length) ByteArray.empty] =
        (pre ++ [bg]) ++ [putU32LE (UInt32.ofNat tiles.length) ByteArray.empty] from by simp]
    rw [concatChunks_snoc_size, h1]
    simp [putU32LE_size]
  rw [show (concatChunks (pre ++ [bg])).size + 4 =
      (concatChunks (pre ++ [bg, putU32LE (UInt32.ofNat tiles.length) ByteArray.empty])).size
      from by rw [h2]; rw [h1]]
  rw [show concatChunks ((pre ++ [bg]) ++ (putU32LE (UInt32.ofNat tiles.length) ByteArray.empty ::
        (putU32LE 0 ByteArray.empty :: (tiles.flatMap RootTile.chunks ++ post)))) =
      concatChunks ((pre ++ [bg, putU32LE (UInt32.ofNat tiles.length) ByteArray.empty]) ++
        (putU32LE 0 ByteArray.empty :: (tiles.flatMap RootTile.chunks ++ post))) from by simp]
  rw [getU32LE_chunk]
  dsimp only
  have h3 : (concatChunks (pre ++ [bg, putU32LE (UInt32.ofNat tiles.length) ByteArray.empty,
      putU32LE 0 ByteArray.empty])).size = (concatChunks pre).size + bg.size + 8 := by
    rw [show pre ++ [bg, putU32LE (UInt32.ofNat tiles.length) ByteArray.empty, putU32LE 0 ByteArray.empty] =
        (pre ++ [bg, putU32LE (UInt32.ofNat tiles.length) ByteArray.empty]) ++ [putU32LE 0 ByteArray.empty]
        from by simp]
    rw [concatChunks_snoc_size, h2]
    simp [putU32LE_size]
  rw [show concatChunks ((pre ++ [bg, putU32LE (UInt32.ofNat tiles.length) ByteArray.empty]) ++
        (putU32LE 0 ByteArray.empty :: (tiles.flatMap RootTile.chunks ++ post))) =
      concatChunks ((pre ++ [bg, putU32LE (UInt32.ofNat tiles.length) ByteArray.empty,
        putU32LE 0 ByteArray.empty]) ++ (tiles.flatMap RootTile.chunks ++ post)) from by simp]
  rw [show (0 : UInt32) = 0 from rfl]
  rw [ite_eq_left rfl]
  rw [show (UInt32.ofNat tiles.length).toNat = tiles.length from by
    rw [show (UInt32.ofNat tiles.length).toNat = tiles.length % UInt32.size from rfl]
    exact Nat.mod_eq_of_lt hlen]
  rw [show (concatChunks (pre ++ [bg])).size + 8 =
      (concatChunks (pre ++ [bg, putU32LE (UInt32.ofNat tiles.length) ByteArray.empty,
        putU32LE 0 ByteArray.empty])).size from by rw [h1, h3]]
  rw [show concatChunks (pre ++ [bg, putU32LE (UInt32.ofNat tiles.length) ByteArray.empty,
        putU32LE 0 ByteArray.empty] ++ (tiles.flatMap RootTile.chunks ++ post)) =
      concatChunks ((pre ++ [bg, putU32LE (UInt32.ofNat tiles.length) ByteArray.empty,
        putU32LE 0 ByteArray.empty]) ++ tiles.flatMap RootTile.chunks ++ post) from by simp]
  have htiles' : ∀ t ∈ tiles, t.value.size = bg.size := by
    intro t ht
    rw [htiles t ht, hbg]
  rw [parseTiles_emit (bg.size) tiles htiles'
    (pre ++ [bg, putU32LE (UInt32.ofNat tiles.length) ByteArray.empty, putU32LE 0 ByteArray.empty]) post]
  simp [RootTopo.chunks, List.append_assoc]


theorem TreeData.parseFrom_emitFrom (vsize : Nat) (t : TreeData)
    (hwf : t.WellFormed vsize) (pre post : List Bytes) :
    TreeData.parseFrom vsize (concatChunks (pre ++ t.chunks ++ post)) (concatChunks pre).size =
      some (t, (concatChunks (pre ++ t.chunks)).size) := by
  rcases t with ⟨r⟩
  have hroot : RootTopo.WellFormed vsize r := hwf
  unfold TreeData.parseFrom TreeData.chunks
  rw [show pre ++ (putI32LE 1 ByteArray.empty :: r.chunks) ++ post =
      pre ++ (putI32LE 1 ByteArray.empty :: (r.chunks ++ post)) from by simp]
  rw [getI32LE_chunk]
  dsimp only
  rw [ite_eq_left (show ((1 : Int32) = 1) from rfl)]
  have h1 : (concatChunks (pre ++ [putI32LE (1 : Int32) ByteArray.empty])).size =
      (concatChunks pre).size + 4 := by
    rw [concatChunks_snoc_size]; simp [putI32LE_size]
  rw [show (concatChunks pre).size + 4 =
      (concatChunks (pre ++ [putI32LE (1 : Int32) ByteArray.empty])).size from h1.symm]
  rw [show concatChunks (pre ++ (putI32LE 1 ByteArray.empty :: (r.chunks ++ post))) =
      concatChunks ((pre ++ [putI32LE (1 : Int32) ByteArray.empty]) ++ (r.chunks ++ post))
      from by simp]
  rw [show concatChunks (pre ++ [putI32LE (1 : Int32) ByteArray.empty] ++ (r.chunks ++ post)) =
      concatChunks ((pre ++ [putI32LE (1 : Int32) ByteArray.empty]) ++ r.chunks ++ post) from by simp]
  rw [RootTopo.parseFrom_emitFrom vsize r hroot (pre ++ [putI32LE (1 : Int32) ByteArray.empty]) post]
  simp [TreeData.chunks, List.append_assoc]


end Vdb
