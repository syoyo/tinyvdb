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

def FileGrid.Canon (g : FileGrid) : Prop :=
  g.uniqueName.size < 2 ^ 32 ∧ g.gridType.size < 2 ^ 32 ∧ g.instanceParent.size < 2 ^ 32

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
  (∀ g ∈ f.grids, g.Canon ∧ g.body.Canonical)

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


/-! ### Emitted positions and chunk decomposition -/




theorem FileGrid.descChunks_sum (g : FileGrid) (pos : Nat) :
    ((g.descriptorAt pos).chunks.map (·.size)).sum =
      descChunkSizes g.uniqueName g.gridType g.instanceParent := by
  simp [FileGrid.descriptorAt, GridDescriptor.chunks, descChunkSizes, putString_size, putU64LE_size]

def FileGrid.totalSize (g : FileGrid) : Nat :=
  descChunkSizes g.uniqueName g.gridType g.instanceParent +
    (g.body.chunks.map (·.size)).sum

def FileGrid.bytesAt (g : FileGrid) (start : Nat) : Bytes :=
  concatChunks ((g.descriptorAt start).chunks ++ g.body.chunks)

def gridsChunksAt : List FileGrid → Nat → List Bytes
  | [], _ => []
  | g :: rest, start => (g.descriptorAt start).chunks ++ g.body.chunks ++ gridsChunksAt rest (start + g.totalSize)

def gridsBytesAt (gs : List FileGrid) (start : Nat) : Bytes :=
  concatChunks (gridsChunksAt gs start)

theorem FileGrid.emitInto_eq (g : FileGrid) (acc : Bytes) :
    g.emitInto acc = concatChunks ([acc] ++ (g.descriptorAt acc.size).chunks ++ g.body.chunks) := by
  unfold FileGrid.emitInto GridBody.emitFrom GridDescriptor.emitFrom
  rw [show acc ++ concatChunks (g.descriptorAt acc.size).chunks =
      concatChunks (acc :: (g.descriptorAt acc.size).chunks) from acc_append_concatChunks acc _]
  rw [show concatChunks (acc :: (g.descriptorAt acc.size).chunks) ++ concatChunks g.body.chunks =
      concatChunks ((acc :: (g.descriptorAt acc.size).chunks) ++ g.body.chunks) from
    by rw [concatChunks_append]]
  simp

theorem FileGrid.emitInto_acc (g : FileGrid) (acc : Bytes) :
    g.emitInto acc = acc ++ g.bytesAt acc.size := by
  rw [FileGrid.emitInto_eq]
  rw [show [acc] ++ (g.descriptorAt acc.size).chunks ++ g.body.chunks =
      acc :: ((g.descriptorAt acc.size).chunks ++ g.body.chunks) from by simp]
  rw [← acc_append_concatChunks]
  rfl

theorem FileGrid.bytesAt_size (g : FileGrid) (start : Nat) :
    (g.bytesAt start).size = g.totalSize := by
  unfold FileGrid.bytesAt FileGrid.totalSize
  rw [concatChunks_size]
  rw [show ((g.descriptorAt start).chunks ++ g.body.chunks).map (·.size) =
      (g.descriptorAt start).chunks.map (·.size) ++ g.body.chunks.map (·.size) from List.map_append]
  rw [List.sum_append, FileGrid.descChunks_sum]

theorem FileGrid.emitInto_size (g : FileGrid) (acc : Bytes) :
    (g.emitInto acc).size = acc.size + g.totalSize := by
  rw [FileGrid.emitInto_acc, ByteArray.size_append, FileGrid.bytesAt_size]

theorem gridsChunksAt_concat (gs : List FileGrid) (start : Nat) :
    concatChunks (gridsChunksAt gs start) = gridsBytesAt gs start := rfl

theorem emitGrids_acc (gs : List FileGrid) : ∀ (acc : Bytes),
    emitGrids gs acc = acc ++ gridsBytesAt gs acc.size := by
  induction gs with
  | nil =>
    intro acc
    simp [emitGrids, gridsBytesAt, gridsChunksAt, concatChunks]
  | cons g rest ih =>
    intro acc
    simp only [emitGrids]
    rw [ih (g.emitInto acc)]
    rw [FileGrid.emitInto_acc, ByteArray.size_append, FileGrid.bytesAt_size]
    show acc ++ g.bytesAt acc.size ++ gridsBytesAt rest (acc.size + g.totalSize) =
      acc ++ gridsBytesAt (g :: rest) acc.size
    rw [show gridsBytesAt (g :: rest) acc.size =
        g.bytesAt acc.size ++ gridsBytesAt rest (acc.size + g.totalSize) from by
      simp [gridsBytesAt, gridsChunksAt, FileGrid.bytesAt, concatChunks_append]
      rw [ByteArray.append_assoc]]
    rw [ByteArray.append_assoc]

theorem UInt64.toNat_ofNat_lt {n : Nat} (h : n < UInt64.size) : (UInt64.ofNat n).toNat = n := by
  simp [UInt64.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem FileGrid.descriptorAt_canonical (g : FileGrid) (hg : g.Canon) (pos : Nat) :
    (g.descriptorAt pos).Canonical := by
  obtain ⟨h1, h2, h3⟩ := hg
  simp [GridDescriptor.Canonical, FileGrid.descriptorAt]
  exact ⟨h1, h2, h3⟩

theorem desc_prefix_size (acc : Bytes) (d : List Bytes) :
    (concatChunks (acc :: d)).size = acc.size + (d.map (·.size)).sum := by
  rw [concatChunks_size, List.map_cons, List.sum_cons]

theorem FileGrid.gridOffset_toNat (g : FileGrid) (pos : Nat)
    (h : pos + descChunkSizes g.uniqueName g.gridType g.instanceParent < UInt64.size) :
    (g.descriptorAt pos).gridOffset.toNat =
      pos + descChunkSizes g.uniqueName g.gridType g.instanceParent := by
  show (UInt64.ofNat (pos + descChunkSizes g.uniqueName g.gridType g.instanceParent)).toNat =
      pos + descChunkSizes g.uniqueName g.gridType g.instanceParent
  exact UInt64.toNat_ofNat_lt h

theorem FileGrid.endOffset_toNat (g : FileGrid) (pos : Nat)
    (h : pos + g.totalSize < UInt64.size) :
    (g.descriptorAt pos).endOffset.toNat = pos + g.totalSize := by
  unfold FileGrid.descriptorAt
  dsimp only
  have h' : pos + g.totalSize < UInt64.size := h
  rw [show pos + descChunkSizes g.uniqueName g.gridType g.instanceParent +
      (g.body.chunks.map (·.size)).sum = pos + g.totalSize from by
    unfold FileGrid.totalSize; omega]
  exact UInt64.toNat_ofNat_lt h'


theorem parseGrid_one (g : FileGrid) (hg : g.Canon) (hgb : g.body.Canonical)
    (ver : UInt32) (hver : 221 ≤ ver) (acc : Bytes)
    (hb : (concatChunks (acc :: gridsChunksAt [g] acc.size)).size < UInt64.size) :
    parseGrids ver (concatChunks (acc :: gridsChunksAt [g] acc.size)) 1 acc.size =
      some ([g], (concatChunks (acc :: gridsChunksAt [g] acc.size)).size) := by
  simp only [gridsChunksAt, List.length_nil, List.append_nil]
  simp only [parseGrids]
  set d := g.descriptorAt acc.size with hd
  have hb_exp : (concatChunks (acc :: (d.chunks ++ g.body.chunks))).size < UInt64.size := by
    simpa [gridsChunksAt] using hb
  have hsize_eq : (concatChunks (acc :: (d.chunks ++ g.body.chunks))).size =
      acc.size + descChunkSizes g.uniqueName g.gridType g.instanceParent +
        (g.body.chunks.map (·.size)).sum := by
    rw [desc_prefix_size]
    simp only [List.map_append, List.sum_append]
    rw [hd, FileGrid.descChunks_sum]
    omega
  have hb_eq : concatChunks (acc :: (d.chunks ++ g.body.chunks)) =
      d.emitFrom acc ++ concatChunks g.body.chunks := by
    rw [← acc_append_concatChunks]
    rw [concatChunks_append]
    rw [show d.emitFrom acc = acc ++ concatChunks d.chunks from rfl]
    rw [ByteArray.append_assoc]
  rw [hb_eq]
  have hexact := GridDescriptor.parseFrom_emitFrom ver hver d
    (FileGrid.descriptorAt_canonical g hg acc.size) acc
  rw [GridDescriptor.parseFrom_append ver hexact]
  dsimp only
  have hgo : d.gridOffset.toNat = acc.size + descChunkSizes g.uniqueName g.gridType g.instanceParent := by
    apply FileGrid.gridOffset_toNat
    have hle : acc.size + descChunkSizes g.uniqueName g.gridType g.instanceParent ≤
        (concatChunks (acc :: (d.chunks ++ g.body.chunks))).size := by
      rw [hsize_eq]; omega
    exact Nat.lt_of_le_of_lt hle hb_exp
  have heo : d.endOffset.toNat = acc.size + g.totalSize := by
    apply FileGrid.endOffset_toNat
    have hle : acc.size + g.totalSize ≤
        (concatChunks (acc :: (d.chunks ++ g.body.chunks))).size := by
      rw [hsize_eq]
      unfold FileGrid.totalSize
      omega
    exact Nat.lt_of_le_of_lt hle hb_exp
  rw [hgo, heo]
  have hb_body : d.emitFrom acc ++ concatChunks g.body.chunks =
      concatChunks ((acc :: d.chunks) ++ g.body.chunks) := by
    rw [show concatChunks ((acc :: d.chunks) ++ g.body.chunks) =
        concatChunks (acc :: (d.chunks ++ g.body.chunks)) from by simp]
    rw [← acc_append_concatChunks, concatChunks_append]
    rw [show d.emitFrom acc = acc ++ concatChunks d.chunks from rfl]
    rw [ByteArray.append_assoc]
  rw [hb_body]
  have hprefix : (concatChunks (acc :: d.chunks)).size =
      acc.size + descChunkSizes g.uniqueName g.gridType g.instanceParent := by
    rw [desc_prefix_size, FileGrid.descChunks_sum]
  have hend : (concatChunks ((acc :: d.chunks) ++ g.body.chunks)).size =
      acc.size + g.totalSize := by
    rw [show (acc :: d.chunks) ++ g.body.chunks = acc :: (d.chunks ++ g.body.chunks) from by simp]
    rw [desc_prefix_size]
    simp only [List.map_append, List.sum_append]
    rw [hd, FileGrid.descChunks_sum]
    unfold FileGrid.totalSize
    omega
  rw [← hprefix, ← hend]
  rw [show concatChunks (acc :: d.chunks ++ g.body.chunks) =
      concatChunks ((acc :: d.chunks) ++ g.body.chunks ++ []) from by simp]
  rw [show (concatChunks ((acc :: d.chunks) ++ g.body.chunks ++ [])).size =
      (concatChunks ((acc :: d.chunks) ++ g.body.chunks)).size from by simp]
  rw [GridBody.parseFromChunks g.body hgb (acc :: d.chunks) []]
  dsimp only
  simp [parseGrids, FileGrid.descriptorAt, hd]


theorem VdbFile.parseFrom_emitFrom_single (f : VdbFile) (g : FileGrid)
    (hc : f.Canonical) (hg : f.grids = [g]) (acc : Bytes)
    (hacc : (f.emitFrom acc).size < UInt64.size) :
    ∃ out, VdbFile.parseFrom (f.emitFrom acc) acc.size = some (f, out) := by
  obtain ⟨hpc, hcount, hver, hgrids⟩ := hc
  have hgin : g ∈ f.grids := by rw [hg]; simp
  have hgcanon : g.Canon := (hgrids g hgin).1
  have hgbody : g.body.Canonical := (hgrids g hgin).2
  have hcount1 : f.prologue.gridCount = 1 := by rw [hcount, hg]; rfl
  set pf := f.prologue.emitFrom acc with hpf
  have hpfchunks : pf = concatChunks (acc :: f.prologue.chunks) := by
    rw [hpf]; exact acc_append_concatChunks acc f.prologue.chunks
  have hbytes : gridsBytesAt [g] pf.size = concatChunks (gridsChunksAt [g] pf.size) := rfl
  set restC := gridsChunksAt [g] pf.size with hr
  have hrest_eq : restC = (g.descriptorAt pf.size).chunks ++ g.body.chunks := by
    rw [hr]
    simp [gridsChunksAt]
  have hb : f.emitFrom acc = concatChunks (acc :: (f.prologue.chunks ++ restC)) := by
    unfold VdbFile.emitFrom
    rw [hg, emitGrids_acc]
    rw [← hpf]
    rw [hbytes]
    rw [hpfchunks]
    rw [← concatChunks_append]
    rw [show acc :: (f.prologue.chunks ++ restC) = (acc :: f.prologue.chunks) ++ restC from by simp]
  rw [hb]
  unfold VdbFile.parseFrom
  rw [show acc.size = (concatChunks [acc]).size from by simp [concatChunks]]
  rw [show concatChunks (acc :: (f.prologue.chunks ++ restC)) =
      concatChunks ([acc] ++ f.prologue.chunks ++ restC) from by simp]
  rw [FilePrefix.parseFromChunks f.prologue hpc [acc] restC]
  dsimp only
  rw [hcount1]
  have hb1 : concatChunks ([acc] ++ f.prologue.chunks ++ restC) =
      concatChunks (concatChunks (acc :: f.prologue.chunks) :: restC) := by
    rw [show [acc] ++ f.prologue.chunks ++ restC =
        (acc :: f.prologue.chunks) ++ restC from by simp]
    rw [concatChunks_append]
    rw [acc_append_concatChunks]
  rw [hb1]
  rw [show (concatChunks ([acc] ++ f.prologue.chunks)).size = pf.size from by
    rw [show [acc] ++ f.prologue.chunks = acc :: f.prologue.chunks from by simp]
    rw [← hpfchunks]]
  have hbeq : concatChunks (pf :: restC) = f.emitFrom acc := by
    rw [hb, hpfchunks]
    rw [← acc_append_concatChunks]
    rw [← acc_append_concatChunks]
    rw [show concatChunks (acc :: (f.prologue.chunks ++ restC)) =
        acc ++ (concatChunks f.prologue.chunks ++ concatChunks restC) from by
      rw [← acc_append_concatChunks, concatChunks_append]]
    rw [ByteArray.append_assoc]
  have hbnd : (concatChunks (pf :: restC)).size < UInt64.size := by
    rw [hbeq]
    exact hacc
  rw [hr]
  rw [show concatChunks (concatChunks (acc :: f.prologue.chunks) :: gridsChunksAt [g] pf.size) =
      concatChunks (pf :: gridsChunksAt [g] pf.size) from by rw [← hpfchunks]]
  rw [parseGrid_one g hgcanon hgbody f.prologue.header.fileVersion hver pf hbnd]
  dsimp only
  refine ⟨(concatChunks (pf :: gridsChunksAt [g] pf.size)).size, ?_⟩
  rw [← hg]


/-- The entry-point form for a single-grid file. -/
theorem VdbFile.parse_emit_single (f : VdbFile) (g : FileGrid)
    (hc : f.Canonical) (hg : f.grids = [g])
    (hacc : (f.emit).size < UInt64.size) :
    ∃ out, VdbFile.parse (f.emit) = some (f, out) := by
  simpa [VdbFile.parse, VdbFile.emit, ByteArray.size_empty] using
    VdbFile.parseFrom_emitFrom_single f g hc hg ByteArray.empty hacc


theorem parseGrids_emit (gs : List FileGrid)
    (hgs : ∀ g ∈ gs, g.Canon ∧ g.body.Canonical)
    (ver : UInt32) (hver : 221 ≤ ver) :
    ∀ (acc : Bytes),
      (concatChunks (acc :: gridsChunksAt gs acc.size)).size < UInt64.size →
      parseGrids ver (concatChunks (acc :: gridsChunksAt gs acc.size)) gs.length acc.size =
        some (gs, (concatChunks (acc :: gridsChunksAt gs acc.size)).size) := by
  induction gs with
  | nil =>
    intro acc hb
    simp [parseGrids, gridsChunksAt, concatChunks]
  | cons g rest ih =>
    intro acc hb
    have hg := (hgs g (by simp)).1
    have hgbody := (hgs g (by simp)).2
    have hrest : ∀ x ∈ rest, x.Canon ∧ x.body.Canonical := fun x hx => hgs x (by simp [hx])
    simp only [List.length_cons, parseGrids]
    set d := g.descriptorAt acc.size with hd
    set restC := gridsChunksAt rest (acc.size + g.totalSize) with hr
    have hchunks : gridsChunksAt (g :: rest) acc.size = d.chunks ++ g.body.chunks ++ restC := rfl
    rw [hchunks]
    have hb_exp : (concatChunks (acc :: (d.chunks ++ g.body.chunks ++ restC))).size < UInt64.size := by
      simpa [hchunks] using hb
    have hsize_eq : (concatChunks (acc :: (d.chunks ++ g.body.chunks ++ restC))).size =
        acc.size + descChunkSizes g.uniqueName g.gridType g.instanceParent +
          (g.body.chunks.map (·.size)).sum + (restC.map (·.size)).sum := by
      rw [desc_prefix_size]
      simp only [List.map_append, List.sum_append]
      rw [hd, FileGrid.descChunks_sum]
      omega
    have hb_eq : concatChunks (acc :: (d.chunks ++ g.body.chunks ++ restC)) =
        d.emitFrom acc ++ (concatChunks g.body.chunks ++ concatChunks restC) := by
      rw [← acc_append_concatChunks]
      rw [concatChunks_append, concatChunks_append]
      simp [GridDescriptor.emitFrom, ByteArray.append_assoc]
    rw [hb_eq]
    have hexact := GridDescriptor.parseFrom_emitFrom ver hver d
      (FileGrid.descriptorAt_canonical g hg acc.size) acc
    rw [GridDescriptor.parseFrom_append ver hexact]
    dsimp only
    have hgo : d.gridOffset.toNat = acc.size + descChunkSizes g.uniqueName g.gridType g.instanceParent := by
      apply FileGrid.gridOffset_toNat
      have hle : acc.size + descChunkSizes g.uniqueName g.gridType g.instanceParent ≤
          (concatChunks (acc :: (d.chunks ++ g.body.chunks ++ restC))).size := by
        rw [hsize_eq]; omega
      exact Nat.lt_of_le_of_lt hle hb_exp
    have heo : d.endOffset.toNat = acc.size + g.totalSize := by
      apply FileGrid.endOffset_toNat
      have hle : acc.size + g.totalSize ≤
          (concatChunks (acc :: (d.chunks ++ g.body.chunks ++ restC))).size := by
        rw [hsize_eq]
        unfold FileGrid.totalSize
        omega
      exact Nat.lt_of_le_of_lt hle hb_exp
    rw [hgo, heo]
    have hb_body : d.emitFrom acc ++ (concatChunks g.body.chunks ++ concatChunks restC) =
        concatChunks ((acc :: d.chunks) ++ g.body.chunks ++ restC) := by
      rw [show concatChunks ((acc :: d.chunks) ++ g.body.chunks ++ restC) =
          concatChunks (acc :: (d.chunks ++ (g.body.chunks ++ restC))) from by simp]
      rw [← acc_append_concatChunks, concatChunks_append]
      rw [show d.emitFrom acc = acc ++ concatChunks d.chunks from rfl]
      simp [ByteArray.append_assoc]
      rw [concatChunks_append]
    rw [hb_body]
    have hprefix : (concatChunks (acc :: d.chunks)).size =
        acc.size + descChunkSizes g.uniqueName g.gridType g.instanceParent := by
      rw [desc_prefix_size, FileGrid.descChunks_sum]
    have hend : (concatChunks ((acc :: d.chunks) ++ g.body.chunks)).size =
        acc.size + g.totalSize := by
      rw [show (acc :: d.chunks) ++ g.body.chunks = acc :: (d.chunks ++ g.body.chunks) from by simp]
      rw [desc_prefix_size]
      simp only [List.map_append, List.sum_append]
      rw [hd, FileGrid.descChunks_sum]
      unfold FileGrid.totalSize
      omega
    rw [← hprefix, ← hend]
    rw [show concatChunks (acc :: d.chunks ++ g.body.chunks ++ restC) =
        concatChunks ((acc :: d.chunks) ++ g.body.chunks ++ restC) from by simp]
    rw [GridBody.parseFromChunks g.body hgbody (acc :: d.chunks) restC]
    dsimp only
    -- tail
    set X := concatChunks ((acc :: d.chunks) ++ g.body.chunks) with hX
    have hX_size : X.size = acc.size + g.totalSize := by rw [hX]; exact hend
    have hrestC : restC = gridsChunksAt rest X.size := by rw [hr, ← hX_size]
    have hb_tail : concatChunks (acc :: d.chunks ++ g.body.chunks ++ restC) =
        concatChunks (X :: gridsChunksAt rest X.size) := by
      rw [hrestC]
      rw [show concatChunks (acc :: d.chunks ++ g.body.chunks ++ gridsChunksAt rest X.size) =
          concatChunks (((acc :: d.chunks) ++ g.body.chunks) ++ gridsChunksAt rest X.size) from by simp]
      rw [concatChunks_append, ← hX, acc_append_concatChunks]
    rw [hb_tail]
    have hbnd : (concatChunks (X :: gridsChunksAt rest X.size)).size < UInt64.size := by
      rw [← hb_tail]
      exact hb_exp
    rw [ih hrest X hbnd]
    simp [hX, FileGrid.descriptorAt, hd]
end Vdb
