/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  BOUNDED dense marching-cubes TOPOLOGY differential twin (next VS-3 slice).
  Driven by `scripts/check_mc_topology.sh` against `scripts/mc_topology_c.c`,
  which calls the REAL `tvdb_sdf_to_mesh_ex` on 258 dense fields and dumps the
  grid geometry, every input sample (Float32 bit pattern), every output vertex
  position (Float32 bit pattern) and every emitted triangle index for both
  winding modes.

  This is a genuine independent computation from the landed tables, not a
  replay of the C indices:

    * the case of each cell is recomputed from the decoded samples;
    * the used cube edges come from `Vdb.McTable.mcEdgeTable` (equal to the
      sign-change mask by T-MC-EDGE) and the triangles from
      `Vdb.McTable.trisOf` (T-MC-COUNT / T-MC-COMPLETE);
    * the weld key of a crossed grid edge is `Vdb.McWeld.GridEdge.key`
      (the C packing `3 * voxel_idx + axis + 1`, injective by T-MC-WELD);
    * vertex ids are allocated on first appearance of a key while sweeping
      cells and cube edges in the C order, and the crossing position is the
      exact-ℚ interpolation of the two decoded Float32 samples (the swap
      independence is `Vdb.McWeld.vertex_pos_swap`).

  Compared: vertex and face counts, face index triples in emission order,
  triangle multisets by welded grid-edge keys (exact), and positions (Float32
  tolerance, with an exact-bit counter). Both TABLE and OUTWARD windings are
  checked; OUTWARD is the same triangle list with vertices 1 and 2 swapped.

  NOT mirrored (reported loudly, never counted as a pass): the C count-then-
  emit two-pass allocation, the rolling/hash slot cache, the arena layout, and
  the double-precision intermediate of `mesh_edge_interpolate` (the twin uses
  exact rationals, hence a Float32 tolerance on positions). The C's Float32
  sample values ARE mirrored bit-exactly via `f32Rat`.

  Coverage: 256 Bourke corner patterns embedded in a padded 4^3 lattice plus
  one analytic sphere and one analytic plane on 8^3 lattices. NOT covered:
  sparse/tree `tool_mesh`, NaN/Inf/nonfinite rejection paths, winding modes
  beyond the two enum values, grids smaller than 2^3, and degenerate
  isovalue-equal samples (the corpus has none). No theorem is weakened.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.McTable
import Vdb.McWeld
import Mathlib.Tactic

namespace Vdb
namespace McTopologyCheck

abbrev Tri := Nat × Nat × Nat

structure R3 where
  x : Rat
  y : Rat
  z : Rat
  deriving Inhabited

/-! ### Exact Float32 decoding -/

/-- Decode an IEEE-754 binary32 bit pattern to an exact rational (the same
    decoder shape as `Vdb.TreeMeshSdfCheck.f32Rat`). Infinities/NaNs map to 0;
    the harness inputs are all finite. -/
def f32Rat (bits : UInt32) : Rat :=
  let neg : Bool := (bits >>> 31) != 0
  let exp : Nat := ((bits >>> 23) &&& 0xff).toNat
  let frac : Nat := (bits &&& 0x7fffff).toNat
  let mag : Rat :=
    if exp == 0 then
      Rat.divInt (frac : Int) ((2 ^ (149 : Nat) : Nat) : Int)
    else if exp == 255 then
      0
    else
      let m : Nat := ((1 : Nat) <<< 23) ||| frac
      let e : Int := (exp : Int) - 127 - 23
      if e >= 0 then Rat.divInt ((m * 2 ^ e.toNat : Nat) : Int) 1
      else Rat.divInt (m : Int) ((2 ^ (-e).toNat : Nat) : Int)
  if neg then -mag else mag

def f32Float (bits : UInt32) : Float := Float32.toFloat (Float32.ofBits bits)

def ratFloat (q : Rat) : Float := Float.ofInt q.num / Float.ofNat q.den

/-! ### The parsed C dump -/

structure Grid where
  nx : Nat := 0
  ny : Nat := 0
  nz : Nat := 0
  ox : Rat := 0
  oy : Rat := 0
  oz : Rat := 0
  vs : Rat := 0
  iso : Rat := 0
  samples : Array Rat := #[]

structure Case where
  grid : Grid := {}
  repNv : Nat := 0
  repNfT : Nat := 0
  repNfO : Nat := 0
  verts : Array (UInt32 × UInt32 × UInt32) := #[]
  facesT : Array Tri := #[]
  facesO : Array Tri := #[]
  deriving Inhabited

inductive Line where
  | fields (n : Nat)
  | caseHead (id : Nat) (g : Grid)
  | sample (id idx : Nat) (bits : UInt32)
  | mesh (id : Nat) (w : String) (nv nf : Nat)
  | vertex (id j : Nat) (v : UInt32 × UInt32 × UInt32)
  | face (id j : Nat) (w : String) (t : Tri)
  | ignored

def parseHex8 (s : String) : Option UInt32 :=
  match s.toList with
  | [c0, c1, c2, c3, c4, c5, c6, c7] =>
      let hexVal (ch : Char) : Option UInt32 :=
        match ch with
        | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
        | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
        | '8' => some 8 | '9' => some 9 | 'a' => some 10 | 'b' => some 11
        | 'c' => some 12 | 'd' => some 13 | 'e' => some 14 | 'f' => some 15
        | _ => none
      [c0, c1, c2, c3, c4, c5, c6, c7].foldlM (fun acc ch => (hexVal ch).map (acc * 16 + ·)) 0
  | _ => none

def parseLine (s : String) : Line :=
  let t := s.splitOn " "
  match t with
  | ["fields", n] =>
      match n.toNat? with
      | some v => .fields v
      | _ => .ignored
  | ["case", id, "nx", nx, "ny", ny, "nz", nz, "ox", ox, "oy", oy, "oz", oz, "vs", vs, "iso", iso] =>
      match id.toNat?, nx.toNat?, ny.toNat?, nz.toNat?,
            parseHex8 ox, parseHex8 oy, parseHex8 oz, parseHex8 vs, parseHex8 iso with
      | some i, some ax, some ay, some az, some bx, some byy, some bz, some bvs, some bi =>
          .caseHead i { nx := ax, ny := ay, nz := az, ox := f32Rat bx, oy := f32Rat byy,
                        oz := f32Rat bz, vs := f32Rat bvs, iso := f32Rat bi }
      | _, _, _, _, _, _, _, _, _ => .ignored
  | ["sample", id, idx, b] =>
      match id.toNat?, idx.toNat?, parseHex8 b with
      | some i, some j, some w => .sample i j w
      | _, _, _ => .ignored
  | ["mesh", id, w, "nv", nv, "nf", nf] =>
      match id.toNat?, nv.toNat?, nf.toNat? with
      | some i, some a, some b => .mesh i w a b
      | _, _, _ => .ignored
  | ["vertex", id, j, xb, yb, zb] =>
      match id.toNat?, j.toNat?, parseHex8 xb, parseHex8 yb, parseHex8 zb with
      | some i, some j, some x, some y, some z => .vertex i j (x, y, z)
      | _, _, _, _, _ => .ignored
  | ["face", id, w, j, a, b, c] =>
      match id.toNat?, j.toNat?, a.toNat?, b.toNat?, c.toNat? with
      | some i, some j, some x, some y, some z => .face i j w (x, y, z)
      | _, _, _, _, _ => .ignored
  | _ => .ignored

/-! ### The independent MC computation -/

/-- Bourke corner offsets, verbatim from `MC_CORNER_OFFSETS` in
    `src/tinyvdb_mesh.c`. -/
def cornerOffsets : Array (Nat × Nat × Nat) :=
  #[(0, 0, 0), (1, 0, 0), (1, 1, 0), (0, 1, 0),
    (0, 0, 1), (1, 0, 1), (1, 1, 1), (0, 1, 1)]

def sampleAt (g : Grid) (x y z : Nat) : Rat :=
  g.samples[((z * g.ny + y) * g.nx + x)]!

/-- The case index of a cell: bit c is set iff corner c is below iso (the C
    `mesh_cube_case` rule). -/
def caseIndex (g : Grid) (x y z : Nat) : Nat :=
  (List.range 8).foldl (fun k c =>
    let (dx, dy, dz) := cornerOffsets[c]!
    if sampleAt g (x + dx) (y + dy) (z + dz) < g.iso then k + 2 ^ c else k) 0

/-- A local cube edge as a grid edge: its lower lattice point and its axis.
    Uses `Vdb.McTable.mcEdgeVerts` (the C Bourke numbering). -/
def edgeLower (x y z e : Nat) : (Nat × Nat × Nat) × Fin 3 :=
  let (a, b) := McTable.mcEdgeVerts[e]!
  let (ax, ay, az) := cornerOffsets[a]!
  let (bx, byy, bz) := cornerOffsets[b]!
  let lo := (x + min ax bx, y + min ay byy, z + min az bz)
  let axis : Fin 3 :=
    if ax ≠ bx then ⟨0, by decide⟩ else if ay ≠ byy then ⟨1, by decide⟩ else ⟨2, by decide⟩
  (lo, axis)

def otherEnd (lo : Nat × Nat × Nat) (axis : Fin 3) : Nat × Nat × Nat :=
  match axis.val with
  | 0 => (lo.1 + 1, lo.2.1, lo.2.2)
  | 1 => (lo.1, lo.2.1 + 1, lo.2.2)
  | _ => (lo.1, lo.2.1, lo.2.2 + 1)

/-- The world coordinate of lattice point i along an axis (cell-centred). -/
def axisPos (g : Grid) (axis : Nat) (i : Nat) : Rat :=
  let base : Rat := match axis with | 0 => g.ox | 1 => g.oy | _ => g.oz
  base + ((i : Rat) + 1 / 2) * g.vs

/-- Exact-ℚ crossing position on a crossed grid edge. The interpolation
    parameter is `t = (iso - v0)/(v1 - v0)` clamped to [0,1], as in the C
    `mesh_edge_interpolate`; `Vdb.McWeld.vertex_pos_swap` makes the choice of
    lower endpoint immaterial. -/
def crossPos (g : Grid) (lo : Nat × Nat × Nat) (axis : Fin 3) : R3 :=
  let hi := otherEnd lo axis
  let v0 := sampleAt g lo.1 lo.2.1 lo.2.2
  let v1 := sampleAt g hi.1 hi.2.1 hi.2.2
  let t0 : Rat := (g.iso - v0) / (v1 - v0)
  let t : Rat := if t0 < 0 then 0 else if t0 > 1 then 1 else t0
  let base : R3 := ⟨axisPos g 0 lo.1, axisPos g 1 lo.2.1, axisPos g 2 lo.2.2⟩
  let step : R3 :=
    match axis.val with
    | 0 => ⟨g.vs, 0, 0⟩
    | 1 => ⟨0, g.vs, 0⟩
    | _ => ⟨0, 0, g.vs⟩
  ⟨base.x + t * step.x, base.y + t * step.y, base.z + t * step.z⟩

structure Expected where
  verts : Array R3 := #[]
  keys : Array Nat := #[]
  facesT : Array Tri := #[]
  facesO : Array Tri := #[]

def findKey (keys : Array Nat) (k : Nat) : Option Nat :=
  (List.range keys.size).find? (fun i => keys[i]! == k)

/-- The expected mesh, computed from the tables and the grid alone. -/
def expectedMesh (g : Grid) : Expected := Id.run do
  let mut e : Expected := {}
  if g.nx < 2 || g.ny < 2 || g.nz < 2 then return e
  for z in List.range (g.nz - 1) do
    for y in List.range (g.ny - 1) do
      for x in List.range (g.nx - 1) do
        let k := caseIndex g x y z
        let mask := McTable.mcEdgeTable[k]!
        if mask != 0 then
          let mut vmap : Array Nat := Array.replicate 12 0
          for eid in List.range 12 do
            if (mask / 2 ^ eid) % 2 == 1 then
              let (lo, axis) := edgeLower x y z eid
              let key := Vdb.GridEdge.key g.nx g.ny ⟨lo, axis⟩
              match findKey e.keys key with
              | some vid => vmap := vmap.set! eid vid
              | none =>
                  let vid := e.keys.size
                  e := { e with keys := e.keys.push key, verts := e.verts.push (crossPos g lo axis) }
                  vmap := vmap.set! eid vid
          for (a, b, c) in McTable.trisOf k do
            let f : Tri := (vmap[a]!, vmap[b]!, vmap[c]!)
            e := { e with facesT := e.facesT.push f, facesO := e.facesO.push (f.1, f.2.2, f.2.1) }
  return e

/-! ### Comparison helpers -/

def removeFirst {α : Type} [DecidableEq α] (x : α) : List α → Option (List α)
  | [] => none
  | y :: ys => if x == y then some ys else (removeFirst x ys).map (fun rest => y :: rest)

def multisetEqList {α : Type} [DecidableEq α] : List α → List α → Bool
  | _, [] => true
  | pool, x :: xs => match removeFirst x pool with
      | some rest => multisetEqList rest xs
      | none => false

def multisetEqArray {α : Type} [DecidableEq α] (a b : Array α) : Bool :=
  if a.size != b.size then false else multisetEqList b.toList a.toList

def keyTriple (keys : Array Nat) (t : Tri) : Option Tri :=
  match keys[t.1]?, keys[t.2.1]?, keys[t.2.2]? with
  | some a, some b, some c => some (a, b, c)
  | _, _, _ => none

def keyTriples (faces : Array Tri) (keys : Array Nat) : Option (Array Tri) := Id.run do
  let mut out : Array Tri := #[]
  for t in faces do
    match keyTriple keys t with
    | some kt => out := out.push kt
    | none => return none
  return some out

def topoEq (cfaces efaces : Array Tri) (keys : Array Nat) : Bool :=
  match keyTriples cfaces keys, keyTriples efaces keys with
  | some c, some e => multisetEqArray c e
  | _, _ => false

def max3 (a b c : Float) : Float := max a (max b c)

/-- Returns (bit-exact?, max component error). -/
def posCheck (b : UInt32 × UInt32 × UInt32) (e : R3) : Bool × Float :=
  let cx := f32Float b.1
  let cy := f32Float b.2.1
  let cz := f32Float b.2.2
  let ex := ratFloat e.x
  let ey := ratFloat e.y
  let ez := ratFloat e.z
  let err := max3 (Float.abs (cx - ex)) (Float.abs (cy - ey)) (Float.abs (cz - ez))
  let bits : Bool := Float32.toBits (Float.toFloat32 ex) == b.1
    && Float32.toBits (Float.toFloat32 ey) == b.2.1
    && Float32.toBits (Float.toFloat32 ez) == b.2.2
  (bits, err)

def posTol (b : UInt32 × UInt32 × UInt32) : Float :=
  let m := max3 (Float.abs (f32Float b.1)) (Float.abs (f32Float b.2.1)) (Float.abs (f32Float b.2.2))
  1e-6 * (if m > 1 then m else 1)

end McTopologyCheck
end Vdb

/-- Twin executable: reads the C dump from argv[0] and prints
    `fields=... verts=... faces_table=... faces_outward=... exact_pos=...
     bad_count=... bad_index_table=... bad_index_outward=...
     bad_topo_table=... bad_topo_outward=... bad_pos=... max_pos_err=...`
    The `main` lives in the root namespace, as the Lake executable entry
    point resolves it there. -/
def main (argv : List String) : IO Unit := do
  match argv with
  | [path] =>
      let raw ← IO.FS.readFile path
      let mut nfields := 0
      let mut cases : Array Vdb.McTopologyCheck.Case := #[]
      for line in raw.splitOn "\n" do
        match Vdb.McTopologyCheck.parseLine line with
        | .fields n => nfields := n
        | .caseHead id g =>
            while cases.size <= id do cases := cases.push {}
            cases := cases.set! id { cases[id]! with grid := g }
        | .sample id idx bits =>
            if id < cases.size then
              let c := cases[id]!
              let s := c.grid.samples
              let s' := if idx < s.size then s.set! idx (Vdb.McTopologyCheck.f32Rat bits)
                        else s.push (Vdb.McTopologyCheck.f32Rat bits)
              cases := cases.set! id { c with grid := { c.grid with samples := s' } }
        | .mesh id w nv nf =>
            if id < cases.size then
              let c := cases[id]!
              let nfT := if w == "TABLE" then nf else c.repNfT
              let nfO := if w == "OUTWARD" then nf else c.repNfO
              cases := cases.set! id { c with repNv := nv, repNfT := nfT, repNfO := nfO }
        | .vertex id j v =>
            if id < cases.size then
              let c := cases[id]!
              let vs := c.verts
              let vs' := if j < vs.size then vs.set! j v else vs.push v
              cases := cases.set! id { c with verts := vs' }
        | .face id j w t =>
            if id < cases.size then
              let c := cases[id]!
              if w == "TABLE" then
                let fs := c.facesT
                cases := cases.set! id { c with facesT := if j < fs.size then fs.set! j t else fs.push t }
              else if w == "OUTWARD" then
                let fs := c.facesO
                cases := cases.set! id { c with facesO := if j < fs.size then fs.set! j t else fs.push t }
        | .ignored => pure ()
      let mut badCount := 0
      let mut badIndexT := 0
      let mut badIndexO := 0
      let mut badTopoT := 0
      let mut badTopoO := 0
      let mut badPos := 0
      let mut exactPos := 0
      let mut verts := 0
      let mut facesT := 0
      let mut facesO := 0
      let mut maxErr : Float := 0
      for c in cases do
        let g := c.grid
        let e := Vdb.McTopologyCheck.expectedMesh g
        if g.samples.size != g.nx * g.ny * g.nz then badCount := badCount + 1
        if e.verts.size != c.verts.size || e.verts.size != c.repNv then badCount := badCount + 1
        if e.facesT.size != c.facesT.size || e.facesT.size != c.repNfT then badCount := badCount + 1
        if e.facesO.size != c.facesO.size || e.facesO.size != c.repNfO then badCount := badCount + 1
        verts := verts + e.verts.size
        facesT := facesT + e.facesT.size
        facesO := facesO + e.facesO.size
        for j in List.range (min e.facesT.size c.facesT.size) do
          if e.facesT[j]! != c.facesT[j]! then badIndexT := badIndexT + 1
        for j in List.range (min e.facesO.size c.facesO.size) do
          if e.facesO[j]! != c.facesO[j]! then badIndexO := badIndexO + 1
        if !Vdb.McTopologyCheck.topoEq c.facesT e.facesT e.keys then badTopoT := badTopoT + 1
        if !Vdb.McTopologyCheck.topoEq c.facesO e.facesO e.keys then badTopoO := badTopoO + 1
        for j in List.range (min e.verts.size c.verts.size) do
          let (bits, err) := Vdb.McTopologyCheck.posCheck c.verts[j]! e.verts[j]!
          if bits then exactPos := exactPos + 1
          if err > maxErr then maxErr := err
          if err > Vdb.McTopologyCheck.posTol c.verts[j]! then badPos := badPos + 1
      if cases.size != nfields then badCount := badCount + 1
      IO.println s!"fields={cases.size} verts={verts} faces_table={facesT} faces_outward={facesO} exact_pos={exactPos} bad_count={badCount} bad_index_table={badIndexT} bad_index_outward={badIndexO} bad_topo_table={badTopoT} bad_topo_outward={badTopoO} bad_pos={badPos} max_pos_err={maxErr} max_pos_err_bits={Float.toBits maxErr}"
      IO.println "stages_unmirrored=count-pass,rolling-hash-cache,arena-layout,double-intermediate"
      if badCount > 0 || badIndexT > 0 || badIndexO > 0 || badTopoT > 0 || badTopoO > 0 ||
         badPos > 0 || verts == 0 || facesT == 0 || facesO == 0 then
        throw (IO.userError "mc topology differential check failed")
  | _ =>
      IO.println "usage: mctopocheck <c-output-file>"
      throw (IO.userError "mctopocheck: bad args")
