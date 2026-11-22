/-
  TinyVDB - Lean 4 formalization of the `.vdb` file format
  and the volume operators.

  BOUNDED sparse/tree marching-cubes TOPOLOGY differential twin (tier 3).
  Driven by `scripts/check_mc_sparse_topology.sh` against
  `scripts/mc_sparse_topology_c.c`, which calls the REAL
  `tvdb_grid_volume_to_mesh` (tool_surface_cells + tool_mesh in
  `src/tinyvdb_sparse_tools.c`) on a deterministic procedural sphere tree
  (16^3 index lattice, radius 4.5, ~380 stored voxels) and dumps every lattice
  sample as the tree reports it, every emitted vertex position (Float32 bits)
  with its geometrically recovered welded key, and every emitted triangle.

  This is an independent computation from the landed tables, not a replay of
  the C indices:

    * the case of each cell is recomputed from the decoded samples (bit c set
      iff corner c is below iso, Bourke corner order);
    * the used cube edges come from `Vdb.McTable.mcEdgeTable` (equal to the
      sign-change mask by T-MC-EDGE) and the triangles from
      `Vdb.McTable.trisOf` (T-MC-COUNT / T-MC-COMPLETE);
    * a welded key is the 4-tuple (lower lattice corner, axis), the sparse
      analogue of `Vdb.McWeld.GridEdge.key` (the C map keys on the same
      lower-corner triple, one map per axis, with x-slab ring reuse that does
      not change first-insert identity);
    * vertex ids are allocated on first appearance of a key while sweeping
      cells and cube edges, and the crossing position is the exact-Q
      interpolation of the two decoded Float32 samples mapped by the grid
      transform (`Vdb.McWeld.vertex_pos_swap` makes the choice of endpoint
      immaterial).

  Compared: vertex/face counts, triangle multisets by welded key (exact, as
  index-key multisets, so the C's internal cell-walk vertex numbering need not
  be mirrored), and positions with an explicit Float32 tolerance (plus an
  exact-bit counter). The winding flip is taken from the C determinant and
  cross-checked against the product of the dumped scales.

  NOT mirrored (reported loudly, never counted as a pass): the region-growing
  collect walk and its owner-side classification, the x-slab ring cache and
  open-addressed hash slots, the count-then-emit allocation, the adaptive
  clustering (adapt = 0 here), and the double-precision intermediate of the C
  interpolation (the twin uses exact rationals, hence a Float32 tolerance).
  The C's Float32 sample and transform values ARE mirrored bit-exactly via
  `f32Rat` / `f64Rat`.

  Coverage: one analytic sphere field on a 16^3 tree with two transforms
  (isotropic and y-stretched). NOT covered: arbitrary tree layouts, tile
  boundaries with span > 1 on the surface, NaN/Inf rejection, winding beyond
  the single determinant-derived value, adaptive clustering, exact-iso
  samples, or very large trees. No theorem is weakened.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.McTable
import Vdb.McWeld
import Mathlib.Tactic

namespace Vdb
namespace McSparseTopologyCheck

abbrev Tri := Nat × Nat × Nat
abbrev EKey := Nat × Nat × Nat × Nat
abbrev KeyTri := EKey × EKey × EKey

structure R3 where
  x : Rat
  y : Rat
  z : Rat
  deriving Inhabited

/-! ### Exact Float32 / Float64 decoding -/

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

def f64Rat (bits : UInt64) : Rat :=
  let neg : Bool := (bits >>> 63) != 0
  let exp : Nat := ((bits >>> 52) &&& 0x7ff).toNat
  let frac : Nat := (bits &&& 0xfffffffffffff).toNat
  let mag : Rat :=
    if exp == 0 then
      Rat.divInt (frac : Int) ((2 ^ (1074 : Nat) : Nat) : Int)
    else if exp == 2047 then
      0
    else
      let m : Nat := ((1 : Nat) <<< 52) ||| frac
      let e : Int := (exp : Int) - 1023 - 52
      if e >= 0 then Rat.divInt ((m * 2 ^ e.toNat : Nat) : Int) 1
      else Rat.divInt (m : Int) ((2 ^ (-e).toNat : Nat) : Int)
  if neg then -mag else mag

def f32Float (bits : UInt32) : Float := Float32.toFloat (Float32.ofBits bits)
def ratFloat (q : Rat) : Float := Float.ofInt q.num / Float.ofNat q.den

/-! ### The parsed C dump -/

structure Grid where
  n : Nat := 0
  iso : Rat := 0
  scale : Array Rat := #[0, 0, 0]
  trans : Array Rat := #[0, 0, 0]
  flip : Nat := 0
  samples : Array Rat := #[]

structure Case where
  grid : Grid := {}
  repNv : Nat := 0
  repNf : Nat := 0
  verts : Array (UInt32 × UInt32 × UInt32) := #[]
  ckeys : Array EKey := #[]
  faces : Array Tri := #[]
  deriving Inhabited

inductive Line where
  | fields (n : Nat)
  | caseHead (id n : Nat) (iso : Rat) (scale trans : Array Rat) (flip : Nat)
  | voxel (id x y z act : Nat) (bits : UInt32)
  | mesh (id nv nf : Nat)
  | vertex (id j : Nat) (v : UInt32 × UInt32 × UInt32) (k : EKey)
  | face (id j : Nat) (t : Tri)
  | ignored

def parseHex (s : String) : Option Nat :=
  let hexVal (ch : Char) : Option Nat :=
    match ch with
    | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
    | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
    | '8' => some 8 | '9' => some 9 | 'a' => some 10 | 'b' => some 11
    | 'c' => some 12 | 'd' => some 13 | 'e' => some 14 | 'f' => some 15
    | 'A' => some 10 | 'B' => some 11 | 'C' => some 12
    | 'D' => some 13 | 'E' => some 14 | 'F' => some 15
    | _ => none
  s.toList.foldlM (fun acc ch => (hexVal ch).map (acc * 16 + ·)) 0

def parseHex32 (s : String) : Option UInt32 :=
  if s.length == 8 then (parseHex s).map (fun v => UInt32.ofNat v) else none

def parseHex64 (s : String) : Option UInt64 :=
  if s.length == 16 then (parseHex s).map (fun v => UInt64.ofNat v) else none

def parseLine (s : String) : Line :=
  let t := s.splitOn " "
  match t with
  | ["fields", n] =>
      match n.toNat? with
      | some v => .fields v
      | _ => .ignored
  | ["case", id, "n", n, "iso", iso, "s0", s0, "s1", s1, "s2", s2,
     "t0", t0, "t1", t1, "t2", t2, "flip", fl] =>
      match id.toNat?, n.toNat?, parseHex32 iso,
            parseHex64 s0, parseHex64 s1, parseHex64 s2,
            parseHex64 t0, parseHex64 t1, parseHex64 t2, fl.toNat? with
      | some i, some nn, some bi, some a0, some a1, some a2,
        some b0, some b1, some b2, some f =>
          .caseHead i nn (f32Rat bi) #[f64Rat a0, f64Rat a1, f64Rat a2]
            #[f64Rat b0, f64Rat b1, f64Rat b2] f
      | _, _, _, _, _, _, _, _, _, _ => .ignored
  | ["voxel", id, x, y, z, "act", act, "val", b] =>
      match id.toNat?, x.toNat?, y.toNat?, z.toNat?, act.toNat?, parseHex32 b with
      | some i, some a, some bb, some c, some d, some w => .voxel i a bb c d w
      | _, _, _, _, _, _ => .ignored
  | ["mesh", id, "nv", nv, "nf", nf] =>
      match id.toNat?, nv.toNat?, nf.toNat? with
      | some i, some a, some b => .mesh i a b
      | _, _, _ => .ignored
  | ["vertex", id, j, xb, yb, zb, kx, ky, kz, ax] =>
      match id.toNat?, j.toNat?, parseHex32 xb, parseHex32 yb, parseHex32 zb,
            kx.toNat?, ky.toNat?, kz.toNat?, ax.toNat? with
      | some i, some jj, some x, some y, some z,
        some a, some b, some c, some d => .vertex i jj (x, y, z) (a, b, c, d)
      | _, _, _, _, _, _, _, _, _ => .ignored
  | ["face", id, j, a, b, c] =>
      match id.toNat?, j.toNat?, a.toNat?, b.toNat?, c.toNat? with
      | some i, some jj, some x, some y, some z => .face i jj (x, y, z)
      | _, _, _, _, _ => .ignored
  | _ => .ignored

/-! ### The independent sparse MC computation -/

/-- Bourke / `tool_corners` corner offsets, verbatim from
    `MC_CORNER_OFFSETS` in `src/tinyvdb_mesh.c`. -/
def cornerOffsets : Array (Nat × Nat × Nat) :=
  #[(0, 0, 0), (1, 0, 0), (1, 1, 0), (0, 1, 0),
    (0, 0, 1), (1, 0, 1), (1, 1, 1), (0, 1, 1)]

def sampleAt (g : Grid) (x y z : Nat) : Rat :=
  g.samples[((z * g.n + y) * g.n + x)]!

def caseIndex (g : Grid) (x y z : Nat) : Nat :=
  (List.range 8).foldl (fun k c =>
    let (dx, dy, dz) := cornerOffsets[c]!
    if sampleAt g (x + dx) (y + dy) (z + dz) < g.iso then k + 2 ^ c else k) 0

/-- A local cube edge as a welded key (lower lattice corner + axis). -/
def edgeKey (x y z e : Nat) : EKey :=
  let (a, b) := McTable.mcEdgeVerts[e]!
  let (ax, ay, az) := cornerOffsets[a]!
  let (bx, byy, bz) := cornerOffsets[b]!
  let lo := (x + min ax bx, y + min ay byy, z + min az bz)
  let axis : Nat :=
    if ax ≠ bx then 0 else if ay ≠ byy then 1 else 2
  (lo.1, lo.2.1, lo.2.2, axis)

/-- The exact-Q crossing position on a crossed lattice edge, mapped through
    the (diagonal) grid transform. The interpolation parameter is
    `t = (iso - v0)/(v1 - v0)` clamped to [0,1], with `v0` the lower endpoint
    along the edge axis; `Vdb.McWeld.vertex_pos_swap` makes that choice
    immaterial. -/
def crossPos (g : Grid) (x y z e : Nat) : R3 :=
  let (a, b) := McTable.mcEdgeVerts[e]!
  let (ax, ay, az) := cornerOffsets[a]!
  let (k0, k1, k2, axis) := edgeKey x y z e
  let loCorner := if (match axis with | 0 => ax | 1 => ay | _ => az) = 0 then a else b
  let hiCorner := if loCorner = a then b else a
  let v0 := sampleAt g (x + cornerOffsets[loCorner]!.1)
                       (y + cornerOffsets[loCorner]!.2.1)
                       (z + cornerOffsets[loCorner]!.2.2)
  let v1 := sampleAt g (x + cornerOffsets[hiCorner]!.1)
                       (y + cornerOffsets[hiCorner]!.2.1)
                       (z + cornerOffsets[hiCorner]!.2.2)
  let t0 : Rat := (g.iso - v0) / (v1 - v0)
  let t : Rat := if t0 < 0 then 0 else if t0 > 1 then 1 else t0
  let lo : Rat := match axis with | 0 => k0 | 1 => k1 | _ => k2
  let q : Array Rat :=
    match axis with
    | 0 => #[lo + t, k1, k2]
    | 1 => #[k0, lo + t, k2]
    | _ => #[k0, k1, lo + t]
  ⟨g.trans[0]! + g.scale[0]! * q[0]!,
   g.trans[1]! + g.scale[1]! * q[1]!,
   g.trans[2]! + g.scale[2]! * q[2]!⟩

structure Expected where
  verts : Array R3 := #[]
  keys : Array EKey := #[]
  faces : Array Tri := #[]

def findKey (keys : Array EKey) (k : EKey) : Option Nat :=
  (List.range keys.size).find? (fun i => keys[i]! == k)

def expectedMesh (g : Grid) (flip : Bool) : Expected := Id.run do
  let mut e : Expected := {}
  if g.n < 2 then return e
  for z in List.range (g.n - 1) do
    for y in List.range (g.n - 1) do
      for x in List.range (g.n - 1) do
        let k := caseIndex g x y z
        let mask := McTable.mcEdgeTable[k]!
        if mask != 0 then
          let mut vmap : Array Nat := Array.replicate 12 0
          for eid in List.range 12 do
            if (mask / 2 ^ eid) % 2 == 1 then
              let key := edgeKey x y z eid
              match findKey e.keys key with
              | some vid => vmap := vmap.set! eid vid
              | none =>
                  let vid := e.keys.size
                  e := { e with keys := e.keys.push key,
                                verts := e.verts.push (crossPos g x y z eid) }
                  vmap := vmap.set! eid vid
          for (a, b, c) in McTable.trisOf k do
            let tri : Tri := if flip then (vmap[a]!, vmap[c]!, vmap[b]!)
                             else (vmap[a]!, vmap[b]!, vmap[c]!)
            e := { e with faces := e.faces.push tri }
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

def keyTriple (keys : Array EKey) (t : Tri) : Option KeyTri :=
  match keys[t.1]?, keys[t.2.1]?, keys[t.2.2]? with
  | some a, some b, some c => some (a, b, c)
  | _, _, _ => none

def keyTriples (faces : Array Tri) (keys : Array EKey) : Option (Array KeyTri) := Id.run do
  let mut out : Array KeyTri := #[]
  for t in faces do
    match keyTriple keys t with
    | some kt => out := out.push kt
    | none => return none
  return some out

/-- Compare the C emitted faces against the expected faces as ordered triples
    of welded keys (the C's internal vertex numbering is intentionally not
    mirrored). -/
def topoEq (cfaces : Array Tri) (ckeys : Array EKey)
           (efaces : Array Tri) (ekeys : Array EKey) : Bool :=
  match keyTriples cfaces ckeys, keyTriples efaces ekeys with
  | some c, some e => multisetEqArray c e
  | _, _ => false

def findKeyPos (keys : Array EKey) (verts : Array R3) (k : EKey) : Option R3 :=
  match findKey keys k with
  | some i => verts[i]?
  | none => none

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
  let m := max3 (Float.abs (f32Float b.1)) (Float.abs (f32Float b.2.1))
                (Float.abs (f32Float b.2.2))
  2e-4 * (if m > 1 then m else 1)

end McSparseTopologyCheck
end Vdb

/-- Twin executable: reads the C dump from argv[0] and prints the explicit
    counters. The `main` lives in the root namespace, as the Lake executable
    entry point resolves it there. -/
def main (argv : List String) : IO Unit := do
  match argv with
  | [path] =>
      let raw ← IO.FS.readFile path
      let mut nfields := 0
      let mut cases : Array Vdb.McSparseTopologyCheck.Case := #[]
      for line in raw.splitOn "\n" do
        match Vdb.McSparseTopologyCheck.parseLine line with
        | .fields n => nfields := n
        | .caseHead id n iso scale trs flip =>
            while cases.size <= id do cases := cases.push {}
            cases := cases.set! id { cases[id]! with
              grid := { n := n, iso := iso, scale := scale, trans := trs, flip := flip } }
        | .voxel id x y z _ bits =>
            if id < cases.size then
              let c := cases[id]!
              let s := c.grid.samples
              let idx := (z * c.grid.n + y) * c.grid.n + x
              let s' := if idx < s.size then s.set! idx (Vdb.McSparseTopologyCheck.f32Rat bits)
                        else s.push (Vdb.McSparseTopologyCheck.f32Rat bits)
              cases := cases.set! id { c with grid := { c.grid with samples := s' } }
        | .mesh id nv nf =>
            if id < cases.size then
              let c := cases[id]!
              cases := cases.set! id { c with repNv := nv, repNf := nf }
        | .vertex id j v k =>
            if id < cases.size then
              let c := cases[id]!
              let vs := c.verts
              let ks := c.ckeys
              cases := cases.set! id { c with
                verts := if j < vs.size then vs.set! j v else vs.push v,
                ckeys := if j < ks.size then ks.set! j k else ks.push k }
        | .face id j t =>
            if id < cases.size then
              let c := cases[id]!
              let fs := c.faces
              cases := cases.set! id { c with
                faces := if j < fs.size then fs.set! j t else fs.push t }
        | .ignored => pure ()
      let mut badCount := 0
      let mut badKey := 0
      let mut badTopo := 0
      let mut badPos := 0
      let mut badFlip := 0
      let mut exactPos := 0
      let mut verts := 0
      let mut faces := 0
      let mut maxErr : Float := 0
      for c in cases do
        let g := c.grid
        let scaleProd := g.scale[0]! * g.scale[1]! * g.scale[2]!
        let flip := scaleProd > 0
        let dumpFlip := g.flip == 1
        if flip != dumpFlip then badFlip := badFlip + 1
        let e := Vdb.McSparseTopologyCheck.expectedMesh g flip
        if g.samples.size != g.n * g.n * g.n then badCount := badCount + 1
        if e.verts.size != c.verts.size || e.verts.size != c.repNv then badCount := badCount + 1
        if e.faces.size != c.faces.size || e.faces.size != c.repNf then badCount := badCount + 1
        verts := verts + e.verts.size
        faces := faces + e.faces.size
        if !Vdb.McSparseTopologyCheck.topoEq c.faces c.ckeys e.faces e.keys then
          badTopo := badTopo + 1
        for j in List.range c.verts.size do
          let k := c.ckeys[j]!
          match Vdb.McSparseTopologyCheck.findKeyPos e.keys e.verts k with
          | none => badKey := badKey + 1
          | some ep =>
              let (bits, err) := Vdb.McSparseTopologyCheck.posCheck c.verts[j]! ep
              if bits then exactPos := exactPos + 1
              if err > maxErr then maxErr := err
              if err > Vdb.McSparseTopologyCheck.posTol c.verts[j]! then badPos := badPos + 1
      if cases.size != nfields then badCount := badCount + 1
      IO.println s!"fields={cases.size} verts={verts} faces={faces} exact_pos={exactPos} bad_count={badCount} bad_key={badKey} bad_topo={badTopo} bad_pos={badPos} bad_flip={badFlip} max_pos_err={maxErr} max_pos_err_bits={Float.toBits maxErr}"
      IO.println "stages_unmirrored=region-collect,owner-classify,x-slab-cache,count-emit,tool-adapt,double-intermediate"
      if badCount > 0 || badKey > 0 || badTopo > 0 || badPos > 0 || badFlip > 0 ||
         verts == 0 || faces == 0 then
        throw (IO.userError "mc sparse topology differential check failed")
  | _ =>
      IO.println "usage: mcsparsetopocheck <c-output-file>"
      throw (IO.userError "mcsparsetopocheck: bad args")
