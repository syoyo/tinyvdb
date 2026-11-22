/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  C-BVH differential harness (model half): exact-ℚ twin of the pruned
  closest-triangle traversal `tvdb_bvh_closest` in `src/tinyvdb_mesh.c`, the
  acceleration used by dense mesh→SDF. It consumes the dump of
  `scripts/meshsdf_bvh_c.c`, which calls the *real* static C routines (the
  driver #includes tinyvdb_mesh.c) on the exact cell centres of the dense
  lattice and prints, per query, the returned squared distance (float bits),
  winning face index and closest-feature tag.

  WHAT IS MIRRORED (exact ℚ):
    * the AABB lower bound `boxDist` and the strict `best < boxDist` prune;
    * strict improvement with the lowest-face-index tie-break (`Vdb.better`);
    * the pruned traversal itself: the executable calls `Vdb.search`, the
      definition proved equal to brute force by `Vdb.search_eq_brute`;
    * seed materialization: a valid dumped seed face is re-measured at the
      current rational query point before it becomes the running candidate;
    * the per-face AABB hypothesis `boxDist (faceBox f) p ≤ d f p` of
      `search_eq_brute`, checked at runtime for every (face, query) pair;
    * tree well-formedness (boxes are unions of child/face boxes), checked at
      runtime; the twin uses a deterministic balanced face-index split.

  WHAT IS NOT MIRRORED (loudly reported, not silently assumed):
    * the C build heuristic (median split on the widest centroid axis): the
      theorem makes the tree shape irrelevant to the result, so the twin uses
      a balanced split. `bvh_*` stats from the dump are printed for evidence;
    * the C DFS stack order (farther child pushed first): also irrelevant by
      the order-independent `(distance, index)` minimum;
    * the Float32 kernel (`tri_closest_point_c`, `dot_c`,
      `tvdb_aabb_dist_sq`) and the double-precision fallback: the twin uses
      exact rational arithmetic on the dyadic Float32 inputs. Distances are
      therefore compared within a documented tolerance, not bit-exactly:
        |qLean - qC| <= (qC + 1) / 10000      (1e-4 relative + absolute).
      Face index and closest-feature tag are compared exactly on every query.
      A disagreement with agreeing distance is reported loudly as an
      unmirrored Float32 tie (`f32_tie_face` / `f32_tie_feature`), never as a
      pass; only distance-disagreeing mismatches fail the gate.

  Printed: a NOT MIRRORED banner, tree evidence lines, up to four tie examples
  and one counters line (see the gate script for the exact expected values).
  `scripts/check_meshsdf_bvh.sh` drives both halves.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/

import Vdb.Bvh

namespace Vdb

/-- Exact rational 3-vector (Float32 dump values are dyadic rationals). -/
abbrev Q3 := Fin 3 → ℚ

def vsub (a b : Q3) : Q3 := fun i => a i - b i
def vadd (a b : Q3) : Q3 := fun i => a i + b i
def vscale (a : Q3) (s : ℚ) : Q3 := fun i => a i * s
def dotq (a b : Q3) : ℚ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2
def dist2 (a b : Q3) : ℚ := let d := vsub a b; dotq d d

/-- Parse exactly 8 lowercase hex digits into a `UInt32` bit pattern. -/
def parseHex8 (s : String) : Option UInt32 :=
  match s.toList with
  | [c0, c1, c2, c3, c4, c5, c6, c7] =>
      let hexVal (c : Char) : Option UInt32 :=
        match c with
        | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
        | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
        | '8' => some 8 | '9' => some 9 | 'a' => some 10 | 'b' => some 11
        | 'c' => some 12 | 'd' => some 13 | 'e' => some 14 | 'f' => some 15
        | _ => none
      [c0, c1, c2, c3, c4, c5, c6, c7].foldlM (fun acc c => (hexVal c).map (acc * 16 + ·)) 0
  | _ => none

/-- Exact rational value of an IEEE-754 binary32 bit pattern. Subnormals and
    normals are dyadic and therefore exact in ℚ. Inf/NaN map to 0 and are
    rejected by the finite-value checks in the corpus. -/
def ratOfF32Bits (bits : UInt32) : ℚ :=
  let sgn : ℚ := if bits &&& 0x80000000 != 0 then -1 else 1
  let e := (bits >>> 23) &&& 0xff
  let m : ℚ := (bits &&& 0x7fffff).toNat
  if e == 0 then sgn * m / (2 : ℚ) ^ 149
  else if e == 255 then 0
  else sgn * ((2 : ℚ) ^ 23 + m) * (2 : ℚ) ^ ((e.toNat : Int) - 150)

/-- One triangle and one closed mesh from the dump. -/
structure Tri where
  a : Nat
  b : Nat
  c : Nat
deriving Inhabited

/-- `Array.get!` on Box needs an Inhabited witness; Box comes from Bvh.lean. -/
instance : Inhabited Box := ⟨{ lo := fun _ => 0, hi := fun _ => 0 }⟩

structure MeshData where
  id : Nat := 0
  verts : Array Q3 := #[]
  faces : Array Tri := #[]
  nx : Nat := 0
  ny : Nat := 0
  nz : Nat := 0
  ox : ℚ := 0
  oy : ℚ := 0
  oz : ℚ := 0
  h : ℚ := 0
  bvhNodes : Nat := 0
  bvhPrims : Nat := 0
  bvhDepth : Nat := 0

structure Query where
  id : Nat := 0
  i : Nat := 0
  p : Q3 := ![0, 0, 0]
  sf : Int := -1
  rd : UInt32 := 0
  rf : Nat := 0
  rfeat : Nat := 6

inductive Line where
  | params (id nv nf nx ny nz : Nat) (ox oy oz h : ℚ)
  | vertex (id j : Nat) (v : Q3)
  | face (id j a b c : Nat)
  | bvh (id nodes prims depth : Nat)
  | query (q : Query)

def parseLine (s : String) : Option Line := do
  match s.splitOn " " with
  | ["mesh", mi, "params", "nv", nv, "nf", nf, "nx", nx, "ny", ny, "nz", nz,
     "ox", ox, "oy", oy, "oz", oz, "h", hh] =>
      let id ← mi.toNat?
      let nv' ← nv.toNat?
      let nf' ← nf.toNat?
      let nx' ← nx.toNat?
      let ny' ← ny.toNat?
      let nz' ← nz.toNat?
      let oxb ← parseHex8 ox
      let oyb ← parseHex8 oy
      let ozb ← parseHex8 oz
      let hb ← parseHex8 hh
      pure (.params id nv' nf' nx' ny' nz' (ratOfF32Bits oxb) (ratOfF32Bits oyb)
              (ratOfF32Bits ozb) (ratOfF32Bits hb))
  | ["mesh", mi, "vertex", sj, x, y, z] =>
      let id ← mi.toNat?
      let j ← sj.toNat?
      let xb ← parseHex8 x
      let yb ← parseHex8 y
      let zb ← parseHex8 z
      pure (.vertex id j ![ratOfF32Bits xb, ratOfF32Bits yb, ratOfF32Bits zb])
  | ["mesh", mi, "face", sj, a, b, c] =>
      let id ← mi.toNat?
      let j ← sj.toNat?
      let av ← a.toNat?
      let bv ← b.toNat?
      let cv ← c.toNat?
      pure (.face id j av bv cv)
  | ["bvh", bi, "nodes", ns, "prims", ps, "maxdepth", ds] =>
      let id ← bi.toNat?
      let ns' ← ns.toNat?
      let ps' ← ps.toNat?
      let ds' ← ds.toNat?
      pure (.bvh id ns' ps' ds')
  | ["query", qi, qj, "px", px, "py", py, "pz", pz, "sf", sf, "rd", rd, "rf", rf, "rfeat", rfeat] =>
      let id ← qi.toNat?
      let j ← qj.toNat?
      let pxb ← parseHex8 px
      let pyb ← parseHex8 py
      let pzb ← parseHex8 pz
      let sf' ← sf.toInt?
      let rdb ← parseHex8 rd
      let rf' ← rf.toNat?
      let feat' ← rfeat.toNat?
      pure (.query { id := id, i := j,
                     p := ![ratOfF32Bits pxb, ratOfF32Bits pyb, ratOfF32Bits pzb],
                     sf := sf', rd := rdb, rf := rf', rfeat := feat' })
  | _ => none

/-- The AABB of one triangle, in exact ℚ. -/
def faceBox (vs : Array Q3) (t : Tri) : Box where
  lo := fun i => min (min (vs[t.a]! i) (vs[t.b]! i)) (vs[t.c]! i)
  hi := fun i => max (max (vs[t.a]! i) (vs[t.b]! i)) (vs[t.c]! i)

/-- Exact point-to-triangle squared distance and closest-feature tag, using the
    same Voronoi-region case analysis as `tri_closest_point_c` but over ℚ.
    Tags: 0/1/2 = vertex a/b/c, 3/4/5 = edge ab/ac/bc, 6 = face interior. -/
def triDist (p a b c : Q3) : ℚ × Nat :=
  let ab := vsub b a
  let ac := vsub c a
  let ap := vsub p a
  let d1 := dotq ab ap
  let d2 := dotq ac ap
  if d1 <= 0 && d2 <= 0 then (dist2 p a, 0)
  else
    let bp := vsub p b
    let d3 := dotq ab bp
    let d4 := dotq ac bp
    if d3 >= 0 && d4 <= d3 then (dist2 p b, 1)
    else
      let vc := d1 * d4 - d3 * d2
      if vc <= 0 && d1 >= 0 && d3 <= 0 then
        let cp := vadd a (vscale ab (d1 / (d1 - d3)))
        (dist2 p cp, 3)
      else
        let cp0 := vsub p c
        let d5 := dotq ab cp0
        let d6 := dotq ac cp0
        if d6 >= 0 && d5 <= d6 then (dist2 p c, 2)
        else
          let vb := d5 * d2 - d1 * d6
          if vb <= 0 && d2 >= 0 && d6 <= 0 then
            let cp := vadd a (vscale ac (d2 / (d2 - d6)))
            (dist2 p cp, 4)
          else
            let va := d3 * d6 - d5 * d4
            if va <= 0 && (d4 - d3) >= 0 && (d5 - d6) >= 0 then
              let cp := vadd b (vscale (vsub c b) ((d4 - d3) / ((d4 - d3) + (d5 - d6))))
              (dist2 p cp, 5)
            else
              let denom := 1 / (va + vb + vc)
              let cp := vadd (vadd a (vscale ab (vb * denom))) (vscale ac (vc * denom))
              (dist2 p cp, 6)

def faceDist (vs : Array Q3) (faces : Array Tri) (p : Q3) (f : Nat) : ℚ × Nat :=
  let t := faces[f]!
  triDist p vs[t.a]! vs[t.b]! vs[t.c]!

/-- Union of face boxes in the half-open range [lo,hi). -/
def unionBox (bs : Array Box) (lo hi : Nat) : Box :=
  (List.range (hi - lo - 1)).foldl (fun acc k =>
    let bx := bs[lo + k + 1]!
    { lo := fun i => min (acc.lo i) (bx.lo i),
      hi := fun i => max (acc.hi i) (bx.hi i) }) (bs[lo]!)

/-- A deterministic balanced BVH. Its shape deliberately does NOT mirror the
    C median split: `Vdb.search_eq_brute` makes the shape irrelevant. -/
def buildTree (bs : Array Box) (lo hi : Nat) : BvhTree :=
  if hi - lo <= 4 then
    .leaf (unionBox bs lo hi) ((List.range (hi - lo)).map (fun k => lo + k))
  else
    let mid := lo + (hi - lo) / 2
    .node (unionBox bs lo hi) (buildTree bs lo mid) (buildTree bs mid hi)

/-- Boolean form of `Box.sub` (the Prop in Bvh.lean is hidden behind a def, so
    typeclass-driven `decide` cannot unfold it at reducible transparency). -/
def boxSubBool (a b : Box) : Bool :=
  decide (b.lo 0 ≤ a.lo 0 ∧ a.hi 0 ≤ b.hi 0 ∧
          b.lo 1 ≤ a.lo 1 ∧ a.hi 1 ≤ b.hi 1 ∧
          b.lo 2 ≤ a.lo 2 ∧ a.hi 2 ≤ b.hi 2)

def wfCheck (bs : Array Box) : BvhTree → Bool
  | .leaf b fs => fs.all fun f => boxSubBool bs[f]! b
  | .node b l r => boxSubBool l.box b && boxSubBool r.box b
                     && wfCheck bs l && wfCheck bs r

/-- Running candidate. A valid dumped seed face is re-measured at this query
    point (matching C's seed materialization). A cold seed uses a rigorous
    upper bound on every face distance plus an unattainable face index. -/
def seedCandidate (vs : Array Q3) (faces : Array Tri) (p : Q3) (sf : Int) : Cand :=
  if sf >= 0 && sf < faces.size then
    let (d, _) := faceDist vs faces p sf.toNat
    (d, sf.toNat)
  else
    let bound := vs.foldl (fun acc v => max acc (dist2 p v)) 0
    (bound + 1, faces.size)

/-- The pruned traversal, in exact ℚ: the executable definition proved equal
    to brute force by `Vdb.search_eq_brute`. -/
def prunedSearch (vs : Array Q3) (faces : Array Tri) (tree : BvhTree)
    (p : Q3) (sf : Int) : Cand :=
  Vdb.search (fun f _ => (faceDist vs faces p f).1) p tree
    (seedCandidate vs faces p sf)

def withinTol (qLean qC : ℚ) : Bool :=
  let diff := if qLean >= qC then qLean - qC else qC - qLean
  decide (diff <= (qC + 1) / 10000)

/-- Assemble the meshes from a dump. -/
def parseDump (raw : String) : Array (Option MeshData) :=
  let n := 2
  let lines := (raw.splitOn "\n").filterMap parseLine
  lines.foldl (fun ms line =>
    match line with
    | .params id _nv _nf nx ny nz ox oy oz h =>
        let m := Option.getD (ms[id]!) ({ id := id } : MeshData)
        ms.set! id (some { m with nx := nx, ny := ny, nz := nz, ox := ox, oy := oy, oz := oz, h := h })
    | .vertex id j v =>
        let m := Option.getD (ms[id]!) ({ id := id } : MeshData)
        ms.set! id (some { m with verts := if m.verts.size > j then m.verts.set! j v else m.verts.push v })
    | .face id j a b c =>
        let m := Option.getD (ms[id]!) ({ id := id } : MeshData)
        let t : Tri := ⟨a, b, c⟩
        ms.set! id (some { m with faces := if m.faces.size > j then m.faces.set! j t else m.faces.push t })
    | .bvh id nodes prims depth =>
        let m := Option.getD (ms[id]!) ({ id := id } : MeshData)
        ms.set! id (some { m with bvhNodes := nodes, bvhPrims := prims, bvhDepth := depth })
    | .query _ => ms) (Array.replicate n (none : Option MeshData))

/-- Number of leaves of a tree (evidence line in main). -/
def leafCount : BvhTree → Nat
  | .leaf _ _ => 1
  | .node _ l r => leafCount l + leafCount r

end Vdb

def main (argv : List String) : IO Unit := do
  match argv with
  | [path] =>
      let raw ← IO.FS.readFile path
      let meshes := Vdb.parseDump raw
      let queries := (raw.splitOn "\n").filterMap Vdb.parseLine |>.filterMap fun l =>
        match l with | .query q => some q | _ => none
      IO.println "NOT MIRRORED: C build heuristic (median centroid split), DFS stack order, Float32 kernel (tri_closest_point_c / dot_c / AABB bound) and its double fallback; see module header."
      let mut boundOk := 0
      let mut wfOk := 0
      let mut searchEqBruteOk := 0
      let mut faceOk := 0
      let mut featureOk := 0
      let mut f32TieFace := 0
      let mut f32TieFeature := 0
      let mut distOk := 0
      let mut badFaceUnexplained := 0
      let mut badFeatureUnexplained := 0
      let mut badDist := 0
      for mesh? in meshes do
        let some m := mesh? | throw (IO.userError "missing mesh in dump")
        let boxes := m.faces.map (Vdb.faceBox m.verts)
        let tree := Vdb.buildTree boxes 0 m.faces.size
        if Vdb.wfCheck boxes tree then wfOk := wfOk + 1
        IO.println s!"bvh mesh {m.id}: nodes={m.bvhNodes} prims={m.bvhPrims} depth={m.bvhDepth} twin_leaves={Vdb.leafCount tree} wf={Vdb.wfCheck boxes tree}"
        for q in queries.filter (fun q => q.id == m.id) do
          -- hypothesis of Vdb.search_eq_brute, instantiated on this corpus
          let mut allBound := true
          for f in [:m.faces.size] do
            if allBound && !(decide (Vdb.boxDist boxes[f]! q.p <= (Vdb.faceDist m.verts m.faces q.p f).1)) then
              allBound := false
          if allBound then boundOk := boundOk + 1

          let d := fun f (_ : Vdb.P3) => (Vdb.faceDist m.verts m.faces q.p f).1
          let seed := Vdb.seedCandidate m.verts m.faces q.p q.sf
          let pruned := Vdb.search d q.p tree seed
          let brute := Vdb.brute d q.p seed tree
          if pruned == brute then searchEqBruteOk := searchEqBruteOk + 1

          let leanFace := pruned.2
          let leanFeature := (Vdb.faceDist m.verts m.faces q.p leanFace).2
          let cDsq := Vdb.ratOfF32Bits q.rd
          let dsqAgree := Vdb.withinTol pruned.1 cDsq
          if dsqAgree then distOk := distOk + 1 else badDist := badDist + 1
          if leanFace == q.rf then
            faceOk := faceOk + 1
            -- Same winning face: an exact-feature disagreement with agreeing
            -- distance is an unmirrored Float32 branch artifact.
            if leanFeature == q.rfeat then featureOk := featureOk + 1
            else if dsqAgree then f32TieFeature := f32TieFeature + 1
            else badFeatureUnexplained := badFeatureUnexplained + 1
          else if dsqAgree then
            -- Different face at the same distance: the exact tie-break picks
            -- the lower index, Float32 rounding on the C kernel breaks it
            -- differently. Loudly counted, never called a pass.
            f32TieFace := f32TieFace + 1
            if f32TieFace <= 4 then
              IO.println s!"F32-TIE-FACE mesh {m.id} query {q.i}: c={q.rf} lean={leanFace} dsq_c_bits={q.rd}"
          else
            badFaceUnexplained := badFaceUnexplained + 1
            if badFaceUnexplained <= 4 then
              IO.println s!"MISMATCH mesh {m.id} query {q.i}: face c={q.rf} lean={leanFace} dsq_c_bits={q.rd}"
      IO.println s!"queries={queries.length} wf_ok={wfOk} bound_ok={boundOk} search_eq_brute_ok={searchEqBruteOk} face_ok={faceOk} feature_ok={featureOk} f32_tie_face={f32TieFace} f32_tie_feature={f32TieFeature} dist_ok={distOk} bad_face_unexplained={badFaceUnexplained} bad_feature_unexplained={badFeatureUnexplained} bad_dist={badDist}"
      if badFaceUnexplained > 0 || badFeatureUnexplained > 0 || badDist > 0 || wfOk < meshes.size ||
         boundOk != queries.length || searchEqBruteOk != queries.length then
        throw (IO.userError "meshsdf-bvh differential check failed")
  | _ =>
      IO.println "usage: meshsdfbvhcheck <c-output-file>"
      throw (IO.userError "meshsdfbvhcheck: bad args")
