/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  BOUNDED sparse/tree mesh→volume differential harness (lane VS-1, first
  slice). This is the Lean half, driven by `scripts/check_treemeshsdf.sh`
  against `scripts/treemeshsdf_c.c`, which calls the real C API
  `tvdb_mesh_to_level_set` (`src/tinyvdb_sparse_tools.c`) on two closed meshes
  (a cube and an octahedron) and dumps:

    * the generated input mesh (vertices/faces as Float32 bit patterns),
    * the level-set options (voxel size and both band widths),
    * the barycentric seed generator's intermediates (per-face `steps` and the
      unique snapped seed voxels), exposed by a verbatim mirror of the C loop,
    * the C result counters and grid topology (background, active count,
      active index bounds),
    * the stored `(active, value bits)` at a fixed index lattice.

  SCOPE — this is deliberately a *value-level bounded twin*, not a full tree
  twin. It recomputes, from the dumped mesh alone and in exact `Rat`
  arithmetic, the final value that the C pipeline stores at each sampled
  lattice point: exact closest-triangle squared distance (min over the three
  vertices, three clamped edges and the plane projection), exact ray-casting
  inside/outside parity (orientation independent, like C's |winding| > 1/2),
  and the ±band clamp `signedFill_eq_clamp`. Active state is the exact
  keep-rule `d < band`.

  The barycentric SEED stage IS mirrored: the twin re-runs the C seeding loop
  in native IEEE-754 doubles with the same operation order (`ceil(2 l/h)`,
  barycentric samples, `floor(p/h + 1/2)` snap, dedup) and compares the
  per-face sample counts and the final seed set bit-exactly. The geometric
  justification (every surface point is within `2h/√3` of a seed) is proved,
  not assumed, in `Vdb.SeedCoverage`.

  The other C stages are NOT mirrored, and are reported by the printed
  `stages_unmirrored=` line: 6-neighbour dilation, the BVH closest-point search
  (including its Float32 closest-point kernel and the double `hypot` used for
  the distance), the fast/exact winding-number evaluation, signed flood fill
  reachability, tree construction/prune and the `tree_find` layout.
  Consequently values are compared with a small explicit tolerance (the C path
  rounds a double distance to Float32, while the twin uses exact rationals),
  while active flags and the seed set are compared bit-exactly. No theorem is
  weakened or changed by this harness.

  Printed: `meshes=<n> voxels=<n> badValue=<n> badActive=<n> badTopo=<n>`
           `exactBits=<n> maxErr=<decimal> maxErrBits=<hex>`
           `seeds=<n> badSeed=<n> badSteps=<n>`
           `stages_unmirrored=dilate,bvh,winding,floodfill,prune,tree-layout`
  The tolerance is `1e-6 * max(1, |c value|)`; in this slice 1406/1458 values
  are bit-exact, the remaining 52 differ by at most 2^-24, and both meshes'
  196 seeds and all 20 per-face sample counts match exactly.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/

namespace Vdb.TreeMeshSdfCheck

/-- Exact rational 3-vector. -/
structure R3 where
  x : Rat
  y : Rat
  z : Rat
  deriving Inhabited

def radd (a b : R3) : R3 := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩
def rsub (a b : R3) : R3 := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩
def rscale (a : R3) (s : Rat) : R3 := ⟨a.x * s, a.y * s, a.z * s⟩
def rdot (a b : R3) : Rat := a.x * b.x + a.y * b.y + a.z * b.z
def rcross (a b : R3) : R3 :=
  ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩
def rdist2 (a b : R3) : Rat := rdot (rsub a b) (rsub a b)

/-- Decode an IEEE-754 binary32 bit pattern to an exact rational. Zero,
    subnormals, normals and infinities/NaNs (the latter map to 0; the harness
    inputs are finite) are handled; no floating-point rounding is used. -/
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

/-- The Float32 bit pattern as a host `Float`, for tolerance reporting. -/
def f32Float (bits : UInt32) : Float := Float32.toFloat (Float32.ofBits bits)

/-- Clamp a rational to [0, 1]. -/
def clamp01 (t : Rat) : Rat :=
  if t < 0 then 0 else if t > 1 then 1 else t

/-- Closest point on segment `ab` to `p` (exact rational projection). -/
def closestSeg (p a b : R3) : R3 :=
  let ab := rsub b a
  let den := rdot ab ab
  let t := if den == 0 then 0 else clamp01 (rdot (rsub p a) ab / den)
  radd a (rscale ab t)

/-- Orthogonal projection of `p` onto the plane of triangle `abc`, but only
    when that projection lies inside the triangle (exact barycentric test).
    Outside the triangle the closest point is on an edge, which the edge
    candidates already cover. -/
def planeCandidate (p a b c : R3) : Option R3 :=
  let e1 := rsub b a
  let e2 := rsub c a
  let n := rcross e1 e2
  let den := rdot n n
  if den == 0 then none else
    let q := rsub p (rscale n (rdot (rsub p a) n / den))
    let d11 := rdot e1 e1
    let d12 := rdot e1 e2
    let d22 := rdot e2 e2
    let det := d11 * d22 - d12 * d12
    if det == 0 then none else
      let r := rsub q a
      let ru := rdot r e1
      let rv := rdot r e2
      let u := (ru * d22 - rv * d12) / det
      let v := (rv * d11 - ru * d12) / det
      if u >= 0 && v >= 0 && u + v <= 1 then some q else none

/-- Exact squared distance from `p` to triangle `abc`: the minimum over the
    three vertices, three clamped edge projections and the (in-triangle)
    plane projection. -/
def triDist2 (p a b c : R3) : Rat :=
  let cands : List (Option R3) := [some a, some b, some c,
                                   some (closestSeg p a b), some (closestSeg p a c),
                                   some (closestSeg p b c), planeCandidate p a b c]
  match (cands.filterMap id).map (rdist2 p) with
  | [] => 0
  | d :: rest => rest.foldl min d

/-- Orientation-independent inside test: Möller–Trumbore ray/triangle
    intersection in exact rationals, counting crossings of a fixed generic
    ray. The direction is chosen with rational components that do not align
    with any mesh edge, so no intersection lands exactly on an edge. -/
def rayDir : R3 := ⟨1, Rat.divInt 37 100, Rat.divInt 11 100⟩

def rayInside (verts : Array R3) (faces : Array (Nat × Nat × Nat)) (p : R3) : Bool := Id.run do
  let mut count : Nat := 0
  for f in faces do
    let a := verts[f.1]!
    let b := verts[f.2.1]!
    let c := verts[f.2.2]!
    let e1 := rsub b a
    let e2 := rsub c a
    let h := rcross rayDir e2
    let det := rdot e1 h
    if det == 0 then continue
    let s := rsub p a
    let u := rdot s h / det
    if u < 0 then continue
    if u > 1 then continue
    let q := rcross s e1
    let v := rdot rayDir q / det
    if v < 0 then continue
    if u + v > 1 then continue
    let t := rdot e2 q / det
    if t > 0 then count := count + 1
  return count % 2 == 1

/-- Native IEEE-754 double 3-vector, used to mirror the C seed loop bit-for-bit. -/
structure F3 where
  x : Float
  y : Float
  z : Float
  deriving Inhabited

/-- One dumped mesh. -/
structure Case where
  hBits : UInt32 := 0
  outBits : UInt32 := 0
  inBits : UInt32 := 0
  bgBits : UInt32 := 0
  reportedActive : Nat := 0
  hasTopo : Bool := false
  verts : Array R3 := #[]
  vertsF : Array F3 := #[]
  faces : Array (Nat × Nat × Nat) := #[]
  voxels : Array (Int × Int × Int × Bool × UInt32) := #[]
  faceStepsDump : Array Nat := #[]
  seedCountDump : Nat := 0
  seedsDump : Array (Int × Int × Int) := #[]
  deriving Inhabited

def fsub3 (a b : F3) : F3 := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩

/-- `sqrt((x*x + y*y) + z*z)`, in the C loop's exact association. -/
def fnorm3 (e : F3) : Float := Float.sqrt ((e.x * e.x + e.y * e.y) + e.z * e.z)

def f32F3 (x y z : UInt32) : F3 := ⟨f32Float x, f32Float y, f32Float z⟩

def pushVoxel (c : Case) (x y z : Int) (act : Bool) (v : UInt32) : Case :=
  { c with voxels := c.voxels.push (x, y, z, act, v) }

def pushVert (c : Case) (j : Nat) (v : R3) : Case :=
  { c with verts := if c.verts.size > j then c.verts.set! j v else c.verts.push v }

def pushVertF (c : Case) (j : Nat) (v : F3) : Case :=
  { c with vertsF := if c.vertsF.size > j then c.vertsF.set! j v else c.vertsF.push v }

def pushFace (c : Case) (j : Nat) (f : Nat × Nat × Nat) : Case :=
  { c with faces := if c.faces.size > j then c.faces.set! j f else c.faces.push f }

def pushFaceStep (c : Case) (j : Nat) (n : Nat) : Case :=
  { c with faceStepsDump := if c.faceStepsDump.size > j then c.faceStepsDump.set! j n else c.faceStepsDump.push n }

def pushSeed (c : Case) (x y z : Int) : Case :=
  { c with seedsDump := c.seedsDump.push (x, y, z) }

/-- The twin value at a lattice point: exact squared distance, exact sign,
    ±band clamp and the exact keep-rule active predicate. Returns
    `(value, active)`. -/
def twinValue (c : Case) (p : R3) : Float × Bool :=
  let d2 := (c.faces.map fun f => triDist2 p c.verts[f.1]! c.verts[f.2.1]! c.verts[f.2.2]!).foldl
    min (triDist2 p c.verts[c.faces[0]!.1]! c.verts[c.faces[0]!.2.1]! c.verts[c.faces[0]!.2.2]!)
  let inside := rayInside c.verts c.faces p
  let bandRat := if inside then f32Rat c.inBits else f32Rat c.outBits
  let bandFloat := if inside then f32Float c.inBits else f32Float c.outBits
  let d : Float := Float.sqrt (Float.ofInt d2.num / Float.ofNat d2.den)
  let v := if inside then -min d bandFloat else min d bandFloat
  (v, d2 < bandRat * bandRat)

/-- The C loop's `steps = ceil(2·l·inv_h)` for one face, as a positive Nat. -/
def faceStepsF (v0 v1 v2 : F3) (invh : Float) : Nat :=
  let e1 := fsub3 v1 v0
  let e2 := fsub3 v2 v0
  let l := max (max (fnorm3 e1) (fnorm3 e2)) (fnorm3 (fsub3 e1 e2))
  let sd : Int := (Float.ceil ((2.0 * l) * invh)).toInt64.toInt
  if sd < 1 then 1 else sd.toNat

/-- Reproduce the C barycentric seed set bit-for-bit in native IEEE doubles.
    Returns `(seeds, per-face steps)`. -/
def computeSeeds (c : Case) : Array (Int × Int × Int) × Array Nat := Id.run do
  let invh : Float := 1.0 / f32Float c.hBits
  let mut seeds : Array (Int × Int × Int) := #[]
  let mut stepsArr : Array Nat := #[]
  for f in c.faces do
    let v0 := c.vertsF[f.1]!
    let v1 := c.vertsF[f.2.1]!
    let v2 := c.vertsF[f.2.2]!
    let e1 := fsub3 v1 v0
    let e2 := fsub3 v2 v0
    let n := faceStepsF v0 v1 v2 invh
    stepsArr := stepsArr.push n
    for i in [0 : n + 1] do
      for j in [0 : n - i + 1] do
        let a : Float := Float.ofNat i / Float.ofNat n
        let b : Float := Float.ofNat j / Float.ofNat n
        let px : Float := (v0.x + a * e1.x) + b * e2.x
        let py : Float := (v0.y + a * e1.y) + b * e2.y
        let pz : Float := (v0.z + a * e1.z) + b * e2.z
        let cx : Int := (Float.floor (px * invh + 0.5)).toInt64.toInt
        let cy : Int := (Float.floor (py * invh + 0.5)).toInt64.toInt
        let cz : Int := (Float.floor (pz * invh + 0.5)).toInt64.toInt
        let mut found := false
        for s in seeds do
          if s.1 == cx && s.2.1 == cy && s.2.2 == cz then found := true
        if !found then seeds := seeds.push (cx, cy, cz)
  return (seeds, stepsArr)

/-- Parse exactly 8 lowercase hex digits into a UInt32 bit pattern. -/
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

def parseNat (s : String) : Option Nat := s.toNat?
def parseInt (s : String) : Option Int := s.toInt?

inductive Line where
  | params (m : Nat) (h out inn : UInt32)
  | vertex (m j : Nat) (v : R3) (vf : F3)
  | face (m j : Nat) (a b c : Nat)
  | voxel (m : Nat) (x y z : Int) (act : Bool) (v : UInt32)
  | topo (m : Nat) (bg : UInt32) (active : Nat)
  | faceStep (m f n : Nat)
  | seedCount (m n : Nat)
  | seed (m : Nat) (x y z : Int)
  | ignored

def parseLine (s : String) : Line :=
  let t := s.splitOn " "
  match t with
  | ["mesh", mi, "params", "h", hb, "out", ob, "in", ib] =>
      match mi.toNat?, parseHex8 hb, parseHex8 ob, parseHex8 ib with
      | some m, some h, some o, some i => .params m h o i
      | _, _, _, _ => .ignored
  | ["mesh", mi, "vertex", sj, xb, yb, zb] =>
      match mi.toNat?, sj.toNat?, parseHex8 xb, parseHex8 yb, parseHex8 zb with
      | some m, some j, some x, some y, some z =>
          .vertex m j ⟨f32Rat x, f32Rat y, f32Rat z⟩ (f32F3 x y z)
      | _, _, _, _, _ => .ignored
  | ["mesh", mi, "face", sj, a, b, c] =>
      match mi.toNat?, sj.toNat?, parseNat a, parseNat b, parseNat c with
      | some m, some j, some x, some y, some z => .face m j x y z
      | _, _, _, _, _ => .ignored
  | ["mesh", mi, "face", sj, "steps", sn] =>
      match mi.toNat?, sj.toNat?, sn.toNat? with
      | some m, some j, some n => .faceStep m j n
      | _, _, _ => .ignored
  | ["mesh", mi, "seedcount", sn] =>
      match mi.toNat?, sn.toNat? with
      | some m, some n => .seedCount m n
      | _, _ => .ignored
  | ["mesh", mi, "seed", sx, sy, sz] =>
      match mi.toNat?, sx.toInt?, sy.toInt?, sz.toInt? with
      | some m, some x, some y, some z => .seed m x y z
      | _, _, _, _ => .ignored
  | ["mesh", mi, "voxel", sx, sy, sz, "act", ac, "val", vb] =>
      match mi.toNat?, parseInt sx, parseInt sy, parseInt sz, parseInt ac, parseHex8 vb with
      | some m, some x, some y, some z, some a, some v => .voxel m x y z (a == 1) v
      | _, _, _, _, _, _ => .ignored
  | ["mesh", mi, "topo", "bg", bg, "active_vox", ac, "imin", _, _, _, "imax", _, _, _] =>
      match mi.toNat?, parseHex8 bg, parseNat ac with
      | some m, some b, some a => .topo m b a
      | _, _, _ => .ignored
  | _ => .ignored

end Vdb.TreeMeshSdfCheck

def main (argv : List String) : IO Unit := do
  match argv with
  | [path] =>
      let raw ← IO.FS.readFile path
      let mut cases : Array Vdb.TreeMeshSdfCheck.Case :=
        Array.replicate 2 { : Vdb.TreeMeshSdfCheck.Case }
      for line in (raw.splitOn "\n").map Vdb.TreeMeshSdfCheck.parseLine do
        match line with
        | .params m h o i =>
            cases := cases.set! m { cases[m]! with hBits := h, outBits := o, inBits := i }
        | .vertex m j v vf =>
            cases := cases.set! m (Vdb.TreeMeshSdfCheck.pushVertF
              (Vdb.TreeMeshSdfCheck.pushVert cases[m]! j v) j vf)
        | .face m j a b c => cases := cases.set! m (Vdb.TreeMeshSdfCheck.pushFace cases[m]! j (a, b, c))
        | .faceStep m j n => cases := cases.set! m (Vdb.TreeMeshSdfCheck.pushFaceStep cases[m]! j n)
        | .seedCount m n => cases := cases.set! m { cases[m]! with seedCountDump := n }
        | .seed m x y z => cases := cases.set! m (Vdb.TreeMeshSdfCheck.pushSeed cases[m]! x y z)
        | .voxel m x y z act v =>
            cases := cases.set! m (Vdb.TreeMeshSdfCheck.pushVoxel cases[m]! x y z act v)
        | .topo m bg active =>
            cases := cases.set! m { cases[m]! with bgBits := bg, reportedActive := active, hasTopo := true }
        | .ignored => pure ()
      let mut badValue := 0
      let mut badActive := 0
      let mut badTopo := 0
      let mut badSeed := 0
      let mut badSteps := 0
      let mut seeds := 0
      let mut exactBits := 0
      let mut voxels := 0
      let mut maxErr : Float := 0
      for c in cases do
        if c.faces.size == 0 then throw (IO.userError "tree meshsdf: missing mesh in dump")
        -- Mirror the C barycentric seed loop in native doubles and compare the
        -- intermediate seed set and per-face sample counts bit-for-bit.
        let (leanSeeds, leanSteps) := Vdb.TreeMeshSdfCheck.computeSeeds c
        if leanSteps != c.faceStepsDump then
          badSteps := badSteps + 1
          if badSteps <= 3 then
            IO.println s!"SEED STEPS MISMATCH: c={c.faceStepsDump} lean={leanSteps}"
        if leanSeeds.size != c.seedsDump.size || c.seedCountDump != c.seedsDump.size then
          badSeed := badSeed + 1
        let missing := (leanSeeds.filter fun s => !c.seedsDump.contains s).size
        let extra := (c.seedsDump.filter fun s => !leanSeeds.contains s).size
        if missing + extra > 0 then
          badSeed := badSeed + missing + extra
          if badSeed <= 5 then
            IO.println s!"SEED SET MISMATCH: missing={missing} extra={extra}"
        seeds := seeds + c.seedsDump.size
        if !c.hasTopo || c.bgBits != c.outBits then
          badTopo := badTopo + 1
        let dumpedActive := (c.voxels.filter fun v => v.2.2.2.1).size
        if dumpedActive != c.reportedActive then
          badTopo := badTopo + 1
          IO.println s!"TOPO MISMATCH: dumped active={dumpedActive} reported={c.reportedActive}"
        for (x, y, z, act, vbits) in c.voxels do
          let p : Vdb.TreeMeshSdfCheck.R3 := ⟨(x : Rat) * Vdb.TreeMeshSdfCheck.f32Rat c.hBits,
                                             (y : Rat) * Vdb.TreeMeshSdfCheck.f32Rat c.hBits,
                                             (z : Rat) * Vdb.TreeMeshSdfCheck.f32Rat c.hBits⟩
          let (twin, twinAct) := Vdb.TreeMeshSdfCheck.twinValue c p
          let cv := Vdb.TreeMeshSdfCheck.f32Float vbits
          let err := Float.abs (twin - cv)
          if Float32.toBits (Float.toFloat32 twin) == vbits then exactBits := exactBits + 1
          if err > maxErr then maxErr := err
          let tol := 1e-6 * (if Float.abs cv > 1 then Float.abs cv else 1)
          if err > tol then
            badValue := badValue + 1
            if badValue <= 5 then
              IO.println s!"VALUE MISMATCH {x} {y} {z}: c={vbits} lean={twin} err={err}"
          if act != twinAct then
            badActive := badActive + 1
            if badActive <= 5 then
              IO.println s!"ACTIVE MISMATCH {x} {y} {z}: c={act} lean={twinAct}"
          voxels := voxels + 1
      IO.println s!"meshes={cases.size} voxels={voxels} badValue={badValue} badActive={badActive} badTopo={badTopo} exactBits={exactBits} maxErr={maxErr} maxErrBits={Float.toBits maxErr}"
      IO.println s!"seeds={seeds} badSeed={badSeed} badSteps={badSteps}"
      IO.println "stages_unmirrored=dilate,bvh,winding,floodfill,prune,tree-layout"
      if badValue > 0 || badActive > 0 || badTopo > 0 || badSeed > 0 || badSteps > 0 then
        throw (IO.userError "tree meshsdf differential check failed")
  | _ =>
      IO.println "usage: treemeshsdfcheck <c-output-file>"
      throw (IO.userError "treemeshsdfcheck: bad args")
