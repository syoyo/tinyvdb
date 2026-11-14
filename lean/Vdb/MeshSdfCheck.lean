/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Dense mesh→SDF differential harness (model half): the Float32 twin of the
  C `tvdb_mesh_to_sdf_ex` (`src/tinyvdb_mesh_conversion.inl`,
  `src/tinyvdb_mesh.c`), compared against `lean/scripts/meshsdf_c.c`, which
  dumps three closed meshes (cube, icosahedron, jittered icosahedron), the
  generated dense grids and the per-voxel signed distance values as float
  **bit patterns**. The twin recomputes every voxel from the dumped mesh
  alone — brute-force closest triangle with the same tie-break (lowest face
  index on an exact squared-distance tie), closest-feature pseudo-normal
  sign (Bærentzen & Aanæs), ±band clamp — and compares bits, bit-exact.

  Deliberately *not* mirrored: the `mesh_triangle_double` double-precision
  closest-point fallback, which requires double→float32 rounding that core
  Lean does not provide. Every branch that C takes into the double fallback
  is detected as a Float32 predicate (`!isFinite` or an exact equality);
  hitting it increments `fallback_hits` and the voxel is not compared, so a
  hit is a loud failure, never a silent pass. These branches are unreachable
  for the harness meshes (finite, non-degenerate geometry); the gate asserts
  `fallback_hits=0`.

  Printed: `voxels=<n> bad=<n> fallback_hits=<n>`.
  `scripts/check_meshsdf.sh` drives both halves.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/

namespace Vdb

/-- A 3-vector in `Float32`, mirroring `tvdb_vec3f`. -/
structure V3f where
  x : Float32
  y : Float32
  z : Float32
deriving BEq, Inhabited

def addf (a b : V3f) : V3f := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩
def subf (a b : V3f) : V3f := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩
def mulf (a : V3f) (s : Float32) : V3f := ⟨a.x * s, a.y * s, a.z * s⟩
def dotf (a b : V3f) : Float32 := a.x * b.x + a.y * b.y + a.z * b.z
def crossf (a b : V3f) : V3f :=
  ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩
/-- `normalize_c`: unit vector (or zero when the length is below `1e-30f`). -/
def normalizef (v : V3f) : V3f :=
  let L := Float32.sqrt (dotf v v)
  if L < 1e-30 then ⟨0, 0, 0⟩ else mulf v (1.0 / L)
/-- `mesh_normal`: per-face normal (cross of edges), normalised. -/
def meshNormal (a b c : V3f) : V3f :=
  let cr := crossf (subf b a) (subf c a)
  let len2 := dotf cr cr
  if !len2.isFinite || len2 <= 0 then ⟨0, 0, 0⟩ else normalizef cr

/-- Closest point on a triangle to `p`, tagged with the closest feature
    (0/1/2 = vertex a/b/c, 3/4/5 = edge ab/ac/bc, 6 = face interior),
    mirroring `tri_closest_point_c`. `true` marks a branch that would have
    taken the C double-precision fallback (not mirrored). -/
def triClosest (p a b c : V3f) : V3f × UInt32 × Bool :=
  let ab := subf b a
  let ac := subf c a
  let ap := subf p a
  let d1 := dotf ab ap
  let d2 := dotf ac ap
  if !d1.isFinite || !d2.isFinite then
    (default, 6, true)
  else if d1 <= 0.0 && d2 <= 0.0 then
    (a, 0, false)
  else
    let bp := subf p b
    let d3 := dotf ab bp
    let d4 := dotf ac bp
    if !d3.isFinite || !d4.isFinite then
      (default, 6, true)
    else if d3 >= 0.0 && d4 <= d3 then
      (b, 1, false)
    else
      let vc := d1 * d4 - d3 * d2
      if !vc.isFinite then
        (default, 6, true)
      else if vc <= 0.0 && d1 >= 0.0 && d3 <= 0.0 then
        if d1 == d3 then
          (default, 6, true)
        else
          let v := d1 / (d1 - d3)
          (addf a (mulf ab v), 3, false)
      else
        let cp := subf p c
        let d5 := dotf ab cp
        let d6 := dotf ac cp
        if !d5.isFinite || !d6.isFinite then
          (default, 6, true)
        else if d6 >= 0.0 && d5 <= d6 then
          (c, 2, false)
        else
          let vb := d5 * d2 - d1 * d6
          if !vb.isFinite then
            (default, 6, true)
          else if vb <= 0.0 && d2 >= 0.0 && d6 <= 0.0 then
            if d2 == d6 then
              (default, 6, true)
            else
              let w := d2 / (d2 - d6)
              (addf a (mulf ac w), 4, false)
          else
            let va := d3 * d6 - d5 * d4
            if !va.isFinite then
              (default, 6, true)
            else if va <= 0.0 && (d4 - d3) >= 0.0 && (d5 - d6) >= 0.0 then
              if (d4 - d3) + (d5 - d6) == 0.0 then
                (default, 6, true)
              else
                let w := (d4 - d3) / ((d4 - d3) + (d5 - d6))
                (addf b (mulf (subf c b) w), 5, false)
            else if !(va + vb + vc).isFinite || va + vb + vc <= 0.0 then
              (default, 6, true)
            else
              let denom := 1.0 / (va + vb + vc)
              (addf (addf a (mulf ab (vb * denom))) (mulf ac (vc * denom)), 6, false)

/-- One closed mesh, as dumped by `meshsdf_c.c`. -/
structure Mesh where
  h : Float32 := 0
  band : Float32 := 0
  ox : Float32 := 0
  oy : Float32 := 0
  oz : Float32 := 0
  nx : Nat := 0
  ny : Nat := 1
  nz : Nat := 1
  verts : Array V3f := #[]
  faces : Array (UInt32 × UInt32 × UInt32) := #[]
  /-- Voxels in row-major order (x fastest): `(x, y, z, value)`. -/
  voxels : Array (Nat × Nat × Nat × Float32) := #[]

namespace Mesh

/-- Per-face normals, recomputed exactly as the C workspace does. -/
def normals (m : Mesh) : Array V3f :=
  m.faces.map fun f => meshNormal (m.verts[f.1.toNat]!) (m.verts[f.2.1.toNat]!) (m.verts[f.2.2.toNat]!)

/-- Faces incident on vertex `vid`, in ascending face order. -/
def vertexFaces (m : Mesh) (vid : Nat) : Array Nat := Id.run do
  let mut acc : Array Nat := #[]
  for i in [:m.faces.size] do
    let f := m.faces[i]!
    if f.1.toNat == vid || f.2.1.toNat == vid || f.2.2.toNat == vid then
      acc := acc.push i
  return acc

/-- Faces incident on the edge with endpoints `x ≤ y`, ascending face order. -/
def edgeFaces (m : Mesh) (x y : Nat) : Array Nat := Id.run do
  let mut acc : Array Nat := #[]
  for i in [:m.faces.size] do
    let f := m.faces[i]!
    let corners : List Nat := [f.1.toNat, f.2.1.toNat, f.2.2.toNat]
    if corners.contains x && corners.contains y then
      acc := acc.push i
  return acc

/-- `mesh_pseudo_normal`: the direction of the inside/outside test for a
    non-face-interior closest feature. Vertex features sum the normals of all
    incident faces; edge features sum the normals of the incident faces on
    that edge; face interiors keep the face normal. Sums that are non-finite
    or non-positive fall back to the face normal. -/
def pseudoNormal (m : Mesh) (normals : Array V3f) (face : Nat) (feature : Nat) : V3f :=
  if feature == 6 || feature > 6 then normals[face]!
  else
    let f := m.faces[face]!
    let incident : Array Nat :=
      if feature < 3 then
        let vid := if feature == 0 then f.1.toNat else if feature == 1 then f.2.1.toNat else f.2.2.toNat
        vertexFaces m vid
      else
        let (x, y) :=
          if feature == 3 then (min f.1.toNat f.2.1.toNat, max f.1.toNat f.2.1.toNat)
          else if feature == 4 then (min f.1.toNat f.2.2.toNat, max f.1.toNat f.2.2.toNat)
          else (min f.2.1.toNat f.2.2.toNat, max f.2.1.toNat f.2.2.toNat)
        edgeFaces m x y
    let sum := incident.foldl (init := ⟨0, 0, 0⟩) fun s i =>
      addf s normals[i]!
    let len2 := dotf sum sum
    if !len2.isFinite || len2 <= 0 then normals[face]!
    else normalizef sum

/-- The closest-triangle query (brute force; the C BVH tree prunes on the
    same acceptance rule `dsq < best || (dsq == best && f < best_face)`, so
    both select the same winner). Returns `(face, feature)`. -/
def closestFace (m : Mesh) (p : V3f) : Nat × UInt32 := Id.run do
  let mut bestFace : Nat := m.faces.size
  let mut bestDsq := Float32.inf
  let mut bestFeature : UInt32 := 6
  for f in [:m.faces.size] do
    let fa := m.faces[f]!
    let (cp, feature, _fb) :=
      triClosest p (m.verts[fa.1.toNat]!) (m.verts[fa.2.1.toNat]!) (m.verts[fa.2.2.toNat]!)
    let d := subf p cp
    let dsq := dotf d d
    if dsq < bestDsq || (dsq == bestDsq && f < bestFace) then
      bestDsq := dsq
      bestFace := f
      bestFeature := feature
  return (bestFace, bestFeature)

/-- One voxel's signed distance value, mirroring `mesh_fill_rows`. -/
def voxelValue (m : Mesh) (normals : Array V3f) (ix iy iz : Nat) : Float32 × Bool :=
  let ox := m.ox; let oy := m.oy; let oz := m.oz
  let point : V3f := ⟨ox + (UInt32.toFloat32 (UInt32.ofNat ix) + 0.5) * m.h,
                      oy + (UInt32.toFloat32 (UInt32.ofNat iy) + 0.5) * m.h,
                      oz + (UInt32.toFloat32 (UInt32.ofNat iz) + 0.5) * m.h⟩
  let (face, feature) := closestFace m point
  let fa := m.faces[face]!
  -- recompute the closest point for this face (same order of operations)
  let (cp, _, fb) :=
    triClosest point (m.verts[fa.1.toNat]!) (m.verts[fa.2.1.toNat]!) (m.verts[fa.2.2.toNat]!)
  let pnormal := pseudoNormal m normals face feature.toNat
  let direction := dotf (subf point cp) pnormal
  let d := subf point cp
  let dsq := dotf d d
  let distance := Float32.sqrt dsq
  let v0 := if direction >= 0.0 then distance else -distance
  let v := if v0 > m.band then m.band else if v0 < -m.band then -m.band else v0
  (v, fb)

/-- Recompute every voxel of the mesh's grid. Returns the voxels in order. -/
def voxelsGrid (m : Mesh) : Array Float32 :=
  let normals := m.normals
  let nx := m.nx
  let ny := m.ny
  (Array.range (m.nz * m.ny * m.nx)).map fun k =>
    let x := k % nx
    let y := (k / nx) % ny
    let z := k / (nx * ny)
    (m.voxelValue normals x y z).1

end Mesh

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

def float32OfHex (s : String) : Option Float32 :=
  (parseHex8 s).map Float32.ofBits

def parseUInt32 (s : String) : Option UInt32 :=
  s.toNat?.map fun n => UInt32.ofNat n

/-- A parsed `mesh` line, carrying the mesh id for dispatch. -/
inductive MeshLine where
  | h (mesh : Nat) (h : Float32) (band : Float32)
  | dims (mesh : Nat) (nx ny nz : Nat) (ox oy oz : Float32)
  | vertex (mesh : Nat) (j : Nat) (v : V3f)
  | face (mesh : Nat) (j : Nat) (a b c : UInt32)
  | voxel (mesh : Nat) (x y z : Nat) (v : Float32)

def parseLine (s : String) : Option MeshLine := do
  match s.splitOn " " with
  | ["mesh", mi, "h", hb, "band", bb] =>
      let mesh ← mi.toNat?
      let h ← float32OfHex hb
      let band ← float32OfHex bb
      pure (.h mesh h band)
  | ["mesh", mi, "dims", "nx", sx, "ny", sy, "nz", sz, "ox", ox, "oy", oy, "oz", oz] =>
      let mesh ← mi.toNat?
      let nx ← sx.toNat?
      let ny ← sy.toNat?
      let nz ← sz.toNat?
      let ox ← float32OfHex ox
      let oy ← float32OfHex oy
      let oz ← float32OfHex oz
      pure (.dims mesh nx ny nz ox oy oz)
  | ["mesh", mi, "vertex", sj, x, y, z] =>
      let mesh ← mi.toNat?
      let j ← sj.toNat?
      let vx ← float32OfHex x
      let vy ← float32OfHex y
      let vz ← float32OfHex z
      pure (.vertex mesh j ⟨vx, vy, vz⟩)
  | ["mesh", mi, "face", sj, a, b, c] =>
      let mesh ← mi.toNat?
      let j ← sj.toNat?
      let av ← parseUInt32 a
      let bv ← parseUInt32 b
      let cv ← parseUInt32 c
      pure (.face mesh j av bv cv)
  | ["mesh", mi, "voxel", sx, sy, sz, v] =>
      let mesh ← mi.toNat?
      let x ← sx.toNat?
      let y ← sy.toNat?
      let z ← sz.toNat?
      let vv ← float32OfHex v
      pure (.voxel mesh x y z vv)
  | _ => none

end Vdb

def main (argv : List String) : IO Unit := do
  match argv with
  | [path] =>
      let raw ← IO.FS.readFile path
      let mut meshes : Array (Option Vdb.Mesh) := Array.replicate 3 none
      for line in (raw.splitOn "\n").filterMap Vdb.parseLine do
        match line with
        | .h i h band =>
            meshes := meshes.set! i (some { h := h, band := band })
        | .dims i nx ny nz ox oy oz =>
            meshes := meshes.set! i
              (meshes[i]!.map fun m => { m with nx := nx, ny := ny, nz := nz, ox := ox, oy := oy, oz := oz })
        | .vertex i j v =>
            meshes := meshes.set! i
              (meshes[i]!.map fun m => { m with verts := if m.verts.size > j then m.verts.set! j v else m.verts.push v })
        | .face i j a b c =>
            meshes := meshes.set! i
              (meshes[i]!.map fun m => { m with faces := if m.faces.size > j then m.faces.set! j (a, b, c) else m.faces.push (a, b, c) })
        | .voxel i x y z v =>
            meshes := meshes.set! i
              (meshes[i]!.map fun m => { m with voxels := m.voxels.push (x, y, z, v) })
      let mut bad := 0
      let mut voxels := 0
      let mut fallbackHits := 0
      for mesh? in meshes do
        let some mesh := mesh? | throw (IO.userError "missing mesh in dump")
        let normals := mesh.normals
        for (x, y, z, expected) in mesh.voxels do
          let (twin, fb) := mesh.voxelValue normals x y z
          if fb then
            fallbackHits := fallbackHits + 1
          else if Float32.toBits twin != Float32.toBits expected then
            bad := bad + 1
            if bad <= 5 then
              IO.println s!"MISMATCH voxel {x} {y} {z}: c={Float32.toBits expected} lean={Float32.toBits twin}"
          voxels := voxels + 1
      IO.println s!"voxels={voxels} bad={bad} fallback_hits={fallbackHits}"
      if bad > 0 || fallbackHits > 0 then
        throw (IO.userError "meshsdf differential check failed")
  | _ =>
      IO.println "usage: meshsdfcheck <c-output-file>"
      throw (IO.userError "meshsdfcheck: bad args")
