/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  BVH tie-explanation twin (model half): turns the 11 Float32 face
  disagreements counted by `Vdb.MeshSdfBvhCheck` ("counted artifacts") into
  *explained* artifacts.

  This executable consumes the dump of `scripts/meshsdf_bvh_ties_c.c`, which
  #includes tinyvdb_mesh.c and therefore calls the REAL static C kernel. For
  every cell-centre query of the same cube + icosahedron corpus (same h/band,
  same row-major seed chain, same C winner `rf`) the dump records the Float32
  squared distance of EVERY face, computed with the exact expression used by
  `tvdb_bvh_closest`:

      cp = tri_closest_point_c(p, a, b, c); d = sub_c(p, cp); dsq = dot_c(d, d)

  (all values as 8-hex IEEE-754 bits). The twin:

    * decodes the mesh vertices and query positions as exact dyadic ℚ;
    * recomputes the exact-ℚ squared distance of every face with the same
      Voronoi case analysis as `Vdb.MeshSdfBvhCheck.triDist`;
    * finds the exact-minimum face set S and its lowest index `lo` (the
      exact-ℚ winner under the proven low-index tie-break of
      `Vdb.search_eq_brute`);
    * for EVERY exact tie (|S| >= 2) checks that the C winner `rf` is in S and
      is the minimum of S under the Float32 pair `(f32 dsq, face index)` —
      i.e. Float32 rounding of the per-face squared distance explains C's
      choice. No theorem is weakened; this is an explanation of unmirrored
      behaviour, not a new claim about the ℚ model.

  Counters: `ties_exact` exact-tie queries, `ties_explained` /
  `ties_unexplained` explained / unexplained exact ties, `f32_dsq_diff` exact
  ties where the C winner's Float32 dsq bit pattern differs from the
  lower-index exact winner's (the 11 C/Lean disagreements).

  NOT MIRRORED (loudly reported, never called a pass): the C build heuristic,
  DFS stack order, and the Float32 kernel itself. The Float32 dsq values are
  taken bit-exactly from the real C kernel dump and interpreted with Lean's
  native `Float32`; they are NOT recomputed by a Lean Float32 port.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

namespace Vdb

/-- Exact rational 3-vector (Float32 dump values are dyadic rationals). -/
abbrev TQ3 := Fin 3 → ℚ

def tvsub (a b : TQ3) : TQ3 := fun i => a i - b i
def tvadd (a b : TQ3) : TQ3 := fun i => a i + b i
def tvscale (a : TQ3) (s : ℚ) : TQ3 := fun i => a i * s
def tdot (a b : TQ3) : ℚ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2
def tdist2 (a b : TQ3) : ℚ := let d := tvsub a b; tdot d d

/-- Parse exactly 8 lowercase hex digits into a `UInt32` bit pattern. -/
def tieParseHex8 (s : String) : Option UInt32 :=
  match s.toList with
  | [_c0, _c1, _c2, _c3, _c4, _c5, _c6, _c7] =>
      let hexVal (c : Char) : Option UInt32 :=
        match c with
        | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
        | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
        | '8' => some 8 | '9' => some 9 | 'a' => some 10 | 'b' => some 11
        | 'c' => some 12 | 'd' => some 13 | 'e' => some 14 | 'f' => some 15
        | _ => none
      s.toList.foldlM (fun acc c => (hexVal c).map (acc * 16 + ·)) 0
  | _ => none

/-- Exact rational value of an IEEE-754 binary32 bit pattern (dyadic). -/
def tieRatOfF32Bits (bits : UInt32) : ℚ :=
  let sgn : ℚ := if bits &&& 0x80000000 != 0 then -1 else 1
  let e := (bits >>> 23) &&& 0xff
  let m : ℚ := (bits &&& 0x7fffff).toNat
  if e == 0 then sgn * m / (2 : ℚ) ^ 149
  else if e == 255 then 0
  else sgn * ((2 : ℚ) ^ 23 + m) * (2 : ℚ) ^ ((e.toNat : Int) - 150)

/-- Exact point-to-triangle squared distance: the ℚ twin of the C case
    analysis. Tags are discarded; only the squared distance matters here. -/
def tieTriDist (p a b c : TQ3) : ℚ :=
  let ab := tvsub b a
  let ac := tvsub c a
  let ap := tvsub p a
  let d1 := tdot ab ap
  let d2 := tdot ac ap
  if d1 <= 0 && d2 <= 0 then tdist2 p a
  else
    let bp := tvsub p b
    let d3 := tdot ab bp
    let d4 := tdot ac bp
    if d3 >= 0 && d4 <= d3 then tdist2 p b
    else
      let vc := d1 * d4 - d3 * d2
      if vc <= 0 && d1 >= 0 && d3 <= 0 then
        let cp := tvadd a (tvscale ab (d1 / (d1 - d3)))
        tdist2 p cp
      else
        let cp0 := tvsub p c
        let d5 := tdot ab cp0
        let d6 := tdot ac cp0
        if d6 >= 0 && d5 <= d6 then tdist2 p c
        else
          let vb := d5 * d2 - d1 * d6
          if vb <= 0 && d2 >= 0 && d6 <= 0 then
            let cp := tvadd a (tvscale ac (d2 / (d2 - d6)))
            tdist2 p cp
          else
            let va := d3 * d6 - d5 * d4
            if va <= 0 && (d4 - d3) >= 0 && (d5 - d6) >= 0 then
              let cp := tvadd b (tvscale (tvsub c b) ((d4 - d3) / ((d4 - d3) + (d5 - d6))))
              tdist2 p cp
            else
              let denom := 1 / (va + vb + vc)
              let cp := tvadd (tvadd a (tvscale ab (vb * denom))) (tvscale ac (vc * denom))
              tdist2 p cp

structure TieTri where
  a : Nat
  b : Nat
  c : Nat
deriving Inhabited

structure TieMeshData where
  id : Nat := 0
  verts : Array TQ3 := #[]
  faces : Array TieTri := #[]
deriving Inhabited

structure TieQuery where
  mid : Nat
  qi : Nat
  p : TQ3
  rd : UInt32
  rf : Nat
  fdbits : Array UInt32 := #[]

inductive TieLine where
  | vertex (id j : Nat) (v : TQ3)
  | face (id j a b c : Nat)
  | tie (q : TieQuery)

def tieTokens (s : String) : List String := (s.splitOn " ").filter (fun t => t != "")

def parseTieLine (s : String) : Option TieLine :=
  match tieTokens s with
  | ["mesh", mi, "vertex", sj, x, y, z] => do
      let id ← mi.toNat?
      let j ← sj.toNat?
      let xb ← tieParseHex8 x
      let yb ← tieParseHex8 y
      let zb ← tieParseHex8 z
      pure (.vertex id j ![tieRatOfF32Bits xb, tieRatOfF32Bits yb, tieRatOfF32Bits zb])
  | ["mesh", mi, "face", sj, a, b, c] => do
      let id ← mi.toNat?
      let j ← sj.toNat?
      let av ← a.toNat?
      let bv ← b.toNat?
      let cv ← c.toNat?
      pure (.face id j av bv cv)
  | "tie" :: mi :: qi :: "px" :: px :: "py" :: py :: "pz" :: pz ::
    "rd" :: rd :: "rf" :: rf :: "dsq" :: rest => do
      let mid ← mi.toNat?
      let qi' ← qi.toNat?
      let pxb ← tieParseHex8 px
      let pyb ← tieParseHex8 py
      let pzb ← tieParseHex8 pz
      let rdb ← tieParseHex8 rd
      let rf' ← rf.toNat?
      let fds ← rest.mapM tieParseHex8
      pure (.tie { mid := mid, qi := qi',
                   p := ![tieRatOfF32Bits pxb, tieRatOfF32Bits pyb, tieRatOfF32Bits pzb],
                   rd := rdb, rf := rf', fdbits := fds.toArray })
  | _ => none

/-- Assemble meshes (geometry only) and queries from the dump. -/
def parseTieDump (raw : String) : Array TieMeshData × Array TieQuery :=
  let lines := (raw.splitOn "\n").filterMap parseTieLine
  let meshes := lines.foldl (fun ms line =>
    match line with
    | .vertex id _j v =>
        let m := ms[id]!
        ms.set! id { m with id := id, verts := m.verts.push v }
    | .face id _j a b c =>
        let m := ms[id]!
        ms.set! id { m with id := id, faces := m.faces.push ⟨a, b, c⟩ }
    | .tie _ => ms) (Array.replicate 2 ({ } : TieMeshData))
  let queries := (lines.filterMap fun l => match l with | .tie q => some q | _ => none).toArray
  (meshes, queries)

/-- Exact minimum face set for one query, plus its lowest index. -/
def exactMinSet (verts : Array TQ3) (faces : Array TieTri) (p : TQ3) : ℚ × List Nat :=
  let ed := faces.map (fun t => tieTriDist p verts[t.a]! verts[t.b]! verts[t.c]!)
  let dmin := (List.range faces.size).foldl (fun acc f => min acc ed[f]!) ed[0]!
  let s := (List.range faces.size).filter (fun f => ed[f]! == dmin)
  (dmin, s)

/-- C's winner `rf` is the minimum of the exact-min set under the Float32
    lexicographic pair (rounded squared distance, face index). The exact part
    (membership in S) is condition (a); the Float32 ordering is condition (b). -/
def f32Explains (q : TieQuery) (s : List Nat) : Bool :=
  let fd := q.fdbits
  let fv (f : Nat) : Float32 := Float32.ofBits fd[f]!
  q.rf ∈ s && s.all (fun f => f == q.rf || fv q.rf < fv f || (fv q.rf == fv f && q.rf < f))

def hex8 (u : UInt32) : String :=
  let dig (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)
  let n := u.toNat
  (List.range 8).foldl (fun acc k => acc.push (dig ((n / 16 ^ (7 - k)) % 16))) ""

end Vdb

def main (argv : List String) : IO Unit := do
  match argv with
  | [path] =>
      let raw ← IO.FS.readFile path
      let (meshes, queries) := Vdb.parseTieDump raw
      IO.println "NOT MIRRORED: tie explanation only. The ℚ model still picks the lowest-index exact-min face; C picks the (Float32 dsq, index) minimum. The Float32 dsq values are the REAL C kernel's per-face results, dumped bit-exactly by scripts/meshsdf_bvh_ties_c.c and interpreted with native Float32 -- not recomputed by a Lean Float32 port. No existing theorem is weakened."
      let mut tiesExact := 0
      let mut tiesExplained := 0
      let mut tiesUnexplained := 0
      let mut f32DsqDiff := 0
      let mut disagreements := 0
      let mut rdConsistent := 0
      let mut badNonTie := 0
      let mut badDump := 0
      for m in meshes do
        for q in queries.filter (fun q => q.mid == m.id) do
          if m.faces.size == 0 || q.rf >= m.faces.size || q.fdbits.size != m.faces.size then
            badDump := badDump + 1
          else
            let ed := m.faces.map (fun t => Vdb.tieTriDist q.p m.verts[t.a]! m.verts[t.b]! m.verts[t.c]!)
            let (_dmin, s) := Vdb.exactMinSet m.verts m.faces q.p
            let lo := s.foldl min (s.head!)
            if q.rd == q.fdbits[q.rf]! then rdConsistent := rdConsistent + 1
            let ok := Vdb.f32Explains q s
            if s.length >= 2 then
              tiesExact := tiesExact + 1
              if ok then tiesExplained := tiesExplained + 1
              else
                tiesUnexplained := tiesUnexplained + 1
                if tiesUnexplained <= 4 then
                  IO.println s!"UNEXPLAINED mesh {m.id} query {q.qi}: c={q.rf} exact_winner={lo} exact_min_set={s}"
            else if q.rf != lo then
              badNonTie := badNonTie + 1
            if q.rf != lo then
              disagreements := disagreements + 1
              if q.fdbits[q.rf]! != q.fdbits[lo]! then f32DsqDiff := f32DsqDiff + 1
              if disagreements <= 11 then
                IO.println s!"EXPLAIN mesh {m.id} query {q.qi}: c_winner={q.rf} exact_winner={lo} exact_dsq_equal={decide (ed[q.rf]! == ed[lo]!)} f32_c={Vdb.hex8 q.fdbits[q.rf]!} f32_exact={Vdb.hex8 q.fdbits[lo]!} f32_c_lt_exact={decide (Float32.ofBits q.fdbits[q.rf]! < Float32.ofBits q.fdbits[lo]!)} explained={ok}"
      IO.println s!"queries={queries.size} ties_exact={tiesExact} ties_explained={tiesExplained} ties_unexplained={tiesUnexplained} f32_dsq_diff={f32DsqDiff} disagreements={disagreements} rd_consistent={rdConsistent} bad_non_tie={badNonTie} bad_dump={badDump}"
      if tiesUnexplained > 0 || badNonTie > 0 || badDump > 0 || rdConsistent != queries.size then
        throw (IO.userError "meshsdf-bvh ties check failed")
  | _ =>
      IO.println "usage: meshsdfbvhtiecheck <ties-dump-file>"
      throw (IO.userError "meshsdfbvhtiecheck: bad args")
