/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  `mesh_triangle_double` double→float32 rounding differential twin
  (executable, no theorems). Driven by `scripts/check_meshsdf_double.sh`
  against `scripts/meshsdf_double_c.c`, which #includes the *real*
  `src/tinyvdb_mesh.c` and constructs 16 queries that actually divert
  `tri_closest_point_c` into its double-precision fallback (float32 overflow
  in the dot products, overflow of `vc`, collinear / identical vertices).

  The C driver dumps, per case:
    * the float32 bit patterns of p, a, b, c (the exact dyadic inputs),
    * the three double closest-point components BEFORE their (float) cast,
      as raw binary64 bit patterns,
    * the float32 values the real `mesh_triangle_double` returns,
    * the final float32 voxel value (the `mesh_fill_rows` per-voxel chain),
    * the float32 fallback reason and the double branch tag.

  WHAT IS CHECKED (exact, no floating-point model in Lean):
    1. round-to-nearest-even binary64→binary32: this module implements the
       IEEE-754 cast over the dumped binary64 bits using integer/Nat
       arithmetic and checks the resulting 32-bit pattern equals the C
       `(float)` cast bit-for-bit. This is the double→float32 rounding that
       the other mesh→SDF twins deliberately do not mirror.
    2. the double computation itself: the double inputs are float32 values,
       hence exact dyadic rationals. The closest point is recomputed in exact
       ℚ with the same Voronoi case analysis as `mesh_triangle_double`
       (including the degenerate edge loop), and compared with the decoded
       double bits within the documented tolerance
           |qLean - qC| ≤ (|qC| + 1) / 10^9
       (the double predicates round, so a bit-exact ℚ comparison is not
       appropriate for the *computation*; the cast check in (1) is exact).
    3. the post-cast float32 voxel chain (subtract / dot / sqrt / sign /
       clamp) is mirrored with Lean's native `Float32` and compared bit-for-
       bit with the C value.
    4. a self-test of the RNE encoder against C-computed anchors.

  The float32 fallback reason and double branch tag are compared to the exact
  ℚ branch derived from the inputs. A corrupted double component in the dump
  fails (1) and (2) — the script's negative control. No theorem is weakened;
  this is an independent executable twin.

  Printed: a self-test line and one counter line (see the gate script).
  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Tactic

namespace Vdb

/- ---------------------------------------------------------------------------
   Hex decoding (bit patterns, not decimal numbers).
-/

def hexNib (c : Char) : Option Nat :=
  match c with
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
  | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
  | '8' => some 8 | '9' => some 9 | 'a' => some 10 | 'b' => some 11
  | 'c' => some 12 | 'd' => some 13 | 'e' => some 14 | 'f' => some 15
  | 'A' => some 10 | 'B' => some 11 | 'C' => some 12
  | 'D' => some 13 | 'E' => some 14 | 'F' => some 15
  | _ => none

def parseHexNat (s : String) : Option Nat :=
  s.toList.foldlM (fun acc c => (hexNib c).map (fun n => acc * 16 + n)) 0

def parseHex32 (s : String) : Option UInt32 := (parseHexNat s).map UInt32.ofNat
def parseHex64 (s : String) : Option UInt64 := (parseHexNat s).map UInt64.ofNat

/- Exact rational value of an IEEE-754 bit pattern. Subnormals/normals are
   dyadic, hence exact in ℚ. Inf/NaN map to 0 (rejected by the corpus). -/
def ratOfF32Bits (bits : UInt32) : ℚ :=
  let sgn : ℚ := if bits &&& 0x80000000 != 0 then -1 else 1
  let e := (bits >>> 23) &&& 0xff
  let m : ℚ := (bits &&& 0x7fffff).toNat
  if e == 0 then sgn * m / (2 : ℚ) ^ 149
  else if e == 255 then 0
  else sgn * ((2 : ℚ) ^ 23 + m) * (2 : ℚ) ^ ((e.toNat : Int) - 150)

def ratOfF64Bits (bits : UInt64) : ℚ :=
  let sgn : ℚ := if bits &&& 0x8000000000000000 != 0 then -1 else 1
  let e := (bits >>> 52) &&& 0x7ff
  let m : ℚ := (bits &&& 0xfffffffffffff).toNat
  if e == 0 then sgn * m / (2 : ℚ) ^ 1074
  else if e == 2047 then 0
  else sgn * ((2 : ℚ) ^ 52 + m) * (2 : ℚ) ^ ((e.toNat : Int) - 1075)

/- ---------------------------------------------------------------------------
   IEEE-754 round-to-nearest-even binary64 → binary32 (the C `(float)` cast).

   Written entirely over Nat/Int: decode the binary64 into an integer
   significand `sig` and a power-of-two exponent `ex` with value
   `(-1)^s · sig · 2^ex`. Let `L = bitlength(sig)`; the unbiased binary32
   exponent of the infinitely precise value is `E = L - 1 + ex`.
     * E > 127                 → ±inf;
     * E ≥ -126 (normal)       → round sig·2^(24-L) to an integer significand
                                 `m ∈ [2^23, 2^24)` (ties to even), with carry;
     * E < -126 (subnormal)    → round sig·2^(ex+149) to `m ∈ [0, 2^23]`.
-/

def natBits (n : Nat) : Nat :=
  if n = 0 then 0 else 1 + natBits (n / 2)
termination_by n
decreasing_by omega

/-- `round(sig / 2^k)` to nearest integer, ties to even, over exact Nat. -/
def roundShift (sig k : Nat) : Nat :=
  if k = 0 then sig else
  let q := sig / 2 ^ k
  let r := sig % 2 ^ k
  let h := 2 ^ (k - 1)
  if r > h then q + 1 else if r = h then q + q % 2 else q

/-- The binary32 bit pattern (as a Nat) of the C `(float)` cast of a double. -/
def f32BitsOfDoubleBits (d : UInt64) : Nat :=
  let sgn : Nat := if d >>> 63 != 0 then 2147483648 else 0
  let e := (d >>> 52 &&& 0x7ff).toNat
  let frac : Nat := (d &&& 0xfffffffffffff).toNat
  if e = 2047 then
    if frac = 0 then sgn + 0x7f800000                -- inf
    else
      let top : Nat := frac / 2 ^ 29                  -- quiet NaN (never 0 here)
      sgn + 0x7f800000 + (if top = 0 then 1 else top)
  else if e = 0 && frac = 0 then
    sgn                                      -- signed zero
  else
    let sig : Nat := if e = 0 then frac else (1 <<< 52) + frac
    let ex : Int := if e = 0 then -1074 else (e : Int) - 1075
    let L : Nat := natBits sig
    let E : Int := (L : Int) - 1 + ex
    if E > 127 then
      sgn + 0x7f800000
    else if E >= -126 then
      let k : Int := 24 - (L : Int)
      let m : Nat := if k >= 0 then sig <<< k.toNat else roundShift sig (-k).toNat
      let carry : Bool := m = 16777216
      let m' : Nat := if carry then 8388608 else m
      let E' : Int := if carry then E + 1 else E
      if E' > 127 then
        sgn + 0x7f800000
      else
        sgn + (E' + 127).toNat * 8388608 + (m' - 8388608)
    else
      let k : Int := ex + 149
      let m : Nat := if k >= 0 then sig <<< k.toNat else roundShift sig (-k).toNat
      if m >= 8388608 then sgn + 8388608 else sgn + m

/- C-computed anchors: binary64 bits → expected binary32 bits. -/
def rneAnchors : Array (UInt64 × Nat) := #[
  (0x3ff0000000000000, 0x3f800000),   -- 1.0
  (0x3fb999999999999a, 0x3dcccccd),   -- 0.1
  (0xc024000000000000, 0xc1200000),   -- -2.5
  (0x46188fc140000001, 0x70c47e0a),   -- tie-ish, set low bits
  (0x4619ecf13fffffff, 0x70cf678a),   -- rounding carry candidate
  (0x460a6f097fffffff, 0x7053784c),
  (0x46193e5940000000, 0x70c9f2ca),   -- 1e30
  (0x0000000000000000, 0x00000000),   -- +0
  (0x8000000000000000, 0x80000000),   -- -0
  (0x7ff0000000000000, 0x7f800000),   -- +inf
  (0x7ff8000000000001, 0x7fc00000),   -- NaN
  (0x0010000000000000, 0x00000000),   -- smallest normal double → 0
  (0x0000000000000001, 0x00000000),   -- smallest subnormal double → 0
  (0x36a0000000000000, 0x00000001)    -- 1e-150 → smallest subnormal float
]

/- ---------------------------------------------------------------------------
   Exact-ℚ closest point (mirrors `mesh_triangle_double`, no isfinite checks).
-/

abbrev Q3 := Fin 3 → ℚ

def vsub (a b : Q3) : Q3 := fun i => a i - b i
def vadd (a b : Q3) : Q3 := fun i => a i + b i
def vscale (a : Q3) (s : ℚ) : Q3 := fun i => a i * s
def dotq (a b : Q3) : ℚ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2
def dist2q (a b : Q3) : ℚ := let d := vsub a b; dotq d d

def crossq (a b : Q3) : Q3 :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-- Closest point on a segment and its squared distance. -/
def segClosestQ (p x y : Q3) : ℚ × Q3 :=
  let d := vsub y x
  let q := vsub p x
  let len := dotq d d
  let t0 : ℚ := if len = 0 then 0 else dotq q d / len
  let t : ℚ := if t0 < 0 then 0 else if t0 > 1 then 1 else t0
  let r := vadd x (vscale d t)
  (dist2q p r, r)

/-- The degenerate-normal edge loop: minimum over the three edges, strict
   improvement keeps the first (edge a-b) on an exact tie, as in C. -/
def degenClosestQ (p a b c : Q3) : Q3 :=
  let e0 := segClosestQ p a b
  let e1 := segClosestQ p b c
  let e2 := segClosestQ p c a
  if e1.1 < e0.1 then
    if e2.1 < e1.1 then e2.2 else e1.2
  else if e2.1 < e0.1 then e2.2 else e0.2

def closestQ (p a b c : Q3) : Q3 × Nat :=
  let pa := vsub p a
  let ab := vsub b a
  let ac := vsub c a
  if dotq (crossq ab ac) (crossq ab ac) = 0 then
    (degenClosestQ p a b c, 0)
  else
    let d1 := dotq ab pa
    let d2 := dotq ac pa
    if d1 <= 0 && d2 <= 0 then (a, 1)
    else
      let pb := vsub p b
      let d3 := dotq ab pb
      let d4 := dotq ac pb
      if d3 >= 0 && d4 <= d3 then (b, 2)
      else
        let vc := d1 * d4 - d3 * d2
        if vc <= 0 && d1 >= 0 && d3 <= 0 then
          (vadd a (vscale ab (d1 / (d1 - d3))), 3)
        else
          let pc := vsub p c
          let d5 := dotq ab pc
          let d6 := dotq ac pc
          if d6 >= 0 && d5 <= d6 then (c, 4)
          else
            let vb := d5 * d2 - d1 * d6
            if vb <= 0 && d2 >= 0 && d6 <= 0 then
              (vadd a (vscale ac (d2 / (d2 - d6))), 5)
            else
              let va := d3 * d6 - d5 * d4
              if va <= 0 && (d4 - d3) >= 0 && (d5 - d6) >= 0 then
                (vadd b (vscale (vsub c b) ((d4 - d3) / ((d4 - d3) + (d5 - d6)))), 6)
              else
                let v := vb / (va + vb + vc)
                let w := vc / (va + vb + vc)
                (vadd (vadd a (vscale ab v)) (vscale ac w), 7)

def qAt (q : Q3) (j : Nat) : ℚ := q ⟨j % 3, Nat.mod_lt j (by decide)⟩

def withinTol (qC qL : ℚ) : Bool :=
  decide (let diff := if qC >= qL then qC - qL else qL - qC;
          diff <= (if qC >= 0 then qC else -qC) + 1 / (1000000000 : ℚ))

/- ---------------------------------------------------------------------------
   Native-Float32 mirror of the post-cast `mesh_fill_rows` chain.
-/

structure V3f where
  x : Float32
  y : Float32
  z : Float32

def fsub (a b : V3f) : V3f := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩
def fdot (a b : V3f) : Float32 := a.x * b.x + a.y * b.y + a.z * b.z
def fcross (a b : V3f) : V3f :=
  ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩

def voxelF32 (p cp a b c : V3f) (band : Float32) : Float32 :=
  let d := fsub p cp
  let dsq := fdot d d
  let dist := Float32.sqrt dsq
  let dir := fdot d (fcross (fsub b a) (fsub c a))
  let v := if dir >= 0.0 then dist else -dist
  if v > band then band else if v < -band then -band else v

/- ---------------------------------------------------------------------------
   Dump parsing.
-/

structure Case where
  id : Nat
  label : String
  p : Array UInt32
  a : Array UInt32
  b : Array UInt32
  c : Array UInt32
  d : Array UInt64
  f : Array UInt32
  v : UInt32
  reason : Nat
  branch : Nat
  txok : Nat
  band : UInt32

def parseCase (s : String) : Option Case := do
  let ts := s.splitOn " "
  let get (i : Nat) : Option String := ts[i]?
  if (get 0) != some "case" then none
  else
    let id ← (get 1).bind String.toNat?
    let label ← get 2
    let px ← (get 4).bind parseHex32; let py ← (get 5).bind parseHex32; let pz ← (get 6).bind parseHex32
    let ax ← (get 8).bind parseHex32; let ay ← (get 9).bind parseHex32; let az ← (get 10).bind parseHex32
    let bx ← (get 12).bind parseHex32; let bY ← (get 13).bind parseHex32; let bz ← (get 14).bind parseHex32
    let cx ← (get 16).bind parseHex32; let cy ← (get 17).bind parseHex32; let cz ← (get 18).bind parseHex32
    let dx ← (get 20).bind parseHex64; let dy ← (get 21).bind parseHex64; let dz ← (get 22).bind parseHex64
    let fx ← (get 24).bind parseHex32; let fy ← (get 25).bind parseHex32; let fz ← (get 26).bind parseHex32
    let vv ← (get 28).bind parseHex32
    let r ← (get 30).bind String.toNat?
    let br ← (get 32).bind String.toNat?
    let tx ← (get 34).bind String.toNat?
    let band' ← (get 36).bind parseHex32
    pure { id := id, label := label,
           p := #[px, py, pz], a := #[ax, ay, az], b := #[bx, bY, bz],
           c := #[cx, cy, cz], d := #[dx, dy, dz], f := #[fx, fy, fz],
           v := vv, reason := r, branch := br, txok := tx, band := band' }

def q3Of (bits : Array UInt32) : Q3 :=
  ![ratOfF32Bits bits[0]!, ratOfF32Bits bits[1]!, ratOfF32Bits bits[2]!]

def v3fOf (bits : Array UInt32) : V3f :=
  ⟨Float32.ofBits bits[0]!, Float32.ofBits bits[1]!, Float32.ofBits bits[2]!⟩

end Vdb

def main (argv : List String) : IO Unit := do
  match argv with
  | [path] =>
      let raw ← IO.FS.readFile path
      let cases := (raw.splitOn "\n").filterMap Vdb.parseCase
      let mut stOk := 0
      for (dbits, want) in Vdb.rneAnchors do
        if Vdb.f32BitsOfDoubleBits dbits == want then stOk := stOk + 1
        else IO.println s!"SELFTEST FAIL {dbits}: got {Vdb.f32BitsOfDoubleBits dbits} want {want}"

      let mut fallbackHits := 0
      let mut badTx := 0
      let mut rneCompOk := 0
      let mut rneOk := 0
      let mut badRne := 0
      let mut branchOk := 0
      let mut badBranch := 0
      let mut distOk := 0
      let mut badDist := 0
      let mut voxelOk := 0
      let mut badVoxel := 0
      for c in cases do
        if c.reason > 0 then fallbackHits := fallbackHits + 1
        if c.txok != 1 then badTx := badTx + 1

        -- (1) exact double→float32 rounding, per component
        let mut compOk := true
        for j in [:3] do
          let got := Vdb.f32BitsOfDoubleBits c.d[j]!
          if got == c.f[j]!.toNat then rneCompOk := rneCompOk + 1 else compOk := false
        if compOk then rneOk := rneOk + 1 else badRne := badRne + 1

        -- (2) exact-ℚ recomputation from the float32 inputs
        let cpQ := Vdb.closestQ (Vdb.q3Of c.p) (Vdb.q3Of c.a) (Vdb.q3Of c.b) (Vdb.q3Of c.c)
        if cpQ.2 == c.branch then branchOk := branchOk + 1
        else do
          badBranch := badBranch + 1
          if badBranch <= 4 then
            IO.println s!"BRANCH case {c.id} {c.label}: c={c.branch} lean={cpQ.2}"
        let mut dOk := true
        for j in [:3] do
          if !(Vdb.withinTol (Vdb.ratOfF64Bits c.d[j]!) (Vdb.qAt cpQ.1 j)) then dOk := false
        if dOk then distOk := distOk + 1
        else do
          badDist := badDist + 1
          if badDist <= 4 then
            IO.println s!"DIST case {c.id} {c.label}: d0={c.d[0]!} q0={Vdb.ratOfF64Bits c.d[0]!} lean0={cpQ.1 0}"

        -- (3) native Float32 post-cast chain from the C float32 closest point
        let vLean := Vdb.voxelF32 (Vdb.v3fOf c.p) (Vdb.v3fOf c.f) (Vdb.v3fOf c.a)
                       (Vdb.v3fOf c.b) (Vdb.v3fOf c.c) (Float32.ofBits c.band)
        if Float32.toBits vLean == c.v then voxelOk := voxelOk + 1
        else do
          badVoxel := badVoxel + 1
          if badVoxel <= 4 then
            IO.println s!"VOXEL case {c.id} {c.label}: c={c.v} lean={Float32.toBits vLean}"

      IO.println s!"selftest_ok={stOk} selftest_total={Vdb.rneAnchors.size}"
      IO.println s!"cases={cases.length} fallback_hits={fallbackHits} txok_ok={cases.length - badTx} bad_tx={badTx} rne_comp_ok={rneCompOk} rne_ok={rneOk} bad_rne={badRne} branch_ok={branchOk} bad_branch={badBranch} dist_ok={distOk} bad_dist={badDist} voxel_ok={voxelOk} bad_voxel={badVoxel}"
      if stOk != Vdb.rneAnchors.size || badTx > 0 || badRne > 0 || badBranch > 0 ||
         badDist > 0 || badVoxel > 0 || cases.length != 16 then
        throw (IO.userError "meshsdf-double differential check failed")
  | _ =>
      IO.println "usage: meshsdfdoublecheck <c-output-file>"
      throw (IO.userError "meshsdfdoublecheck: bad args")
