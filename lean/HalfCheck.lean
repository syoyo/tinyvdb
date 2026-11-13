import VdbSpec

/-! Model-side half-float differential check (driven by
`scripts/check_half.sh`).

Modes:

* `h2f` — dump `h hex16 bits hex32` for all 65536 half bit patterns
  (`halfToFloatBits` vs the C `tvdb__half_to_float`).
* `f2h` — dump `u hex32 h hex16` for one witness per float-to-half RNE
  rounding fiber (`floatToHalfRNE` vs the C `tvdb__float_to_half`). The
  rounding decision depends only on the sign, the exponent, the kept
  mantissa bits `q` and whether the dropped residue `rem` is below, equal
  to or above half the weight of the kept bit; the exhaustive fiber
  partition is machine-validated by the C harness's `audit` mode, which
  also reports the number of observed fibers — this program emits the
  same count of witnesses.
-/

open Vdb

def hexDigit (d : Nat) : Char :=
  if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

/-- Hex of `n`, most significant digit first, exactly `w` characters. -/
def hexW (w : Nat) (n : Nat) : String :=
  String.ofList ((List.range w).reverse.map fun i => hexDigit ((n / 16 ^ i) % 16))

/-- One f2h witness line. -/
def emitF2H (u : Nat) : IO Unit := do
  let h := floatToHalfRNE (UInt32.ofNat u)
  IO.println s!"{hexW 8 u} {hexW 4 h.toNat}"

/-- All witnesses of the float-to-half fiber partition, one line each,
    matching `scripts/half_check_c.c` exactly. -/
def runF2H : IO Unit := do
  -- e == 0xFF: Inf (mant == 0) and one NaN fiber per payload (10 bits).
  for sign in [0, 1] do
    emitF2H ((sign <<< 31) ||| 0x7f800000)
    for t in [0:1024] do
      let mant := if t == 0 then 1 else t <<< 13
      emitF2H ((sign <<< 31) ||| 0x7f800000 ||| mant)
  -- e in [143, 254]: overflow -> Inf, one witness each.
  for e in [143:255] do
    for sign in [0, 1] do
      emitF2H ((sign <<< 31) ||| (e <<< 23))
  -- e in [113, 142] (normal half): x = 0x800000|mant, k = 13.
  for e in [113:143] do
    for sign in [0, 1] do
      for q in [0x400:(0x800)] do
        for rem in [0x0000, 0x1000, 0x1001] do
          let mant := ((q <<< 13) ||| rem) &&& 0x7fffff
          emitF2H ((sign <<< 31) ||| (e <<< 23) ||| mant)
  -- e in [102, 112] (subnormal half): k = 126 - e in [14, 24].
  for e in [102:113] do
    let k := 126 - e
    let qmin := 0x800000 >>> k
    let qmax := 0xffffff >>> k
    let half := (1 : Nat) <<< (k - 1)
    let maxrem := (1 <<< k) - 1
    for sign in [0, 1] do
      for q in List.range (qmax - qmin + 1) do
        let qq := q + qmin
        let xlo := if 0x800000 > (qq <<< k) then 0x800000 else (qq <<< k)
        let xhi := min ((qq <<< k) ||| maxrem) 0xffffff
        let lo := xlo - (qq <<< k)
        let hi := xhi - (qq <<< k)
        if lo < half then
          emitF2H ((sign <<< 31) ||| (e <<< 23) ||| (xlo &&& 0x7fffff))
        if lo ≤ half && half ≤ hi then
          emitF2H ((sign <<< 31) ||| (e <<< 23) ||| (((qq <<< k) ||| half) &&& 0x7fffff))
        if hi > half then
          emitF2H ((sign <<< 31) ||| (e <<< 23) ||| (xhi &&& 0x7fffff))
  -- e in [0, 101]: everything flushes to +-0 (validated by audit);
  -- one witness per (e, sign) fiber: the all-ones mantissa.
  for e in [0:102] do
    for sign in [0, 1] do
      emitF2H ((sign <<< 31) ||| (e <<< 23) ||| 0x7fffff)

/-- All half bit patterns, expanded to float bits. -/
def runH2F : IO Unit := do
  for h in List.range 65536 do
    let bits := halfToFloatBits (UInt16.ofNat h)
    IO.println s!"{hexW 4 h} {hexW 8 bits.toNat}"

def main (args : List String) : IO Unit := do
  match args with
  | ["h2f"] => runH2F
  | ["f2h"] => runF2H
  | _ => do
    IO.println "usage: halfcheck {h2f|f2h}"
    IO.Process.exit 2
