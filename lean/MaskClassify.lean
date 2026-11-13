import VdbSpec

/-! Model-side enumeration for the mask-compression differential check.

Prints, for every 8-slot node (all 256 value masks × every assignment of the
five-symbol alphabet to the inactive slots — `sum_j C(8,j) 5^j = 6^8
= 1,679,616` nodes), one line:

```
mask assign code v0 v1 sel
```

`assign` enumerates inactive-slot assignments in base 5 (inactive slots in
increasing order, least significant digit first) and is identical to the C
harness `scripts/mask_classify_c.c`, so the outputs can be compared directly.
`code` is the wire code byte (0-6), `v0`/`v1` the eight lowercase hex digits
of the little-endian byte sequence of the stored inactive value ("-" when the
code carries no such value) and `sel` the two hex digits of the selection
byte ("-" when the code carries none).
-/

open Vdb

/-- The five float symbols used by the enumeration (and the C harness):
    bg, -bg, 2.5f, 3.5f, 4.5f, with bg = 1.5f. -/
def syms (i : Nat) : UInt32 :=
  match i with
  | 0 => 0x3FC00000
  | 1 => 0xBFC00000
  | 2 => 0x40200000
  | 3 => 0x40600000
  | 4 => 0x40800000
  | _ => 0x3FC00000

def bgVal : VoxelValue := .f32 0x3FC00000

def hexDigit (d : Nat) : Char :=
  if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

def byteHex (b : Nat) : String :=
  String.ofList [hexDigit ((b / 16) % 16), hexDigit (b % 16)]

/-- Hex of the little-endian byte sequence of a 32-bit word (matches the
    file's byte order and the C harness's `%02x%02x%02x%02x`). -/
def hexLE (b : UInt32) : String :=
  let n := b.toNat
  byteHex n ++ byteHex (n >>> 8) ++ byteHex (n >>> 16) ++ byteHex (n >>> 24)

def valHex (v : VoxelValue) : String :=
  match v with
  | .f32 b => hexLE b
  | _ => "??"

def line (mask assign : Nat) (c : Compressed) : String :=
  let code := c.code.toNat
  let v0 := if code == 2 || code == 4 || code == 5 then valHex c.val0 else "-"
  let v1 := if code == 5 then valHex c.val1 else "-"
  let sel :=
    if code == 3 || code == 4 || code == 5 then byteHex (c.selection % 256) else "-"
  s!"{mask} {assign} {code} {v0} {v1} {sel}"

def main : IO Unit := do
  for mask in List.range 256 do
    let inactive := (List.range 8).filter (fun i => !mask.testBit i)
    let nin := inactive.length
    let total := 5 ^ nin
    for assign in List.range total do
      let slots :=
        ((List.range nin).foldl (fun (acc : Array VoxelValue × Nat) i =>
          let (slots, a) := acc
          let sym := VoxelValue.f32 (syms (a % 5))
          (slots.set! inactive[i]! sym, a / 5)) ((List.replicate 8 bgVal).toArray, assign)).1
      let values : Nat → VoxelValue := fun i => slots.getD i bgVal
      let c := classify bgVal values mask 8
      IO.println (line mask assign c)
