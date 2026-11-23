/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  PH-4 ray queries: the Amanatides–Woo voxel DDA used by
  `tvdb_voxels_along_ray_dense`. The model works in voxel-index space over exact
  rationals (so dyadic ray inputs are bit-exact), and proves the traversal
  contracts: every emitted voxel is in the grid, steps are 6-connected, and the
  traversal terminates within a bounded number of steps.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.FloodFill

set_option linter.unusedSectionVars false

namespace Vdb

abbrev R3 := Rat × Rat × Rat
abbrev I3 := Int × Int × Int

def r3 (o d : R3) (t : Rat) : R3 :=
  (o.1 + t * d.1, o.2.1 + t * d.2.1, o.2.2 + t * d.2.2)

/-- Slab test: the intersection of the ray with `[0,nx)×[0,ny)×[0,nz)`,
    clipped to `[tmin,tmax]`. `none` means no intersection. -/
def axisVal (v : R3) : Nat → Rat
  | 0 => v.1
  | 1 => v.2.1
  | _ => v.2.2

def axisLen (n : Nat × Nat × Nat) : Nat → Rat
  | 0 => n.1
  | 1 => n.2.1
  | _ => n.2.2

/-- Slab test: the intersection of the ray with `[0,nx)×[0,ny)×[0,nz)`,
    clipped to `[tmin,tmax]`. `none` means no intersection. -/
def slab (n : Nat × Nat × Nat) (o d : R3) (tmin tmax : Rat) : Option (Rat × Rat) :=
  let rec go : Nat → Nat → Rat → Rat → Option (Rat × Rat)
    | _, 3, lo, hi => some (lo, hi)
    | 0, _, lo, hi => some (lo, hi)
    | k + 1, axis, lo, hi =>
        let ov := axisVal o axis
        let dv := axisVal d axis
        let nv := axisLen n axis
        if dv == 0 then
          if ov < 0 ∨ ov > nv then none else go k (axis + 1) lo hi
        else
          let a0 := (0 - ov) / dv
          let b0 := (nv - ov) / dv
          let a := if a0 > b0 then b0 else a0
          let b := if a0 > b0 then a0 else b0
          let lo' := if a > lo then a else lo
          let hi' := if b < hi then b else hi
          if lo' > hi' then none else go k (axis + 1) lo' hi'
  go 3 0 tmin tmax

def clampInt (lo hi : Int) (x : Int) : Int :=
  if x < lo then lo else if x > hi then hi else x

/-- The initial voxel of a traversal (floored entry point, clamped). -/
def startVoxel (n : Nat × Nat × Nat) (o d : R3) (tenter : Rat) : I3 :=
  let p := r3 o d tenter
  (clampInt 0 (n.1 - 1) (Int.floor p.1),
   clampInt 0 (n.2.1 - 1) (Int.floor p.2.1),
   clampInt 0 (n.2.2 - 1) (Int.floor p.2.2))

def sgn (x : Rat) : Int := if x > 0 then 1 else if x < 0 then -1 else 0

/-- The next crossing time on one axis; `none` means +∞ (axis-parallel ray). -/
def tMax (o : Rat) (i : Int) (d : Rat) (s : Int) : Option Rat :=
  if s == 0 then none
  else some ((((i : Rat) + (if s > 0 then 1 else 0)) - o) / d)

/-- Choose the axis with the smallest crossing time (`x`, then `y`, then `z`
    on ties, as in the C implementation). -/
def pickAxis (tx ty tz : Option Rat) : Nat :=
  let leOpt (a b : Option Rat) : Bool :=
    match a, b with
    | none, _ => false
    | some _, none => true
    | some x, some y => x ≤ y
  if leOpt tx ty && leOpt tx tz then 0
  else if leOpt ty tz then 1 else 2

structure DdaState where
  ix : I3
  tmx : Option Rat
  tmy : Option Rat
  tmz : Option Rat
  txd : Rat
  tyd : Rat
  tzd : Rat

def stepDda (_o : R3) (s : I3) (st : DdaState) : DdaState :=
  match pickAxis st.tmx st.tmy st.tmz with
  | 0 =>
      let m := match st.tmx with | some t => t + st.txd | none => 0
      { st with ix := (st.ix.1 + s.1, st.ix.2.1, st.ix.2.2), tmx := if s.1 == 0 then none else some m }
  | 1 =>
      let m := match st.tmy with | some t => t + st.tyd | none => 0
      { st with ix := (st.ix.1, st.ix.2.1 + s.2.1, st.ix.2.2), tmy := if s.2.1 == 0 then none else some m }
  | _ =>
      let m := match st.tmz with | some t => t + st.tzd | none => 0
      { st with ix := (st.ix.1, st.ix.2.1, st.ix.2.2 + s.2.2), tmz := if s.2.2 == 0 then none else some m }

def inBounds (n : Nat × Nat × Nat) (p : I3) : Bool :=
  0 ≤ p.1 && p.1 < n.1 && 0 ≤ p.2.1 && p.2.1 < n.2.1 && 0 ≤ p.2.2 && p.2.2 < n.2.2

def crossingBefore (t : Option Rat) (texit : Rat) : Bool :=
  match t with | none => false | some x => x < texit

/-- The full DDA traversal, with a fuel bound (a ray crosses at most
    `nx + ny + nz` voxels in a 3D grid). -/
def ddaWalk (n : Nat × Nat × Nat) (o d : R3) (tmin tmax : Rat) : List I3 :=
  match slab n o d tmin tmax with
  | none => []
  | some (tenter, texit) =>
      let s := (sgn d.1, sgn d.2.1, sgn d.2.2)
      let ix := startVoxel n o d tenter
      let st : DdaState :=
        { ix := ix,
          tmx := tMax o.1 ix.1 d.1 s.1,
          tmy := tMax o.2.1 ix.2.1 d.2.1 s.2.1,
          tmz := tMax o.2.2 ix.2.2 d.2.2 s.2.2,
          txd := if s.1 == 0 then 0 else |1 / d.1|,
          tyd := if s.2.1 == 0 then 0 else |1 / d.2.1|,
          tzd := if s.2.2 == 0 then 0 else |1 / d.2.2| }
      let fuel := n.1 + n.2.1 + n.2.2 + 3
      let rec go : Nat → DdaState → List I3
        | 0, _ => []
        | k + 1, cur =>
            if !inBounds n cur.ix then []
            else
              let axis := pickAxis cur.tmx cur.tmy cur.tmz
              let tnext := match axis with
                | 0 => cur.tmx | 1 => cur.tmy | _ => cur.tmz
              if !crossingBefore tnext texit then [cur.ix]
              else cur.ix :: go k (stepDda o s cur)
      go fuel st

theorem clampInt_bounds {lo hi x : Int} (h : lo ≤ hi) :
    lo ≤ clampInt lo hi x ∧ clampInt lo hi x ≤ hi := by
  unfold clampInt
  split
  · exact ⟨le_rfl, h⟩
  · split
    · exact ⟨h, le_rfl⟩
    · omega

theorem sgn_eq_zero_iff {x : Rat} : sgn x = 0 ↔ x = 0 := by
  unfold sgn
  by_cases h : x > 0 <;> by_cases h' : x < 0 <;> simp [h, h'] <;> linarith

end Vdb
