/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  PH-4 ray queries: the SDF zero-crossing scan of `tvdb_segments_along_ray`.
  Samples along a ray are classified against an isovalue (`v < iso` is inside),
  and every state change emits an entry/exit pair with linearly interpolated
  crossing times. The interpolation parameter lies in `[0,1]` for a genuine
  sign change, which is the contract a contact/ray query relies on.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

namespace Vdb

/-- Linear interpolation parameter between two samples of opposite sign. -/
def crossingParam (a b : Rat) : Rat := a / (a - b)

theorem crossingParam_mem_Icc {a b : Rat} (ha : a < 0) (hb : 0 < b) :
    0 ≤ crossingParam a b ∧ crossingParam a b ≤ 1 := by
  have hne : a - b ≠ 0 := by linarith
  unfold crossingParam
  constructor
  · have hden : a - b < 0 := by linarith
    exact le_of_lt (div_pos_of_neg_of_neg ha hden)
  · rw [div_le_iff_of_neg (by linarith : a - b < 0)]
    nlinarith

theorem crossingParam_mem_Icc_of_pos {a b : Rat} (ha : 0 < a) (hb : b < 0) :
    0 ≤ crossingParam a b ∧ crossingParam a b ≤ 1 := by
  have hpos : 0 < a - b := by linarith
  unfold crossingParam
  constructor
  · exact div_nonneg (le_of_lt ha) (le_of_lt hpos)
  · rw [div_le_iff₀ hpos]
    linarith

/-- Scan a list of sampled field values at spacing `dt`; emit (entry, exit)
    parameter pairs for each contiguous inside run. -/
def scanCrossings (vs : List Rat) (iso : Rat) (dt : Rat) : List (Rat × Rat) :=
  match vs with
  | [] => []
  | v0 :: rest =>
      let rec go : Nat → Rat → Bool → Rat → List Rat → List (Rat × Rat)
        | i, _prev, inside, enter, [] =>
            if inside then [(enter, (i - 1 : Nat) * dt)] else []
        | i, prev, inside, enter, v :: tail =>
            let tprev := (i - 1 : Nat) * dt
            if (v < iso) = inside then
              go (i + 1) v inside enter tail
            else
              let cross := tprev + crossingParam (prev - iso) (v - iso) * dt
              if v < iso then go (i + 1) v true cross tail
              else (enter, cross) :: go (i + 1) v false enter tail
      go 1 v0 (v0 < iso) 0 rest

theorem scanCrossings_empty (iso dt : Rat) : scanCrossings [] iso dt = [] := rfl

theorem scanCrossings_all_outside (v iso dt : Rat) (h : iso ≤ v) :
    scanCrossings [v] iso dt = [] := by
  simp [scanCrossings, scanCrossings.go, not_lt.mpr h]

end Vdb
