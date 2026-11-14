/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Executable model of the NaN behaviour of the C `</>?/>=` comparisons used
  by the dense CSG/elementwise ops (`src/tinyvdb_ops.c`) and the mesh→SDF
  sign test (`src/tinyvdb_mesh_conversion.inl`).

  The C emitted form for `tvdb_csg_union` and friends is `a < b ? a : b`,
  which does **not** implement IEEE-754's `minNum`/`maxNum` (those drop NaN
  from *either* operand). The IEEE ordered comparisons used by the C code:

  * `a < b` is false when either operand is NaN;
  * `a >= b` is false when either operand is NaN;
  * `0.0/0.0` is NaN.

  Consequences, all executable here with `native_decide` on the actual
  IEEE double operations:

  * `x < NaN` is false and `NaN < x` is false, so `csgPick x NaN` returns
    `NaN` (the *right* operand's NaN propagates), while `csgPick NaN x`
    returns `x` (the left operand's NaN is dropped) — an **asymmetry**: the
    C union/difference depends on operand order under NaN;
  * IEEE `minNum`/`maxNum` (modelled by `floatMinNum`/`floatMaxNum`) drop
    NaN from *either* operand — what the C code would need for a NaN-
    tolerant CSG;
  * the mesh→SDF sign test `direction >= 0 ? 1 : -1` classifies a NaN
    direction as *inside* (`floatSDFSign_nan`).

  This is the NaN counterpart of the F11/F12 findings. The instances below
  are executed by `native_decide` on this platform's IEEE double semantics;
  a universally-quantified theory over every NaN payload is a
  `Float.Model`-level fact that is deliberately out of scope here.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

namespace Vdb

/-- A quiet NaN (`0/0`), evaluated by the native IEEE double semantics. -/
def nan : Float := 0.0 / 0.0

/-- The C pick: `a < b ? a : b` (IEEE ordered comparison; false on NaN).
    What `tvdb_csg_union`, `tvdb_csg_difference` and the elementwise
    min/max family emit. -/
def csgPick (a b : Float) : Float :=
  if a < b then a else b

/-- IEEE 754 `minNum(x, y)`: the non-NaN operand, or `y` if both are NaN. -/
def floatMinNum (x y : Float) : Float :=
  if y.isNaN then x else if x.isNaN then y else csgPick x y

/-- IEEE 754 `maxNum(x, y)`: the non-NaN operand, or `y` if both are NaN. -/
def floatMaxNum (x y : Float) : Float :=
  if x.isNaN then y else if y.isNaN then x else (if y < x then x else y)

/-- The C sign test `direction >= 0 ? 1 : -1` (mesh→SDF sign). -/
def floatSDFSign (x : Float) : Int :=
  if x >= 0.0 then 1 else -1

/-- `floatMinNum` is the min of two non-NaN values (sanity instance). -/
theorem floatMinNum_3_5 : floatMinNum 3.0 5.0 = 3.0 := by
  native_decide

theorem floatMinNum_5_3 : floatMinNum 5.0 3.0 = 3.0 := by
  native_decide

theorem floatMaxNum_3_5 : floatMaxNum 3.0 5.0 = 5.0 := by
  native_decide

/-- The C pick computes the minimum on non-NaN inputs. -/
theorem csgPick_3_5 : csgPick 3.0 5.0 = 3.0 := by
  native_decide

theorem csgPick_5_3 : csgPick 5.0 3.0 = 3.0 := by
  native_decide

/-- `x < NaN` is false (concrete). -/
theorem lt_nan_right : (3.0 < nan) = false := by
  native_decide

theorem lt_nan_left : (nan < 3.0) = false := by
  native_decide

/-- The C pick drops a NaN on the *left*: `pick NaN y = y` (concrete). -/
theorem csgPick_nan_left : csgPick nan 3.0 = 3.0 := by
  native_decide

/-- The C pick propagates a NaN on the *right*: `pick x NaN = NaN` (concrete). -/
theorem csgPick_nan_right : csgPick 3.0 nan = nan := by
  native_decide

/-- The C union/difference is therefore order-dependent under NaN. -/
theorem csg_nan_order_dependent : csgPick nan 3.0 ≠ csgPick 3.0 nan := by
  native_decide

/-- IEEE `minNum` drops NaN from both sides. -/
theorem floatMinNum_nan_left : floatMinNum nan 3.0 = 3.0 := by
  native_decide

theorem floatMinNum_nan_right : floatMinNum 3.0 nan = 3.0 := by
  native_decide

/-- IEEE `maxNum` drops NaN from both sides. -/
theorem floatMaxNum_nan_left : floatMaxNum nan 3.0 = 3.0 := by
  native_decide

theorem floatMaxNum_nan_right : floatMaxNum 3.0 nan = 3.0 := by
  native_decide

/-- Contrast: the C pick is *not* `minNum` (it propagates the right operand). -/
theorem csgPick_ne_minNum : csgPick 3.0 nan ≠ floatMinNum 3.0 nan := by
  native_decide

/-- The C pick drops a NaN on the left even against a NaN on the right. -/
theorem csgPick_nan_nan : csgPick nan nan = nan := by
  native_decide

/-- The C union of `nan` with itself vs with a number differs from `minNum`. -/
theorem csgPick_eq_minNum_nonnNaN : floatMinNum 3.0 5.0 = csgPick 3.0 5.0 := by
  native_decide

/-- The mesh→SDF sign test classifies a NaN direction as *inside*. -/
theorem floatSDFSign_nan : floatSDFSign nan = -1 := by
  native_decide

/-- The sign test on a negative direction is `-1`. -/
theorem floatSDFSign_neg : floatSDFSign (-1.5) = -1 := by
  native_decide

/-- The sign test on a positive direction is `1`. -/
theorem floatSDFSign_pos : floatSDFSign 1.5 = 1 := by
  native_decide

/-- The sign test on `0.0` is `1` (zero counts as outside the surface). -/
theorem floatSDFSign_zero : floatSDFSign 0.0 = 1 := by
  native_decide

/-- The sign test on `-0.0` is `1` (IEEE `-0.0 >= 0.0` is true). -/
theorem floatSDFSign_negzero : floatSDFSign (-0.0) = 1 := by
  native_decide

/-- Associativity of the min used by the elementwise ops, on non-NaN values. -/
theorem csgPick_min_assoc :
    csgPick (csgPick 1.0 2.0) 3.0 = csgPick 1.0 (csgPick 2.0 3.0) := by
  native_decide

theorem csgPick_min_assoc' :
    csgPick (csgPick 3.0 1.0) 2.0 = csgPick 3.0 (csgPick 1.0 2.0) := by
  native_decide
