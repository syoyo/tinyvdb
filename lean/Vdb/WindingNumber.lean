/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Generalized winding numbers (src/tinyvdb_winding.c).

  The C code evaluates the generalized winding number of a triangle soup
  about a point `p` as

      wn(p) = (1 / 4π) * Σ_faces 2 * atan2(num, den)

      num = (a - p) · ((b - p) × (c - p))
      den = |a - p| |b - p| |c - p|
          + (a - p)·(b - p) |c - p|
          + (b - p)·(c - p) |a - p|
          + (c - p)·(a - p) |b - p|

  (Van Oosterom and Strackee 1983, the `atan2` branch the C code uses).

  Here we model that formula and prove the basic structural facts the C
  implementation relies on:

  * orientation flip negates the solid angle (and, globally, the mesh
    winding number) — the sign chain the winding-number API is built on;
  * additivity over the face list (the sum the code accumulates);
  * translation invariance (the formula depends only on relative vectors);
  * rotation invariance under `Qᵀ Q = 1` with `Q.det = 1` (proper
    rotations), and negation under reflections (`Q.det = -1`) — the scalar
    triple product is a determinant, so those are determinant facts;
  * the generalized winding number of the whole mesh is invariant (or
    negates) as well.

  Branch note: `atan2'` models C's `atan2`. Where `num = 0` and `den < 0`
  the angle is `±π` and its sign flips under orientation reversal (a branch
  cut everywhere); the flip theorems are stated under `num ≠ 0`, which holds
  whenever `p` is not coplanar with the face — the C code has the same
  behaviour.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

namespace Vdb

open scoped Matrix

noncomputable section

/-! ### `atan2` model -/

/-- Model of C's `atan2(y, x)`: principal value of the angle, `x < 0`
    branch included. Total (unlike a naive `arctan(y / x)`). -/
def atan2' (y x : ℝ) : ℝ :=
  if x > 0 then Real.arctan (y / x)
  else if x = 0 then (if 0 < y then Real.pi / 2 else if y < 0 then -(Real.pi / 2) else 0)
  else if 0 ≤ y then Real.arctan (y / x) + Real.pi else Real.arctan (y / x) - Real.pi

/-- `atan2'` is odd in its first argument (for `y ≠ 0`; at `y = 0` and
    `x < 0` the two sides are `±π`, a branch cut). -/
theorem atan2'_neg_y (y : ℝ) (x : ℝ) (hy : y ≠ 0) : atan2' (-y) x = -atan2' y x := by
  rcases lt_trichotomy y 0 with hy' | hy' | hy'
  · simp only [atan2']
    split_ifs <;> simp_all [Real.arctan_neg, neg_div] <;> try linarith
  · exact absurd hy' hy
  · simp only [atan2']
    split_ifs <;> simp_all [Real.arctan_neg, neg_div] <;> try linarith

/-! ### 3-vectors and the scalar triple product -/

/-- A 3D vector (the winding code works on double triples). -/
structure V3 where
  x : ℝ
  y : ℝ
  z : ℝ
  deriving DecidableEq

theorem V3.ext {a b : V3} (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  cases a; cases b; subst hx; subst hy; subst hz; rfl

namespace V3

def add (a b : V3) : V3 := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩
def sub (a b : V3) : V3 := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩
def dot (a b : V3) : ℝ := a.x * b.x + a.y * b.y + a.z * b.z

/-- The 3×3 matrix whose columns are `a`, `b`, `c`. -/
def cols (a b c : V3) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![a.x, b.x, c.x], ![a.y, b.y, c.y], ![a.z, b.z, c.z]]

@[simp] theorem cols_00 (a b c : V3) : cols a b c 0 0 = a.x := rfl
@[simp] theorem cols_01 (a b c : V3) : cols a b c 0 1 = b.x := rfl
@[simp] theorem cols_02 (a b c : V3) : cols a b c 0 2 = c.x := rfl
@[simp] theorem cols_10 (a b c : V3) : cols a b c 1 0 = a.y := rfl
@[simp] theorem cols_11 (a b c : V3) : cols a b c 1 1 = b.y := rfl
@[simp] theorem cols_12 (a b c : V3) : cols a b c 1 2 = c.y := rfl
@[simp] theorem cols_20 (a b c : V3) : cols a b c 2 0 = a.z := rfl
@[simp] theorem cols_21 (a b c : V3) : cols a b c 2 1 = b.z := rfl
@[simp] theorem cols_22 (a b c : V3) : cols a b c 2 2 = c.z := rfl

/-- The scalar triple product, as a determinant (so rotation invariance and
    orientation flip are determinant facts). -/
def triple (a b c : V3) : ℝ := Matrix.det (cols a b c)

theorem triple_swap (a b c : V3) : triple a c b = - triple a b c := by
  have hσ : (⟨1, by decide⟩ : Fin 3) ≠ (⟨2, by decide⟩ : Fin 3) := by decide
  set σ : Equiv.Perm (Fin 3) := Equiv.swap ⟨1, by decide⟩ ⟨2, by decide⟩ with hσdef
  have hcols : cols a c b = (cols a b c).submatrix id σ := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [triple, triple, hcols, Matrix.det_permute']
  rw [hσdef, Equiv.Perm.sign_swap hσ]
  simp

/-- Matrix action on a vector (explicit unrolling; the winding code does the
    same thing on doubles). -/
def applyMat (Q : Matrix (Fin 3) (Fin 3) ℝ) (v : V3) : V3 :=
  ⟨Q 0 0 * v.x + Q 0 1 * v.y + Q 0 2 * v.z,
   Q 1 0 * v.x + Q 1 1 * v.y + Q 1 2 * v.z,
   Q 2 0 * v.x + Q 2 1 * v.y + Q 2 2 * v.z⟩

theorem sub_applyMat (Q : Matrix (Fin 3) (Fin 3) ℝ) (a b : V3) :
    sub (applyMat Q a) (applyMat Q b) = applyMat Q (sub a b) := by
  apply V3.ext <;> simp only [sub, applyMat] <;> ring

theorem sub_add_cancel_left (a t p : V3) : sub (add a t) (add p t) = sub a p := by
  apply V3.ext <;> simp only [add, sub] <;> ring

@[simp] theorem applyMat_sub (Q : Matrix (Fin 3) (Fin 3) ℝ) (a b : V3) :
    applyMat Q (sub a b) = sub (applyMat Q a) (applyMat Q b) :=
  (sub_applyMat Q a b).symm

/-- Columns of `Q` applied to `a`, `b`, `c` are `Q` times the columns. -/
theorem cols_applyMat (Q : Matrix (Fin 3) (Fin 3) ℝ) (a b c : V3) :
    cols (applyMat Q a) (applyMat Q b) (applyMat Q c) = Q * cols a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, applyMat]

/-- The scalar triple product is `det Q` times the original. -/
theorem triple_apply (Q : Matrix (Fin 3) (Fin 3) ℝ) (a b c : V3) :
    triple (applyMat Q a) (applyMat Q b) (applyMat Q c) = Q.det * triple a b c := by
  rw [triple, triple, cols_applyMat, Matrix.det_mul]

/-- Dot product of the unfolded matrix action. -/
theorem dot_applyMat (Q : Matrix (Fin 3) (Fin 3) ℝ) (a b : V3) :
    dot (applyMat Q a) (applyMat Q b) =
      (Q 0 0 * a.x + Q 0 1 * a.y + Q 0 2 * a.z) * (Q 0 0 * b.x + Q 0 1 * b.y + Q 0 2 * b.z)
    + (Q 1 0 * a.x + Q 1 1 * a.y + Q 1 2 * a.z) * (Q 1 0 * b.x + Q 1 1 * b.y + Q 1 2 * b.z)
    + (Q 2 0 * a.x + Q 2 1 * a.y + Q 2 2 * a.z) * (Q 2 0 * b.x + Q 2 1 * b.y + Q 2 2 * b.z) := rfl

/-- Dot products are preserved by any `Q` whose columns are orthonormal
    (`Qᵀ * Q = 1`). -/
theorem dot_apply (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Qᵀ * Q = 1) (a b : V3) :
    dot (applyMat Q a) (applyMat Q b) = dot a b := by
  have key : ∀ j k : Fin 3, ∑ i, Q i j * Q i k = if j = k then (1 : ℝ) else 0 := by
    intro j k
    have h1 : (Qᵀ * Q) j k = ∑ i, Q i j * Q i k := by
      rw [Matrix.mul_apply]
      simp [Matrix.transpose_apply]
    rw [hQ] at h1
    rw [← h1, Matrix.one_apply]
  have h00 := key 0 0
  have h01 := key 0 1
  have h02 := key 0 2
  have h10 := key 1 0
  have h11 := key 1 1
  have h12 := key 1 2
  have h20 := key 2 0
  have h21 := key 2 1
  have h22 := key 2 2
  simp only [Fin.sum_univ_three] at h00 h01 h02 h10 h11 h12 h20 h21 h22
  simp at h00 h01 h02 h10 h11 h12 h20 h21 h22
  rw [dot_applyMat]
  simp only [dot]
  linear_combination
    (a.x * b.x) * h00 + (a.y * b.y) * h11 + (a.z * b.z) * h22
  + (a.x * b.y) * h01 + (a.y * b.x) * h10
  + (a.x * b.z) * h02 + (a.z * b.x) * h20
  + (a.y * b.z) * h12 + (a.z * b.y) * h21

/-! ### The solid angle -/

/-- The solid angle (Van Oosterom–Strackee `atan2` form) of triangle
    `(a, b, c)` seen from `p`. -/
def solidAngle (a b c p : V3) : ℝ :=
  2 * atan2' (triple (sub a p) (sub b p) (sub c p))
    (Real.sqrt (dot (sub a p) (sub a p)) * Real.sqrt (dot (sub b p) (sub b p))
     * Real.sqrt (dot (sub c p) (sub c p))
     + dot (sub a p) (sub b p) * Real.sqrt (dot (sub c p) (sub c p))
     + dot (sub b p) (sub c p) * Real.sqrt (dot (sub a p) (sub a p))
     + dot (sub c p) (sub a p) * Real.sqrt (dot (sub b p) (sub b p)))

/-- The generalized winding number of a triangle soup about `p`,
    `(1 / 4π) Σ 2·atan2(num, den)`. -/
def meshWinding (fs : List (V3 × V3 × V3)) (p : V3) : ℝ :=
  ((fs.map fun f => solidAngle f.1 f.2.1 f.2.2 p).sum) / (4 * Real.pi)

/-- Negation distributes over `List.map` into `List.sum`. -/
theorem list_sum_map_neg {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map fun x => - f x).sum = - (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.sum_cons, ih]; ring

/-- Additivity: the winding number splits over face concatenation. -/
theorem meshWinding_append (fs gs : List (V3 × V3 × V3)) (p : V3) :
    meshWinding (fs ++ gs) p = meshWinding fs p + meshWinding gs p := by
  simp only [meshWinding, List.map_append, List.sum_append, add_div]

/-- Flipping the orientation of the triangle negates its solid angle
    (provided the point is not coplanar with it). -/
theorem solidAngle_flip (a b c p : V3) (h : triple (sub a p) (sub b p) (sub c p) ≠ 0) :
    solidAngle a c b p = - solidAngle a b c p := by
  have hden : Real.sqrt (dot (sub a p) (sub a p)) * Real.sqrt (dot (sub c p) (sub c p))
               * Real.sqrt (dot (sub b p) (sub b p))
              + dot (sub a p) (sub c p) * Real.sqrt (dot (sub b p) (sub b p))
              + dot (sub c p) (sub b p) * Real.sqrt (dot (sub a p) (sub a p))
              + dot (sub b p) (sub a p) * Real.sqrt (dot (sub c p) (sub c p))
            = Real.sqrt (dot (sub a p) (sub a p)) * Real.sqrt (dot (sub b p) (sub b p))
               * Real.sqrt (dot (sub c p) (sub c p))
              + dot (sub a p) (sub b p) * Real.sqrt (dot (sub c p) (sub c p))
              + dot (sub b p) (sub c p) * Real.sqrt (dot (sub a p) (sub a p))
              + dot (sub c p) (sub a p) * Real.sqrt (dot (sub b p) (sub b p)) := by
    simp only [dot]
    ring
  simp only [solidAngle]
  rw [hden]
  rw [triple_swap (sub a p) (sub c p) (sub b p)]
  have h2 : triple (sub a p) (sub c p) (sub b p) ≠ 0 := by
    rw [triple_swap (sub a p) (sub b p) (sub c p)]
    exact neg_ne_zero.mpr h
  rw [atan2'_neg_y _ _ h2]
  ring

/-- Orientation flip on the whole soup negates the winding number
    (point not coplanar with any face). -/
theorem meshWinding_reverse (fs : List (V3 × V3 × V3)) (p : V3)
    (h : ∀ f ∈ fs, triple (sub f.1 p) (sub f.2.1 p) (sub f.2.2 p) ≠ 0) :
    meshWinding (fs.map fun f => (f.1, f.2.2, f.2.1)) p = - meshWinding fs p := by
  simp only [meshWinding]
  have hmap : (fs.map fun f => (f.1, f.2.2, f.2.1)).map (fun f => solidAngle f.1 f.2.1 f.2.2 p)
            = fs.map (fun f => - solidAngle f.1 f.2.1 f.2.2 p) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro f hf
    exact solidAngle_flip f.1 f.2.1 f.2.2 p (h f hf)
  rw [hmap, list_sum_map_neg]
  ring

/-- Translation invariance of the solid angle. -/
theorem solidAngle_translate (t p a b c : V3) :
    solidAngle (add a t) (add b t) (add c t) (add p t) = solidAngle a b c p := by
  simp only [solidAngle]
  rw [sub_add_cancel_left a t p, sub_add_cancel_left b t p, sub_add_cancel_left c t p]

/-- Translation invariance: the winding number depends only on relative
    vectors, so shifting mesh and point together changes nothing. -/
theorem meshWinding_translate (t p : V3) (fs : List (V3 × V3 × V3)) :
    meshWinding (fs.map fun f => (add f.1 t, add f.2.1 t, add f.2.2 t)) (add p t) =
      meshWinding fs p := by
  simp only [meshWinding, List.map_map]
  apply congrArg (fun s => s / (4 * Real.pi))
  apply congrArg List.sum
  apply List.map_congr_left
  intro f _
  exact solidAngle_translate t p f.1 f.2.1 f.2.2

/-- Rotation invariance of the solid angle under `Qᵀ Q = 1`, `Q.det = 1`. -/
theorem solidAngle_rotate (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hO : Qᵀ * Q = 1) (hdet : Q.det = 1) (a b c p : V3) :
    solidAngle (applyMat Q a) (applyMat Q b) (applyMat Q c) (applyMat Q p) =
      solidAngle a b c p := by
  simp only [solidAngle]
  rw [sub_applyMat, sub_applyMat, sub_applyMat]
  rw [triple_apply Q (sub a p) (sub b p) (sub c p), hdet, one_mul]
  rw [dot_apply Q hO, dot_apply Q hO, dot_apply Q hO]
  rw [dot_apply Q hO, dot_apply Q hO, dot_apply Q hO]

/-- Reflection reverses the winding sign: `Qᵀ Q = 1`, `Q.det = -1`. -/
theorem solidAngle_reflect (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hO : Qᵀ * Q = 1) (hdet : Q.det = -1) (a b c p : V3)
    (h : triple (sub a p) (sub b p) (sub c p) ≠ 0) :
    solidAngle (applyMat Q a) (applyMat Q b) (applyMat Q c) (applyMat Q p) =
      - solidAngle a b c p := by
  simp only [solidAngle]
  rw [sub_applyMat, sub_applyMat, sub_applyMat]
  rw [triple_apply Q (sub a p) (sub b p) (sub c p), hdet]
  rw [dot_apply Q hO, dot_apply Q hO, dot_apply Q hO]
  rw [dot_apply Q hO, dot_apply Q hO, dot_apply Q hO]
  rw [neg_one_mul, atan2'_neg_y _ _ h]
  ring

/-- Rotation invariance: the winding number is unchanged when the soup and
    the query point are both transformed by a proper rotation. -/
theorem meshWinding_rotate (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hO : Qᵀ * Q = 1) (hdet : Q.det = 1)
    (fs : List (V3 × V3 × V3)) (p : V3) :
    meshWinding (fs.map fun f => (applyMat Q f.1, applyMat Q f.2.1, applyMat Q f.2.2))
      (applyMat Q p) = meshWinding fs p := by
  simp only [meshWinding, List.map_map]
  apply congrArg (fun s => s / (4 * Real.pi))
  apply congrArg List.sum
  apply List.map_congr_left
  intro f _
  exact solidAngle_rotate Q hO hdet f.1 f.2.1 f.2.2 p

/-- Reflection negates the winding number (soup and query point transformed
    by a determinant `-1` orthogonal matrix; no face coplanar with `p`). -/
theorem meshWinding_reflect (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hO : Qᵀ * Q = 1) (hdet : Q.det = -1)
    (fs : List (V3 × V3 × V3)) (p : V3)
    (h : ∀ f ∈ fs, triple (sub f.1 p) (sub f.2.1 p) (sub f.2.2 p) ≠ 0) :
    meshWinding (fs.map fun f => (applyMat Q f.1, applyMat Q f.2.1, applyMat Q f.2.2))
      (applyMat Q p) = - meshWinding fs p := by
  simp only [meshWinding]
  have hmap : (fs.map fun f => (applyMat Q f.1, applyMat Q f.2.1, applyMat Q f.2.2)).map
                  (fun f => solidAngle f.1 f.2.1 f.2.2 (applyMat Q p))
            = fs.map (fun f => - solidAngle f.1 f.2.1 f.2.2 p) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro f hf
    exact solidAngle_reflect Q hO hdet f.1 f.2.1 f.2.2 p (h f hf)
  rw [hmap, list_sum_map_neg]
  ring

end V3

end

end Vdb
