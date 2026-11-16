/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  The general-`r` closed form of the staircase face count on the L¹ ball
  (`Vdb/StaircaseRatio.lean`): on the `(2r+1)`-box the directed face count is
  `12 r² + 12 r + 6` for **every** `r`.

  Proof outline. The count is a triple sum over the box of a per-point
  indicator. Splitting the six directions by axis, the sum along one axis,
  for a fixed cross-section `(y, z)`, is `2` if `(y, z)` lies in the planar
  L¹ diamond of radius `r` and `0` otherwise: the two directions along the
  axis exit the ball exactly at the two ends of the chord (a pointwise
  identity). So each axis contributes `2 |D_r|`, where `|D_r|` is the number
  of lattice points of the radius-`r` diamond, `2 r² + 2 r + 1`.

  Together with `StaircaseRatio.overshoot_of_closed_form` this makes the
  overshoot of the staircase estimator over the true octahedron area
  (`√3 ·` area `≤` faces) unconditional.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.StaircaseRatio

set_option linter.unusedSimpArgs false

namespace Vdb

namespace StaircaseRatio

/-! ### Step 1: the count as a triple `Finset` sum -/

theorem sum_map_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

theorem sum_map_flatMap {α β : Type} (l : List α) (g : α → List β) (G : β → ℕ) :
    ((l.flatMap g).map G).sum = (l.map fun a => ((g a).map G).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem foldl_filter_map {α : Type} (P : α → Bool) (f : α → ℕ) (l : List α) :
    List.foldl (· + ·) 0 ((l.filter P).map f) = (l.map fun a => if P a then f a else 0).sum := by
  rw [← List.sum_eq_foldl]
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : P a = true
    · simp [h, ih]
    · have h' : P a = false := by simpa using h
      simp [h', ih]

theorem flatMap_singleton_eq_map {α β : Type} (f : α → β) (l : List α) :
    l.flatMap (fun a => [f a]) = l.map f := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem cast_list (n : ℕ) :
    (do let a ← List.range n; pure (a : ℤ) : List ℤ)
      = (List.range n).map (fun (a : ℕ) => (a : ℤ)) := by
  simp only [bind_pure_comp, List.map_eq_flatMap]
  exact (flatMap_singleton_eq_map _ _).symm ▸ rfl

theorem allPoints_eq (n : ℕ) : allPoints n =
    (List.range n).flatMap fun (x : ℕ) => (List.range n).flatMap fun (y : ℕ) =>
      (List.range n).map fun (z : ℕ) => ((x : ℤ), (y : ℤ), (z : ℤ)) := by
  unfold allPoints
  generalize hL : (do let a ← List.range n; pure (a : ℤ) : List ℤ) = L
  have hL' : L = (List.range n).map (fun (a : ℕ) => (a : ℤ)) := by rw [← hL]; exact cast_list n
  subst hL'
  simp only [List.flatMap_map, List.map_map]
  rfl

/-- The per-point face indicator count: `0` off the ball, otherwise the number
    of the six axis directions that leave it. -/
def G (n r : ℕ) (p : ℤ × ℤ × ℤ) : ℕ :=
  if deep n r p then
    (dirs.filter fun d => !deep n r (p.1 + d.1, p.2.1 + d.2.1, p.2.2 + d.2.2)).length
  else 0

theorem l1BallFaces_eq_sum (n r : ℕ) :
    l1BallFaces n r = ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n,
      G n r ((x : ℤ), (y : ℤ), (z : ℤ)) := by
  unfold l1BallFaces
  simp only
  rw [foldl_filter_map, allPoints_eq]
  have : ∀ p : ℤ × ℤ × ℤ, (if deep n r p then
        (dirs.filter fun d => !deep n r (p.1 + d.1, p.2.1 + d.2.1, p.2.2 + d.2.2)).length else 0)
        = G n r p := fun p => rfl
  simp only [this]
  rw [sum_map_flatMap, sum_map_range]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sum_map_flatMap, sum_map_range]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [List.map_map, sum_map_range]
  rfl

/-! ### Step 2: the line sum -/

/-- Exiting in the `+` axis direction at position `x`, cross-section weight `m`. -/
def lineP (r x m : ℕ) : ℕ :=
  if Int.natAbs ((x : ℤ) - r) + m ≤ r ∧ ¬ (Int.natAbs ((x : ℤ) + 1 - r) + m ≤ r) then 1 else 0

/-- Exiting in the `-` axis direction. -/
def lineM (r x m : ℕ) : ℕ :=
  if Int.natAbs ((x : ℤ) - r) + m ≤ r ∧ ¬ (Int.natAbs ((x : ℤ) + -1 - r) + m ≤ r) then 1 else 0

/-- The two axis directions exiting the ball at position `x`, for a
    cross-section of L¹ weight `m`. -/
def lineTerm (r x m : ℕ) : ℕ := lineP r x m + lineM r x m

/-- **The line sum**: along one axis, a cross-section of weight `m ≤ r`
    contributes exactly `2` exiting directions, and one of weight `m > r`
    contributes none. -/
theorem line_sum (r m : ℕ) :
    ∑ x ∈ Finset.range (2 * r + 1), lineTerm r x m = if m ≤ r then 2 else 0 := by
  by_cases hm : m ≤ r
  · have hpt : ∀ x ∈ Finset.range (2 * r + 1), lineTerm r x m
        = (if x = r + (r - m) then 1 else 0) + (if x = r - (r - m) then 1 else 0) := by
      intro x _
      unfold lineTerm lineP lineM
      split_ifs <;> omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq']
    have h1 : r + (r - m) < 2 * r + 1 := by omega
    have h2 : r - (r - m) < 2 * r + 1 := by omega
    simp [h1, h2, hm]
  · have h0 : (if m ≤ r then 2 else 0) = 0 := by simp [hm]
    rw [h0]
    refine Finset.sum_eq_zero fun x _ => ?_
    unfold lineTerm lineP lineM
    split_ifs <;> omega

/-! ### Step 3: the planar L¹ diamond has `2 r² + 2 r + 1` points -/

/-- For a fixed `y` at L¹ distance `a ≤ r` from the centre, the `z` values of
    the box inside the diamond number `2 (r - a) + 1`. -/
theorem diamond_inner (r a : ℕ) (ha : a ≤ r) :
    ∑ z ∈ Finset.range (2 * r + 1), (if a + Int.natAbs ((z : ℤ) - r) ≤ r then 1 else 0)
      = 2 * (r - a) + 1 := by
  rw [Finset.sum_boole]
  have hset : (Finset.range (2 * r + 1)).filter (fun (z : ℕ) => a + Int.natAbs ((z : ℤ) - r) ≤ r)
      = Finset.Ico a (2 * r - a + 1) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset, Nat.card_Ico]
  simp only [Nat.cast_id]
  omega

/-- The weights `r - |y - r|` over the box sum to `r²`. -/
theorem weight_sum (r : ℕ) :
    ∑ y ∈ Finset.range (2 * r + 1), (r - Int.natAbs ((y : ℤ) - r)) = r ^ 2 := by
  have hsplit : 2 * r + 1 = r + (r + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have h1 : ∑ y ∈ Finset.range r, (r - Int.natAbs ((y : ℤ) - r)) = ∑ y ∈ Finset.range r, y := by
    refine Finset.sum_congr rfl fun y hy => ?_
    have := Finset.mem_range.mp hy
    omega
  have h2 : ∑ k ∈ Finset.range (r + 1), (r - Int.natAbs (((r + k : ℕ) : ℤ) - r))
      = ∑ k ∈ Finset.range (r + 1), (r - k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_range.mp hk
    omega
  have h3 : ∑ k ∈ Finset.range (r + 1), (r - k) = ∑ k ∈ Finset.range (r + 1), k := by
    have := Finset.sum_range_reflect (fun k => k) (r + 1)
    simpa using this
  rw [h1, h2, h3]
  have g1 := Finset.sum_range_id_mul_two r
  have g2 := Finset.sum_range_id_mul_two (r + 1)
  rcases r with _ | r
  · simp
  · simp only [Nat.add_sub_cancel] at g1 g2
    nlinarith

/-- **The diamond count**: the radius-`r` planar L¹ diamond has `2 r² + 2 r + 1`
    lattice points. -/
theorem diamond_card (r : ℕ) :
    ∑ y ∈ Finset.range (2 * r + 1), ∑ z ∈ Finset.range (2 * r + 1),
      (if Int.natAbs ((y : ℤ) - r) + Int.natAbs ((z : ℤ) - r) ≤ r then 1 else 0)
      = 2 * r ^ 2 + 2 * r + 1 := by
  have hin : ∀ y ∈ Finset.range (2 * r + 1),
      ∑ z ∈ Finset.range (2 * r + 1),
        (if Int.natAbs ((y : ℤ) - r) + Int.natAbs ((z : ℤ) - r) ≤ r then 1 else 0)
      = 2 * (r - Int.natAbs ((y : ℤ) - r)) + 1 := by
    intro y hy
    have := Finset.mem_range.mp hy
    exact diamond_inner r _ (by omega)
  rw [Finset.sum_congr rfl hin, Finset.sum_add_distrib, ← Finset.mul_sum, weight_sum]
  simp
  ring

/-! ### Step 4: axis decomposition and the closed form -/

theorem deep_iff (r : ℕ) (a b c : ℤ) :
    deep (2 * r + 1) r (a, b, c)
      = decide (Int.natAbs (a - r) + Int.natAbs (b - r) + Int.natAbs (c - r) ≤ r) := by
  unfold deep
  have : (((2 * r + 1 : ℕ) : ℤ) - 1) / 2 = (r : ℤ) := by omega
  simp only [this]

theorem length_filter_eq_sum {α : Type} (P : α → Bool) (l : List α) :
    (l.filter P).length = (l.map fun a => if P a = true then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : P a = true
    · simp [List.filter_cons, h, ih, add_comm]
    · have h' : P a = false := by simpa using h
      simp [List.filter_cons, h', ih]

/-- Indicator that direction `d` leaves the ball from `p`. -/
def gT (r : ℕ) (p d : ℤ × ℤ × ℤ) : ℕ :=
  if deep (2 * r + 1) r p = true ∧
      deep (2 * r + 1) r (p.1 + d.1, p.2.1 + d.2.1, p.2.2 + d.2.2) = false then 1 else 0

/-- The per-point count as a sum over the six directions. -/
theorem G_eq_dirs (r : ℕ) (p : ℤ × ℤ × ℤ) :
    G (2 * r + 1) r p = (dirs.map (gT r p)).sum := by
  unfold G gT
  by_cases h : deep (2 * r + 1) r p = true
  · simp only [h, true_and, ↓reduceIte]
    rw [length_filter_eq_sum]
    congr 1
    refine List.map_congr_left fun d _ => ?_
    simp
  · simp [h]

theorem gT_px (r x y z : ℕ) : gT r ((x : ℤ), (y : ℤ), (z : ℤ)) (1, 0, 0)
    = lineP r x (Int.natAbs ((y : ℤ) - r) + Int.natAbs ((z : ℤ) - r)) := by
  unfold gT lineP; simp only [deep_iff, add_zero]; split_ifs <;> simp_all <;> omega

theorem gT_mx (r x y z : ℕ) : gT r ((x : ℤ), (y : ℤ), (z : ℤ)) (-1, 0, 0)
    = lineM r x (Int.natAbs ((y : ℤ) - r) + Int.natAbs ((z : ℤ) - r)) := by
  unfold gT lineM; simp only [deep_iff, add_zero]; split_ifs <;> simp_all <;> omega

theorem gT_py (r x y z : ℕ) : gT r ((x : ℤ), (y : ℤ), (z : ℤ)) (0, 1, 0)
    = lineP r y (Int.natAbs ((x : ℤ) - r) + Int.natAbs ((z : ℤ) - r)) := by
  unfold gT lineP; simp only [deep_iff, add_zero]; split_ifs <;> simp_all <;> omega

theorem gT_my (r x y z : ℕ) : gT r ((x : ℤ), (y : ℤ), (z : ℤ)) (0, -1, 0)
    = lineM r y (Int.natAbs ((x : ℤ) - r) + Int.natAbs ((z : ℤ) - r)) := by
  unfold gT lineM; simp only [deep_iff, add_zero]; split_ifs <;> simp_all <;> omega

theorem gT_pz (r x y z : ℕ) : gT r ((x : ℤ), (y : ℤ), (z : ℤ)) (0, 0, 1)
    = lineP r z (Int.natAbs ((x : ℤ) - r) + Int.natAbs ((y : ℤ) - r)) := by
  unfold gT lineP; simp only [deep_iff, add_zero]; split_ifs <;> simp_all <;> omega

theorem gT_mz (r x y z : ℕ) : gT r ((x : ℤ), (y : ℤ), (z : ℤ)) (0, 0, -1)
    = lineM r z (Int.natAbs ((x : ℤ) - r) + Int.natAbs ((y : ℤ) - r)) := by
  unfold gT lineM; simp only [deep_iff, add_zero]; split_ifs <;> simp_all <;> omega

/-- The per-point count splits by axis. -/
theorem G_eq (r x y z : ℕ) :
    G (2 * r + 1) r ((x : ℤ), (y : ℤ), (z : ℤ))
      = lineTerm r x (Int.natAbs ((y : ℤ) - r) + Int.natAbs ((z : ℤ) - r))
        + lineTerm r y (Int.natAbs ((x : ℤ) - r) + Int.natAbs ((z : ℤ) - r))
        + lineTerm r z (Int.natAbs ((x : ℤ) - r) + Int.natAbs ((y : ℤ) - r)) := by
  rw [G_eq_dirs]
  simp only [dirs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, gT_px, gT_mx,
    gT_py, gT_my, gT_pz, gT_mz, lineTerm]
  omega

/-- Twice the diamond count. -/
theorem diamond2 (r : ℕ) :
    ∑ a ∈ Finset.range (2 * r + 1), ∑ b ∈ Finset.range (2 * r + 1),
      (if Int.natAbs ((a : ℤ) - r) + Int.natAbs ((b : ℤ) - r) ≤ r then 2 else 0)
      = 2 * (2 * r ^ 2 + 2 * r + 1) := by
  rw [← diamond_card, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

/-- **The closed form of the staircase face count** for every `r`:
    the directed faces of the L¹ ball of radius `r` on the `(2r+1)`-box
    number `12 r² + 12 r + 6`. -/
theorem l1BallFaces_closed (r : ℕ) :
    l1BallFaces (2 * r + 1) r = 12 * r ^ 2 + 12 * r + 6 := by
  rw [l1BallFaces_eq_sum]
  simp only [G_eq, Finset.sum_add_distrib]
  have hx : ∑ x ∈ Finset.range (2 * r + 1), ∑ y ∈ Finset.range (2 * r + 1),
      ∑ z ∈ Finset.range (2 * r + 1),
        lineTerm r x (Int.natAbs ((y : ℤ) - r) + Int.natAbs ((z : ℤ) - r))
      = 2 * (2 * r ^ 2 + 2 * r + 1) := by
    rw [Finset.sum_comm]
    have : ∀ y ∈ Finset.range (2 * r + 1), ∑ x ∈ Finset.range (2 * r + 1),
        ∑ z ∈ Finset.range (2 * r + 1),
          lineTerm r x (Int.natAbs ((y : ℤ) - r) + Int.natAbs ((z : ℤ) - r))
        = ∑ z ∈ Finset.range (2 * r + 1),
          (if Int.natAbs ((y : ℤ) - r) + Int.natAbs ((z : ℤ) - r) ≤ r then 2 else 0) := by
      intro y _
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun z _ => line_sum r _
    rw [Finset.sum_congr rfl this]
    exact diamond2 r
  have hy : ∑ x ∈ Finset.range (2 * r + 1), ∑ y ∈ Finset.range (2 * r + 1),
      ∑ z ∈ Finset.range (2 * r + 1),
        lineTerm r y (Int.natAbs ((x : ℤ) - r) + Int.natAbs ((z : ℤ) - r))
      = 2 * (2 * r ^ 2 + 2 * r + 1) := by
    have : ∀ x ∈ Finset.range (2 * r + 1), ∑ y ∈ Finset.range (2 * r + 1),
        ∑ z ∈ Finset.range (2 * r + 1),
          lineTerm r y (Int.natAbs ((x : ℤ) - r) + Int.natAbs ((z : ℤ) - r))
        = ∑ z ∈ Finset.range (2 * r + 1),
          (if Int.natAbs ((x : ℤ) - r) + Int.natAbs ((z : ℤ) - r) ≤ r then 2 else 0) := by
      intro x _
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun z _ => line_sum r _
    rw [Finset.sum_congr rfl this]
    exact diamond2 r
  have hz : ∑ x ∈ Finset.range (2 * r + 1), ∑ y ∈ Finset.range (2 * r + 1),
      ∑ z ∈ Finset.range (2 * r + 1),
        lineTerm r z (Int.natAbs ((x : ℤ) - r) + Int.natAbs ((y : ℤ) - r))
      = 2 * (2 * r ^ 2 + 2 * r + 1) := by
    have : ∀ x ∈ Finset.range (2 * r + 1), ∑ y ∈ Finset.range (2 * r + 1),
        ∑ z ∈ Finset.range (2 * r + 1),
          lineTerm r z (Int.natAbs ((x : ℤ) - r) + Int.natAbs ((y : ℤ) - r))
        = ∑ y ∈ Finset.range (2 * r + 1),
          (if Int.natAbs ((x : ℤ) - r) + Int.natAbs ((y : ℤ) - r) ≤ r then 2 else 0) := by
      intro x _
      exact Finset.sum_congr rfl fun y _ => line_sum r _
    rw [Finset.sum_congr rfl this]
    exact diamond2 r
  rw [hx, hy, hz]
  ring

/-- **Unconditional overshoot**: for every `r`, the staircase face count of the
    L¹ ball is at least `√3` times the true octahedron area `4·√3·r²`. -/
theorem l1BallFaces_overshoot (r : ℕ) :
    Real.sqrt 3 * (4 * Real.sqrt 3 * (r : ℝ) ^ 2) ≤ (l1BallFaces (2 * r + 1) r : ℝ) :=
  overshoot_of_closed_form r _ (l1BallFaces_closed r)

/-- Strict form: the count strictly exceeds the true area, for every `r`. -/
theorem l1BallFaces_strict_overshoot (r : ℕ) :
    4 * Real.sqrt 3 * (r : ℝ) ^ 2 < (l1BallFaces (2 * r + 1) r : ℝ) :=
  strict_overshoot_of_closed_form r _ (l1BallFaces_closed r)


end StaircaseRatio

end Vdb
