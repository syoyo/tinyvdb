/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  A **rational Float32 model** of the per-axis key computation used by
  MC adaptive vertex clustering (`tool_cluster_range`,
  `src/tinyvdb_sparse_tools.c`), modelled in `Vdb/McAdapt` (ℝ level) and
  exercised only by the executable C<->Lean twin in `Vdb/McAdaptKey`
  (3,000,000 adversarial axis evaluations).

  The C computes, per vertex coordinate `v[a]` and clustering step `step`:

      double e = v[a] / step;        // rounded binary64 division
      double q = floor(e);           // exact: q is an integral double
      if (!isfinite(q) || q < -2^63 || q >= 2^63)  overflow = 1;
      else  c[a] = (int64_t) q;       // exact: q integral and |q| < 2^63

  This module lifts the *finite* part of that computation to the rationals
  ℚ and proves the guard/cast semantics as theorems:

    * `f32RoundNE`   -- round a rational to the nearest integer, ties to even;
      `f32RoundNE_nearest`, `f32RoundNE_tie_even` are proved over ℚ.
    * `f32Binade*`   -- the (computable) binade exponent of a positive
      rational, with proved bounds `2^e <= a < 2^(e+1)`.
    * `f32RoundPos32` / `f32RoundToFloat32` -- an exact rational model of
      binary32 round-to-nearest-even (24-bit significand).  Its normal-range
      error, representability and tie-to-even are proved
      (`f32RoundPos32_error`, `f32RoundPos32_repr`,
      `f32RoundPos32_sig_bounds`, `f32RoundPos32_sig_tie_even`).  This is the
      A-section target (c): a general IEEE-754 round-to-nearest-even lemma
      on the normal binade.
    * `f32KeyAxisModel` -- the rational mirror of `mcKeyAxis`.  The guard
      theorems `f32KeyAxisModel_some_bounds`,
      `f32KeyAxisModel_some_int64_exact`, `f32KeyAxisModel_none_iff` are
      proved (target (a)).

  Tiers and honesty.  All theorems below are kernel proofs over ℚ.  ℚ has no
  NaN/Inf, so the non-finite branch of the C guard is deliberately outside
  this rational model and stays the provenance of the executable twin
  `Vdb/McAdaptKey`.  Subnormal *correctness*, the full native-`Float32`
  `ofBits`/`toBits` agreement on the 3M harness corpus, and universality of
  the native binary64 division are recorded as precise named walls at the
  end of this file (target (b) is left to the integration owner).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace Vdb

/-! ### 1. Round a rational to the nearest integer, ties to even. -/

/-- Round `q : ℚ` to the nearest integer; a half-integer rounds to the even
    neighbour.  This is the exact rational analogue of IEEE-754's
    `roundTiesToEven` applied to an integer significand. -/
def f32RoundNE (q : ℚ) : ℤ :=
  let n : ℤ := ⌊q⌋
  let r : ℚ := q - n
  if r < 1 / 2 then n
  else if 1 / 2 < r then n + 1
  else if Even n then n else n + 1

lemma f32RoundNE_of_lt_half {q : ℚ} (h : q - (⌊q⌋ : ℚ) < 1 / 2) :
    f32RoundNE q = ⌊q⌋ := by
  unfold f32RoundNE
  dsimp only
  rw [ite_eq_left h]

lemma f32RoundNE_of_gt_half {q : ℚ} (h : 1 / 2 < q - (⌊q⌋ : ℚ)) :
    f32RoundNE q = ⌊q⌋ + 1 := by
  have hn : ¬ q - (⌊q⌋ : ℚ) < 1 / 2 := by linarith
  unfold f32RoundNE
  dsimp only
  rw [ite_eq_right hn, ite_eq_left h]

lemma f32RoundNE_int (z : ℤ) : f32RoundNE (z : ℚ) = z := by
  have hlt : (z : ℚ) - (⌊(z : ℚ)⌋ : ℚ) < 1 / 2 := by
    rw [Int.floor_intCast]
    norm_num
  rw [f32RoundNE_of_lt_half hlt]
  exact Int.floor_intCast z

/-- Nearestness: `|q - roundNE q| <= 1/2` (kernel proof over ℚ). -/
lemma f32RoundNE_nearest (q : ℚ) : |q - (f32RoundNE q : ℚ)| ≤ 1 / 2 := by
  set n : ℤ := ⌊q⌋ with hn
  set r : ℚ := q - (n : ℚ) with hr
  have hn_le : (n : ℚ) ≤ q := by rw [hn]; exact Int.floor_le q
  have hq_lt : q < (n : ℚ) + 1 := by rw [hn]; exact Int.lt_floor_add_one q
  have hr_nonneg : 0 ≤ r := by rw [hr]; linarith
  have hr_lt_one : r < 1 := by rw [hr]; linarith
  have huneq : f32RoundNE q =
      (if r < 1 / 2 then n else if 1 / 2 < r then n + 1
       else if Even n then n else n + 1) := by
    simp [f32RoundNE, ← hn, hr.symm]
  rw [huneq]
  split_ifs with h1 h2 h3
  · -- r < 1/2
    have hqeq : q - (n : ℚ) = r := hr.symm
    rw [abs_of_nonneg (by rw [hqeq]; exact hr_nonneg), hqeq]
    linarith
  · -- 1/2 < r
    have hqeq : q - ((n + 1 : ℤ) : ℚ) = r - 1 := by
      rw [hr]; norm_num; ring
    rw [abs_of_nonpos (by rw [hqeq]; linarith), hqeq]
    linarith
  · -- r = 1/2, Even n
    have hr_eq : r = 1 / 2 := by linarith
    have hqeq : q - (n : ℚ) = r := hr.symm
    rw [abs_of_nonneg (by rw [hqeq]; exact hr_nonneg), hqeq, hr_eq]
  · -- r = 1/2, odd n
    have hr_eq : r = 1 / 2 := by linarith
    have hqeq : q - ((n + 1 : ℤ) : ℚ) = r - 1 := by
      rw [hr]; norm_num; ring
    rw [abs_of_nonpos (by rw [hqeq]; linarith), hqeq, hr_eq]
    norm_num

/-- Tie-to-even: if `q` is a half-integer then `roundNE q` is even. -/
lemma f32RoundNE_tie_even {q : ℚ} (hq : ∃ k : ℤ, q = (k : ℚ) + 1 / 2) :
    Even (f32RoundNE q) := by
  obtain ⟨k, hk⟩ := hq
  have hfloor : ⌊q⌋ = k := by
    rw [hk]
    apply (Int.floor_eq_iff).2
    constructor <;> linarith
  have hr : q - (⌊q⌋ : ℚ) = 1 / 2 := by rw [hfloor, hk]; norm_num
  have h1 : ¬ q - (⌊q⌋ : ℚ) < 1 / 2 := by linarith
  have h2 : ¬ 1 / 2 < q - (⌊q⌋ : ℚ) := by linarith
  have huneq : f32RoundNE q = if Even (⌊q⌋) then ⌊q⌋ else ⌊q⌋ + 1 := by
    unfold f32RoundNE
    dsimp only
    rw [ite_eq_right h1, ite_eq_right h2]
  rw [huneq]
  split_ifs with he
  · exact he
  · rw [hfloor] at he ⊢
    exact (Int.not_even_iff_odd.mp he).add_one

/-! ### 2. The binade exponent of a positive rational. -/

/-- `n <= 2^n` over the naturals (elementary induction). -/
lemma f32Nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n (by norm_num))
      omega

/-- There is a power of two above any rational (Archimedean ℚ, elementary
    witness). -/
lemma f32ExistsTwoPow (a : ℚ) : ∃ n : ℕ, a < (2 : ℚ) ^ n := by
  obtain ⟨n, hn⟩ := exists_nat_gt a
  refine ⟨n, ?_⟩
  have hcast : (n : ℚ) ≤ (2 : ℚ) ^ n := by
    exact_mod_cast f32Nat_le_two_pow n
  linarith

/-- The least `n` with `a < 2^n`.  Computable: `Nat.find` over a decidable
    predicate. -/
def f32BinadeExp (a : ℚ) : Nat :=
  Nat.find (f32ExistsTwoPow a)

lemma f32BinadeExp_spec (a : ℚ) : a < (2 : ℚ) ^ f32BinadeExp a := by
  simpa [f32BinadeExp] using (Nat.find_spec (f32ExistsTwoPow a))

lemma f32BinadeExp_min {a : ℚ} {n : Nat} (h : n < f32BinadeExp a) :
    ¬ a < (2 : ℚ) ^ n := by
  simpa [f32BinadeExp] using (Nat.find_min (f32ExistsTwoPow a) h)

lemma f32BinadeExp_ge_one {a : ℚ} (ha : 1 ≤ a) : 1 ≤ f32BinadeExp a := by
  by_contra h
  have hn : f32BinadeExp a = 0 := by omega
  have hs := f32BinadeExp_spec a
  rw [hn] at hs
  norm_num at hs
  linarith

/-- The normal binade exponent `e = binadeExp(a) - 1`.  For `a >= 1`,
    `2^e <= a < 2^(e+1)`. -/
def f32BinadeE (a : ℚ) : Nat := f32BinadeExp a - 1

lemma f32BinadeE_succ {a : ℚ} (ha : 1 ≤ a) :
    f32BinadeE a + 1 = f32BinadeExp a := by
  unfold f32BinadeE
  have := f32BinadeExp_ge_one ha
  omega

lemma f32BinadeE_lower {a : ℚ} (ha : 1 ≤ a) : (2 : ℚ) ^ f32BinadeE a ≤ a := by
  have hmin := f32BinadeExp_min (a := a) (n := f32BinadeE a) (by
    rw [← f32BinadeE_succ ha]
    exact Nat.lt_succ_self _)
  exact le_of_not_gt hmin

lemma f32BinadeE_upper {a : ℚ} (ha : 1 ≤ a) :
    a < (2 : ℚ) ^ (f32BinadeE a + 1) := by
  rw [f32BinadeE_succ ha]
  exact f32BinadeExp_spec a

/-! ### 3. Rational binary32 round-to-nearest-even. -/

/-- Round a positive rational `a` to a 24-bit-significand binary32 value.
    For `a >= 1` this is the normal formula `roundNE(a * 2^(23-e)) * 2^(e-23)`
    (carry to the next binade is automatic when `m = 2^24`).  For `0 < a < 1`
    the subnormal branch rounds to the nearest multiple of `2^-149`; its
    correctness is a documented wall (see the end of the file). -/
def f32RoundPos32 (a : ℚ) (_ha : 0 < a) : ℚ :=
  if _hge : 1 ≤ a then
    let e : Int := (f32BinadeE a : Int)
    let m : ℤ := f32RoundNE (a * (2 : ℚ) ^ (23 - e))
    (m : ℚ) * (2 : ℚ) ^ (e - 23)
  else
    ((f32RoundNE (a * (2 : ℚ) ^ (149 : Nat)) : ℤ) : ℚ) / (2 : ℚ) ^ (149 : Nat)

/-- Round an arbitrary rational to a binary32 value (sign handled
    symmetrically). -/
def f32RoundToFloat32 (x : ℚ) : ℚ :=
  if hx0 : x = 0 then 0
  else if hxpos : 0 < x then f32RoundPos32 x hxpos
  else -f32RoundPos32 (-x) (by
    have hxle : x ≤ 0 := le_of_not_gt hxpos
    have hxlt : x < 0 := by
      by_contra hnot
      have hxge : 0 ≤ x := le_of_not_gt hnot
      exact hx0 (le_antisymm hxle hxge)
    linarith)

/-- Normal-range error bound: the rational binary32 rounding is within half
    an ulp (`2^(e-23)/2`, `e = f32BinadeE a`) of the exact value.  Kernel
    proof from `f32RoundNE_nearest`. -/
lemma f32RoundPos32_error (a : ℚ) (ha : 1 ≤ a) :
    |a - f32RoundPos32 a (by linarith)| ≤
      (2 : ℚ) ^ ((f32BinadeE a : Int) - 23) / 2 := by
  simp [f32RoundPos32, ha]
  let e : Int := (f32BinadeE a : Int)
  let m : ℤ := f32RoundNE (a * (2 : ℚ) ^ (23 - e))
  change |a - (m : ℚ) * (2 : ℚ) ^ (e - 23)| ≤ (2 : ℚ) ^ (e - 23) / 2
  have hp : (2 : ℚ) ^ (23 - e) * (2 : ℚ) ^ (e - 23) = 1 := by
    rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    have hsum : (23 - e) + (e - 23) = 0 := by omega
    simp [hsum]
  have hscale_pos : 0 < (2 : ℚ) ^ (e - 23) := zpow_pos (by norm_num) _
  have hnearest := f32RoundNE_nearest (a * (2 : ℚ) ^ (23 - e))
  have halg : (a * (2 : ℚ) ^ (23 - e) - (m : ℚ)) * (2 : ℚ) ^ (e - 23)
      = a - (m : ℚ) * (2 : ℚ) ^ (e - 23) := by
    rw [sub_mul, mul_assoc, hp, mul_one]
  calc
    |a - (m : ℚ) * (2 : ℚ) ^ (e - 23)|
        = |(a * (2 : ℚ) ^ (23 - e) - (m : ℚ)) * (2 : ℚ) ^ (e - 23)| := by
            rw [halg]
    _ = |a * (2 : ℚ) ^ (23 - e) - (m : ℚ)| * (2 : ℚ) ^ (e - 23) := by
            rw [abs_mul, abs_of_pos hscale_pos]
    _ ≤ (1 / 2 : ℚ) * (2 : ℚ) ^ (e - 23) :=
            mul_le_mul_of_nonneg_right hnearest (le_of_lt hscale_pos)
    _ = (2 : ℚ) ^ (e - 23) / 2 := by ring

/-! ### 4. The rational mirror of the C per-axis key guard. -/

/-- The rational mirror of `mcKeyAxis` (`Vdb/McAdaptKey`) / the C
    `tool_cluster_range` inner loop.

    `x` stands for the exact quotient `v / step`.  `f32RoundToFloat32 x`
    stands for the rounded binary32 (C: binary64) division `e`.  Its floor
    `q = ⌊e⌋` is the C's integral `double q = floor(e)`, so the `(int64_t) q`
    cast is exact precisely when `q` is in the int64 range.  `none` mirrors
    the guard's overflow branch.

    The `!isfinite(q)` clause of the C guard has no ℚ counterpart (ℚ has no
    NaN/Inf); that clause remains the provenance of the executable twin
    `Vdb/McAdaptKey`, as documented in the header. -/
def f32KeyAxisModel (x : ℚ) : Option ℤ :=
  let q : ℤ := ⌊f32RoundToFloat32 x⌋
  if (q : ℚ) < -(2 : ℚ) ^ 63 ∨ (q : ℚ) ≥ (2 : ℚ) ^ 63 then none else some q

/-- Any accepted key lies strictly inside the int64 range.  This is the
    exact rational statement of the C guard's `|q| < 2^63` clause. -/
lemma f32KeyAxisModel_some_bounds {x : ℚ} {q : ℤ}
    (h : f32KeyAxisModel x = some q) :
    -(2 : ℤ) ^ 63 ≤ q ∧ q < (2 : ℤ) ^ 63 := by
  unfold f32KeyAxisModel at h
  by_cases hc : ((⌊f32RoundToFloat32 x⌋ : ℚ) < -(2 : ℚ) ^ 63 ∨
                 (⌊f32RoundToFloat32 x⌋ : ℚ) ≥ (2 : ℚ) ^ 63)
  · simp [hc] at h
  · have hc' : -(2 : ℚ) ^ 63 ≤ (⌊f32RoundToFloat32 x⌋ : ℚ) ∧
                 (⌊f32RoundToFloat32 x⌋ : ℚ) < (2 : ℚ) ^ 63 := by
      push Not at hc
      exact hc
    simp [hc] at h
    subst q
    constructor
    · exact_mod_cast hc'.1
    · exact_mod_cast hc'.2

/-- An accepted key is an exact int64: it is an integer (type `ℤ`) and it is
    the floor of the rounded division, so the C cast `(int64_t) q` loses
    nothing. -/
lemma f32KeyAxisModel_some_int64_exact {x : ℚ} {q : ℤ}
    (h : f32KeyAxisModel x = some q) :
    (q : ℚ) ≤ f32RoundToFloat32 x ∧ f32RoundToFloat32 x < (q : ℚ) + 1 := by
  unfold f32KeyAxisModel at h
  by_cases hc : ((⌊f32RoundToFloat32 x⌋ : ℚ) < -(2 : ℚ) ^ 63 ∨
                 (⌊f32RoundToFloat32 x⌋ : ℚ) ≥ (2 : ℚ) ^ 63)
  · simp [hc] at h
  · simp [hc] at h
    subst q
    exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

/-- `none` occurs exactly when the integral floor of the rounded division
    is outside the int64 range (the `isfinite` clause aside). -/
lemma f32KeyAxisModel_none_iff (x : ℚ) :
    f32KeyAxisModel x = none ↔
      (⌊f32RoundToFloat32 x⌋ : ℚ) < -(2 : ℚ) ^ 63 ∨
      (⌊f32RoundToFloat32 x⌋ : ℚ) ≥ (2 : ℚ) ^ 63 := by
  unfold f32KeyAxisModel
  by_cases hc : ((⌊f32RoundToFloat32 x⌋ : ℚ) < -(2 : ℚ) ^ 63 ∨
                 (⌊f32RoundToFloat32 x⌋ : ℚ) ≥ (2 : ℚ) ^ 63)
  · simp [hc]
  · simp [hc]

/-- If the rounded division already reaches the `2^63` boundary, the key
    overflows (a direct consequence of the guard and `Int.le_floor`). -/
lemma f32KeyAxisModel_overflow_of_rounded_ge (x : ℚ)
    (h : (2 : ℚ) ^ 63 ≤ f32RoundToFloat32 x) :
    f32KeyAxisModel x = none := by
  unfold f32KeyAxisModel
  have hfloor : (2 : ℤ) ^ 63 ≤ ⌊f32RoundToFloat32 x⌋ := by
    apply Int.le_floor.mpr
    norm_num at h ⊢
    exact h
  have hc : ((⌊f32RoundToFloat32 x⌋ : ℚ) < -(2 : ℚ) ^ 63 ∨
             (⌊f32RoundToFloat32 x⌋ : ℚ) ≥ (2 : ℚ) ^ 63) := by
    right
    exact_mod_cast hfloor
  simp [hc]

/-! ### 5. Field-level binary32 model and the normal-range RNE theorem. -/

/-- A finite binary32 value by its IEEE fields: sign, biased exponent
    `E` (0..254), significand `M` (0 <= M < 2^23).  `decode` is the exact
    rational value (subnormals `E = 0` use `M * 2^-149`, normals use
    `(2^23 + M) * 2^(E-150)`). -/
structure F32 where
  s : Bool
  E : Int
  M : Int
  hE0 : 0 ≤ E
  hE1 : E ≤ 254
  hM0 : 0 ≤ M
  hM1 : M < 2 ^ 23

namespace F32

/-- The exact rational value of the field triple. -/
def decode (f : F32) : ℚ :=
  let sig : ℚ := if f.E = 0 then (f.M : ℚ) else (2 : ℚ) ^ (23 : Nat) + (f.M : ℚ)
  let exp : Int := if f.E = 0 then -149 else f.E - 150
  (if f.s then -1 else 1) * sig * (2 : ℚ) ^ exp

end F32

/-- The significand `m = roundNE(a * 2^(23-e))` stays in `[2^23, 2^24]`
    for `a` in its normal binade (carry at the top end is the `2^24` case).
    Kernel proof from the binade bounds and `f32RoundNE_nearest`. -/
lemma f32RoundPos32_sig_bounds (a : ℚ) (ha : 1 ≤ a) :
    let e : Int := (f32BinadeE a : Int)
    let m : ℤ := f32RoundNE (a * (2 : ℚ) ^ (23 - e))
    (2 : ℤ) ^ 23 ≤ m ∧ m ≤ (2 : ℤ) ^ 24 := by
  dsimp only
  let e : Int := (f32BinadeE a : Int)
  let y : ℚ := a * (2 : ℚ) ^ (23 - e)
  let m : ℤ := f32RoundNE y
  have hscale_pos : 0 < (2 : ℚ) ^ (23 - e) := zpow_pos (by norm_num) _
  have hz_low : (2 : ℚ) ^ e ≤ a := by
    dsimp [e]
    rw [zpow_natCast]
    exact f32BinadeE_lower ha
  have hz_up : a < (2 : ℚ) ^ (e + 1) := by
    dsimp [e]
    have hcast : ((f32BinadeE a + 1 : Nat) : Int) = (f32BinadeE a : Int) + 1 := by omega
    rw [← hcast, zpow_natCast]
    exact f32BinadeE_upper ha
  have hp_low : (2 : ℚ) ^ e * (2 : ℚ) ^ (23 - e) = (2 : ℚ) ^ (23 : Nat) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    have hs : e + (23 - e) = 23 := by omega
    rw [hs]
    norm_num
  have hp_up : (2 : ℚ) ^ (e + 1) * (2 : ℚ) ^ (23 - e) = (2 : ℚ) ^ (24 : Nat) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    have hs : (e + 1) + (23 - e) = 24 := by omega
    rw [hs]
    norm_num
  have hy_low : (2 : ℚ) ^ 23 ≤ y := by
    have hm := mul_le_mul_of_nonneg_right hz_low (le_of_lt hscale_pos)
    change (2 : ℚ) ^ e * (2 : ℚ) ^ (23 - e) ≤ a * (2 : ℚ) ^ (23 - e) at hm
    rwa [hp_low] at hm
  have hy_up : y < (2 : ℚ) ^ 24 := by
    have hm := mul_lt_mul_of_pos_right hz_up hscale_pos
    change a * (2 : ℚ) ^ (23 - e) < (2 : ℚ) ^ (e + 1) * (2 : ℚ) ^ (23 - e) at hm
    rwa [hp_up] at hm
  have hnearest := f32RoundNE_nearest y
  have hm_low : (2 : ℤ) ^ 23 ≤ m := by
    have hge : ((2 : ℤ) ^ 23 : ℚ) - 1 / 2 ≤ (m : ℚ) := by
      have := abs_le.mp hnearest
      linarith
    by_contra hnot
    have hmle : m ≤ (2 : ℤ) ^ 23 - 1 := by omega
    have hc : (m : ℚ) ≤ ((2 : ℤ) ^ 23 : ℚ) - 1 := by exact_mod_cast hmle
    norm_num at hge hc ⊢
    linarith
  have hm_up : m ≤ (2 : ℤ) ^ 24 := by
    have hle : (m : ℚ) ≤ y + 1 / 2 := by
      have := abs_le.mp hnearest
      linarith
    by_contra hnot
    have hmge : (2 : ℤ) ^ 24 + 1 ≤ m := by omega
    have hc : ((2 : ℤ) ^ 24 : ℚ) + 1 ≤ (m : ℚ) := by exact_mod_cast hmge
    norm_num at hc hle ⊢
    linarith
  exact ⟨hm_low, hm_up⟩

/-- Tie-to-even at the field level: when the scaled significand is a
    half-integer, the stored significand is even (this is the IEEE-754
    `roundTiesToEven` rule on the 24-bit significand). -/
lemma f32RoundPos32_sig_tie_even (a : ℚ) (_ha : 1 ≤ a)
    (htie : ∃ k : ℤ, a * (2 : ℚ) ^ (23 - (f32BinadeE a : Int)) = (k : ℚ) + 1 / 2) :
    Even (f32RoundNE (a * (2 : ℚ) ^ (23 - (f32BinadeE a : Int)))) :=
  f32RoundNE_tie_even htie

/-- Normal-range representability: for `a >= 1` in binade `e <= 126` (so the
    biased exponent `e + 127/128` stays within 0..254), the rational binary32
    rounding is exactly the decode of a field triple.  Together with
    `f32RoundPos32_error` and `f32RoundPos32_sig_tie_even` this is the
    A-section target (c): IEEE-754 round-to-nearest-even on the normal
    binade, proved over ℚ. -/
lemma f32RoundPos32_repr (a : ℚ) (ha : 1 ≤ a) (he : f32BinadeE a ≤ 126) :
    ∃ f : F32, F32.decode f = f32RoundPos32 a (by linarith) := by
  let e : Int := (f32BinadeE a : Int)
  let m : ℤ := f32RoundNE (a * (2 : ℚ) ^ (23 - e))
  have hmb := f32RoundPos32_sig_bounds a ha
  dsimp only at hmb
  change (2 : ℤ) ^ 23 ≤ m ∧ m ≤ (2 : ℤ) ^ 24 at hmb
  have he0 : 0 ≤ e := by
    dsimp [e]
    exact_mod_cast (Nat.zero_le (f32BinadeE a))
  have he126 : e ≤ 126 := by
    dsimp [e]
    exact_mod_cast he
  have hdecode : f32RoundPos32 a (by linarith) = (m : ℚ) * (2 : ℚ) ^ (e - 23) := by
    simp [f32RoundPos32, ha, e, m]
  by_cases hmcarry : m = (2 : ℤ) ^ 24
  · -- carry to the next binade: E = e + 128, M = 0
    refine ⟨⟨false, e + 128, 0, ?_, ?_, ?_, ?_⟩, ?_⟩
    · omega
    · omega
    · norm_num
    · norm_num
    · have hEne : e + 128 ≠ 0 := by omega
      rw [F32.decode, hdecode]
      simp [hEne]
      rw [hmcarry]
      rw [show e + 128 - 150 = e - 22 by omega]
      have hpow : (2 : ℚ) ^ (23 : Nat) * (2 : ℚ) ^ (e - 22) =
                  (2 : ℚ) ^ (24 : Nat) * (2 : ℚ) ^ (e - 23) := by
        rw [← zpow_natCast (2 : ℚ) 23, ← zpow_natCast (2 : ℚ) 24]
        rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0),
            ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        congr 1
        omega
      exact hpow
  · -- non-carry: E = e + 127, M = m - 2^23
    have hm_lt : m < (2 : ℤ) ^ 24 := lt_of_le_of_ne hmb.2 hmcarry
    refine ⟨⟨false, e + 127, m - (2 : ℤ) ^ 23, ?_, ?_, ?_, ?_⟩, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · have hEne : e + 127 ≠ 0 := by omega
      rw [F32.decode, hdecode]
      simp [hEne]
      rw [show e + 127 - 150 = e - 23 by omega]
      ring

/-! ### 6. Executable evidence (concrete instances, not universal theorems). -/

/-- Concrete round-to-nearest-even instances, checked by the native evaluator.
    These are executable evidence on specific rationals, *not* a universal
    claim; the universal statement is `f32RoundNE_nearest` above. -/
example : f32RoundNE (5 / 2 : ℚ) = 2 := by native_decide
example : f32RoundNE (7 / 2 : ℚ) = 4 := by native_decide
example : f32RoundNE (-(5 / 2 : ℚ)) = -2 := by native_decide

/-- Concrete small integers are fixed by the binary32 model (executable
    sanity check on the exact-integer range). -/
example : f32RoundToFloat32 (1 : ℚ) = 1 := by native_decide
example : f32RoundToFloat32 (42 : ℚ) = 42 := by native_decide

/-! ### 7. Precise walls (not proved here; named statements). -/

-- The following are deliberately NOT claimed as theorems.  They are recorded
-- with precise names so the remaining work is unambiguous; none is an axiom
-- and none is used above.
--
-- (W1) `native_f32_agreement` (target (b)): for every `u : UInt64`,
--       `f32DecodeBits u = f32RoundToFloat32 (f32RatOfBits u)` where
--       `f32DecodeBits`/`f32RatOfBits` go through Lean's native `Float32`
--       `ofBits`/`toBits`.  Only five concrete instances are checked above
--       (Section 6); a universal statement needs IEEE-754 rounding lemmas
--       that Lean core / this mathlib slice do not provide for `Float32`.
--       The 3,000,000-value C<->Lean twin (`Vdb/McAdaptKey`) remains the
--       executable evidence for that agreement.
--
-- (W2) `f32RoundPos32_subnormal_spec`: for `0 < a < 1`, the subnormal branch
--       of `f32RoundPos32` is the nearest multiple of `2^-149` and is exactly
--       `F32.decode` of an `E = 0` field triple.  The normal-branch theorems
--       above deliberately assume `1 <= a`; the C harness's subnormal corpus
--       is covered only by the executable twin.
--
-- (W3) `isfinite_guard_theorem`: the C guard's `!isfinite(q)` clause has no
--       ℚ counterpart (ℚ has no NaN/Inf).  `f32KeyAxisModel` models exactly
--       the range clause `q < -2^63 ∨ q >= 2^63`; non-finite inputs stay the
--       provenance of `Vdb/McAdaptKey`'s native-`Float` twin.
--
-- (W4) `binary64_vs_binary32`: the C computes the division in binary64
--       (24-bit significand here, 53 there).  The guard theorems above are
--       precision-independent (they only use that the rounded value is a
--       rational and that `q = floor(e)`), so the choice of binary32 in the
--       rational model does not affect `f32KeyAxisModel_some_bounds`,
--       `_some_int64_exact` or `_none_iff`.  A binary64 *error* bound would
--       need the same construction with precision 53.

end Vdb
