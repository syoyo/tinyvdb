/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  Boundary position classes for the general-`n` padded-grid cuberille /
  DMC assembly (`Vdb/PadGrid.lean`). The balanced-assembly question
  (T-DMC0-CYCLE for arbitrary `n`) is reduced, per `balanced_iff_local`,
  to showing that every face's two local counts agree. This file proves
  that equality for the position classes forced by shell pinning; the
  interior class is discharged in `Vdb.PadGrid.localCount_x_interior`.

  Shell pinning hypothesis used throughout: `forall p, isShell n p = true
  -> s p = false`. Cells with a coordinate `>= n` are handled by the
  `out-of-grid` lemmas, where every candidate is blocked either by the
  lattice-membership test or by the pinned signs of a shell endpoint.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.PadGrid

set_option linter.unusedSimpArgs false

namespace Vdb

namespace PadGrid

/-- `x` face, `z = 0` boundary, `y` strictly interior (`1 ≤ Y`, `Y + 1 < n`).
    Both `e` and `f'` sit on the shell and are pinned to `false`; `g` and `h`
    are free. -/
theorem localCount_x_z0_yint (n : Nat) (s : Lat → Bool) (X Y : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hX : X + 1 < n) (hY0 : 1 ≤ Y) (hYn : Y + 1 < n) (hn : 3 ≤ n) :
    localCount n s ((X, Y, 0), 0) true = localCount n s ((X, Y, 0), 0) false := by
  have hc : candidates ((X, Y, 0), 0) =
      [((X + 1, Y - 1, 0), 2), ((X + 1, Y, 0 - 1), 1),
       ((X + 1, Y, 0), 1), ((X + 1, Y, 0), 2),
       ((X + 1, Y, 0 + 1), 1), ((X + 1, Y + 1, 0), 2)] := rfl
  have iL2 : decide (InLattice n (X + 1, Y, 0)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ Y ≤ n ∧ 0 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (X + 1, Y + 1, 0)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ Y + 1 ≤ n ∧ 0 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL3' : decide (InLattice n (X + 1, Y, 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ Y ≤ n ∧ 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL4' : decide (InLattice n (X + 1, Y + 1, 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ Y + 1 ≤ n ∧ 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have hm2 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
  have hm3 : decide (1 ≤ Y) = true := decide_eq_true_eq.mpr hY0
  have he : s (X + 1, Y, 0) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hf : s (X + 1, Y + 1, 0) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_x, e2_contributes_false_x]
  simp only [contrib_x2, contrib_x3, contrib_x4, contrib_x5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, he, hf,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.not_true, Bool.false_eq_true]
  generalize hg : s (X + 1, Y, 1) = g
  generalize hh : s (X + 1, Y + 1, 1) = h
  clear hg hh
  revert g h
  native_decide

/-- `x` face, `z = 0, y = 0` corner (in-grid): both `e` and `f'` pin to the
    shell on `Z = 0`, `g` pins on `Y = 0`; `h` is interior when `n ≥ 2`. -/
theorem localCount_x_z0_y0 (n : Nat) (s : Lat → Bool) (X : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hX : X + 1 < n) (hn : 2 ≤ n) :
    localCount n s ((X, 0, 0), 0) true = localCount n s ((X, 0, 0), 0) false := by
  have hc : candidates ((X, 0, 0), 0) =
      [((X + 1, 0 - 1, 0), 2), ((X + 1, 0, 0 - 1), 1),
       ((X + 1, 0, 0), 1), ((X + 1, 0, 0), 2),
       ((X + 1, 0, 0 + 1), 1), ((X + 1, 0 + 1, 0), 2)] := rfl
  have iL2 : decide (InLattice n (X + 1, 0, 0)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ 0 ≤ n ∧ 0 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (X + 1, 0 + 1, 0)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ 0 + 1 ≤ n ∧ 0 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL3' : decide (InLattice n (X + 1, 0, 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ 0 ≤ n ∧ 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL4' : decide (InLattice n (X + 1, 0 + 1, 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ 0 + 1 ≤ n ∧ 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have hm2 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
  have hm3 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
  have he : s (X + 1, 0, 0) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inr (Or.inr (Or.inl rfl)))
  have hf : s (X + 1, 0 + 1, 0) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hg : s (X + 1, 0, 0 + 1) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inr (Or.inr (Or.inl rfl)))
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_x, e2_contributes_false_x]
  simp only [contrib_x2, contrib_x3, contrib_x4, contrib_x5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, he, hf, hg,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize hh : s (X + 1, 0 + 1, 1) = h
  clear hh
  revert h
  native_decide

/-- `x` face, `z = 0` boundary, `y = n - 1` (in-grid): `e`, `f'` pin on
    `Z = 0` and `h` pins on `Y + 1 = n`; `g` is free. -/
theorem localCount_x_z0_yn (n : Nat) (s : Lat → Bool) (X : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hX : X + 1 < n) (hn : 2 ≤ n) :
    localCount n s ((X, n - 1, 0), 0) true = localCount n s ((X, n - 1, 0), 0) false := by
  have hc : candidates ((X, n - 1, 0), 0) =
      [((X + 1, n - 1 - 1, 0), 2), ((X + 1, n - 1, 0 - 1), 1),
       ((X + 1, n - 1, 0), 1), ((X + 1, n - 1, 0), 2),
       ((X + 1, n - 1, 0 + 1), 1), ((X + 1, n - 1 + 1, 0), 2)] := rfl
  have iL2 : decide (InLattice n (X + 1, n - 1, 0)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ n - 1 ≤ n ∧ 0 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (X + 1, n - 1 + 1, 0)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ n - 1 + 1 ≤ n ∧ 0 ≤ n
    omega
  have iL3' : decide (InLattice n (X + 1, n - 1, 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ n - 1 ≤ n ∧ 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL4' : decide (InLattice n (X + 1, n - 1 + 1, 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ n - 1 + 1 ≤ n ∧ 1 ≤ n
    omega
  have hm2 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
  have hm3 : decide (1 ≤ n - 1) = true := decide_eq_true_eq.mpr (by omega)
  have he : s (X + 1, n - 1, 0) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hf : s (X + 1, n - 1 + 1, 0) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; left
    show (X + 1, n - 1 + 1, 0).2.1 = n
    show n - 1 + 1 = n
    omega
  have hh : s (X + 1, n - 1 + 1, 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; left
    show (X + 1, n - 1 + 1, 1).2.1 = n
    show n - 1 + 1 = n
    omega
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_x, e2_contributes_false_x]
  simp only [contrib_x2, contrib_x3, contrib_x4, contrib_x5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, he, hf, hh,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize hg : s (X + 1, n - 1, 0 + 1) = g
  clear hg
  revert g
  native_decide

/-- `x` face, `z = n - 1` boundary, `y = 0` (in-grid): `e`, `g` pin on
    `Y = 0` and `h` pins on `Z + 1 = n`; `f'` is free. -/
theorem localCount_x_zn_y0 (n : Nat) (s : Lat → Bool) (X : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hX : X + 1 < n) (hn : 2 ≤ n) :
    localCount n s ((X, 0, n - 1), 0) true = localCount n s ((X, 0, n - 1), 0) false := by
  have hc : candidates ((X, 0, n - 1), 0) =
      [((X + 1, 0 - 1, n - 1), 2), ((X + 1, 0, n - 1 - 1), 1),
       ((X + 1, 0, n - 1), 1), ((X + 1, 0, n - 1), 2),
       ((X + 1, 0, n - 1 + 1), 1), ((X + 1, 0 + 1, n - 1), 2)] := rfl
  have iL2 : decide (InLattice n (X + 1, 0, n - 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ 0 ≤ n ∧ n - 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (X + 1, 0 + 1, n - 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ 0 + 1 ≤ n ∧ n - 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL3' : decide (InLattice n (X + 1, 0, n - 1 + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ 0 ≤ n ∧ n - 1 + 1 ≤ n
    omega
  have iL4' : decide (InLattice n (X + 1, 0 + 1, n - 1 + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ 0 + 1 ≤ n ∧ n - 1 + 1 ≤ n
    omega
  have hm2 : decide (1 ≤ n - 1) = true := decide_eq_true_eq.mpr (by omega)
  have hm3 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
  have he : s (X + 1, 0, n - 1) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inr (Or.inr (Or.inl rfl)))
  have hg : s (X + 1, 0, n - 1 + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; right; right
    show (X + 1, 0, n - 1 + 1).2.2 = n
    show n - 1 + 1 = n
    omega
  have hh : s (X + 1, 0 + 1, n - 1 + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; right; right
    show (X + 1, 0 + 1, n - 1 + 1).2.2 = n
    show n - 1 + 1 = n
    omega
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_x, e2_contributes_false_x]
  simp only [contrib_x2, contrib_x3, contrib_x4, contrib_x5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, he, hg, hh,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize hf' : s (X + 1, 0 + 1, n - 1) = f
  clear hf'
  revert f
  native_decide

/-- `x` face, `z = n - 1` boundary, `y` strictly interior: `g`, `h` pin on
    `Z + 1 = n`; both `e` and `f'` are free. -/
theorem localCount_x_zn_yint (n : Nat) (s : Lat → Bool) (X Y : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hX : X + 1 < n) (hY0 : 1 ≤ Y) (hYn : Y + 1 ≤ n - 1) (hn : 3 ≤ n) :
    localCount n s ((X, Y, n - 1), 0) true = localCount n s ((X, Y, n - 1), 0) false := by
  have hc : candidates ((X, Y, n - 1), 0) =
      [((X + 1, Y - 1, n - 1), 2), ((X + 1, Y, n - 1 - 1), 1),
       ((X + 1, Y, n - 1), 1), ((X + 1, Y, n - 1), 2),
       ((X + 1, Y, n - 1 + 1), 1), ((X + 1, Y + 1, n - 1), 2)] := rfl
  have iL2 : decide (InLattice n (X + 1, Y, n - 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ Y ≤ n ∧ n - 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (X + 1, Y + 1, n - 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ Y + 1 ≤ n ∧ n - 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL3' : decide (InLattice n (X + 1, Y, n - 1 + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ Y ≤ n ∧ n - 1 + 1 ≤ n
    omega
  have iL4' : decide (InLattice n (X + 1, Y + 1, n - 1 + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ Y + 1 ≤ n ∧ n - 1 + 1 ≤ n
    omega
  have hm2 : decide (1 ≤ n - 1) = true := decide_eq_true_eq.mpr (by omega)
  have hm3 : decide (1 ≤ Y) = true := decide_eq_true_eq.mpr hY0
  have hg : s (X + 1, Y, n - 1 + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; right; right
    show (X + 1, Y, n - 1 + 1).2.2 = n
    show n - 1 + 1 = n
    omega
  have hh : s (X + 1, Y + 1, n - 1 + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; right; right
    show (X + 1, Y + 1, n - 1 + 1).2.2 = n
    show n - 1 + 1 = n
    omega
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_x, e2_contributes_false_x]
  simp only [contrib_x2, contrib_x3, contrib_x4, contrib_x5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, hg, hh,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.not_true, Bool.false_eq_true]
  generalize he : s (X + 1, Y, n - 1) = e
  generalize hf : s (X + 1, Y + 1, n - 1) = f
  clear he hf
  revert e f
  native_decide

/-- `x` face, `X + 1 = n`: all four corner lattice points sit on the shell,
    so all four corner signs are pinned to `false` and the count is zero
    in both directions. -/
theorem localCount_x_xn1 (n : Nat) (s : Lat → Bool) (Y Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false) (hn : 1 ≤ n) :
    localCount n s ((n - 1, Y, Z), 0) true = localCount n s ((n - 1, Y, Z), 0) false := by
  have hc : candidates ((n - 1, Y, Z), 0) =
      [((n - 1 + 1, Y - 1, Z), 2), ((n - 1 + 1, Y, Z - 1), 1),
       ((n - 1 + 1, Y, Z), 1), ((n - 1 + 1, Y, Z), 2),
       ((n - 1 + 1, Y, Z + 1), 1), ((n - 1 + 1, Y + 1, Z), 2)] := rfl
  have he : s (n - 1 + 1, Y, Z) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; left
    show (n - 1 + 1, Y, Z).1 = n
    show n - 1 + 1 = n
    omega
  have hf : s (n - 1 + 1, Y + 1, Z) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; left
    show (n - 1 + 1, Y + 1, Z).1 = n
    show n - 1 + 1 = n
    omega
  have hg : s (n - 1 + 1, Y, Z + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; left
    show (n - 1 + 1, Y, Z + 1).1 = n
    show n - 1 + 1 = n
    omega
  have hh : s (n - 1 + 1, Y + 1, Z + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; left
    show (n - 1 + 1, Y + 1, Z + 1).1 = n
    show n - 1 + 1 = n
    omega
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_x, e2_contributes_false_x]
  simp only [contrib_x2, contrib_x3, contrib_x4, contrib_x5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    he, hf, hg, hh,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize hu : decide (InLattice n (n - 1 + 1, Y, Z)) = u
  generalize hv : decide (InLattice n (n - 1 + 1, Y + 1, Z)) = v
  generalize hw : decide (InLattice n (n - 1 + 1, Y, Z + 1)) = w
  generalize hxx : decide (InLattice n (n - 1 + 1, Y + 1, Z + 1)) = xx
  generalize hm2 : decide (1 ≤ Z) = m2
  generalize hm3 : decide (1 ≤ Y) = m3
  clear hu hv hw hxx hm2 hm3
  revert u v w xx m2 m3
  native_decide

/-- `x` face, `Z` strictly interior, `Y = 0` (in-grid): both `e` and `g`
    sit on the shell and are pinned to `false`; both `f'` and `h` are free. -/
theorem localCount_x_zint_y0 (n : Nat) (s : Lat → Bool) (X Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hX : X + 1 < n) (hZ0 : 1 ≤ Z) (hZn : Z + 1 ≤ n - 1) (hn : 3 ≤ n) :
    localCount n s ((X, 0, Z), 0) true = localCount n s ((X, 0, Z), 0) false := by
  have hc : candidates ((X, 0, Z), 0) =
      [((X + 1, 0 - 1, Z), 2), ((X + 1, 0, Z - 1), 1),
       ((X + 1, 0, Z), 1), ((X + 1, 0, Z), 2),
       ((X + 1, 0, Z + 1), 1), ((X + 1, 0 + 1, Z), 2)] := rfl
  have iL2 : decide (InLattice n (X + 1, 0, Z)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ 0 ≤ n ∧ Z ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (X + 1, 0 + 1, Z)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ 0 + 1 ≤ n ∧ Z ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL3' : decide (InLattice n (X + 1, 0, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ 0 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL4' : decide (InLattice n (X + 1, 0 + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ 0 + 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have hm2 : decide (1 ≤ Z) = true := decide_eq_true_eq.mpr hZ0
  have hm3 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
  have he : s (X + 1, 0, Z) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inr (Or.inr (Or.inl rfl)))
  have hg : s (X + 1, 0, Z + 1) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inr (Or.inr (Or.inl rfl)))
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_x, e2_contributes_false_x]
  simp only [contrib_x2, contrib_x3, contrib_x4, contrib_x5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, he, hg,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize hf : s (X + 1, 0 + 1, Z) = f
  generalize hh : s (X + 1, 0 + 1, Z + 1) = h
  clear hf hh
  revert f h
  native_decide

/-- `x` face, `Z` strictly interior, `Y = n - 1` (in-grid): both `f'` and
    `h` pin on `Y + 1 = n`; both `e` and `g` are free. -/
theorem localCount_x_zint_yn (n : Nat) (s : Lat → Bool) (X Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hX : X + 1 < n) (hZ0 : 1 ≤ Z) (hZn : Z + 1 ≤ n - 1) (hn : 3 ≤ n) :
    localCount n s ((X, n - 1, Z), 0) true = localCount n s ((X, n - 1, Z), 0) false := by
  have hc : candidates ((X, n - 1, Z), 0) =
      [((X + 1, n - 1 - 1, Z), 2), ((X + 1, n - 1, Z - 1), 1),
       ((X + 1, n - 1, Z), 1), ((X + 1, n - 1, Z), 2),
       ((X + 1, n - 1, Z + 1), 1), ((X + 1, n - 1 + 1, Z), 2)] := rfl
  have iL2 : decide (InLattice n (X + 1, n - 1, Z)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ n - 1 ≤ n ∧ Z ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (X + 1, n - 1 + 1, Z)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ n - 1 + 1 ≤ n ∧ Z ≤ n
    omega
  have iL3' : decide (InLattice n (X + 1, n - 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ n - 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL4' : decide (InLattice n (X + 1, n - 1 + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ n - 1 + 1 ≤ n ∧ Z + 1 ≤ n
    omega
  have hm2 : decide (1 ≤ Z) = true := decide_eq_true_eq.mpr hZ0
  have hm3 : decide (1 ≤ n - 1) = true := decide_eq_true_eq.mpr (by omega)
  have hf : s (X + 1, n - 1 + 1, Z) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; left
    show (X + 1, n - 1 + 1, Z).2.1 = n
    show n - 1 + 1 = n
    omega
  have hh : s (X + 1, n - 1 + 1, Z + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; left
    show (X + 1, n - 1 + 1, Z + 1).2.1 = n
    show n - 1 + 1 = n
    omega
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_x, e2_contributes_false_x]
  simp only [contrib_x2, contrib_x3, contrib_x4, contrib_x5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, hf, hh,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize he : s (X + 1, n - 1, Z) = e
  generalize hg : s (X + 1, n - 1, Z + 1) = g
  clear he hg
  revert e g
  native_decide

/-- `x` face, `Z = n - 1` boundary, `Y = n - 1` (in-grid): `f'`, `g`, `h`
    pin (on `Y + 1 = n` and `Z + 1 = n`); only `e` is free. -/
theorem localCount_x_zn_yn (n : Nat) (s : Lat → Bool) (X : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hX : X + 1 < n) (hn : 2 ≤ n) :
    localCount n s ((X, n - 1, n - 1), 0) true = localCount n s ((X, n - 1, n - 1), 0) false := by
  have hc : candidates ((X, n - 1, n - 1), 0) =
      [((X + 1, n - 1 - 1, n - 1), 2), ((X + 1, n - 1, n - 1 - 1), 1),
       ((X + 1, n - 1, n - 1), 1), ((X + 1, n - 1, n - 1), 2),
       ((X + 1, n - 1, n - 1 + 1), 1), ((X + 1, n - 1 + 1, n - 1), 2)] := rfl
  have iL2 : decide (InLattice n (X + 1, n - 1, n - 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ n - 1 ≤ n ∧ n - 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (X + 1, n - 1 + 1, n - 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ n - 1 + 1 ≤ n ∧ n - 1 ≤ n
    omega
  have iL3' : decide (InLattice n (X + 1, n - 1, n - 1 + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ n - 1 ≤ n ∧ n - 1 + 1 ≤ n
    omega
  have iL4' : decide (InLattice n (X + 1, n - 1 + 1, n - 1 + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ n - 1 + 1 ≤ n ∧ n - 1 + 1 ≤ n
    omega
  have hm2 : decide (1 ≤ n - 1) = true := decide_eq_true_eq.mpr (by omega)
  have hm3 : decide (1 ≤ n - 1) = true := decide_eq_true_eq.mpr (by omega)
  have hf : s (X + 1, n - 1 + 1, n - 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; left
    show (X + 1, n - 1 + 1, n - 1).2.1 = n
    show n - 1 + 1 = n
    omega
  have hg : s (X + 1, n - 1, n - 1 + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; right; right
    show (X + 1, n - 1, n - 1 + 1).2.2 = n
    show n - 1 + 1 = n
    omega
  have hh : s (X + 1, n - 1 + 1, n - 1 + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; right; right
    show (X + 1, n - 1 + 1, n - 1 + 1).2.2 = n
    show n - 1 + 1 = n
    omega
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_x, e2_contributes_false_x]
  simp only [contrib_x2, contrib_x3, contrib_x4, contrib_x5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, hf, hg, hh,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize he : s (X + 1, n - 1, n - 1) = e
  clear he
  revert e
  native_decide

/-- `x` face, out-of-grid along `X` (`n ≤ X`): every candidate's InL gate
    fails (`X + 1 > n`), so the local count vanishes in both directions. -/
theorem localCount_x_out_x (n : Nat) (s : Lat → Bool) (X Y Z : Nat) (hX : n ≤ X) :
    localCount n s ((X, Y, Z), 0) true = localCount n s ((X, Y, Z), 0) false := by
  have hc : candidates ((X, Y, Z), 0) =
      [((X + 1, Y - 1, Z), 2), ((X + 1, Y, Z - 1), 1),
       ((X + 1, Y, Z), 1), ((X + 1, Y, Z), 2),
       ((X + 1, Y, Z + 1), 1), ((X + 1, Y + 1, Z), 2)] := rfl
  unfold localCount
  rw [hc]
  have hA : decide (InLattice n (X + 1, Y, Z)) = false := by
    apply decide_eq_false
    show ¬(X + 1 ≤ n ∧ Y ≤ n ∧ Z ≤ n)
    omega
  have hB : decide (InLattice n (X + 1, Y + 1, Z)) = false := by
    apply decide_eq_false
    show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z ≤ n)
    omega
  have hC : decide (InLattice n (X + 1, Y, Z + 1)) = false := by
    apply decide_eq_false
    show ¬(X + 1 ≤ n ∧ Y ≤ n ∧ Z + 1 ≤ n)
    omega
  have hD : decide (InLattice n (X + 1, Y + 1, Z + 1)) = false := by
    apply decide_eq_false
    show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
    omega
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_x, e2_contributes_false_x]
  simp only [contrib_x2, contrib_x3, contrib_x4, contrib_x5]
  simp only [hcrossedB, hsn0, hsn1, hsn2, hA, hB, hC, hD,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]

/-- `x` face, out-of-grid along `Y` (`n ≤ Y`): either `Y = n` (shell-pinned
    corner points, contributing zero on both sides) or `Y > n` (all InL gates
    fail). -/
theorem localCount_x_out_y (n : Nat) (s : Lat → Bool) (X Y Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false) (hY : n ≤ Y) :
    localCount n s ((X, Y, Z), 0) true = localCount n s ((X, Y, Z), 0) false := by
  by_cases hYn : Y = n
  · -- Y = n: e and g sit on the shell and are pinned false; the InL gates
    -- for Y + 1 = n + 1 fail; only InL2, m2, m3 and f', h remain free.
    have hc : candidates ((X, Y, Z), 0) =
        [((X + 1, Y - 1, Z), 2), ((X + 1, Y, Z - 1), 1),
         ((X + 1, Y, Z), 1), ((X + 1, Y, Z), 2),
         ((X + 1, Y, Z + 1), 1), ((X + 1, Y + 1, Z), 2)] := by rfl
    have hA : decide (InLattice n (X + 1, Y + 1, Z)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z ≤ n)
      omega
    have hB : decide (InLattice n (X + 1, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    have he : s (X + 1, Y, Z) = false := by
      apply hpin
      refine shell_of_or n _ ?_
      right; right; right; left
      show (X + 1, Y, Z).2.1 = n
      exact hYn
    have hg : s (X + 1, Y, Z + 1) = false := by
      apply hpin
      refine shell_of_or n _ ?_
      right; right; right; left
      show (X + 1, Y, Z + 1).2.1 = n
      exact hYn
    unfold localCount
    rw [hc]
    simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
      List.length_cons, List.length_nil, Bool.false_eq_true,
      e1_contributes_false_x, e2_contributes_false_x]
    simp only [contrib_x2, contrib_x3, contrib_x4, contrib_x5]
    simp only [hcrossedB, hsn0, hsn1, hsn2, hA, hB, he, hg,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
      Bool.not_false, Bool.false_eq_true]
    generalize hu : decide (InLattice n (X + 1, Y, Z)) = u
    generalize hw : decide (InLattice n (X + 1, Y, Z + 1)) = w
    generalize hm2 : decide (1 ≤ Z) = m2
    generalize hm3 : decide (1 ≤ Y) = m3
    generalize hf : s (X + 1, Y + 1, Z) = f
    generalize hh : s (X + 1, Y + 1, Z + 1) = h
    clear hu hw hm2 hm3 hf hh
    revert u w m2 m3 f h
    native_decide
  · -- Y > n: every InL gate fails
    have hc : candidates ((X, Y, Z), 0) =
        [((X + 1, Y - 1, Z), 2), ((X + 1, Y, Z - 1), 1),
         ((X + 1, Y, Z), 1), ((X + 1, Y, Z), 2),
         ((X + 1, Y, Z + 1), 1), ((X + 1, Y + 1, Z), 2)] := by rfl
    have hA : decide (InLattice n (X + 1, Y, Z)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y ≤ n ∧ Z ≤ n)
      omega
    have hB : decide (InLattice n (X + 1, Y + 1, Z)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z ≤ n)
      omega
    have hC : decide (InLattice n (X + 1, Y, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y ≤ n ∧ Z + 1 ≤ n)
      omega
    have hD : decide (InLattice n (X + 1, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    unfold localCount
    rw [hc]
    simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
      List.length_cons, List.length_nil, Bool.false_eq_true,
      e1_contributes_false_x, e2_contributes_false_x]
    simp only [contrib_x2, contrib_x3, contrib_x4, contrib_x5]
    simp only [hcrossedB, hsn0, hsn1, hsn2, hA, hB, hC, hD,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
      Bool.not_false, Bool.false_eq_true]

/-- `x` face, out-of-grid along `Z` (`n ≤ Z`): either `Z = n` (shell-pinned
    corner points) or `Z > n` (all InL gates fail). -/
theorem localCount_x_out_z (n : Nat) (s : Lat → Bool) (X Y Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false) (hZ : n ≤ Z) :
    localCount n s ((X, Y, Z), 0) true = localCount n s ((X, Y, Z), 0) false := by
  by_cases hZn : Z = n
  · -- Z = n: e and f' pinned false (shell); InL3'/InL4'/InL5' fail
    have hc : candidates ((X, Y, Z), 0) =
        [((X + 1, Y - 1, Z), 2), ((X + 1, Y, Z - 1), 1),
         ((X + 1, Y, Z), 1), ((X + 1, Y, Z), 2),
         ((X + 1, Y, Z + 1), 1), ((X + 1, Y + 1, Z), 2)] := by rfl
    have hA : decide (InLattice n (X + 1, Y, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y ≤ n ∧ Z + 1 ≤ n)
      omega
    have hB : decide (InLattice n (X + 1, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    have he : s (X + 1, Y, Z) = false := by
      apply hpin
      refine shell_of_or n _ ?_
      right; right; right; right; right
      show (X + 1, Y, Z).2.2 = n
      exact hZn
    have hf : s (X + 1, Y + 1, Z) = false := by
      apply hpin
      refine shell_of_or n _ ?_
      right; right; right; right; right
      show (X + 1, Y + 1, Z).2.2 = n
      exact hZn
    unfold localCount
    rw [hc]
    simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
      List.length_cons, List.length_nil, Bool.false_eq_true,
      e1_contributes_false_x, e2_contributes_false_x]
    simp only [contrib_x2, contrib_x3, contrib_x4, contrib_x5]
    simp only [hcrossedB, hsn0, hsn1, hsn2, hA, hB, he, hf,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
      Bool.not_false, Bool.false_eq_true]
    generalize hu : decide (InLattice n (X + 1, Y, Z)) = u
    generalize hv : decide (InLattice n (X + 1, Y + 1, Z)) = v
    generalize hm2 : decide (1 ≤ Z) = m2
    generalize hm3 : decide (1 ≤ Y) = m3
    generalize hg : s (X + 1, Y, Z + 1) = g
    generalize hh : s (X + 1, Y + 1, Z + 1) = h
    clear hu hv hm2 hm3 hg hh
    revert u v m2 m3 g h
    native_decide
  · -- Z > n: every InL gate fails
    have hc : candidates ((X, Y, Z), 0) =
        [((X + 1, Y - 1, Z), 2), ((X + 1, Y, Z - 1), 1),
         ((X + 1, Y, Z), 1), ((X + 1, Y, Z), 2),
         ((X + 1, Y, Z + 1), 1), ((X + 1, Y + 1, Z), 2)] := by rfl
    have hA : decide (InLattice n (X + 1, Y, Z)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y ≤ n ∧ Z ≤ n)
      omega
    have hB : decide (InLattice n (X + 1, Y + 1, Z)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z ≤ n)
      omega
    have hC : decide (InLattice n (X + 1, Y, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y ≤ n ∧ Z + 1 ≤ n)
      omega
    have hD : decide (InLattice n (X + 1, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    unfold localCount
    rw [hc]
    simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
      List.length_cons, List.length_nil, Bool.false_eq_true,
      e1_contributes_false_x, e2_contributes_false_x]
    simp only [contrib_x2, contrib_x3, contrib_x4, contrib_x5]
    simp only [hcrossedB, hsn0, hsn1, hsn2, hA, hB, hC, hD,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
      Bool.not_false, Bool.false_eq_true]
/-- **x-face universal local balance**: for the x-normal direction, the two
    local counts agree for every cell and every shell-pinned sign field. -/
theorem localCount_x_face (n : Nat) (s : Lat → Bool) (X Y Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false) :
    localCount n s ((X, Y, Z), 0) true = localCount n s ((X, Y, Z), 0) false := by
  by_cases hXn : n ≤ X
  · exact localCount_x_out_x n s X Y Z hXn
  by_cases hYn : n ≤ Y
  · exact localCount_x_out_y n s X Y Z hpin hYn
  by_cases hZn : n ≤ Z
  · exact localCount_x_out_z n s X Y Z hpin hZn
  by_cases hX1 : X + 1 < n
  · by_cases hY0 : Y = 0
    · by_cases hZ0 : Z = 0
      · rw [hY0, hZ0]; exact localCount_x_z0_y0 n s X hpin hX1 (by omega)
      by_cases hZn1 : Z = n - 1
      · rw [hY0, hZn1]; exact localCount_x_zn_y0 n s X hpin hX1 (by omega)
      have hZ1 : 1 ≤ Z := by omega
      have hZ2 : Z + 1 ≤ n - 1 := by omega
      rw [hY0]
      exact localCount_x_zint_y0 n s X Z hpin hX1 hZ1 hZ2 (by omega)
    by_cases hYn1 : Y = n - 1
    · by_cases hZ0 : Z = 0
      · rw [hYn1, hZ0]; exact localCount_x_z0_yn n s X hpin hX1 (by omega)
      by_cases hZn1 : Z = n - 1
      · rw [hYn1, hZn1]; exact localCount_x_zn_yn n s X hpin hX1 (by omega)
      have hZ1 : 1 ≤ Z := by omega
      have hZ2 : Z + 1 ≤ n - 1 := by omega
      rw [hYn1]
      exact localCount_x_zint_yn n s X Z hpin hX1 hZ1 hZ2 (by omega)
    have hYi1 : 1 ≤ Y := by omega
    have hYi2 : Y + 1 ≤ n - 1 := by omega
    by_cases hZ0 : Z = 0
    · rw [hZ0]
      exact localCount_x_z0_yint n s X Y hpin hX1 hYi1 (by omega) (by omega)
    by_cases hZn1 : Z = n - 1
    · rw [hZn1]
      exact localCount_x_zn_yint n s X Y hpin hX1 hYi1 hYi2 (by omega)
    have hZi1 : 1 ≤ Z := by omega
    have hZi2 : Z + 1 ≤ n - 1 := by omega
    exact localCount_x_interior n s X Y Z hX1 hYi1 hZi1 (by omega) (by omega)
  · have hn1 : 1 ≤ n := by omega
    have hXeq : X = n - 1 := by omega
    rw [hXeq]
    exact localCount_x_xn1 n s Y Z hpin hn1


end PadGrid

end Vdb
