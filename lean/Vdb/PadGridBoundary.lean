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


/-! ### The candidate contribution lemmas (y faces) -/

theorem contrib_y2 (n : Nat) (s : Lat → Bool) (X Y Z : Nat) (d : Bool) :
    contributes n s ((X, Y, Z), 1) d ((X, Y + 1, Z), 0) =
      (crossedB n s ((X, Y + 1, Z), 0) && decide (1 ≤ Z) && (s (X, Y + 1, Z) == d)) := by
  have hcontributes : ∀ f dir e, contributes n s f dir e =
      (crossedB n s e && (labels e.1 e.2 (s e.1)).contains ⟨f, dir⟩) := fun f dir e => rfl
  rw [hcontributes, hLabels0]
  simp only [decide_eq_true (show (1 ≤ Y + 1) from by omega), Bool.true_and, Bool.and_true]
  by_cases hc : (decide (1 ≤ Z) = true)
  · rw [ite_eq_left hc]
    simp only [decide_eq_true_eq] at hc
    have hZ : Z - 1 + 1 = Z := by omega
    rw [hij0]
    cases he : s (X, Y + 1, Z) <;> cases d <;>
      simp [Prod.mk.injEq, he, hadd1, hadd2, hZ, hc] <;> omega
  · rw [ite_eq_right hc]
    simp [hc]

theorem contrib_y3 (n : Nat) (s : Lat → Bool) (X Y Z : Nat) (d : Bool) :
    contributes n s ((X, Y, Z), 1) d ((X, Y + 1, Z), 2) =
      (crossedB n s ((X, Y + 1, Z), 2) && decide (1 ≤ X) && (s (X, Y + 1, Z) != d)) := by
  have hcontributes : ∀ f dir e, contributes n s f dir e =
      (crossedB n s e && (labels e.1 e.2 (s e.1)).contains ⟨f, dir⟩) := fun f dir e => rfl
  rw [hcontributes, hLabels2]
  simp only [decide_eq_true (show (1 ≤ Y + 1) from by omega), Bool.true_and, Bool.and_true]
  by_cases hc : (decide (1 ≤ X) = true)
  · rw [ite_eq_left hc]
    simp only [decide_eq_true_eq] at hc
    have hX' : X - 1 + 1 = X := by omega
    rw [hij2]
    cases he : s (X, Y + 1, Z) <;> cases d <;>
      simp [Prod.mk.injEq, he, hadd0, hX', hc] <;> omega
  · rw [ite_eq_right hc]
    simp [hc]

theorem contrib_y4 (n : Nat) (s : Lat → Bool) (X Y Z : Nat) (d : Bool) :
    contributes n s ((X, Y, Z), 1) d ((X, Y + 1, Z + 1), 0) =
      (crossedB n s ((X, Y + 1, Z + 1), 0) && (s (X, Y + 1, Z + 1) != d)) := by
  have hcontributes : ∀ f dir e, contributes n s f dir e =
      (crossedB n s e && (labels e.1 e.2 (s e.1)).contains ⟨f, dir⟩) := fun f dir e => rfl
  rw [hcontributes, hLabels0]
  simp only [decide_eq_true (show (1 ≤ Y + 1) from by omega),
    decide_eq_true (show (1 ≤ Z + 1) from by omega), Bool.and_true, Bool.true_and, ite_true]
  rw [hij0]
  cases he : s (X, Y + 1, Z + 1) <;> cases d <;>
    simp [Prod.mk.injEq, he, hadd0, hadd1, hadd2]

theorem contrib_y5 (n : Nat) (s : Lat → Bool) (X Y Z : Nat) (d : Bool) :
    contributes n s ((X, Y, Z), 1) d ((X + 1, Y + 1, Z), 2) =
      (crossedB n s ((X + 1, Y + 1, Z), 2) && (s (X + 1, Y + 1, Z) == d)) := by
  have hcontributes : ∀ f dir e, contributes n s f dir e =
      (crossedB n s e && (labels e.1 e.2 (s e.1)).contains ⟨f, dir⟩) := fun f dir e => rfl
  rw [hcontributes, hLabels2]
  simp only [decide_eq_true (show (1 ≤ Y + 1) from by omega),
    decide_eq_true (show (1 ≤ X + 1) from by omega), Bool.and_true, Bool.true_and, ite_true]
  rw [hij2]
  cases he : s (X + 1, Y + 1, Z) <;> cases d <;>
    simp [Prod.mk.injEq, he, hadd0, hadd1, hadd2]

/-- **Local count balance at an interior y-face**: all corner lattice points
    are interior; reduces like the x-face interior case to the window identity. -/
theorem localCount_y_interior (n : Nat) (s : Lat → Bool) (X Y Z : Nat)
    (hX1 : X + 1 ≤ n) (hY1 : Y + 1 ≤ n) (hZ1 : Z + 1 ≤ n)
    (hXi : 1 ≤ X) (hZi : 1 ≤ Z) :
    localCount n s ((X, Y, Z), 1) true = localCount n s ((X, Y, Z), 1) false := by
  have hc : candidates ((X, Y, Z), 1) =
      [((X - 1, Y + 1, Z), 2), ((X, Y + 1, Z - 1), 0),
       ((X, Y + 1, Z), 0), ((X, Y + 1, Z), 2),
       ((X, Y + 1, Z + 1), 0), ((X + 1, Y + 1, Z), 2)] := rfl
  have iL2 : decide (InLattice n (X, Y + 1, Z)) = true := by
    apply decide_eq_true_eq.mpr
    show X ≤ n ∧ Y + 1 ≤ n ∧ Z ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (X + 1, Y + 1, Z)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL3' : decide (InLattice n (X, Y + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL4' : decide (InLattice n (X + 1, Y + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have hm2 : decide (1 ≤ Z) = true := decide_eq_true_eq.mpr hZi
  have hm3 : decide (1 ≤ X) = true := decide_eq_true_eq.mpr hXi
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_y, e2_contributes_false_y]
  simp only [contrib_y2, contrib_y3, contrib_y4, contrib_y5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3,
    Bool.and_true, Bool.true_and, ite_true, ite_false]
  generalize he : s (X, Y + 1, Z) = e
  generalize hf : s (X + 1, Y + 1, Z) = f
  generalize hg : s (X, Y + 1, Z + 1) = g
  generalize hh : s (X + 1, Y + 1, Z + 1) = h
  clear he hf hg hh
  revert e f g h
  native_decide
/-- `y` face, `z = 0` boundary, `x` strictly interior: `e`, `f` pin on
    `Z = 0`; both `g` and `h` are free. -/
theorem localCount_y_z0_xint (n : Nat) (s : Lat → Bool) (X Y : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hX0 : 1 ≤ X) (hX1 : X ≤ n - 2) (hY1 : Y + 1 ≤ n) (hn : 3 ≤ n) :
    localCount n s ((X, Y, 0), 1) true = localCount n s ((X, Y, 0), 1) false := by
  have hc : candidates ((X, Y, 0), 1) =
      [((X - 1, Y + 1, 0), 2), ((X, Y + 1, 0 - 1), 0),
       ((X, Y + 1, 0), 0), ((X, Y + 1, 0), 2),
       ((X, Y + 1, 0 + 1), 0), ((X + 1, Y + 1, 0), 2)] := rfl
  have iL2 : decide (InLattice n (X, Y + 1, 0)) = true := by
    apply decide_eq_true_eq.mpr
    show X ≤ n ∧ Y + 1 ≤ n ∧ 0 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (X + 1, Y + 1, 0)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ Y + 1 ≤ n ∧ 0 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL3' : decide (InLattice n (X, Y + 1, 0 + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X ≤ n ∧ Y + 1 ≤ n ∧ 0 + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL4' : decide (InLattice n (X + 1, Y + 1, 0 + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ Y + 1 ≤ n ∧ 0 + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have hm2 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
  have hm3 : decide (1 ≤ X) = true := decide_eq_true_eq.mpr hX0
  have he : s (X, Y + 1, 0) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hf : s (X + 1, Y + 1, 0) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_y, e2_contributes_false_y]
  simp only [contrib_y2, contrib_y3, contrib_y4, contrib_y5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, he, hf,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize hg : s (X, Y + 1, 0 + 1) = g
  generalize hh : s (X + 1, Y + 1, 0 + 1) = h
  clear hg hh
  revert g h
  native_decide

/-- `y` face, `z = n - 1` boundary, `x` strictly interior: `g`, `h` pin on
    `Z + 1 = n`; both `e` and `f` are free. -/
theorem localCount_y_zn_xint (n : Nat) (s : Lat → Bool) (X Y : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hX0 : 1 ≤ X) (hX1 : X ≤ n - 2) (hY1 : Y + 1 ≤ n) (hn : 3 ≤ n) :
    localCount n s ((X, Y, n - 1), 1) true = localCount n s ((X, Y, n - 1), 1) false := by
  have hc : candidates ((X, Y, n - 1), 1) =
      [((X - 1, Y + 1, n - 1), 2), ((X, Y + 1, n - 1 - 1), 0),
       ((X, Y + 1, n - 1), 0), ((X, Y + 1, n - 1), 2),
       ((X, Y + 1, n - 1 + 1), 0), ((X + 1, Y + 1, n - 1), 2)] := rfl
  have iL2 : decide (InLattice n (X, Y + 1, n - 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X ≤ n ∧ Y + 1 ≤ n ∧ n - 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (X + 1, Y + 1, n - 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ Y + 1 ≤ n ∧ n - 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL3' : decide (InLattice n (X, Y + 1, n - 1 + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X ≤ n ∧ Y + 1 ≤ n ∧ n - 1 + 1 ≤ n
    omega
  have iL4' : decide (InLattice n (X + 1, Y + 1, n - 1 + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ Y + 1 ≤ n ∧ n - 1 + 1 ≤ n
    omega
  have hm2 : decide (1 ≤ n - 1) = true := decide_eq_true_eq.mpr (by omega)
  have hm3 : decide (1 ≤ X) = true := decide_eq_true_eq.mpr hX0
  have hg : s (X, Y + 1, n - 1 + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; right; right
    show (X, Y + 1, n - 1 + 1).2.2 = n
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
    e1_contributes_false_y, e2_contributes_false_y]
  simp only [contrib_y2, contrib_y3, contrib_y4, contrib_y5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, hg, hh,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.not_true, Bool.false_eq_true]
  generalize he : s (X, Y + 1, n - 1) = e
  generalize hf : s (X + 1, Y + 1, n - 1) = f
  clear he hf
  revert e f
  native_decide

/-- `y` face, `z = 0` corner, `x = 0` corner (in-grid): `e`, `f` pin on
    `Z = 0`, `g` pins on `X = 0`; only `h` is interior. -/
theorem localCount_y_z0_x0 (n : Nat) (s : Lat → Bool) (Y : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hY1 : Y + 1 ≤ n) (hn : 2 ≤ n) :
    localCount n s ((0, Y, 0), 1) true = localCount n s ((0, Y, 0), 1) false := by
  have hc : candidates ((0, Y, 0), 1) =
      [((0 - 1, Y + 1, 0), 2), ((0, Y + 1, 0 - 1), 0),
       ((0, Y + 1, 0), 0), ((0, Y + 1, 0), 2),
       ((0, Y + 1, 0 + 1), 0), ((0 + 1, Y + 1, 0), 2)] := rfl
  have iL2 : decide (InLattice n (0, Y + 1, 0)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 ≤ n ∧ Y + 1 ≤ n ∧ 0 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (0 + 1, Y + 1, 0)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 + 1 ≤ n ∧ Y + 1 ≤ n ∧ 0 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL3' : decide (InLattice n (0, Y + 1, 0 + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 ≤ n ∧ Y + 1 ≤ n ∧ 0 + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL4' : decide (InLattice n (0 + 1, Y + 1, 0 + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 + 1 ≤ n ∧ Y + 1 ≤ n ∧ 0 + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have hm2 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
  have hm3 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
  have he : s (0, Y + 1, 0) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inl rfl)
  have hf : s (0 + 1, Y + 1, 0) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hg : s (0, Y + 1, 0 + 1) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inl rfl)
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_y, e2_contributes_false_y]
  simp only [contrib_y2, contrib_y3, contrib_y4, contrib_y5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, he, hf, hg,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize hh : s (0 + 1, Y + 1, 0 + 1) = h
  clear hh
  revert h
  native_decide

/-- `y` face, `z = n - 1` boundary, `x = 0` (in-grid): `e`, `g` pin on
    `X = 0`, `h` pins on `Z + 1 = n`; `f` is free. -/
theorem localCount_y_zn_x0 (n : Nat) (s : Lat → Bool) (Y : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hY1 : Y + 1 ≤ n) (hn : 2 ≤ n) :
    localCount n s ((0, Y, n - 1), 1) true = localCount n s ((0, Y, n - 1), 1) false := by
  have hc : candidates ((0, Y, n - 1), 1) =
      [((0 - 1, Y + 1, n - 1), 2), ((0, Y + 1, n - 1 - 1), 0),
       ((0, Y + 1, n - 1), 0), ((0, Y + 1, n - 1), 2),
       ((0, Y + 1, n - 1 + 1), 0), ((0 + 1, Y + 1, n - 1), 2)] := rfl
  have iL2 : decide (InLattice n (0, Y + 1, n - 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 ≤ n ∧ Y + 1 ≤ n ∧ n - 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (0 + 1, Y + 1, n - 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 + 1 ≤ n ∧ Y + 1 ≤ n ∧ n - 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL3' : decide (InLattice n (0, Y + 1, n - 1 + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 ≤ n ∧ Y + 1 ≤ n ∧ n - 1 + 1 ≤ n
    omega
  have iL4' : decide (InLattice n (0 + 1, Y + 1, n - 1 + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 + 1 ≤ n ∧ Y + 1 ≤ n ∧ n - 1 + 1 ≤ n
    omega
  have hm2 : decide (1 ≤ n - 1) = true := decide_eq_true_eq.mpr (by omega)
  have hm3 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
  have he : s (0, Y + 1, n - 1) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inl rfl)
  have hg : s (0, Y + 1, n - 1 + 1) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inl rfl)
  have hh : s (0 + 1, Y + 1, n - 1 + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; right; right
    show (0 + 1, Y + 1, n - 1 + 1).2.2 = n
    show n - 1 + 1 = n
    omega
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_y, e2_contributes_false_y]
  simp only [contrib_y2, contrib_y3, contrib_y4, contrib_y5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, he, hg, hh,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize hf : s (0 + 1, Y + 1, n - 1) = f
  clear hf
  revert f
  native_decide

/-- `y` face, `y = n - 1` (top of grid): all four corner lattice points sit
    on the shell; all signs pinned false; count vanishes both ways. -/
theorem localCount_y_yn1 (n : Nat) (s : Lat → Bool) (X Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false) (hn : 1 ≤ n) :
    localCount n s ((X, n - 1, Z), 1) true = localCount n s ((X, n - 1, Z), 1) false := by
  have hc : candidates ((X, n - 1, Z), 1) =
      [((X - 1, n - 1 + 1, Z), 2), ((X, n - 1 + 1, Z - 1), 0),
       ((X, n - 1 + 1, Z), 0), ((X, n - 1 + 1, Z), 2),
       ((X, n - 1 + 1, Z + 1), 0), ((X + 1, n - 1 + 1, Z), 2)] := rfl
  have he : s (X, n - 1 + 1, Z) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; left
    show (X, n - 1 + 1, Z).2.1 = n
    show n - 1 + 1 = n
    omega
  have hf : s (X + 1, n - 1 + 1, Z) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; left
    show (X + 1, n - 1 + 1, Z).2.1 = n
    show n - 1 + 1 = n
    omega
  have hg : s (X, n - 1 + 1, Z + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; left
    show (X, n - 1 + 1, Z + 1).2.1 = n
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
    e1_contributes_false_y, e2_contributes_false_y]
  simp only [contrib_y2, contrib_y3, contrib_y4, contrib_y5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    he, hf, hg, hh,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize hu : decide (InLattice n (X, n - 1 + 1, Z)) = u
  generalize hv : decide (InLattice n (X + 1, n - 1 + 1, Z)) = v
  generalize hw : decide (InLattice n (X, n - 1 + 1, Z + 1)) = w
  generalize hxx : decide (InLattice n (X + 1, n - 1 + 1, Z + 1)) = xx
  generalize hm2 : decide (1 ≤ Z) = m2
  generalize hm3 : decide (1 ≤ X) = m3
  clear hu hv hw hxx hm2 hm3
  revert u v w xx m2 m3
  native_decide
/-- `y` face, `z` strictly interior, `x = 0` (in-grid): both `e` and `g`
    sit on the shell (`X = 0`); both `f` and `h` are free. -/
theorem localCount_y_zint_x0 (n : Nat) (s : Lat → Bool) (Y Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hY1 : Y + 1 ≤ n - 1) (hZ0 : 1 ≤ Z) (hZn : Z + 1 ≤ n - 1) (hn : 3 ≤ n) :
    localCount n s ((0, Y, Z), 1) true = localCount n s ((0, Y, Z), 1) false := by
  have hc : candidates ((0, Y, Z), 1) =
      [((0 - 1, Y + 1, Z), 2), ((0, Y + 1, Z - 1), 0),
       ((0, Y + 1, Z), 0), ((0, Y + 1, Z), 2),
       ((0, Y + 1, Z + 1), 0), ((0 + 1, Y + 1, Z), 2)] := rfl
  have iL2 : decide (InLattice n (0, Y + 1, Z)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 ≤ n ∧ Y + 1 ≤ n ∧ Z ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (0 + 1, Y + 1, Z)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL3' : decide (InLattice n (0, Y + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL4' : decide (InLattice n (0 + 1, Y + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have hm2 : decide (1 ≤ Z) = true := decide_eq_true_eq.mpr hZ0
  have hm3 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
  have he : s (0, Y + 1, Z) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inl rfl)
  have hg : s (0, Y + 1, Z + 1) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inl rfl)
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_y, e2_contributes_false_y]
  simp only [contrib_y2, contrib_y3, contrib_y4, contrib_y5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, he, hg,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize hf : s (0 + 1, Y + 1, Z) = f
  generalize hh : s (0 + 1, Y + 1, Z + 1) = h
  clear hf hh
  revert f h
  native_decide

/-- `y` face, `z = 0` boundary, `x = n - 1` (in-grid): `f`, `h` pin on
    `X + 1 = n`; both `e` and `g` are free. -/
theorem localCount_y_z0_xn1 (n : Nat) (s : Lat → Bool) (Y : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hY1 : Y + 1 ≤ n - 1) (hn : 2 ≤ n) :
    localCount n s ((n - 1, Y, 0), 1) true = localCount n s ((n - 1, Y, 0), 1) false := by
  have hc : candidates ((n - 1, Y, 0), 1) =
      [((n - 1 - 1, Y + 1, 0), 2), ((n - 1, Y + 1, 0 - 1), 0),
       ((n - 1, Y + 1, 0), 0), ((n - 1, Y + 1, 0), 2),
       ((n - 1, Y + 1, 0 + 1), 0), ((n - 1 + 1, Y + 1, 0), 2)] := rfl
  have iL2 : decide (InLattice n (n - 1, Y + 1, 0)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 ≤ n ∧ Y + 1 ≤ n ∧ 0 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (n - 1 + 1, Y + 1, 0)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 + 1 ≤ n ∧ Y + 1 ≤ n ∧ 0 ≤ n
    omega
  have iL3' : decide (InLattice n (n - 1, Y + 1, 0 + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 ≤ n ∧ Y + 1 ≤ n ∧ 0 + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL4' : decide (InLattice n (n - 1 + 1, Y + 1, 0 + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 + 1 ≤ n ∧ Y + 1 ≤ n ∧ 0 + 1 ≤ n
    omega
  have hm2 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
  have hm3 : decide (1 ≤ n - 1) = true := decide_eq_true_eq.mpr (by omega)
  have he : s (n - 1, Y + 1, 0) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hf : s (n - 1 + 1, Y + 1, 0) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; left
    show (n - 1 + 1, Y + 1, 0).1 = n
    show n - 1 + 1 = n
    omega
  have hh : s (n - 1 + 1, Y + 1, 0 + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; left
    show (n - 1 + 1, Y + 1, 0 + 1).1 = n
    show n - 1 + 1 = n
    omega
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_y, e2_contributes_false_y]
  simp only [contrib_y2, contrib_y3, contrib_y4, contrib_y5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, he, hf, hh,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize he : s (n - 1, Y + 1, 0) = e
  generalize hg : s (n - 1, Y + 1, 0 + 1) = g
  clear he hg
  revert e g
  native_decide

/-- `y` face, `z` strictly interior, `x = n - 1` (in-grid): `f`, `h` pin;
    both `e` and `g` are free. -/
theorem localCount_y_zint_xn1 (n : Nat) (s : Lat → Bool) (Y Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hY1 : Y + 1 ≤ n - 1) (hZ0 : 1 ≤ Z) (hZn : Z + 1 ≤ n - 1) (hn : 3 ≤ n) :
    localCount n s ((n - 1, Y, Z), 1) true = localCount n s ((n - 1, Y, Z), 1) false := by
  have hc : candidates ((n - 1, Y, Z), 1) =
      [((n - 1 - 1, Y + 1, Z), 2), ((n - 1, Y + 1, Z - 1), 0),
       ((n - 1, Y + 1, Z), 0), ((n - 1, Y + 1, Z), 2),
       ((n - 1, Y + 1, Z + 1), 0), ((n - 1 + 1, Y + 1, Z), 2)] := rfl
  have iL2 : decide (InLattice n (n - 1, Y + 1, Z)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 ≤ n ∧ Y + 1 ≤ n ∧ Z ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (n - 1 + 1, Y + 1, Z)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z ≤ n
    omega
  have iL3' : decide (InLattice n (n - 1, Y + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL4' : decide (InLattice n (n - 1 + 1, Y + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n
    omega
  have hm2 : decide (1 ≤ Z) = true := decide_eq_true_eq.mpr hZ0
  have hm3 : decide (1 ≤ n - 1) = true := decide_eq_true_eq.mpr (by omega)
  have hf : s (n - 1 + 1, Y + 1, Z) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; left
    show (n - 1 + 1, Y + 1, Z).1 = n
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
    e1_contributes_false_y, e2_contributes_false_y]
  simp only [contrib_y2, contrib_y3, contrib_y4, contrib_y5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, hf, hh,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize he : s (n - 1, Y + 1, Z) = e
  generalize hg : s (n - 1, Y + 1, Z + 1) = g
  clear he hg
  revert e g
  native_decide

/-- `y` face, `z = n - 1` boundary, `x = n - 1` (in-grid): `f`, `g`, `h` pin
    (`X + 1 = n` and `Z + 1 = n`); only `e` is free. -/
theorem localCount_y_zn_xn1 (n : Nat) (s : Lat → Bool) (Y : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hY1 : Y + 1 ≤ n - 1) (hn : 2 ≤ n) :
    localCount n s ((n - 1, Y, n - 1), 1) true = localCount n s ((n - 1, Y, n - 1), 1) false := by
  have hc : candidates ((n - 1, Y, n - 1), 1) =
      [((n - 1 - 1, Y + 1, n - 1), 2), ((n - 1, Y + 1, n - 1 - 1), 0),
       ((n - 1, Y + 1, n - 1), 0), ((n - 1, Y + 1, n - 1), 2),
       ((n - 1, Y + 1, n - 1 + 1), 0), ((n - 1 + 1, Y + 1, n - 1), 2)] := rfl
  have iL2 : decide (InLattice n (n - 1, Y + 1, n - 1)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 ≤ n ∧ Y + 1 ≤ n ∧ n - 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (n - 1 + 1, Y + 1, n - 1)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 + 1 ≤ n ∧ Y + 1 ≤ n ∧ n - 1 ≤ n
    omega
  have iL3' : decide (InLattice n (n - 1, Y + 1, n - 1 + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 ≤ n ∧ Y + 1 ≤ n ∧ n - 1 + 1 ≤ n
    omega
  have iL4' : decide (InLattice n (n - 1 + 1, Y + 1, n - 1 + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 + 1 ≤ n ∧ Y + 1 ≤ n ∧ n - 1 + 1 ≤ n
    omega
  have hm2 : decide (1 ≤ n - 1) = true := decide_eq_true_eq.mpr (by omega)
  have hm3 : decide (1 ≤ n - 1) = true := decide_eq_true_eq.mpr (by omega)
  have hf : s (n - 1 + 1, Y + 1, n - 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; left
    show (n - 1 + 1, Y + 1, n - 1).1 = n
    show n - 1 + 1 = n
    omega
  have hg : s (n - 1, Y + 1, n - 1 + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; right; right
    show (n - 1, Y + 1, n - 1 + 1).2.2 = n
    show n - 1 + 1 = n
    omega
  have hh : s (n - 1 + 1, Y + 1, n - 1 + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; right; right
    show (n - 1 + 1, Y + 1, n - 1 + 1).2.2 = n
    show n - 1 + 1 = n
    omega
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_y, e2_contributes_false_y]
  simp only [contrib_y2, contrib_y3, contrib_y4, contrib_y5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, hf, hg, hh,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize he : s (n - 1, Y + 1, n - 1) = e
  clear he
  revert e
  native_decide

/-- `y` face, out-of-grid along `X` (`n ≤ X`): `e` and `g` sit on the shell
    when `X = n` (pinned false); every InL gate with `X` or `X + 1` beyond
    `n` fails, so candidate 2's second gate (`X + 1 ≤ n`) fails for every
    `X ≥ n`. -/
theorem localCount_y_out_x (n : Nat) (s : Lat → Bool) (X Y Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false) (hX : n ≤ X) :
    localCount n s ((X, Y, Z), 1) true = localCount n s ((X, Y, Z), 1) false := by
  by_cases hXn : X = n
  · -- X = n: e and g pinned false (shell); candidate gates with X+1 > n fail
    have hc : candidates ((X, Y, Z), 1) =
        [((X - 1, Y + 1, Z), 2), ((X, Y + 1, Z - 1), 0),
         ((X, Y + 1, Z), 0), ((X, Y + 1, Z), 2),
         ((X, Y + 1, Z + 1), 0), ((X + 1, Y + 1, Z), 2)] := by rfl
    have hA : decide (InLattice n (X + 1, Y + 1, Z)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z ≤ n)
      omega
    have hB : decide (InLattice n (X + 1, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    have he : s (X, Y + 1, Z) = false := by
      apply hpin
      refine shell_of_or n _ ?_
      right; left
      show (X, Y + 1, Z).1 = n
      exact hXn
    have hg : s (X, Y + 1, Z + 1) = false := by
      apply hpin
      refine shell_of_or n _ ?_
      right; left
      show (X, Y + 1, Z + 1).1 = n
      exact hXn
    unfold localCount
    rw [hc]
    simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
      List.length_cons, List.length_nil, Bool.false_eq_true,
      e1_contributes_false_y, e2_contributes_false_y]
    simp only [contrib_y2, contrib_y3, contrib_y4, contrib_y5]
    simp only [hcrossedB, hsn0, hsn1, hsn2, hA, hB, he, hg,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
      Bool.not_false, Bool.false_eq_true]
    generalize hu : decide (InLattice n (X, Y + 1, Z)) = u
    generalize hw : decide (InLattice n (X, Y + 1, Z + 1)) = w
    generalize hm2 : decide (1 ≤ Z) = m2
    generalize hm3 : decide (1 ≤ X) = m3
    generalize hf : s (X + 1, Y + 1, Z) = f
    generalize hh : s (X + 1, Y + 1, Z + 1) = h
    clear hu hw hm2 hm3 hf hh
    revert u w m2 m3 f h
    native_decide
  · -- X > n: every InL gate fails
    have hc : candidates ((X, Y, Z), 1) =
        [((X - 1, Y + 1, Z), 2), ((X, Y + 1, Z - 1), 0),
         ((X, Y + 1, Z), 0), ((X, Y + 1, Z), 2),
         ((X, Y + 1, Z + 1), 0), ((X + 1, Y + 1, Z), 2)] := by rfl
    have hA : decide (InLattice n (X, Y + 1, Z)) = false := by
      apply decide_eq_false
      show ¬(X ≤ n ∧ Y + 1 ≤ n ∧ Z ≤ n)
      omega
    have hB : decide (InLattice n (X + 1, Y + 1, Z)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z ≤ n)
      omega
    have hC : decide (InLattice n (X, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    have hD : decide (InLattice n (X + 1, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    unfold localCount
    rw [hc]
    simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
      List.length_cons, List.length_nil, Bool.false_eq_true,
      e1_contributes_false_y, e2_contributes_false_y]
    simp only [contrib_y2, contrib_y3, contrib_y4, contrib_y5]
    simp only [hcrossedB, hsn0, hsn1, hsn2, hA, hB, hC, hD,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
      Bool.not_false, Bool.false_eq_true]

/-- `y` face, out-of-grid along `Y` (`n ≤ Y`): the cell is outside the
    `n^3` grid; every corner lattice point is off-lattice or on the top
    shell — in particular, InL gates with `Y + 1 > n` all fail. -/
theorem localCount_y_out_y_general (n : Nat) (s : Lat → Bool) (X Y Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false) (hY : n ≤ Y) :
    localCount n s ((X, Y, Z), 1) true = localCount n s ((X, Y, Z), 1) false := by
  by_cases hYn : Y = n - 1 ∧ 1 ≤ n
  · -- Y = n - 1 with n ≥ 1: the top of the grid, all corner points shell
    rcases hYn with ⟨hYne, hn⟩
    rw [hYne]
    exact localCount_y_yn1 n s X Z hpin hn
  · -- Y ≥ n: corners at Y + 1 ≥ n + 1 are off-lattice, all gates fail
    have hc : candidates ((X, Y, Z), 1) =
        [((X - 1, Y + 1, Z), 2), ((X, Y + 1, Z - 1), 0),
         ((X, Y + 1, Z), 0), ((X, Y + 1, Z), 2),
         ((X, Y + 1, Z + 1), 0), ((X + 1, Y + 1, Z), 2)] := by rfl
    have hA : decide (InLattice n (X, Y + 1, Z)) = false := by
      apply decide_eq_false
      show ¬(X ≤ n ∧ Y + 1 ≤ n ∧ Z ≤ n)
      omega
    have hB : decide (InLattice n (X + 1, Y + 1, Z)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z ≤ n)
      omega
    have hC : decide (InLattice n (X, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    have hD : decide (InLattice n (X + 1, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    unfold localCount
    rw [hc]
    simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
      List.length_cons, List.length_nil, Bool.false_eq_true,
      e1_contributes_false_y, e2_contributes_false_y]
    simp only [contrib_y2, contrib_y3, contrib_y4, contrib_y5]
    simp only [hcrossedB, hsn0, hsn1, hsn2, hA, hB, hC, hD,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
      Bool.not_false, Bool.false_eq_true]

theorem localCount_y_out_y (n : Nat) (s : Lat → Bool) (X Y Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false) (hY : n ≤ Y) :
    localCount n s ((X, Y, Z), 1) true = localCount n s ((X, Y, Z), 1) false := by
  exact localCount_y_out_y_general n s X Y Z hpin hY

/-- `y` face, out-of-grid along `Z` (`n ≤ Z`): either `Z = n - 1` or
    `Z ≥ n`; either all corner points sit on the shell (`Z = n`), or every
    InL gate with `Z` or `Z + 1` beyond `n` fails. -/
theorem localCount_y_out_z (n : Nat) (s : Lat → Bool) (X Y Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false) (hZ : n ≤ Z) :
    localCount n s ((X, Y, Z), 1) true = localCount n s ((X, Y, Z), 1) false := by
  by_cases hZn : Z = n
  · -- Z = n: e and f pinned false (shell); InL with Z + 1 fails
    have hc : candidates ((X, Y, Z), 1) =
        [((X - 1, Y + 1, Z), 2), ((X, Y + 1, Z - 1), 0),
         ((X, Y + 1, Z), 0), ((X, Y + 1, Z), 2),
         ((X, Y + 1, Z + 1), 0), ((X + 1, Y + 1, Z), 2)] := by rfl
    have hA : decide (InLattice n (X, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    have hB : decide (InLattice n (X + 1, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    have he : s (X, Y + 1, Z) = false := by
      apply hpin
      refine shell_of_or n _ ?_
      right; right; right; right; right
      show (X, Y + 1, Z).2.2 = n
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
      e1_contributes_false_y, e2_contributes_false_y]
    simp only [contrib_y2, contrib_y3, contrib_y4, contrib_y5]
    simp only [hcrossedB, hsn0, hsn1, hsn2, hA, hB, he, hf,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
      Bool.not_false, Bool.false_eq_true]
    generalize hu : decide (InLattice n (X, Y + 1, Z)) = u
    generalize hv : decide (InLattice n (X + 1, Y + 1, Z)) = v
    generalize hm2 : decide (1 ≤ Z) = m2
    generalize hm3 : decide (1 ≤ X) = m3
    generalize hg : s (X, Y + 1, Z + 1) = g
    generalize hh : s (X + 1, Y + 1, Z + 1) = h
    clear hu hv hm2 hm3 hg hh
    revert u v m2 m3 g h
    native_decide
  · -- Z > n: every InL gate fails
    have hc : candidates ((X, Y, Z), 1) =
        [((X - 1, Y + 1, Z), 2), ((X, Y + 1, Z - 1), 0),
         ((X, Y + 1, Z), 0), ((X, Y + 1, Z), 2),
         ((X, Y + 1, Z + 1), 0), ((X + 1, Y + 1, Z), 2)] := by rfl
    have hA : decide (InLattice n (X, Y + 1, Z)) = false := by
      apply decide_eq_false
      show ¬(X ≤ n ∧ Y + 1 ≤ n ∧ Z ≤ n)
      omega
    have hB : decide (InLattice n (X + 1, Y + 1, Z)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z ≤ n)
      omega
    have hC : decide (InLattice n (X, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    have hD : decide (InLattice n (X + 1, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    unfold localCount
    rw [hc]
    simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
      List.length_cons, List.length_nil, Bool.false_eq_true,
      e1_contributes_false_y, e2_contributes_false_y]
    simp only [contrib_y2, contrib_y3, contrib_y4, contrib_y5]
    simp only [hcrossedB, hsn0, hsn1, hsn2, hA, hB, hC, hD,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
      Bool.not_false, Bool.false_eq_true]

/-- `y` face universal local balance. -/
theorem localCount_y_face (n : Nat) (s : Lat → Bool) (X Y Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false) :
    localCount n s ((X, Y, Z), 1) true = localCount n s ((X, Y, Z), 1) false := by
  by_cases hXn : n ≤ X
  · exact localCount_y_out_x n s X Y Z hpin hXn
  by_cases hYn : n ≤ Y
  · exact localCount_y_out_y n s X Y Z hpin hYn
  by_cases hZn : n ≤ Z
  · exact localCount_y_out_z n s X Y Z hpin hZn
  by_cases hY1 : Y + 1 < n
  · by_cases hZ0 : Z = 0
    · by_cases hX0 : X = 0
      · rw [hX0, hZ0]; exact localCount_y_z0_x0 n s Y hpin (by omega) (by omega)
      by_cases hXn1 : X = n - 1
      · rw [hXn1, hZ0]; exact localCount_y_z0_xn1 n s Y hpin (by omega) (by omega)
      have hXi : 1 ≤ X := by omega
      have hX2 : X ≤ n - 2 := by omega
      rw [hZ0]
      exact localCount_y_z0_xint n s X Y hpin hXi hX2 (by omega) (by omega)
    by_cases hZn1 : Z = n - 1
    · by_cases hX0 : X = 0
      · rw [hX0, hZn1]; exact localCount_y_zn_x0 n s Y hpin (by omega) (by omega)
      by_cases hXn1 : X = n - 1
      · rw [hXn1, hZn1]; exact localCount_y_zn_xn1 n s Y hpin (by omega) (by omega)
      have hXi : 1 ≤ X := by omega
      have hX2 : X ≤ n - 2 := by omega
      rw [hZn1]
      exact localCount_y_zn_xint n s X Y hpin hXi hX2 (by omega) (by omega)
    have hZi1 : 1 ≤ Z := by omega
    have hZi2 : Z + 1 ≤ n - 1 := by omega
    by_cases hX0 : X = 0
    · rw [hX0]
      have hY2 : Y + 1 ≤ n - 1 := by omega
      exact localCount_y_zint_x0 n s Y Z hpin hY2 hZi1 hZi2 (by omega)
    by_cases hXn1 : X = n - 1
    · rw [hXn1]
      have hY2 : Y + 1 ≤ n - 1 := by omega
      exact localCount_y_zint_xn1 n s Y Z hpin hY2 hZi1 hZi2 (by omega)
    have hXi : 1 ≤ X := by omega
    exact localCount_y_interior n s X Y Z (by omega) (by omega) (by omega) hXi hZi1
  · -- Y = n - 1 (n ≥ 1 since we are in-grid)
    have hYeq : Y = n - 1 := by omega
    rw [hYeq]
    have hn1 : 1 ≤ n := by omega
    exact localCount_y_yn1 n s X Z hpin hn1

/-! ### The candidate contribution lemmas (z faces) -/

theorem contrib_z2 (n : Nat) (s : Lat → Bool) (X Y Z : Nat) (d : Bool) :
    contributes n s ((X, Y, Z), 2) d ((X, Y, Z + 1), 0) =
      (crossedB n s ((X, Y, Z + 1), 0) && decide (1 ≤ Y) && (s (X, Y, Z + 1) != d)) := by
  have hcontributes : ∀ f dir e, contributes n s f dir e =
      (crossedB n s e && (labels e.1 e.2 (s e.1)).contains ⟨f, dir⟩) := fun f dir e => rfl
  rw [hcontributes, hLabels0]
  simp only [decide_eq_true (show (1 ≤ Z + 1) from by omega), Bool.true_and, Bool.and_true]
  by_cases hc : (decide (1 ≤ Y) = true)
  · rw [ite_eq_left hc]
    simp only [decide_eq_true_eq] at hc
    have hY' : Y - 1 + 1 = Y := by omega
    rw [hij0]
    cases he : s (X, Y, Z + 1) <;> cases d <;>
      simp [Prod.mk.injEq, he, hadd1, hadd2, hY', hc] <;> omega
  · rw [ite_eq_right hc]
    simp [hc]

theorem contrib_z3 (n : Nat) (s : Lat → Bool) (X Y Z : Nat) (d : Bool) :
    contributes n s ((X, Y, Z), 2) d ((X, Y, Z + 1), 1) =
      (crossedB n s ((X, Y, Z + 1), 1) && decide (1 ≤ X) && (s (X, Y, Z + 1) == d)) := by
  have hcontributes : ∀ f dir e, contributes n s f dir e =
      (crossedB n s e && (labels e.1 e.2 (s e.1)).contains ⟨f, dir⟩) := fun f dir e => rfl
  rw [hcontributes, hLabels1]
  simp only [decide_eq_true (show (1 ≤ Z + 1) from by omega), Bool.true_and, Bool.and_true]
  by_cases hc : (decide (1 ≤ X) = true)
  · rw [ite_eq_left hc]
    simp only [decide_eq_true_eq] at hc
    have hX' : X - 1 + 1 = X := by omega
    rw [hij1]
    cases he : s (X, Y, Z + 1) <;> cases d <;>
      simp [Prod.mk.injEq, he, hadd0, hadd2, hX', hc] <;> omega
  · rw [ite_eq_right hc]
    simp [hc]

theorem contrib_z4 (n : Nat) (s : Lat → Bool) (X Y Z : Nat) (d : Bool) :
    contributes n s ((X, Y, Z), 2) d ((X, Y + 1, Z + 1), 0) =
      (crossedB n s ((X, Y + 1, Z + 1), 0) && (s (X, Y + 1, Z + 1) == d)) := by
  have hcontributes : ∀ f dir e, contributes n s f dir e =
      (crossedB n s e && (labels e.1 e.2 (s e.1)).contains ⟨f, dir⟩) := fun f dir e => rfl
  rw [hcontributes, hLabels0]
  simp only [decide_eq_true (show (1 ≤ Y + 1) from by omega),
    decide_eq_true (show (1 ≤ Z + 1) from by omega), Bool.and_true, Bool.true_and, ite_true]
  rw [hij0]
  cases he : s (X, Y + 1, Z + 1) <;> cases d <;>
    simp [Prod.mk.injEq, he, hadd0, hadd1, hadd2]

theorem contrib_z5 (n : Nat) (s : Lat → Bool) (X Y Z : Nat) (d : Bool) :
    contributes n s ((X, Y, Z), 2) d ((X + 1, Y, Z + 1), 1) =
      (crossedB n s ((X + 1, Y, Z + 1), 1) && (s (X + 1, Y, Z + 1) != d)) := by
  have hcontributes : ∀ f dir e, contributes n s f dir e =
      (crossedB n s e && (labels e.1 e.2 (s e.1)).contains ⟨f, dir⟩) := fun f dir e => rfl
  rw [hcontributes, hLabels1]
  simp only [decide_eq_true (show (1 ≤ X + 1) from by omega),
    decide_eq_true (show (1 ≤ Z + 1) from by omega), Bool.and_true, Bool.true_and, ite_true]
  rw [hij1]
  cases he : s (X + 1, Y, Z + 1) <;> cases d <;>
    simp [Prod.mk.injEq, he, hadd0, hadd1, hadd2]

/-- **Local count balance at an interior z-face**. -/
theorem localCount_z_interior (n : Nat) (s : Lat → Bool) (X Y Z : Nat)
    (hX1 : X + 1 ≤ n) (hY1 : Y + 1 ≤ n) (hZ1 : Z + 1 ≤ n)
    (hXi : 1 ≤ X) (hYi : 1 ≤ Y) :
    localCount n s ((X, Y, Z), 2) true = localCount n s ((X, Y, Z), 2) false := by
  have hc : candidates ((X, Y, Z), 2) =
      [((X - 1, Y, Z + 1), 1), ((X, Y - 1, Z + 1), 0),
       ((X, Y, Z + 1), 0), ((X, Y, Z + 1), 1),
       ((X, Y + 1, Z + 1), 0), ((X + 1, Y, Z + 1), 1)] := rfl
  have iL2 : decide (InLattice n (X, Y, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X ≤ n ∧ Y ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (X + 1, Y, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ Y ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL3' : decide (InLattice n (X, Y + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL4' : decide (InLattice n (X + 1, Y + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have hm2 : decide (1 ≤ Y) = true := decide_eq_true_eq.mpr hYi
  have hm3 : decide (1 ≤ X) = true := decide_eq_true_eq.mpr hXi
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_z, e2_contributes_false_z]
  simp only [contrib_z2, contrib_z3, contrib_z4, contrib_z5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3,
    Bool.and_true, Bool.true_and, ite_true, ite_false]
  generalize he : s (X, Y, Z + 1) = e
  generalize hf : s (X + 1, Y, Z + 1) = f
  generalize hg : s (X, Y + 1, Z + 1) = g
  generalize hh : s (X + 1, Y + 1, Z + 1) = h
  clear he hf hg hh
  revert e f g h
  native_decide
/-- `z` face, `Z = n - 1` (top): all four corner points sit on the shell;
    all signs pinned false; count vanishes both ways. -/
theorem localCount_z_zn1 (n : Nat) (s : Lat → Bool) (X Y : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false) (hn : 1 ≤ n) :
    localCount n s ((X, Y, n - 1), 2) true = localCount n s ((X, Y, n - 1), 2) false := by
  have hc : candidates ((X, Y, n - 1), 2) =
      [((X - 1, Y, n - 1 + 1), 1), ((X, Y - 1, n - 1 + 1), 0),
       ((X, Y, n - 1 + 1), 0), ((X, Y, n - 1 + 1), 1),
       ((X, Y + 1, n - 1 + 1), 0), ((X + 1, Y, n - 1 + 1), 1)] := rfl
  have he : s (X, Y, n - 1 + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; right; right
    show (X, Y, n - 1 + 1).2.2 = n
    show n - 1 + 1 = n
    omega
  have hf : s (X + 1, Y, n - 1 + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; right; right
    show (X + 1, Y, n - 1 + 1).2.2 = n
    show n - 1 + 1 = n
    omega
  have hg : s (X, Y + 1, n - 1 + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; right; right
    show (X, Y + 1, n - 1 + 1).2.2 = n
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
    e1_contributes_false_z, e2_contributes_false_z]
  simp only [contrib_z2, contrib_z3, contrib_z4, contrib_z5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    he, hf, hg, hh,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize hu : decide (InLattice n (X, Y, n - 1 + 1)) = u
  generalize hv : decide (InLattice n (X + 1, Y, n - 1 + 1)) = v
  generalize hw : decide (InLattice n (X, Y + 1, n - 1 + 1)) = w
  generalize hxx : decide (InLattice n (X + 1, Y + 1, n - 1 + 1)) = xx
  generalize hm2 : decide (1 ≤ Y) = m2
  generalize hm3 : decide (1 ≤ X) = m3
  clear hu hv hw hxx hm2 hm3
  revert u v w xx m2 m3
  native_decide

/-- `z` face, `Y = 0` boundary: both `e` and `f` sit on the shell; interior in `X`. -/
theorem localCount_z_y0 (n : Nat) (s : Lat → Bool) (X Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hX0 : 1 ≤ X) (hX1 : X ≤ n - 2) (hZ1 : Z + 1 ≤ n) (hn : 2 ≤ n) :
    localCount n s ((X, 0, Z), 2) true = localCount n s ((X, 0, Z), 2) false := by
  have hc : candidates ((X, 0, Z), 2) =
      [((X - 1, 0, Z + 1), 1), ((X, 0 - 1, Z + 1), 0),
       ((X, 0, Z + 1), 0), ((X, 0, Z + 1), 1),
       ((X, 0 + 1, Z + 1), 0), ((X + 1, 0, Z + 1), 1)] := rfl
  have iL2 : decide (InLattice n (X, 0, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X ≤ n ∧ 0 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (X + 1, 0, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ 0 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL3' : decide (InLattice n (X, 0 + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X ≤ n ∧ 0 + 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL4' : decide (InLattice n (X + 1, 0 + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ 0 + 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have hm2 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
  have hm3 : decide (1 ≤ X) = true := decide_eq_true_eq.mpr hX0
  have he : s (X, 0, Z + 1) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inr (Or.inr (Or.inl rfl)))
  have hf : s (X + 1, 0, Z + 1) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inr (Or.inr (Or.inl rfl)))
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_z, e2_contributes_false_z]
  simp only [contrib_z2, contrib_z3, contrib_z4, contrib_z5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, he, hf,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize hg : s (X, 0 + 1, Z + 1) = g
  generalize hh : s (X + 1, 0 + 1, Z + 1) = h
  clear hg hh
  revert g h
  native_decide

/-- `z` face, `Y = 0` corner, `X = 0` corner (in-grid): both `e` and `g`
    pinned (`Y = 0` / `X = 0`); only `h` interior. -/
theorem localCount_z_y0_x0 (n : Nat) (s : Lat → Bool) (Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hZ1 : Z + 1 ≤ n) (hn : 2 ≤ n) :
    localCount n s ((0, 0, Z), 2) true = localCount n s ((0, 0, Z), 2) false := by
  have hc : candidates ((0, 0, Z), 2) =
      [((0 - 1, 0, Z + 1), 1), ((0, 0 - 1, Z + 1), 0),
       ((0, 0, Z + 1), 0), ((0, 0, Z + 1), 1),
       ((0, 0 + 1, Z + 1), 0), ((0 + 1, 0, Z + 1), 1)] := rfl
  have iL2 : decide (InLattice n (0, 0, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 ≤ n ∧ 0 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (0 + 1, 0, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 + 1 ≤ n ∧ 0 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL3' : decide (InLattice n (0, 0 + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 ≤ n ∧ 0 + 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL4' : decide (InLattice n (0 + 1, 0 + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 + 1 ≤ n ∧ 0 + 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have hm2 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
  have hm3 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
  have he : s (0, 0, Z + 1) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inr (Or.inr (Or.inl rfl)))
  have hf : s (0 + 1, 0, Z + 1) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inr (Or.inr (Or.inl rfl)))
  have hg : s (0, 0 + 1, Z + 1) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inl rfl)
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_z, e2_contributes_false_z]
  simp only [contrib_z2, contrib_z3, contrib_z4, contrib_z5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, he, hf, hg,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize hh : s (0 + 1, 0 + 1, Z + 1) = h
  clear hh
  revert h
  native_decide

/-- `z` face, `Y = n - 1` boundary: both `g` and `h` sit on the shell;
    both `e` and `f` are free. -/
theorem localCount_z_yn1 (n : Nat) (s : Lat → Bool) (X Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hX0 : 1 ≤ X) (hX1 : X ≤ n - 2) (hZ1 : Z + 1 ≤ n) (hn : 2 ≤ n) :
    localCount n s ((X, n - 1, Z), 2) true = localCount n s ((X, n - 1, Z), 2) false := by
  have hc : candidates ((X, n - 1, Z), 2) =
      [((X - 1, n - 1, Z + 1), 1), ((X, n - 1 - 1, Z + 1), 0),
       ((X, n - 1, Z + 1), 0), ((X, n - 1, Z + 1), 1),
       ((X, n - 1 + 1, Z + 1), 0), ((X + 1, n - 1, Z + 1), 1)] := rfl
  have iL2 : decide (InLattice n (X, n - 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X ≤ n ∧ n - 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (X + 1, n - 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ n - 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL3' : decide (InLattice n (X, n - 1 + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X ≤ n ∧ n - 1 + 1 ≤ n ∧ Z + 1 ≤ n
    omega
  have iL4' : decide (InLattice n (X + 1, n - 1 + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show X + 1 ≤ n ∧ n - 1 + 1 ≤ n ∧ Z + 1 ≤ n
    omega
  have hm2 : decide (1 ≤ n - 1) = true := decide_eq_true_eq.mpr (by omega)
  have hm3 : decide (1 ≤ X) = true := decide_eq_true_eq.mpr hX0
  have hg : s (X, n - 1 + 1, Z + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; left
    show (X, n - 1 + 1, Z + 1).2.1 = n
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
    e1_contributes_false_z, e2_contributes_false_z]
  simp only [contrib_z2, contrib_z3, contrib_z4, contrib_z5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, hg, hh,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize he : s (X, n - 1, Z + 1) = e
  generalize hf : s (X + 1, n - 1, Z + 1) = f
  clear he hf
  revert e f
  native_decide

/-- `z` face, `Y = 0` corner, `X = n - 1` (in-grid): both `e` and `g` pin
    (`Y = 0` / `X = 0` shell cases); only `h` interior. -/
theorem localCount_z_y0_xn1 (n : Nat) (s : Lat → Bool) (Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hZ1 : Z + 1 ≤ n) (hn : 2 ≤ n) :
    localCount n s ((n - 1, 0, Z), 2) true = localCount n s ((n - 1, 0, Z), 2) false := by
  have hc : candidates ((n - 1, 0, Z), 2) =
      [((n - 1 - 1, 0, Z + 1), 1), ((n - 1, 0 - 1, Z + 1), 0),
       ((n - 1, 0, Z + 1), 0), ((n - 1, 0, Z + 1), 1),
       ((n - 1, 0 + 1, Z + 1), 0), ((n - 1 + 1, 0, Z + 1), 1)] := rfl
  have iL2 : decide (InLattice n (n - 1, 0, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 ≤ n ∧ 0 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (n - 1 + 1, 0, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 + 1 ≤ n ∧ 0 ≤ n ∧ Z + 1 ≤ n
    omega
  have iL3' : decide (InLattice n (n - 1, 0 + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 ≤ n ∧ 0 + 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL4' : decide (InLattice n (n - 1 + 1, 0 + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 + 1 ≤ n ∧ 0 + 1 ≤ n ∧ Z + 1 ≤ n
    omega
  have hm2 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
  have hm3 : decide (1 ≤ n - 1) = true := decide_eq_true_eq.mpr (by omega)
  have he : s (n - 1, 0, Z + 1) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inr (Or.inr (Or.inl rfl)))
  have hf : s (n - 1 + 1, 0, Z + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; left
    show (n - 1 + 1, 0, Z + 1).1 = n
    show n - 1 + 1 = n
    omega
  have hh : s (n - 1 + 1, 0 + 1, Z + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; left
    show (n - 1 + 1, 0 + 1, Z + 1).1 = n
    show n - 1 + 1 = n
    omega
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_z, e2_contributes_false_z]
  simp only [contrib_z2, contrib_z3, contrib_z4, contrib_z5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, he, hf, hh,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize hg : s (n - 1, 0 + 1, Z + 1) = g
  clear hg
  revert g
  native_decide

/-- `z` face, `Y = n - 1` corner, `X = n - 1` (in-grid): the two `Y = n`
    corner lattice points are on the shell; the two `X = n` corners are shell
    too; only the inner corner is free. -/
theorem localCount_z_yn1_xn1 (n : Nat) (s : Lat → Bool) (Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false) (hn : 2 ≤ n) :
    localCount n s ((n - 1, n - 1, Z), 2) true = localCount n s ((n - 1, n - 1, Z), 2) false := by
  have hc : candidates ((n - 1, n - 1, Z), 2) =
      [((n - 1 - 1, n - 1, Z + 1), 1), ((n - 1, n - 1 - 1, Z + 1), 0),
       ((n - 1, n - 1, Z + 1), 0), ((n - 1, n - 1, Z + 1), 1),
       ((n - 1, n - 1 + 1, Z + 1), 0), ((n - 1 + 1, n - 1, Z + 1), 1)] := rfl
  have hf : s (n - 1 + 1, n - 1, Z + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; left
    show (n - 1 + 1, n - 1, Z + 1).1 = n
    show n - 1 + 1 = n
    omega
  have hg : s (n - 1, n - 1 + 1, Z + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; left
    show (n - 1, n - 1 + 1, Z + 1).2.1 = n
    show n - 1 + 1 = n
    omega
  have hh : s (n - 1 + 1, n - 1 + 1, Z + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; left
    show (n - 1 + 1, n - 1 + 1, Z + 1).2.1 = n
    show n - 1 + 1 = n
    omega
  by_cases hZ1 : Z + 1 ≤ n
  · -- Z + 1 ≤ n: every gate is true; both counts equal the window identity
    have hu : decide (InLattice n (n - 1, n - 1, Z + 1)) = true := by
      apply decide_eq_true_eq.mpr
      show n - 1 ≤ n ∧ n - 1 ≤ n ∧ Z + 1 ≤ n
      exact ⟨by omega, by omega, hZ1⟩
    have hv : decide (InLattice n (n - 1 + 1, n - 1, Z + 1)) = true := by
      apply decide_eq_true_eq.mpr
      show n - 1 + 1 ≤ n ∧ n - 1 ≤ n ∧ Z + 1 ≤ n
      omega
    have hw : decide (InLattice n (n - 1, n - 1 + 1, Z + 1)) = true := by
      apply decide_eq_true_eq.mpr
      show n - 1 ≤ n ∧ n - 1 + 1 ≤ n ∧ Z + 1 ≤ n
      omega
    have hxx : decide (InLattice n (n - 1 + 1, n - 1 + 1, Z + 1)) = true := by
      apply decide_eq_true_eq.mpr
      show n - 1 + 1 ≤ n ∧ n - 1 + 1 ≤ n ∧ Z + 1 ≤ n
      omega
    have hm2 : decide (1 ≤ n - 1) = true := decide_eq_true_eq.mpr (by omega)
    have hm3 : decide (1 ≤ n - 1) = true := decide_eq_true_eq.mpr (by omega)
    unfold localCount
    rw [hc]
    simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
      List.length_cons, List.length_nil, Bool.false_eq_true,
      e1_contributes_false_z, e2_contributes_false_z]
    simp only [contrib_z2, contrib_z3, contrib_z4, contrib_z5]
    simp only [hcrossedB, hsn0, hsn1, hsn2,
      hu, hv, hw, hxx, hm2, hm3, hf, hg, hh,
      Bool.and_true, Bool.true_and, ite_true, ite_false]
    generalize he : s (n - 1, n - 1, Z + 1) = e
    clear he
    revert e
    native_decide
  · -- Z + 1 > n: every gate is false; both counts are zero
    have hu : decide (InLattice n (n - 1, n - 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(n - 1 ≤ n ∧ n - 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    have hv : decide (InLattice n (n - 1 + 1, n - 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(n - 1 + 1 ≤ n ∧ n - 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    have hw : decide (InLattice n (n - 1, n - 1 + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(n - 1 ≤ n ∧ n - 1 + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    have hxx : decide (InLattice n (n - 1 + 1, n - 1 + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(n - 1 + 1 ≤ n ∧ n - 1 + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    unfold localCount
    rw [hc]
    simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
      List.length_cons, List.length_nil, Bool.false_eq_true,
      e1_contributes_false_z, e2_contributes_false_z]
    simp only [contrib_z2, contrib_z3, contrib_z4, contrib_z5]
    simp only [hcrossedB, hsn0, hsn1, hsn2,
      hu, hv, hw, hxx,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
      Bool.not_false, Bool.false_eq_true]

/-- `z` face, `Y = n - 1` corner, `X = 0` (in-grid): `e`, `g`, `h` pin on
    the shell; only `f` is interior. -/
theorem localCount_z_yn1_x0 (n : Nat) (s : Lat → Bool) (Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hZ1 : Z + 1 ≤ n) (hn : 2 ≤ n) :
    localCount n s ((0, n - 1, Z), 2) true = localCount n s ((0, n - 1, Z), 2) false := by
  have hc : candidates ((0, n - 1, Z), 2) =
      [((0 - 1, n - 1, Z + 1), 1), ((0, n - 1 - 1, Z + 1), 0),
       ((0, n - 1, Z + 1), 0), ((0, n - 1, Z + 1), 1),
       ((0, n - 1 + 1, Z + 1), 0), ((0 + 1, n - 1, Z + 1), 1)] := rfl
  have iL2 : decide (InLattice n (0, n - 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 ≤ n ∧ n - 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (0 + 1, n - 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 + 1 ≤ n ∧ n - 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL3' : decide (InLattice n (0, n - 1 + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 ≤ n ∧ n - 1 + 1 ≤ n ∧ Z + 1 ≤ n
    omega
  have iL4' : decide (InLattice n (0 + 1, n - 1 + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 + 1 ≤ n ∧ n - 1 + 1 ≤ n ∧ Z + 1 ≤ n
    omega
  have hm2 : decide (1 ≤ n - 1) = true := decide_eq_true_eq.mpr (by omega)
  have hm3 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
  have he : s (0, n - 1, Z + 1) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inl rfl)
  have hg : s (0, n - 1 + 1, Z + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; left
    show (0, n - 1 + 1, Z + 1).2.1 = n
    show n - 1 + 1 = n
    omega
  have hh : s (0 + 1, n - 1 + 1, Z + 1) = false := by
    apply hpin
    refine shell_of_or n _ ?_
    right; right; right; left
    show (0 + 1, n - 1 + 1, Z + 1).2.1 = n
    show n - 1 + 1 = n
    omega
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_z, e2_contributes_false_z]
  simp only [contrib_z2, contrib_z3, contrib_z4, contrib_z5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, he, hg, hh,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize hf : s (0 + 1, n - 1, Z + 1) = f
  clear hf
  revert f
  native_decide

/-- `z` face, `x = 0` boundary, `y` strictly interior: both `e` and `g` sit
    on the shell; both `f` and `h` are free. -/
theorem localCount_z_zint_x0 (n : Nat) (s : Lat → Bool) (Y Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hY0 : 1 ≤ Y) (hY1 : Y + 1 ≤ n - 1) (hZ1 : Z + 1 ≤ n) (hn : 3 ≤ n) :
    localCount n s ((0, Y, Z), 2) true = localCount n s ((0, Y, Z), 2) false := by
  have hc : candidates ((0, Y, Z), 2) =
      [((0 - 1, Y, Z + 1), 1), ((0, Y - 1, Z + 1), 0),
       ((0, Y, Z + 1), 0), ((0, Y, Z + 1), 1),
       ((0, Y + 1, Z + 1), 0), ((0 + 1, Y, Z + 1), 1)] := rfl
  have iL2 : decide (InLattice n (0, Y, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 ≤ n ∧ Y ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (0 + 1, Y, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 + 1 ≤ n ∧ Y ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL3' : decide (InLattice n (0, Y + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL4' : decide (InLattice n (0 + 1, Y + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show 0 + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have hm2 : decide (1 ≤ Y) = true := decide_eq_true_eq.mpr hY0
  have hm3 : decide (1 ≤ 0) = false := decide_eq_false (by omega)
  have he : s (0, Y, Z + 1) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inl rfl)
  have hg : s (0, Y + 1, Z + 1) = false := by
    apply hpin
    exact shell_of_or n _ (Or.inl rfl)
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_z, e2_contributes_false_z]
  simp only [contrib_z2, contrib_z3, contrib_z4, contrib_z5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, he, hg,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize hf : s (0 + 1, Y, Z + 1) = f
  generalize hh : s (0 + 1, Y + 1, Z + 1) = h
  clear hf hh
  revert f h
  native_decide

/-- `z` face, `x = n - 1` boundary, `y` strictly interior: both `f` and `h`
    sit on the shell; both `e` and `g` are free. -/
theorem localCount_z_xn1_yint (n : Nat) (s : Lat → Bool) (Y Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hY0 : 1 ≤ Y) (hY1 : Y + 1 ≤ n - 1) (hZ1 : Z + 1 ≤ n) (hn : 3 ≤ n) :
    localCount n s ((n - 1, Y, Z), 2) true = localCount n s ((n - 1, Y, Z), 2) false := by
  have hc : candidates ((n - 1, Y, Z), 2) =
      [((n - 1 - 1, Y, Z + 1), 1), ((n - 1, Y - 1, Z + 1), 0),
       ((n - 1, Y, Z + 1), 0), ((n - 1, Y, Z + 1), 1),
       ((n - 1, Y + 1, Z + 1), 0), ((n - 1 + 1, Y, Z + 1), 1)] := rfl
  have iL2 : decide (InLattice n (n - 1, Y, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 ≤ n ∧ Y ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL2' : decide (InLattice n (n - 1 + 1, Y, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 + 1 ≤ n ∧ Y ≤ n ∧ Z + 1 ≤ n
    omega
  have iL3' : decide (InLattice n (n - 1, Y + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n
    exact ⟨by omega, by omega, by omega⟩
  have iL4' : decide (InLattice n (n - 1 + 1, Y + 1, Z + 1)) = true := by
    apply decide_eq_true_eq.mpr
    show n - 1 + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n
    omega
  have hm2 : decide (1 ≤ Y) = true := decide_eq_true_eq.mpr hY0
  have hm3 : decide (1 ≤ n - 1) = true := decide_eq_true_eq.mpr (by omega)
  have hf : s (n - 1 + 1, Y, Z + 1) = false := by
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
    e1_contributes_false_z, e2_contributes_false_z]
  simp only [contrib_z2, contrib_z3, contrib_z4, contrib_z5]
  simp only [hcrossedB, hsn0, hsn1, hsn2,
    iL2, iL2', iL3', iL4', hm2, hm3, hf, hh,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]
  generalize he : s (n - 1, Y, Z + 1) = e
  generalize hg : s (n - 1, Y + 1, Z + 1) = g
  clear he hg
  revert e g
  native_decide

/-- `z` face, out-of-grid along `X` (`n ≤ X`): the face's corners sit at the
    boundary or beyond; the gate with `X + 1 = n + 1` fails. -/
theorem localCount_z_out_x (n : Nat) (s : Lat → Bool) (X Y Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false) (hX : n ≤ X) :
    localCount n s ((X, Y, Z), 2) true = localCount n s ((X, Y, Z), 2) false := by
  by_cases hXn : X = n
  · -- X = n: e and g pinned false (shell); gates with X+1 > n fail
    have hc : candidates ((X, Y, Z), 2) =
        [((X - 1, Y, Z + 1), 1), ((X, Y - 1, Z + 1), 0),
         ((X, Y, Z + 1), 0), ((X, Y, Z + 1), 1),
         ((X, Y + 1, Z + 1), 0), ((X + 1, Y, Z + 1), 1)] := by rfl
    have hA : decide (InLattice n (X + 1, Y, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y ≤ n ∧ Z + 1 ≤ n)
      omega
    have hB : decide (InLattice n (X + 1, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    have he : s (X, Y, Z + 1) = false := by
      apply hpin
      refine shell_of_or n _ ?_
      right; left
      show (X, Y, Z + 1).1 = n
      exact hXn
    have hg : s (X, Y + 1, Z + 1) = false := by
      apply hpin
      refine shell_of_or n _ ?_
      right; left
      show (X, Y + 1, Z + 1).1 = n
      exact hXn
    unfold localCount
    rw [hc]
    simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
      List.length_cons, List.length_nil, Bool.false_eq_true,
      e1_contributes_false_z, e2_contributes_false_z]
    simp only [contrib_z2, contrib_z3, contrib_z4, contrib_z5]
    simp only [hcrossedB, hsn0, hsn1, hsn2, hA, hB, he, hg,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
      Bool.not_false, Bool.false_eq_true]
    generalize hu : decide (InLattice n (X, Y, Z + 1)) = u
    generalize hw : decide (InLattice n (X, Y + 1, Z + 1)) = w
    generalize hm2 : decide (1 ≤ Y) = m2
    generalize hm3 : decide (1 ≤ X) = m3
    generalize hf : s (X + 1, Y, Z + 1) = f
    generalize hh : s (X + 1, Y + 1, Z + 1) = h
    clear hu hw hm2 hm3 hf hh
    revert u w m2 m3 f h
    native_decide
  · -- X > n: every InL gate fails
    have hc : candidates ((X, Y, Z), 2) =
        [((X - 1, Y, Z + 1), 1), ((X, Y - 1, Z + 1), 0),
         ((X, Y, Z + 1), 0), ((X, Y, Z + 1), 1),
         ((X, Y + 1, Z + 1), 0), ((X + 1, Y, Z + 1), 1)] := by rfl
    have hA : decide (InLattice n (X, Y, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X ≤ n ∧ Y ≤ n ∧ Z + 1 ≤ n)
      omega
    have hB : decide (InLattice n (X + 1, Y, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y ≤ n ∧ Z + 1 ≤ n)
      omega
    have hC : decide (InLattice n (X, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    have hD : decide (InLattice n (X + 1, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    unfold localCount
    rw [hc]
    simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
      List.length_cons, List.length_nil, Bool.false_eq_true,
      e1_contributes_false_z, e2_contributes_false_z]
    simp only [contrib_z2, contrib_z3, contrib_z4, contrib_z5]
    simp only [hcrossedB, hsn0, hsn1, hsn2, hA, hB, hC, hD,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
      Bool.not_false, Bool.false_eq_true]

/-- `z` face, out-of-grid along `Y` (`n ≤ Y`): the cell sits off-lattice or
    near the top layer; InL gates with Y+1 > n all fail. -/
theorem localCount_z_out_y (n : Nat) (s : Lat → Bool) (X Y Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false) (hY : n ≤ Y) :
    localCount n s ((X, Y, Z), 2) true = localCount n s ((X, Y, Z), 2) false := by
  by_cases hYn : Y = n
  · -- Y = n: e and g sit on the shell (pinned false); gates with Y + 1 = n + 1 fail
    have hc : candidates ((X, Y, Z), 2) =
        [((X - 1, Y, Z + 1), 1), ((X, Y - 1, Z + 1), 0),
         ((X, Y, Z + 1), 0), ((X, Y, Z + 1), 1),
         ((X, Y + 1, Z + 1), 0), ((X + 1, Y, Z + 1), 1)] := by rfl
    have hA : decide (InLattice n (X, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    have hB : decide (InLattice n (X + 1, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    have he : s (X, Y, Z + 1) = false := by
      apply hpin
      refine shell_of_or n _ ?_
      right; right; right; left
      show (X, Y, Z + 1).2.1 = n
      exact hYn
    have hf : s (X + 1, Y, Z + 1) = false := by
      apply hpin
      refine shell_of_or n _ ?_
      right; right; right; left
      show (X + 1, Y, Z + 1).2.1 = n
      exact hYn
    unfold localCount
    rw [hc]
    simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
      List.length_cons, List.length_nil, Bool.false_eq_true,
      e1_contributes_false_z, e2_contributes_false_z]
    simp only [contrib_z2, contrib_z3, contrib_z4, contrib_z5]
    simp only [hcrossedB, hsn0, hsn1, hsn2, hA, hB, he, hf,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
      Bool.not_false, Bool.false_eq_true]
    generalize hu : decide (InLattice n (X, Y, Z + 1)) = u
    generalize hx : decide (InLattice n (X + 1, Y, Z + 1)) = x1
    generalize hm2 : decide (1 ≤ Y) = m2
    generalize hm3 : decide (1 ≤ X) = m3
    clear hu hx hm2 hm3
    revert u x1 m2 m3
    native_decide
  · -- Y > n: corners at Y + 1 ≥ n + 2 are off-lattice; every gate fails
    have hc : candidates ((X, Y, Z), 2) =
        [((X - 1, Y, Z + 1), 1), ((X, Y - 1, Z + 1), 0),
         ((X, Y, Z + 1), 0), ((X, Y, Z + 1), 1),
         ((X, Y + 1, Z + 1), 0), ((X + 1, Y, Z + 1), 1)] := by rfl
    have hA : decide (InLattice n (X, Y, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X ≤ n ∧ Y ≤ n ∧ Z + 1 ≤ n)
      omega
    have hB : decide (InLattice n (X + 1, Y, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y ≤ n ∧ Z + 1 ≤ n)
      omega
    have hC : decide (InLattice n (X, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    have hD : decide (InLattice n (X + 1, Y + 1, Z + 1)) = false := by
      apply decide_eq_false
      show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
      omega
    unfold localCount
    rw [hc]
    simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
      List.length_cons, List.length_nil, Bool.false_eq_true,
      e1_contributes_false_z, e2_contributes_false_z]
    simp only [contrib_z2, contrib_z3, contrib_z4, contrib_z5]
    simp only [hcrossedB, hsn0, hsn1, hsn2, hA, hB, hC, hD,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
      Bool.not_false, Bool.false_eq_true]

/-- `z` face, out-of-grid along `Z` (`n ≤ Z`): the corner lattice points at
    Z + 1 ≥ n + 1 are off-lattice, all gates fail. -/
theorem localCount_z_out_z (n : Nat) (s : Lat → Bool) (X Y Z : Nat)
    (_hpin : ∀ p, isShell n p = true → s p = false) (hZ : n ≤ Z) :
    localCount n s ((X, Y, Z), 2) true = localCount n s ((X, Y, Z), 2) false := by
  -- Z ≥ n: corner lattice points at Z + 1 ≥ n + 1 are off-lattice; every gate fails
  have hc : candidates ((X, Y, Z), 2) =
      [((X - 1, Y, Z + 1), 1), ((X, Y - 1, Z + 1), 0),
       ((X, Y, Z + 1), 0), ((X, Y, Z + 1), 1),
       ((X, Y + 1, Z + 1), 0), ((X + 1, Y, Z + 1), 1)] := by rfl
  have hA : decide (InLattice n (X, Y, Z + 1)) = false := by
    apply decide_eq_false
    show ¬(X ≤ n ∧ Y ≤ n ∧ Z + 1 ≤ n)
    omega
  have hB : decide (InLattice n (X + 1, Y, Z + 1)) = false := by
    apply decide_eq_false
    show ¬(X + 1 ≤ n ∧ Y ≤ n ∧ Z + 1 ≤ n)
    omega
  have hC : decide (InLattice n (X, Y + 1, Z + 1)) = false := by
    apply decide_eq_false
    show ¬(X ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
    omega
  have hD : decide (InLattice n (X + 1, Y + 1, Z + 1)) = false := by
    apply decide_eq_false
    show ¬(X + 1 ≤ n ∧ Y + 1 ≤ n ∧ Z + 1 ≤ n)
    omega
  unfold localCount
  rw [hc]
  simp only [List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_z, e2_contributes_false_z]
  simp only [contrib_z2, contrib_z3, contrib_z4, contrib_z5]
  simp only [hcrossedB, hsn0, hsn1, hsn2, hA, hB, hC, hD,
    Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, ite_true, ite_false,
    Bool.not_false, Bool.false_eq_true]

/-- `z` face universal local balance. -/
theorem localCount_z_face (n : Nat) (s : Lat → Bool) (X Y Z : Nat)
    (hpin : ∀ p, isShell n p = true → s p = false) :
    localCount n s ((X, Y, Z), 2) true = localCount n s ((X, Y, Z), 2) false := by
  by_cases hXn : n ≤ X
  · exact localCount_z_out_x n s X Y Z hpin hXn
  by_cases hYn : n ≤ Y
  · exact localCount_z_out_y n s X Y Z hpin hYn
  by_cases hZn : n ≤ Z
  · exact localCount_z_out_z n s X Y Z hpin hZn
  by_cases hZ1 : Z + 1 < n
  · by_cases hY0 : Y = 0
    · by_cases hX0 : X = 0
      · rw [hX0, hY0]; exact localCount_z_y0_x0 n s Z hpin (by omega) (by omega)
      by_cases hXn1 : X = n - 1
      · rw [hXn1, hY0]; exact localCount_z_y0_xn1 n s Z hpin (by omega) (by omega)
      have hXi : 1 ≤ X := by omega
      have hX2 : X ≤ n - 2 := by omega
      rw [hY0]
      exact localCount_z_y0 n s X Z hpin hXi hX2 (by omega) (by omega)
    by_cases hYn1 : Y = n - 1
    · by_cases hX0 : X = 0
      · rw [hX0, hYn1]; exact localCount_z_yn1_x0 n s Z hpin (by omega) (by omega)
      by_cases hXn1 : X = n - 1
      · rw [hXn1, hYn1]; exact localCount_z_yn1_xn1 n s Z hpin (by omega)
      have hXi : 1 ≤ X := by omega
      have hX2 : X ≤ n - 2 := by omega
      rw [hYn1]
      exact localCount_z_yn1 n s X Z hpin hXi hX2 (by omega) (by omega)
    have hYi1 : 1 ≤ Y := by omega
    have hYi2 : Y + 1 ≤ n - 1 := by omega
    by_cases hX0 : X = 0
    · rw [hX0]
      exact localCount_z_zint_x0 n s Y Z hpin hYi1 hYi2 (by omega) (by omega)
    by_cases hXn1 : X = n - 1
    · rw [hXn1]
      exact localCount_z_xn1_yint n s Y Z hpin hYi1 hYi2 (by omega) (by omega)
    have hXi : 1 ≤ X := by omega
    exact localCount_z_interior n s X Y Z (by omega) (by omega) (by omega) hXi hYi1
  · -- Z = n - 1 (n ≥ 1 since we are in-grid)
    have hZeq : Z = n - 1 := by omega
    rw [hZeq]
    have hn1 : 1 ≤ n := by omega
    exact localCount_z_zn1 n s X Y hpin hn1

/-- **The general-`n` balance theorem** (T-DMC0-CYCLE for shell-pinned sign
    fields): every face's two local candidate counts agree, hence the
    assembled stencil is `Balanced`. Assembled from the three universal
    orientation dispatchers (`localCount_x_face`, `localCount_y_face`,
    `localCount_z_face`) via the bridge `balanced_iff_local`; directions
    `≥ 3` are unused. -/
theorem balanced_general (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false) :
    (cuberilleStencil n s).Balanced := by
  rw [balanced_iff_local]
  intro f
  obtain ⟨c, i⟩ := f
  obtain ⟨X, Y, Z⟩ := c
  by_cases h0 : i = 0
  · rw [h0]
    exact localCount_x_face n s X Y Z hpin
  by_cases h1 : i = 1
  · rw [h1]
    exact localCount_y_face n s X Y Z hpin
  by_cases h2 : i = 2
  · rw [h2]
    exact localCount_z_face n s X Y Z hpin
  · have hge : 3 ≤ i := by omega
    rw [localCount_eq_zero_of_nf_ge_three n s (X, Y, Z) i hge true,
        localCount_eq_zero_of_nf_ge_three n s (X, Y, Z) i hge false]

/-- **The general-`n` mesh is edge-closed** (T-DMC0-CYCLE, edge form): the
    assembled surface of every shell-pinned sign field is watertight in the
    edge-manifold sense. -/
theorem edgeClosed_general (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false) :
    EdgeClosed (cuberilleStencil n s).mesh :=
  (cuberilleStencil n s).watertight (balanced_general n s hpin)

end PadGrid

end Vdb
