/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  Convex polyhedra (finite half-space intersections), the Hilbert
  projection onto them, and the **sign dichotomy for the convex case of
  the mesh→SDF closest-feature rule** — the mathematical content behind
  finding F16's fix in the C code (see `lean/VERIFICATION.md`):

  * `halfSpaces`, `isClosed_halfSpaces`, `convex_halfSpaces` — finite
    half-space intersections are closed and convex;
  * `projection_exists` — the Hilbert projection theorem instantiated:
    every point has a closest point in a nonempty closed convex set;
  * `Tight`, `Admissible` — the constraints active at `q` and the
    directions `y` that do not violate them;
  * `exists_pos_smul_mem_halfSpaces` — the **local normal cone step**:
    an admissible direction stays inside the half-space intersection for
    a small positive scaling (the non-tight constraints have positive
    slack; finite `ι`);
  * **`proj_inner_le_zero_of_admissible`** — the usable form of the
    normal-cone characterization: `⟪p − q, y⟫ ≤ 0` for every
    admissible `y` at the closest point `q`;
  * **`exists_tight_pairing_pos`** — an outside point pairs **strictly
    positively** with at least one tight face normal: `∃ i, Tight n b q i
    ∧ 0 < ⟪n i, p − q⟫`. This is the convex case of the
    any-incident-face-pairs-positively rule the C code uses to sign
    mesh→SDF voxels (F16);
  * **`inside_inner_le_zero`** — an inside point pairs non-positively
    with every tight face normal (the elementary inside direction);
  * `tetra_outside_pairings` / `tetra_inside_pairings` — the concrete
    F16 counterexample re-run through the machinery: at the apex of the
    rational-coordinate tetrahedron, `p = (t, 0, 0)` pairs strictly
    positively with the `n₁` face and non-positively with `n₂`, `n₃`
    (the F16 trap), and a concrete inside point pairs non-positively
    with every face.

  What is *not* claimed: the expansion `p − q = Σᵢ λᵢ nᵢ` with `λᵢ ≥ 0`
  (the finitely-generated cone is not shown to be closed, which is the
  step that would need the bipolar theorem). The sign dichotomy does
  **not** need it: `exists_tight_pairing_pos` follows from
  `proj_inner_le_zero_of_admissible` and the projection characterization.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Vdb

open scoped RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-! ### Half-space intersections -/

/-- A finite intersection of closed half-spaces `{x | ⟪n i, x⟫ ≤ b i}`. -/
def halfSpaces {ι : Type*} (n : ι → F) (b : ι → ℝ) : Set F :=
  {x | ∀ i, ⟪n i, x⟫ ≤ b i}

theorem mem_halfSpaces {ι : Type*} {n : ι → F} {b : ι → ℝ} {x : F} :
    x ∈ halfSpaces n b ↔ ∀ i, ⟪n i, x⟫ ≤ b i := Iff.rfl

theorem isClosed_halfSpaces {ι : Type*} {n : ι → F} {b : ι → ℝ} :
    IsClosed (halfSpaces n b) := by
  rw [show halfSpaces n b = ⋂ i, {x | ⟪n i, x⟫ ≤ b i} from (Set.iInter_ofPred _).symm]
  exact isClosed_iInter fun i => isClosed_le
    (show Continuous fun x => ⟪n i, x⟫ by fun_prop) continuous_const

theorem convex_halfSpaces {ι : Type*} {n : ι → F} {b : ι → ℝ} :
    Convex ℝ (halfSpaces n b) := by
  intro x hx y hy a c ha hc hac i
  show ⟪n i, a • x + c • y⟫ ≤ b i
  calc ⟪n i, a • x + c • y⟫
      = a * ⟪n i, x⟫ + c * ⟪n i, y⟫ := by
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    _ ≤ a * b i + c * b i := by nlinarith [hx i, hy i, ha, hc]
    _ = b i := by rw [← add_mul, hac, one_mul]

/-! ### The closest point (Hilbert projection) -/

/-- The Hilbert projection theorem instantiated for a nonempty closed
    convex set in a finite-dimensional real inner product space. -/
theorem projection_exists {K : Set F} (hne : K.Nonempty) (hclosed : IsClosed K)
    (hconv : Convex ℝ K) :
    ∀ u : F, ∃ v ∈ K, ‖u - v‖ = ⨅ w : K, ‖u - w‖ := by
  have := FiniteDimensional.completeSpace (𝕜 := ℝ) (E := F)
  exact exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv

/-! ### Tight constraints and admissible directions -/

/-- The constraints tight at `q` — the faces incident at `q`. -/
def Tight {ι : Type*} (n : ι → F) (b : ι → ℝ) (q : F) (i : ι) : Prop :=
  ⟪n i, q⟫ = b i

/-- A direction `y` is admissible at `q` when it does not violate any
    tight constraint (the local cone at `q`, without the closedness
    theorem). -/
def Admissible {ι : Type*} (n : ι → F) (b : ι → ℝ) (q : F) (y : F) : Prop :=
  ∀ i, Tight n b q i → ⟪n i, y⟫ ≤ 0

/-- The slack of the `i`-th constraint at `q` (positive iff not tight). -/
def slack {ι : Type*} (n : ι → F) (b : ι → ℝ) (q : F) (i : ι) : ℝ :=
  b i - ⟪n i, q⟫

/-- **Local normal cone step**: an admissible direction stays inside the
    half-space intersection for a small positive scaling. -/
theorem exists_pos_smul_mem_halfSpaces {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ι → F} {b : ι → ℝ} {q y : F}
    (hq : q ∈ halfSpaces n b) (hadm : Admissible n b q y) :
    ∃ t > 0, ∀ s : ℝ, 0 ≤ s → s ≤ t → q + s • y ∈ halfSpaces n b := by
  classical
  by_cases hall : ∀ i, ⟪n i, q⟫ = b i
  · refine ⟨1, one_pos, fun s hs _ i => ?_⟩
    have hy := hadm i (hall i)
    calc ⟪n i, q + s • y⟫
        = ⟪n i, q⟫ + s * ⟪n i, y⟫ := by
          rw [inner_add_right, real_inner_smul_right]
      _ ≤ ⟪n i, q⟫ := by nlinarith
      _ = b i := hall i
  · push Not at hall
    obtain ⟨i₀, hi₀⟩ := hall
    let T : Finset ι := Finset.univ.filter fun i => ¬ ⟪n i, q⟫ = b i
    have hT : T.Nonempty := ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩⟩
    have hslack : ∀ i ∈ T, 0 < slack n b q i := by
      intro i hi
      have hle : ⟪n i, q⟫ ≤ b i := hq i
      have hne : ⟪n i, q⟫ ≠ b i := (Finset.mem_filter.mp hi).2
      simp only [slack]
      have hlt : ⟪n i, q⟫ < b i := lt_of_le_of_ne hle hne
      linarith
    let ratio : ι → ℝ := fun i => slack n b q i / (|⟪n i, y⟫| + 1)
    have hratio : ∀ i ∈ T, 0 < ratio i := by
      intro i hi
      have h1 := hslack i hi
      have h2 : 0 < |⟪n i, y⟫| + 1 := by
        have := abs_nonneg (⟪n i, y⟫)
        nlinarith
      exact div_pos h1 h2
    let t := (T.image ratio).min' (hT.image ratio)
    have ht : 0 < t := by
      have hmem : t ∈ T.image ratio := Finset.min'_mem _ _
      obtain ⟨i, hiT, hi_eq⟩ := Finset.mem_image.mp hmem
      rw [show t = ratio i from hi_eq.symm]
      exact hratio i hiT
    have hTsmall : ∀ i ∈ T, t * (|⟪n i, y⟫| + 1) ≤ slack n b q i := by
      intro i hi
      have hmem : ratio i ∈ T.image ratio := Finset.mem_image.mpr ⟨i, hi, rfl⟩
      have hle := Finset.min'_le _ _ hmem
      have hpos : 0 < |⟪n i, y⟫| + 1 := by
        have := abs_nonneg (⟪n i, y⟫)
        nlinarith
      rw [show t = (T.image ratio).min' (hT.image ratio) from rfl]
      rw [le_div_iff₀ hpos] at hle
      nlinarith [hle]
    refine ⟨t, ht, fun s hs hs' i => ?_⟩
    by_cases htight : ⟪n i, q⟫ = b i
    · have hy := hadm i htight
      calc ⟪n i, q + s • y⟫
          = ⟪n i, q⟫ + s * ⟪n i, y⟫ := by
            rw [inner_add_right, real_inner_smul_right]
        _ ≤ ⟪n i, q⟫ := by nlinarith
        _ = b i := htight
    · have hiT : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, htight⟩
      have hle := hq i
      have hsl := hTsmall i hiT
      have hy_abs : ⟪n i, y⟫ ≤ |⟪n i, y⟫| := le_abs_self _
      calc ⟪n i, q + s • y⟫
          = ⟪n i, q⟫ + s * ⟪n i, y⟫ := by
            rw [inner_add_right, real_inner_smul_right]
        _ ≤ ⟪n i, q⟫ + s * |⟪n i, y⟫| := by nlinarith
        _ ≤ ⟪n i, q⟫ + t * (|⟪n i, y⟫| + 1) := by
            nlinarith [abs_nonneg (⟪n i, y⟫), hs, hs']
        _ ≤ ⟪n i, q⟫ + slack n b q i := by nlinarith
        _ = b i := by simp [slack]

/-! ### The sign dichotomy -/

/-- The projection characterization in usable form: every admissible
    direction at the closest point pairs non-positively. -/
theorem proj_inner_le_zero_of_admissible {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ι → F} {b : ι → ℝ} {p q : F}
    (hq : q ∈ halfSpaces n b)
    (hm : ‖p - q‖ = ⨅ w : (halfSpaces n b), ‖p - w‖)
    {y : F} (hadm : Admissible n b q y) :
    ⟪p - q, y⟫ ≤ 0 := by
  obtain ⟨t, ht, htmem⟩ := exists_pos_smul_mem_halfSpaces hq hadm
  have hmem : q + t • y ∈ halfSpaces n b := htmem t ht.le le_rfl
  have hchar := (norm_eq_iInf_iff_real_inner_le_zero (convex_halfSpaces (n := n) (b := b)) hq).mp hm
    (q + t • y) hmem
  have hsub : (q + t • y) - q = t • y := by abel
  rw [hsub, real_inner_smul_right] at hchar
  have ht' : 0 < t := ht
  nlinarith [hchar, ht']

/-- **Outside direction (convex case)**: an outside point pairs strictly
    positively with at least one tight face normal at the closest point. -/
theorem exists_tight_pairing_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ι → F} {b : ι → ℝ} {p q : F}
    (hq : q ∈ halfSpaces n b) (hp : p ∉ halfSpaces n b)
    (hm : ‖p - q‖ = ⨅ w : (halfSpaces n b), ‖p - w‖) :
    ∃ i, Tight n b q i ∧ 0 < ⟪n i, p - q⟫ := by
  by_contra hcon
  push Not at hcon
  have hadm : Admissible n b q (p - q) := fun i hi => hcon i hi
  have h1 := proj_inner_le_zero_of_admissible hq hm hadm
  have h2 : ⟪p - q, p - q⟫ ≤ 0 := h1
  have h3 : ⟪p - q, p - q⟫ = ‖p - q‖ ^ 2 := real_inner_self_eq_norm_sq _
  have h4 : p - q = 0 := by
    have : ‖p - q‖ ^ 2 ≤ 0 := by linarith
    have hnonneg := sq_nonneg (‖p - q‖)
    have hnorm : ‖p - q‖ = 0 := by nlinarith
    exact norm_eq_zero.mp hnorm
  have h5 : p = q := sub_eq_zero.mp h4
  exact hp (h5 ▸ hq)

/-- **Inside direction**: an inside point pairs non-positively with
    every tight face normal at `q` (the elementary half-space fact). -/
theorem inside_inner_le_zero {ι : Type*} {n : ι → F} {b : ι → ℝ} {p q : F}
    (hp : p ∈ halfSpaces n b) (_hq : q ∈ halfSpaces n b)
    {i : ι} (hi : Tight n b q i) :
    ⟪n i, p - q⟫ ≤ 0 := by
  have h1 : ⟪n i, p⟫ ≤ b i := hp i
  have h2 : ⟪n i, q⟫ = b i := hi
  have h3 : ⟪n i, p - q⟫ = ⟪n i, p⟫ - ⟪n i, q⟫ := by rw [inner_sub_right]
  rw [h3, h2]
  linarith

end Vdb

/-! ### The concrete F16 tetrahedron instance -/

namespace Vdb

open scoped RealInnerProductSpace

namespace Tetra

/-- The four outward unit normals of the F16 rational tetrahedron:
    apex at the origin, base `z = -1`, faces `x = 0`, two through the
    apex sloping into `z < 0`, and the base. -/
noncomputable def n1 : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![1, 0, 0]
noncomputable def n2 : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![-2/3, 2/3, 1/3]
noncomputable def n3 : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![-2/3, -2/3, 1/3]
noncomputable def n4 : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![0, 0, -1]

/-- The corresponding half-space constants (`b = 0` for the three apex
    faces, `b = 1` for the base `z ≥ -1`). -/
def b : Fin 4 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | _ => 1

/-- The tetrahedron as a half-space intersection. -/
noncomputable def K : Set (EuclideanSpace ℝ (Fin 3)) :=
  halfSpaces (fun i => match i with | 0 => n1 | 1 => n2 | 2 => n3 | _ => n4) b

/-- The outside point on the `n₁` ray (`t > 0`) pairs strictly positively
    with face 1, non-positively with faces 2 and 3, and zero with the
    base — the F16 trap configuration, checked by evaluation. -/
theorem pairing_outside {t : ℝ} (_ht : 0 < t) :
    ⟪n1, WithLp.toLp 2 ![t, 0, 0] - 0⟫ = t ∧
    ⟪n2, WithLp.toLp 2 ![t, 0, 0] - 0⟫ = -2/3 * t ∧
    ⟪n3, WithLp.toLp 2 ![t, 0, 0] - 0⟫ = -2/3 * t ∧
    ⟪n4, WithLp.toLp 2 ![t, 0, 0] - 0⟫ = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [n1, n2, n3, n4, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
      sub_eq_add_neg, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] <;>
    ring

/-- An outside point of the tetrahedron pairs strictly positively with
    at least one face (the `n₁` face, with gap `t`). -/
theorem outside_pairing_pos {t : ℝ} (ht : 0 < t) :
    ∃ i : Fin 4,
      ⟪(match i with | 0 => n1 | 1 => n2 | 2 => n3 | _ => n4),
          WithLp.toLp 2 ![t, 0, 0] - 0⟫ > 0 := by
  exact ⟨0, by
    simp [n1, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
      sub_eq_add_neg, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    exact ht⟩

/-- A concrete inside point: the centroid-ish rational point
    `(-1/6, 0, -1/2)` pairs non-positively with every face normal. -/
theorem inside_pairings :
    ⟪n1, WithLp.toLp 2 ![-1/6, 0, -1/2]⟫ ≤ 0 ∧
    ⟪n2, WithLp.toLp 2 ![-1/6, 0, -1/2]⟫ ≤ 0 ∧
    ⟪n3, WithLp.toLp 2 ![-1/6, 0, -1/2]⟫ ≤ 0 ∧
    ⟪n4, WithLp.toLp 2 ![-1/6, 0, -1/2]⟫ ≤ 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [n1, n2, n3, n4, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] <;>
    norm_num

end Tetra

end Vdb
