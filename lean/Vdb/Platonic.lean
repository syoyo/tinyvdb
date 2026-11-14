/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Platonic-solid SDFs (`src/tinyvdb_levelset.c`, `lvl_platonic_sdf`).

  The C code fills a grid with the signed field

      f(p) = max_i ⟪nᵢ, p − c⟫ − inradius,

  where `nᵢ` are the (unit) outward face normals of the regular solid and
  `inradius = radius·ratio`. This is the level-set analogue of CSG-union as a
  max of half-space fields — it is **not** the exact distance to the
  polytope: it underestimates it everywhere (this module proves that as a
  theorem, `platonicField_abs_le_dist_boundary`, mirroring the CSG
  documentation).

  What is proved (over `Point = EuclideanSpace ℝ (Fin 3)`, the same model as
  `Vdb/LevelSet.lean`):

  * the zero set is exactly the polytope boundary (`platonicField_zero_iff`,
    `platonicField_levelSet`): `f p = 0` iff `p` lies on a face with all
    other faces satisfied;
  * the sign is correct: `f p < 0` iff `p` is strictly inside, `0 ≤ f p` iff
    `p` is in the (closed) polytope, `0 < f p` iff some face is exceeded;
  * `f` is 1-Lipschitz (`platonicField_isSDF`), like the sphere/plane/box
    fields in `LevelSet.lean`;
  * **`platonicField_abs_le_dist_boundary`**: for every boundary point `q`,
    `|f p| ≤ dist p q` — the field is a lower bound on the distance to the
    boundary (underestimate everywhere);
  * membership structure of the face maximum (`faceMax_mem`, `faceMax_le`).

  What is *not* modelled: the platonic generators themselves (face-normal
  tables), the grid sizing around the solid, or the narrow-band clamp of the
  output.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.LevelSet
import Mathlib.Tactic

namespace Vdb

open scoped RealInnerProductSpace

/-! ### The representation -/

/-- A convex polytope centered at `c`, bounded by the half-spaces
    `⟪nᵢ, p − c⟫ ≤ inradius` with unit outward normals. -/
structure PlatonicField where
  center : Point
  normals : List Point
  hn_nonempty : normals ≠ []
  hn_unit : ∀ n ∈ normals, ‖n‖ = 1
  inradius : ℝ
  inradius_pos : 0 < inradius

/-- Inside the (closed) polytope. -/
def inPolytope (P : PlatonicField) (p : Point) : Prop :=
  ∀ n ∈ P.normals, ⟪n, p - P.center⟫ ≤ P.inradius

/-- On the boundary. -/
def polytopeBoundary (P : PlatonicField) (p : Point) : Prop :=
  inPolytope P p ∧ ∃ n ∈ P.normals, ⟪n, p - P.center⟫ = P.inradius

/-- The maximum over the face half-space values. -/
noncomputable def faceMax (P : PlatonicField) (p : Point) : ℝ :=
  (P.normals.map (fun n => ⟪n, p - P.center⟫)).max?.getD 0

/-- The signed distance-like field: `max_i ⟪nᵢ, p − c⟫ − inradius`. -/
noncomputable def platonicField (P : PlatonicField) (p : Point) : ℝ :=
  faceMax P p - P.inradius

/-! ### The face maximum -/

theorem faceMax_mem (P : PlatonicField) (p : Point) :
    faceMax P p ∈ P.normals.map (fun n => ⟪n, p - P.center⟫) := by
  unfold faceMax
  have hne : (P.normals.map fun n => ⟪n, p - P.center⟫) ≠ [] :=
    fun h => P.hn_nonempty (List.map_eq_nil_iff.mp h)
  cases hmax : (P.normals.map fun n => ⟪n, p - P.center⟫).max? with
  | none => exact absurd ((List.max?_eq_none_iff ..).mp hmax) hne
  | some m =>
      have hm : m ∈ (P.normals.map fun n => ⟪n, p - P.center⟫) :=
        (List.max?_eq_some_iff.mp hmax).1
      exact hm

theorem faceMax_le (P : PlatonicField) (p : Point) {n : Point} (hn : n ∈ P.normals) :
    ⟪n, p - P.center⟫ ≤ faceMax P p := by
  unfold faceMax
  have hne : (P.normals.map fun n => ⟪n, p - P.center⟫) ≠ [] :=
    fun h => P.hn_nonempty (List.map_eq_nil_iff.mp h)
  cases hmax : (P.normals.map fun n => ⟪n, p - P.center⟫).max? with
  | none => exact absurd ((List.max?_eq_none_iff ..).mp hmax) hne
  | some m =>
      have hm : ∀ b ∈ (P.normals.map fun n => ⟪n, p - P.center⟫), b ≤ m :=
        (List.max?_eq_some_iff.mp hmax).2
      exact hm _ (List.mem_map_of_mem hn)

/-! ### Zero set and sign -/

/-- The zero set of the field is the polytope boundary. -/
theorem platonicField_zero_iff (P : PlatonicField) (p : Point) :
    platonicField P p = 0 ↔
      (∀ n ∈ P.normals, ⟪n, p - P.center⟫ ≤ P.inradius) ∧
        ∃ n ∈ P.normals, ⟪n, p - P.center⟫ = P.inradius := by
  unfold platonicField
  rw [sub_eq_zero]
  constructor
  · intro h
    constructor
    · intro n hn
      rw [← h]
      exact faceMax_le P p hn
    · obtain ⟨n, hn, hmn⟩ := List.mem_map.mp (faceMax_mem P p)
      exact ⟨n, hn, by rw [hmn, h]⟩
  · rintro ⟨h1, ⟨n, hn, hnq⟩⟩
    have hle : faceMax P p ≤ P.inradius := by
      obtain ⟨n', hn', hmn'⟩ := List.mem_map.mp (faceMax_mem P p)
      rw [← hmn']
      exact h1 n' hn'
    have hge : P.inradius ≤ faceMax P p :=
      calc P.inradius = ⟪n, p - P.center⟫ := hnq.symm
        _ ≤ faceMax P p := faceMax_le P p hn
    exact le_antisymm hle hge

/-- The zero level set is the polytope boundary. -/
theorem platonicField_levelSet (P : PlatonicField) :
    levelSet (platonicField P) 0 = {p | polytopeBoundary P p} := by
  ext p
  change platonicField P p = 0 ↔ _
  rw [platonicField_zero_iff]
  rfl

/-- Strictly negative exactly strictly inside. -/
theorem platonicField_neg_iff (P : PlatonicField) (p : Point) :
    platonicField P p < 0 ↔ ∀ n ∈ P.normals, ⟪n, p - P.center⟫ < P.inradius := by
  unfold platonicField
  constructor
  · intro h n hn
    have h1 := faceMax_le P p hn
    linarith
  · intro h
    obtain ⟨n, hn, hmn⟩ := List.mem_map.mp (faceMax_mem P p)
    have h2 := h n hn
    rw [← hmn]
    linarith

/-- Nonpositive exactly inside (closed polytope). -/
theorem platonicField_nonpos_iff (P : PlatonicField) (p : Point) :
    platonicField P p ≤ 0 ↔ inPolytope P p := by
  unfold platonicField inPolytope
  constructor
  · intro h n hn
    have h1 := faceMax_le P p hn
    linarith
  · intro h
    obtain ⟨n, hn, hmn⟩ := List.mem_map.mp (faceMax_mem P p)
    have h2 := h n hn
    rw [← hmn]
    linarith

/-- Strictly positive exactly outside some face. -/
theorem platonicField_pos_iff (P : PlatonicField) (p : Point) :
    0 < platonicField P p ↔ ∃ n ∈ P.normals, P.inradius < ⟪n, p - P.center⟫ := by
  unfold platonicField
  constructor
  · intro h
    obtain ⟨n, hn, hmn⟩ := List.mem_map.mp (faceMax_mem P p)
    exact ⟨n, hn, by rw [hmn]; linarith⟩
  · rintro ⟨n, hn, h⟩
    calc 0 = P.inradius - P.inradius := (sub_self P.inradius).symm
      _ < ⟪n, p - P.center⟫ - P.inradius := by linarith
      _ ≤ faceMax P p - P.inradius := by linarith [faceMax_le P p hn]

theorem inner_sub_center {n p q c : Point} :
    ⟪n, p - c⟫ - ⟪n, q - c⟫ = ⟪n, p - q⟫ := by
  have hsub : (p - c) - (q - c) = p - q := by abel
  conv_rhs => rw [← hsub, inner_sub_right]

/-! ### 1-Lipschitz -/

/-- The field is 1-Lipschitz — the same magnitude law as the sphere/plane/box
    fields in `LevelSet.lean`. -/
theorem platonicField_isSDF (P : PlatonicField) : IsSDF (platonicField P) := by
  intro p q
  rw [dist_eq_norm, abs_sub_le_iff]
  have hdot : platonicField P p - platonicField P q = faceMax P p - faceMax P q := by
    simp only [platonicField]; ring
  have hdot' : platonicField P q - platonicField P p = faceMax P q - faceMax P p := by
    simp only [platonicField]; ring
  constructor
  · rw [hdot]
    obtain ⟨n, hn, hmn⟩ := List.mem_map.mp (faceMax_mem P p)
    calc faceMax P p - faceMax P q
        = ⟪n, p - P.center⟫ - faceMax P q := by rw [← hmn]
      _ ≤ ⟪n, p - P.center⟫ - ⟪n, q - P.center⟫ :=
          sub_le_sub_left (faceMax_le P q hn) _
      _ = ⟪n, p - q⟫ := inner_sub_center
      _ ≤ ‖n‖ * ‖p - q‖ := real_inner_le_norm _ _
      _ = ‖p - q‖ := by rw [P.hn_unit n hn, one_mul]
  · rw [hdot']
    obtain ⟨n, hn, hmn⟩ := List.mem_map.mp (faceMax_mem P q)
    calc faceMax P q - faceMax P p
        = ⟪n, q - P.center⟫ - faceMax P p := by rw [← hmn]
      _ ≤ ⟪n, q - P.center⟫ - ⟪n, p - P.center⟫ :=
          sub_le_sub_left (faceMax_le P p hn) _
      _ = ⟪n, q - p⟫ := inner_sub_center
      _ ≤ ‖n‖ * ‖q - p‖ := real_inner_le_norm _ _
      _ = ‖q - p‖ := by rw [P.hn_unit n hn, one_mul]
      _ = ‖p - q‖ := by rw [norm_sub_rev]

/-! ### The underestimate -/

/-- **The field underestimates the boundary distance everywhere** (like the
    CSG `min`/`max` fields, it is a lower bound, not the distance): for every
    boundary point `q`, `|f p| ≤ dist p q`. Inside this comes from
    `∂P ⊆ ⋃ face planes`; outside from `P` lying in the half-spaces. -/
theorem platonicField_abs_le_dist_boundary (P : PlatonicField) {p q : Point}
    (hq : polytopeBoundary P q) :
    |platonicField P p| ≤ dist p q := by
  obtain ⟨hqin, n, hn, hnq⟩ := hq
  rw [dist_eq_norm]
  have hnn : ‖n‖ = 1 := P.hn_unit n hn
  by_cases hf : 0 ≤ platonicField P p
  · obtain ⟨n', hn', hmn'⟩ := List.mem_map.mp (faceMax_mem P p)
    have hnq' : ⟪n', q - P.center⟫ ≤ P.inradius := hqin n' hn'
    have hf' : 0 ≤ faceMax P p - P.inradius := hf
    rw [platonicField, abs_of_nonneg hf', ← hmn']
    calc ⟪n', p - P.center⟫ - P.inradius
        ≤ ⟪n', p - P.center⟫ - ⟪n', q - P.center⟫ := by linarith
      _ = ⟪n', p - q⟫ := inner_sub_center
      _ ≤ ‖n'‖ * ‖p - q‖ := real_inner_le_norm _ _
      _ = ‖p - q‖ := by rw [P.hn_unit n' hn', one_mul]
  · have hf2 : platonicField P p < 0 := lt_of_not_ge hf
    have hneg : |platonicField P p| = P.inradius - faceMax P p := by
      rw [abs_of_neg (by linarith : platonicField P p < 0)]
      simp [platonicField]
    rw [hneg]
    calc P.inradius - faceMax P p
        ≤ P.inradius - ⟪n, p - P.center⟫ := sub_le_sub_left (faceMax_le P p hn) _
      _ = ⟪n, q - P.center⟫ - ⟪n, p - P.center⟫ := by rw [hnq]
      _ = ⟪n, q - p⟫ := inner_sub_center
      _ ≤ ‖n‖ * ‖q - p‖ := real_inner_le_norm _ _
      _ = ‖q - p‖ := by rw [hnn, one_mul]
      _ = ‖p - q‖ := by rw [norm_sub_rev]
