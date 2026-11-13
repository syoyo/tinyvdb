/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Planar reconstruction: the composition half of the volume operators. If a
  grid samples a *linear* field (a plane), then

  * marching cubes places every edge crossing exactly on the plane
    (`planeF_crossing`, `planeF_cube_crossings`), and
  * trilinear interpolation of the corner values reproduces the plane at
    every point of the cube (`trilinear_planeF`).

  Both are stated over exact rational geometry (`Q3 = Fin 3 → ℚ`), so the
  claims are genuinely exact rather than tolerance-based. Together they say
  that `level_set_rebuild` on a sampled plane reproduces the plane field.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.DualVertex

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Vdb

/-- The rational inner product on `Q3`. -/
def dot (n x : Q3) : ℚ :=
  ∑ i : Fin 3, n i * x i

theorem dot_lerpQ (n a b : Q3) (t : ℚ) :
    dot n (lerpQ a b t) = (1 - t) * dot n a + t * dot n b := by
  unfold dot
  simp only [lerpQ_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The rational plane field `x ↦ ⟨n, x⟩ - d`. -/
def planeF (n : Q3) (d : ℚ) (x : Q3) : ℚ :=
  dot n x - d

/-- The plane field is affine, so linear edge interpolation is exact. -/
theorem planeF_lerpQ (n : Q3) (d : ℚ) (a b : Q3) (t : ℚ) :
    planeF n d (lerpQ a b t) = (1 - t) * planeF n d a + t * planeF n d b := by
  unfold planeF
  rw [dot_lerpQ]
  ring

/-- **The marching-cubes crossing of a plane is on the plane**: for an edge
    whose endpoints differ in value, the interpolated crossing point has
    exactly zero plane field. -/
theorem planeF_crossing (n : Q3) (d : ℚ) (a b : Q3)
    (h : planeF n d a ≠ planeF n d b) :
    planeF n d (lerpQ a b (edgeParam (planeF n d a) (planeF n d b))) = 0 := by
  rw [planeF_lerpQ]
  have hz := lerp_zero (a := planeF n d a) (b := planeF n d b) h
  unfold lerp at hz
  have he : (1 - edgeParam (planeF n d a) (planeF n d b)) * planeF n d a +
      edgeParam (planeF n d a) (planeF n d b) * planeF n d b =
      planeF n d a + edgeParam (planeF n d a) (planeF n d b) *
        (planeF n d b - planeF n d a) := by
    ring
  rw [he, hz]

/-- On a unit cube at `o`, every crossing of a plane edge is on the plane
    (so the marching-cubes reconstruction of a sampled plane is exact). -/
theorem planeF_cube_crossings (n : Q3) (d : ℚ) (o : Q3) (i j : Fin 8)
    (h : planeF n d (fun k => o k + cornerPos i k) ≠
      planeF n d (fun k => o k + cornerPos j k)) :
    planeF n d (lerpQ (fun k => o k + cornerPos i k) (fun k => o k + cornerPos j k)
      (edgeParam (planeF n d (fun k => o k + cornerPos i k))
        (planeF n d (fun k => o k + cornerPos j k)))) = 0 :=
  planeF_crossing n d _ _ h



/-- The trilinear weight of cube corner `k` at the point `p` in the unit cube. -/
def triWeight (p : Q3) (k : Fin 8) : ℚ :=
  (if k.val % 2 = 1 then p 0 else 1 - p 0) *
  (if (k.val / 2) % 2 = 1 then p 1 else 1 - p 1) *
  (if (k.val / 4) % 2 = 1 then p 2 else 1 - p 2)

theorem triWeight_sum (p : Q3) : (∑ k : Fin 8, triWeight p k) = 1 := by
  rw [Fin.sum_univ_eight]
  simp [triWeight]
  ring

theorem triWeight_moment (p : Q3) (j : Fin 3) :
    (∑ k : Fin 8, triWeight p k * cornerPos k j) = p j := by
  fin_cases j <;>
    (rw [Fin.sum_univ_eight]; simp [triWeight, cornerPos]; ring)

/-- **Trilinear interpolation reproduces a plane exactly**: sampling the
    rational plane field at the cube corners and interpolating gives the
    plane field at every point of the unit cube. -/
theorem trilinear_planeF (n : Q3) (d : ℚ) (p : Q3) :
    (∑ k : Fin 8, triWeight p k * planeF n d (cornerPos k)) = planeF n d p := by
  unfold planeF dot
  have h1 : (∑ k : Fin 8, triWeight p k * (∑ j : Fin 3, n j * cornerPos k j)) =
      ∑ j : Fin 3, n j * p j := by
    calc (∑ k : Fin 8, triWeight p k * (∑ j : Fin 3, n j * cornerPos k j))
        = ∑ k : Fin 8, ∑ j : Fin 3, triWeight p k * (n j * cornerPos k j) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
      _ = ∑ j : Fin 3, ∑ k : Fin 8, triWeight p k * (n j * cornerPos k j) :=
          Finset.sum_comm
      _ = ∑ j : Fin 3, n j * (∑ k : Fin 8, triWeight p k * cornerPos k j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ = ∑ j : Fin 3, n j * p j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [triWeight_moment]
  have h2 : (∑ k : Fin 8, triWeight p k * d) = d := by
    rw [← Finset.sum_mul, triWeight_sum, one_mul]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [h1, h2]


/-! ### Planar level-set rebuild -/

theorem dot_add (n a b : Q3) : dot n (fun j => a j + b j) = dot n a + dot n b := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Shifting the cube origin only shifts the plane's offset. -/
theorem planeF_offset (n : Q3) (d : ℚ) (o c : Q3) :
    planeF n d (fun j => o j + c j) = planeF n (d - dot n o) c := by
  unfold planeF
  rw [dot_add]
  ring

/-- **Trilinear reconstruction of a plane is exact in any cube.** -/
theorem trilinear_planeF_offset (n : Q3) (d : ℚ) (o p : Q3) :
    (∑ k : Fin 8, triWeight p k * planeF n d (fun j => o j + cornerPos k j)) =
      planeF n d (fun j => o j + p j) := by
  simp only [planeF_offset]
  exact trilinear_planeF n (d - dot n o) p

/-- **Planar `level_set_rebuild`**: for a grid sampling a linear field, both
    halves of the operator composition are exact — every marching-cubes
    crossing lands on the plane, and trilinear resampling reproduces the
    plane field everywhere in the cube. -/
theorem plane_level_set_rebuild (n : Q3) (d : ℚ) (o : Q3) (i j : Fin 8)
    (h : planeF n d (fun k => o k + cornerPos i k) ≠
      planeF n d (fun k => o k + cornerPos j k)) :
    planeF n d (lerpQ (fun k => o k + cornerPos i k) (fun k => o k + cornerPos j k)
        (edgeParam (planeF n d (fun k => o k + cornerPos i k))
          (planeF n d (fun k => o k + cornerPos j k)))) = 0 ∧
      (∀ p : Q3, (∑ k : Fin 8, triWeight p k *
        planeF n d (fun j' => o j' + cornerPos k j')) =
          planeF n d (fun j' => o j' + p j')) :=
  ⟨planeF_cube_crossings n d o i j h, fun p => trilinear_planeF_offset n d o p⟩


/-! ### The dual vertex of a sampled plane -/

theorem fin3_sum_list_sum (l : List Q3) (g : Fin 3 → Q3 → ℚ) :
    (∑ i : Fin 3, (l.map (fun p => g i p)).sum) =
      (l.map (fun p => ∑ i : Fin 3, g i p)).sum := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- The inner product commutes with the average. -/
theorem dot_avgQ (n : Q3) (l : List Q3) :
    dot n (avgQ l) =
      ((l.map (fun p => dot n p)).sum) / (l.length : ℚ) := by
  unfold dot avgQ
  have h1 : ∀ i : Fin 3, n i * ((l.map (fun p => p i)).sum / (l.length : ℚ)) =
      (n i * (l.map (fun p => p i)).sum) / (l.length : ℚ) := fun i => by ring
  simp only [h1]
  rw [← Finset.sum_div]
  congr 1
  calc (∑ i : Fin 3, n i * (l.map (fun p => p i)).sum)
      = ∑ i : Fin 3, (l.map (fun p => n i * p i)).sum := by
        apply Finset.sum_congr rfl
        intro i _
        rw [List.sum_map_mul_left]
    _ = (l.map (fun p => ∑ i : Fin 3, n i * p i)).sum :=
        fin3_sum_list_sum l (fun i p => n i * p i)

/-- A nonempty list of zeros averages to zero. -/
theorem planeF_avgQ {n : Q3} {d : ℚ} {l : List Q3} (hne : l ≠ [])
    (h : ∀ p ∈ l, planeF n d p = 0) : planeF n d (avgQ l) = 0 := by
  unfold planeF at *
  rw [dot_avgQ]
  have hlen : (0 : ℚ) < l.length := by
    have hpos : 0 < l.length := by
      cases l with
      | nil => exact absurd rfl hne
      | cons p ps => simp
    exact_mod_cast hpos
  have hconst : ∀ (m : List Q3), (m.map (fun _ => d)).sum = (m.length : ℚ) * d := by
    intro m
    induction m with
    | nil => simp
    | cons p ps ih => simp [ih]; ring
  have hsum : (l.map (fun p => dot n p)).sum = (l.length : ℚ) * d := by
    have hmap : l.map (fun p => dot n p) = l.map (fun _ => d) := by
      apply List.map_congr_left
      intro p hp
      have := h p hp
      linarith
    rw [hmap, hconst]
  rw [hsum]
  field_simp
  ring

/-- **The DMC dual vertex of a sampled plane lies on the plane**: a crossing on
    a plane edge is on the plane, and the plane field is affine, so their
    average is too. -/
theorem planeF_dualVertex {n : Q3} {d : ℚ} {o : Q3} {edges : List (Fin 8 × Fin 8)}
    (hne : edges ≠ [])
    (h : ∀ e ∈ edges, planeF n d (fun k => o k + cornerPos e.1 k) ≠
      planeF n d (fun k => o k + cornerPos e.2 k)) :
    planeF n d (avgQ (edges.map (fun e =>
      lerpQ (fun k => o k + cornerPos e.1 k) (fun k => o k + cornerPos e.2 k)
        (edgeParam (planeF n d (fun k => o k + cornerPos e.1 k))
          (planeF n d (fun k => o k + cornerPos e.2 k)))))) = 0 := by
  apply planeF_avgQ
  · obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil edges hne
    exact List.ne_nil_of_mem (List.mem_map.mpr ⟨e, he, rfl⟩)
  · intro p hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    exact planeF_cube_crossings n d o e.1 e.2 (h e he)

end Vdb
