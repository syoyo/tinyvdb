/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Integer-valuedness / topological degree of the generalized winding number.

  `Vdb/WindingNumber.lean` models the C solid-angle sum and proves its
  symmetries. This module takes the next step toward the A-section degree
  claim ("for p off a closed oriented mesh, meshWinding fs p ∈ ℤ, equal to 1
  inside a closed sphere-like mesh and 0 outside"). Full degree theory — the
  Gauss-map/holonomy argument that the oriented solid angles sum to 4π·deg —
  is not attempted here. What is landed instead:

    * unconditional structural facts (cancellation of a soup with its reverse
      gives winding number 0; continuity of the winding number on the *regular*
      set where every face's numerator and denominator are nonzero);
    * a rigorous **degree-reduction theorem**: if degree theory supplies the
      crossing-jump identity and the vanishing-at-infinity value, then
      `meshWinding fs p` is an integer (the signed crossing count), is 0 at the
      far endpoint, and is constant on preconnected pieces of the complement
      (by continuity + discreteness of ℤ ⊂ ℝ);
    * the concrete inside/outside specialisations (`= 1` for one oriented
      crossing, `= 0` for none).

  The jump identity / vanishing value are *explicit named hypotheses*, not
  axioms added to the imports: the theorem states exactly what remains to be
  proved for a full unconditional degree theorem and what follows from it.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.WindingNumber
import Vdb.WindingFarField
import Mathlib.Tactic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.LocallyConstant.Basic

namespace Vdb

open scoped Matrix
open Filter Topology
open Vdb.V3

noncomputable section

/-! ### A topology on `V3` (pulled back from its three coordinates) -/

/-- The product topology on the vector type, so the winding number can be
    viewed as a function of the query point. -/
instance : TopologicalSpace V3 :=
  TopologicalSpace.induced (fun v : V3 => (v.x, v.y, v.z)) inferInstance

/-- The coordinate tuple is continuous by construction of the topology. -/
theorem continuous_v3Tuple : Continuous (fun v : V3 => (v.x, v.y, v.z)) :=
  continuous_induced_dom

/-- The three coordinate projections are continuous. -/
theorem continuous_v3_x : Continuous (fun v : V3 => v.x) :=
  continuous_fst.comp continuous_v3Tuple

theorem continuous_v3_y : Continuous (fun v : V3 => v.y) :=
  continuous_fst.comp (continuous_snd.comp continuous_v3Tuple)

theorem continuous_v3_z : Continuous (fun v : V3 => v.z) :=
  continuous_snd.comp (continuous_snd.comp continuous_v3Tuple)

attribute [fun_prop] continuous_v3_x continuous_v3_y continuous_v3_z

/-! ### Faces, numerator, denominator -/

/-- An oriented triangle of the soup (the representation used by `meshWinding`). -/
abbrev Face := V3 × V3 × V3

/-- Reverse the orientation of a face. -/
def flipFace (f : Face) : Face := (f.1, f.2.2, f.2.1)

/-- The oriented numerator of the solid angle of `f` at `p`. -/
def faceNum (f : Face) (p : V3) : ℝ :=
  triple (sub f.1 p) (sub f.2.1 p) (sub f.2.2 p)

/-- The denominator of the solid angle of `f` at `p`
    (the Van Oosterom–Strackee `den`). -/
def faceDen (f : Face) (p : V3) : ℝ :=
  Real.sqrt (dot (sub f.1 p) (sub f.1 p)) *
    Real.sqrt (dot (sub f.2.1 p) (sub f.2.1 p)) *
      Real.sqrt (dot (sub f.2.2 p) (sub f.2.2 p))
  + dot (sub f.1 p) (sub f.2.1 p) *
      Real.sqrt (dot (sub f.2.2 p) (sub f.2.2 p))
  + dot (sub f.2.1 p) (sub f.2.2 p) *
      Real.sqrt (dot (sub f.1 p) (sub f.1 p))
  + dot (sub f.2.2 p) (sub f.1 p) *
      Real.sqrt (dot (sub f.2.1 p) (sub f.2.1 p))

/-- Unfolding `solidAngle` in terms of the numerator/denominator. -/
theorem solidAngle_eq_face (f : Face) (p : V3) :
    solidAngle f.1 f.2.1 f.2.2 p = 2 * atan2' (faceNum f p) (faceDen f p) := rfl

/-! ### Unconditional cancellation facts -/

/-- A soup together with its reverse has winding number 0. This is an
    unconditional integer-valuedness fact for the largest trivial family of
    "closed" soups (degree 0). -/
theorem meshWinding_face_cancel (fs : List Face) (p : V3)
    (h : ∀ f ∈ fs, faceNum f p ≠ 0) :
    meshWinding (fs ++ fs.map flipFace) p = 0 := by
  have hw : meshWinding (fs.map flipFace) p = - meshWinding fs p := by
    change meshWinding (fs.map (fun f => (f.1, f.2.2, f.2.1))) p = - meshWinding fs p
    exact meshWinding_reverse fs p h
  rw [meshWinding_append, hw]
  ring

/-- The empty soup has winding number 0. -/
theorem meshWinding_empty (p : V3) : meshWinding ([] : List Face) p = 0 := by
  simp [meshWinding]

/-! ### Continuity on the regular set -/

set_option maxHeartbeats 800000 in
/-- `atan2'` is continuous wherever its numerator and denominator are both
    nonzero. (The only discontinuity of the model is the branch cut at
    numerator = 0, denominator < 0, which is exactly the approach to a face.
    Avoiding numerator = 0 and denominator = 0 keeps us in the regime where
    `atan2'` is an ordinary `arctan` branch.) -/
theorem atan2'_continuousAt_of_ne (y x : ℝ) (hy : y ≠ 0) (hx : x ≠ 0) :
    ContinuousAt (fun z : ℝ × ℝ => atan2' z.1 z.2) (y, x) := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · rcases lt_or_gt_of_ne hy with hyneg | hypos
    · -- x < 0, y < 0:  atan2' = arctan(y/x) - π
      have hz2 : ∀ᶠ z in nhds (y, x), z.2 < 0 :=
        continuousAt_snd.eventually (Iio_mem_nhds hxneg)
      have hz1 : ∀ᶠ z in nhds (y, x), z.1 < 0 :=
        continuousAt_fst.eventually (Iio_mem_nhds hyneg)
      have heq : (fun z : ℝ × ℝ => atan2' z.1 z.2) =ᶠ[nhds (y, x)]
          (fun z => Real.arctan (z.1 / z.2) - Real.pi) := by
        filter_upwards [hz2, hz1] with z hz2 hz1
        have hp : ¬ z.2 > 0 := by linarith
        have hz : ¬ z.2 = 0 := by linarith
        have hn : ¬ 0 ≤ z.1 := by linarith
        simp [atan2', hp, hz, hn]
      have hrhs : ContinuousAt (fun z : ℝ × ℝ => Real.arctan (z.1 / z.2) - Real.pi) (y, x) :=
        (Real.continuousAt_arctan.comp (continuousAt_fst.div continuousAt_snd hx)).sub continuousAt_const
      exact hrhs.congr heq.symm
    · -- x < 0, y > 0:  atan2' = arctan(y/x) + π
      have hz2 : ∀ᶠ z in nhds (y, x), z.2 < 0 :=
        continuousAt_snd.eventually (Iio_mem_nhds hxneg)
      have hz1 : ∀ᶠ z in nhds (y, x), 0 < z.1 :=
        continuousAt_fst.eventually (eventually_gt_nhds hypos)
      have heq : (fun z : ℝ × ℝ => atan2' z.1 z.2) =ᶠ[nhds (y, x)]
          (fun z => Real.arctan (z.1 / z.2) + Real.pi) := by
        filter_upwards [hz2, hz1] with z hz2 hz1
        have hp : ¬ z.2 > 0 := by linarith
        have hz : ¬ z.2 = 0 := by linarith
        have hn : 0 ≤ z.1 := le_of_lt hz1
        simp [atan2', hp, hz, hn]
      have hrhs : ContinuousAt (fun z : ℝ × ℝ => Real.arctan (z.1 / z.2) + Real.pi) (y, x) :=
        (Real.continuousAt_arctan.comp (continuousAt_fst.div continuousAt_snd hx)).add continuousAt_const
      exact hrhs.congr heq.symm
  · -- x > 0:  atan2' = arctan(y/x)
    have hz2 : ∀ᶠ z in nhds (y, x), 0 < z.2 :=
      continuousAt_snd.eventually (eventually_gt_nhds hxpos)
    have heq : (fun z : ℝ × ℝ => atan2' z.1 z.2) =ᶠ[nhds (y, x)]
        (fun z => Real.arctan (z.1 / z.2)) := by
      filter_upwards [hz2] with z hz2
      simp [atan2', hz2]
    have hrhs : ContinuousAt (fun z : ℝ × ℝ => Real.arctan (z.1 / z.2)) (y, x) :=
      Real.continuousAt_arctan.comp (continuousAt_fst.div continuousAt_snd hx)
    exact hrhs.congr heq.symm

set_option maxHeartbeats 800000 in
private theorem continuousAt_faceNum (f : Face) (p : V3) :
    ContinuousAt (fun q => faceNum f q) p := by
  have hcols : Continuous (fun q => cols (sub f.1 q) (sub f.2.1 q) (sub f.2.2 q)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j <;> simp [cols, sub] <;> fun_prop
  simpa [faceNum, triple] using hcols.matrix_det.continuousAt

set_option maxHeartbeats 800000 in
private theorem continuousAt_faceDen (f : Face) (p : V3) :
    ContinuousAt (fun q => faceDen f q) p := by
  simp only [faceDen, sub, dot]
  fun_prop

set_option maxHeartbeats 800000 in
/-- A single face's solid angle is continuous at `p` away from the branch cut. -/
theorem continuousAt_solidAngle_of_generic (f : Face) (p : V3)
    (hnum : faceNum f p ≠ 0) (hden : faceDen f p ≠ 0) :
    ContinuousAt (fun q => solidAngle f.1 f.2.1 f.2.2 q) p := by
  rw [show (fun q => solidAngle f.1 f.2.1 f.2.2 q) =
      (fun q => 2 * atan2' (faceNum f q) (faceDen f q)) by
        funext q
        exact solidAngle_eq_face f q]
  have hpair : ContinuousAt (fun q => (faceNum f q, faceDen f q)) p :=
    (continuousAt_faceNum f p).prodMk (continuousAt_faceDen f p)
  have hatan : ContinuousAt (fun q => atan2' (faceNum f q) (faceDen f q)) p := by
    change ContinuousAt ((fun z : ℝ × ℝ => atan2' z.1 z.2) ∘
      (fun q : V3 => (faceNum f q, faceDen f q))) p
    exact (atan2'_continuousAt_of_ne (faceNum f p) (faceDen f p) hnum hden).comp (x := p) hpair
  exact continuousAt_const.mul hatan

set_option maxHeartbeats 800000 in
/-- The whole winding number is continuous at `p` when no face is in the
    branch-cut regime. -/
theorem continuousAt_meshWinding_of_generic (fs : List Face) (p : V3)
    (h : ∀ f ∈ fs, faceNum f p ≠ 0 ∧ faceDen f p ≠ 0) :
    ContinuousAt (meshWinding fs) p := by
  have hsum : ContinuousAt (fun q => (fs.map fun f => solidAngle f.1 f.2.1 f.2.2 q).sum) p := by
    induction fs with
    | nil =>
        simpa using (continuousAt_const : ContinuousAt (fun _ : V3 => (0 : ℝ)) p)
    | cons f fs ih =>
        simp only [List.map_cons, List.sum_cons]
        exact (continuousAt_solidAngle_of_generic f p (h f (by simp)).1 (h f (by simp)).2).add
          (ih (by intro g hg; exact h g (by simp [hg])))
  change ContinuousAt (fun q => (fs.map fun f => solidAngle f.1 f.2.1 f.2.2 q).sum / (4 * Real.pi)) p
  exact hsum.div_const (4 * Real.pi)

/-! ### Degree reduction -/

/-- Points off every face and off the branch cut of each face. This is the
    open set on which the winding number is continuous (by
    `continuousAt_meshWinding_of_generic`). -/
def regularSet (fs : List Face) : Set V3 :=
  {p | ∀ f ∈ fs, faceNum f p ≠ 0 ∧ faceDen f p ≠ 0}

/-- **Integer-valuedness from crossing data (conditional degree theorem).**
    Let `jumps` be the ordered list of oriented crossing signs supplied by a
    generic ray from `p` to a far point `q` (each entry is `+1` or `-1`). If the
    winding-number change along that ray is the integer sum of the jumps
    (the solid-angle-jump axiom of degree theory) and the far endpoint has
    winding number `0` (vanishing at infinity), then the winding number at `p`
    is an integer, namely that signed crossing number. -/
theorem winding_eq_degree (fs : List Face) (p q : V3) (jumps : List ℤ)
    (hstep : meshWinding fs p - meshWinding fs q = (jumps.sum : ℝ))
    (hfar : meshWinding fs q = 0) :
    ∃ d : ℤ, meshWinding fs p = (d : ℝ) ∧ d = jumps.sum := by
  refine ⟨jumps.sum, ?_, rfl⟩
  simpa [hfar] using hstep

/-- 1 inside a closed sphere-like mesh: a single oriented crossing from the
    inside point to a far outside point. -/
theorem winding_eq_one_of_single_crossing (fs : List Face) (p q : V3)
    (hstep : meshWinding fs p - meshWinding fs q = (1 : ℝ))
    (hfar : meshWinding fs q = 0) :
    meshWinding fs p = 1 := by
  linarith

/-- 0 outside a closed mesh: no oriented crossings on a ray to infinity. -/
theorem winding_eq_zero_of_no_crossing (fs : List Face) (p q : V3)
    (hstep : meshWinding fs p - meshWinding fs q = (0 : ℝ))
    (hfar : meshWinding fs q = 0) :
    meshWinding fs p = 0 := by
  linarith

/-! ### Constancy on connected components of the complement -/

/-- ℤ embeds as a discrete subset of ℝ (so a continuous ℝ-valued function
    whose values all lie in `ℤ` is constant on a preconnected set). -/
private theorem intRange_discrete : IsDiscrete (Set.range fun d : ℤ => (d : ℝ)) :=
  Int.isClosedEmbedding_coe_real.isInducing.isDiscrete_range

/-- A continuous function into ℝ that only takes integer values is constant on
    every preconnected set. Applied to `meshWinding fs`, this gives constancy
    on each connected component of the complement once integer-valuedness is
    known there. -/
theorem meshWinding_const_of_integer_on_preconnected
    (fs : List Face) (s : Set V3) (hs : IsPreconnected s)
    (hcont : ContinuousOn (meshWinding fs) s)
    (hint : ∀ x ∈ s, ∃ d : ℤ, meshWinding fs x = (d : ℝ))
    {x y : V3} (hx : x ∈ s) (hy : y ∈ s) :
    meshWinding fs x = meshWinding fs y := by
  exact IsPreconnected.constant_of_mapsTo hs intRange_discrete hcont (by
    intro z hz
    rcases hint z hz with ⟨d, hd⟩
    exact ⟨d, hd.symm⟩) hx hy

/-- The same conclusion from local constancy (the topological input packaged
    directly), without needing integer-valuedness as a separate premise. -/
theorem meshWinding_const_of_locallyConstant (fs : List Face)
    (hloc : IsLocallyConstant (fun p : V3 => meshWinding fs p))
    (s : Set V3) (hs : IsPreconnected s) {x y : V3} (hx : x ∈ s) (hy : y ∈ s) :
    meshWinding fs x = meshWinding fs y :=
  hloc.apply_eq_of_isPreconnected hs hx hy

/-- **Headline reduction.** For a regular preconnected piece `s` of the
    complement: if the crossing data makes the winding number an integer at
    every point of `s`, then the winding number is constant on `s`, and the
    value at `p` is the signed crossing count computed from the ray to the far
    point `q`. This is the rigorous bridge from the solid-angle jump axiom to
    "1 inside / 0 outside, constant on components". -/
theorem closed_mesh_winding_degree
    (fs : List Face) (p q : V3) (jumps : List ℤ)
    (hstep : meshWinding fs p - meshWinding fs q = (jumps.sum : ℝ))
    (hfar : meshWinding fs q = 0)
    (s : Set V3) (hs : IsPreconnected s) (hsub : s ⊆ regularSet fs)
    (hint : ∀ x ∈ s, ∃ d : ℤ, meshWinding fs x = (d : ℝ)) :
    meshWinding fs p = (jumps.sum : ℝ) ∧
      (∀ {x y : V3}, x ∈ s → y ∈ s → meshWinding fs x = meshWinding fs y) := by
  have hcont : ContinuousOn (meshWinding fs) s := by
    intro z hz
    exact (continuousAt_meshWinding_of_generic fs z (hsub hz)).continuousWithinAt
  refine ⟨?_, ?_⟩
  · simpa [hfar] using hstep
  · intro x y hx hy
    exact meshWinding_const_of_integer_on_preconnected fs s hs hcont hint hx hy

/-! ### Vanishing at infinity (radial escape; the two named hypotheses, part 1)

The unconditional far-field lemmas in `Vdb.WindingFarField` already show that,
along any escaping ray `p = t • d` with `d ≠ 0`, the Van Oosterom numerator
over denominator tends to `0` and the denominator is eventually positive.
Combining them with continuity of `arctan` gives the vanishing of each face's
solid angle, hence of the whole (finite) soup, in the limit `t → ∞`.

This is the limit form of "vanishing at infinity" (the winding number is not
*eventually exactly* `0`; it decays like `‖p‖⁻²`). The subclass proved here is
the **radial** one: escape to infinity along a fixed ray. Uniformity over all
directions (the full norm filter on `V3`) is not claimed. -/

set_option maxHeartbeats 800000 in
/-- The solid angle of a fixed face tends to `0` along any escaping ray. -/
theorem solidAngle_ray_tendsto_zero (A B C d : V3) (hd : 0 < dot d d) :
    Tendsto (fun t : ℝ => solidAngle A B C (ray t d)) atTop (𝓝 0) := by
  have hnum : Tendsto (fun t : ℝ => numOf A B C d t / denOf A B C d t) atTop (𝓝 0) :=
    numOf_div_denOf_tendsto_zero A B C d hd
  have hden : ∀ᶠ t : ℝ in atTop, 0 < denOf A B C d t :=
    denOf_pos_eventually A B C d hd
  have harctan : Tendsto
      (fun t : ℝ => Real.arctan (numOf A B C d t / denOf A B C d t)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuousAt_arctan.tendsto.comp hnum)
  have htwo : Tendsto
      (fun t : ℝ => 2 * Real.arctan (numOf A B C d t / denOf A B C d t)) atTop (𝓝 0) := by
    simpa using harctan.const_mul (2 : ℝ)
  refine htwo.congr' ?_
  filter_upwards [hden] with t ht
  rw [solidAngle_eq_arctan_of_pos A B C d t ht]
  rfl

set_option maxHeartbeats 800000 in
/-- A finite triangle soup has winding number tending to `0` along any
    escaping ray (the far-endpoint value `hfar` used by the degree-reduction
    theorems). -/
theorem meshWinding_ray_tendsto_zero (fs : List Face) (d : V3) (hd : 0 < dot d d) :
    Tendsto (fun t : ℝ => meshWinding fs (ray t d)) atTop (𝓝 0) := by
  have hsum : Tendsto (fun t : ℝ =>
      (fs.map fun f => solidAngle f.1 f.2.1 f.2.2 (ray t d)).sum) atTop (𝓝 0) := by
    induction fs with
    | nil => simp
    | cons f fs ih =>
        simp only [List.map_cons, List.sum_cons]
        simpa using (solidAngle_ray_tendsto_zero f.1 f.2.1 f.2.2 d hd).add ih
  have h := hsum.div_const (4 * Real.pi)
  simpa [meshWinding] using h

/-! ### Solid-angle jump across a face (the named hypotheses, part 2)

We prove the jump in the **canonical** subclass: the triangle with vertices
`(0,0,0)`, `(1,0,0)`, `(0,1,0)` and the vertical crossing at its centroid
projection `(1/3, 1/3, 0)`. A general closed mesh reduces to this picture by
the already-proved rotation and translation invariance of `solidAngle`, plus
continuity of every *other* face at the crossing point
(`continuousAt_solidAngle_of_generic`); that global reduction is not attempted
here.

Two one-sided atan2 limits are the engine. Near a point inside the circumcircle
the Van Oosterom denominator is negative, and the numerator changes sign across
the face; `atan2'` therefore jumps between `+π` and `-π`, i.e. `solidAngle`
jumps by `4π` and `meshWinding` by `1`. -/

/-- The canonical oriented triangle. -/
def jumpA : V3 := ⟨0, 0, 0⟩
def jumpB : V3 := ⟨1, 0, 0⟩
def jumpC : V3 := ⟨0, 1, 0⟩
def jumpFace : Face := (jumpA, jumpB, jumpC)

/-- The vertical line through the centroid projection of `jumpFace`. -/
def jumpPoint (t : ℝ) : V3 := ⟨1 / 3, 1 / 3, t⟩

set_option maxHeartbeats 800000 in
/-- The numerator of the canonical face at `jumpPoint t` is exactly `-t`
    (linear in the height, with slope `-2 · area = -1`). -/
lemma jumpFace_num (t : ℝ) : faceNum jumpFace (jumpPoint t) = -t := by
  rw [faceNum, triple, Matrix.det_fin_three]
  simp [jumpFace, jumpA, jumpB, jumpC, jumpPoint, sub]
  ring

set_option maxHeartbeats 800000 in
/-- At the centroid projection the canonical face's denominator is strictly
    negative (the query point lies inside the triangle, hence in its
    circumcircle). This fixes the `atan2'` branch used below. -/
lemma jumpFace_den_neg : faceDen jumpFace (jumpPoint 0) < 0 := by
  have hs2sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs5sq : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs2nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs5nn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hs25 : Real.sqrt 2 < 2 * Real.sqrt 5 := by
    have hsq : (Real.sqrt 2) ^ 2 < (2 * Real.sqrt 5) ^ 2 := by
      rw [hs2sq]
      nlinarith [hs5sq]
    have habs : |Real.sqrt 2| < |2 * Real.sqrt 5| := sq_lt_sq.mp hsq
    rwa [abs_of_nonneg hs2nn, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt 5)] at habs
  simp [faceDen, jumpFace, jumpA, jumpB, jumpC, jumpPoint, sub, dot]
  norm_num
  set x := Real.sqrt 2
  set y := Real.sqrt 5
  have hxx : x * x = 2 := by
    rw [show x = Real.sqrt 2 by rfl, ← pow_two]
    exact Real.sq_sqrt (by norm_num)
  have hyy : y * y = 5 := by
    rw [show y = Real.sqrt 5 by rfl, ← pow_two]
    exact Real.sq_sqrt (by norm_num)
  have hxyy : x * y * y = 5 * x := by
    rw [mul_assoc, hyy]
    ring
  have hxy : x < 2 * y := by simpa [x, y] using hs25
  nlinarith

set_option maxHeartbeats 800000 in
/-- The path `t ↦ jumpPoint t` is continuous (the topology on `V3` is induced
    by its three coordinates). -/
lemma jumpPoint_continuous : Continuous (fun t : ℝ => jumpPoint t) := by
  rw [continuous_induced_rng]
  change Continuous (fun t : ℝ => ((1 / 3 : ℝ), (1 / 3 : ℝ), t))
  exact Continuous.prodMk continuous_const (Continuous.prodMk continuous_const continuous_id)

/-- `atan2'` tends to `-π` when `y → 0` from below and `x → c < 0`. -/
private lemma atan2'_tendsto_negPi_of {α : Type*} {l : Filter α} {y x : α → ℝ} {c : ℝ}
    (hy0 : Tendsto y l (𝓝 0)) (hx0 : Tendsto x l (𝓝 c)) (hc : c < 0)
    (hyneg : ∀ᶠ t in l, y t < 0) :
    Tendsto (fun t => atan2' (y t) (x t)) l (𝓝 (-Real.pi)) := by
  have hxneg : ∀ᶠ t in l, x t < 0 := hx0.eventually (Iio_mem_nhds hc)
  have heq : (fun t => atan2' (y t) (x t)) =ᶠ[l]
      (fun t => Real.arctan (y t / x t) - Real.pi) := by
    filter_upwards [hxneg, hyneg] with t hxt hyt
    have hp : ¬ x t > 0 := by linarith
    have hz : ¬ x t = 0 := by linarith
    have hn : ¬ 0 ≤ y t := by linarith
    simp [atan2', hp, hz, hn]
  have hratio : Tendsto (fun t => y t / x t) l (𝓝 0) := by
    change Tendsto (y / x) l (𝓝 0)
    simpa using hy0.div hx0 (ne_of_lt hc)
  have harctan : Tendsto (fun t => Real.arctan (y t / x t)) l (𝓝 0) := by
    simpa [Function.comp_def] using Real.continuousAt_arctan.tendsto.comp hratio
  have hsub : Tendsto (fun t => Real.arctan (y t / x t) - Real.pi) l (𝓝 (-Real.pi)) := by
    simpa using harctan.sub tendsto_const_nhds
  exact hsub.congr' heq.symm

/-- `atan2'` tends to `+π` when `y → 0` from above and `x → c < 0`. -/
private lemma atan2'_tendsto_posPi_of {α : Type*} {l : Filter α} {y x : α → ℝ} {c : ℝ}
    (hy0 : Tendsto y l (𝓝 0)) (hx0 : Tendsto x l (𝓝 c)) (hc : c < 0)
    (hypos : ∀ᶠ t in l, 0 < y t) :
    Tendsto (fun t => atan2' (y t) (x t)) l (𝓝 Real.pi) := by
  have hxneg : ∀ᶠ t in l, x t < 0 := hx0.eventually (Iio_mem_nhds hc)
  have heq : (fun t => atan2' (y t) (x t)) =ᶠ[l]
      (fun t => Real.arctan (y t / x t) + Real.pi) := by
    filter_upwards [hxneg, hypos] with t hxt hyt
    have hp : ¬ x t > 0 := by linarith
    have hz : ¬ x t = 0 := by linarith
    have hn : 0 ≤ y t := le_of_lt hyt
    simp [atan2', hp, hz, hn]
  have hratio : Tendsto (fun t => y t / x t) l (𝓝 0) := by
    change Tendsto (y / x) l (𝓝 0)
    simpa using hy0.div hx0 (ne_of_lt hc)
  have harctan : Tendsto (fun t => Real.arctan (y t / x t)) l (𝓝 0) := by
    simpa [Function.comp_def] using Real.continuousAt_arctan.tendsto.comp hratio
  have hadd : Tendsto (fun t => Real.arctan (y t / x t) + Real.pi) l (𝓝 Real.pi) := by
    simpa using harctan.add tendsto_const_nhds
  exact hadd.congr' heq.symm

set_option maxHeartbeats 800000 in
/-- **Solid-angle jump at a canonical face crossing.** For `ε → 0⁺`, the point
    above the face (`jumpPoint ε`) has solid angle tending to `-2π`, while the
    point below (`jumpPoint (-ε)`) has solid angle tending to `+2π`. -/
theorem canonical_crossing_solidAngle_jump :
    Tendsto (fun ε : ℝ =>
        solidAngle jumpA jumpB jumpC (jumpPoint ε) -
          solidAngle jumpA jumpB jumpC (jumpPoint (-ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-4 * Real.pi)) := by
  have hden0 : faceDen jumpFace (jumpPoint 0) < 0 := jumpFace_den_neg
  have hdn_path : ContinuousAt (fun ε : ℝ => jumpPoint (-ε)) 0 :=
    (jumpPoint_continuous.comp continuous_neg).continuousAt
  have hden_cont_up : ContinuousAt (fun ε : ℝ => faceDen jumpFace (jumpPoint ε)) 0 :=
    (continuousAt_faceDen jumpFace (jumpPoint 0)).comp jumpPoint_continuous.continuousAt
  have hden_cont_dn : ContinuousAt (fun ε : ℝ => faceDen jumpFace (jumpPoint (-ε))) 0 :=
    (continuousAt_faceDen jumpFace (jumpPoint 0)).comp_of_eq hdn_path (by simp)
  have hden_tend_up : Tendsto (fun ε : ℝ => faceDen jumpFace (jumpPoint ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (faceDen jumpFace (jumpPoint 0))) :=
    hden_cont_up.tendsto.mono_left nhdsWithin_le_nhds
  have hden_tend_dn : Tendsto (fun ε : ℝ => faceDen jumpFace (jumpPoint (-ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (faceDen jumpFace (jumpPoint 0))) := by
    simpa using hden_cont_dn.tendsto.mono_left nhdsWithin_le_nhds
  have hnum_up : Tendsto (fun ε : ℝ => faceNum jumpFace (jumpPoint ε))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [jumpFace_num] using
      ((tendsto_id.mono_left nhdsWithin_le_nhds).neg :
        Tendsto (fun ε : ℝ => -ε) (𝓝[>] (0 : ℝ)) (𝓝 (-0)))
  have hnum_dn : Tendsto (fun ε : ℝ => faceNum jumpFace (jumpPoint (-ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [jumpFace_num] using
      (show Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) from
        tendsto_id.mono_left nhdsWithin_le_nhds)
  have hnum_up_neg : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), faceNum jumpFace (jumpPoint ε) < 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [jumpFace_num]
    exact neg_neg_of_pos hε
  have hnum_dn_pos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < faceNum jumpFace (jumpPoint (-ε)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [jumpFace_num]
    simpa using hε
  have hatan_up : Tendsto (fun ε : ℝ =>
      atan2' (faceNum jumpFace (jumpPoint ε)) (faceDen jumpFace (jumpPoint ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-Real.pi)) :=
    atan2'_tendsto_negPi_of hnum_up hden_tend_up hden0 hnum_up_neg
  have hatan_dn : Tendsto (fun ε : ℝ =>
      atan2' (faceNum jumpFace (jumpPoint (-ε))) (faceDen jumpFace (jumpPoint (-ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 Real.pi) :=
    atan2'_tendsto_posPi_of hnum_dn hden_tend_dn hden0 hnum_dn_pos
  have hsolid_up : Tendsto (fun ε : ℝ => solidAngle jumpA jumpB jumpC (jumpPoint ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * (-Real.pi))) := by
    have h2 := hatan_up.const_mul (2 : ℝ)
    refine h2.congr' ?_
    filter_upwards [] with ε
    rfl
  have hsolid_dn : Tendsto (fun ε : ℝ => solidAngle jumpA jumpB jumpC (jumpPoint (-ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * Real.pi)) := by
    have h2 := hatan_dn.const_mul (2 : ℝ)
    refine h2.congr' ?_
    filter_upwards [] with ε
    rfl
  have hdiff := hsolid_up.sub hsolid_dn
  have hconst : -(2 * Real.pi) - 2 * Real.pi = -4 * Real.pi := by ring
  simpa [hconst] using hdiff

set_option maxHeartbeats 800000 in
/-- **Winding jump across a crossing face = ±1** in the canonical subclass:
    the single face's `meshWinding` changes by `-1` as we pass from above to
    below the oriented triangle. -/
theorem canonical_crossing_winding_jump :
    Tendsto (fun ε : ℝ =>
        meshWinding [jumpFace] (jumpPoint ε) - meshWinding [jumpFace] (jumpPoint (-ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
  have hsolid := canonical_crossing_solidAngle_jump
  have hdiv := hsolid.div_const (4 * Real.pi)
  have hconst : (-4 * Real.pi) / (4 * Real.pi) = (-1 : ℝ) := by
    field_simp [Real.pi_ne_zero]
  have heq : (fun ε : ℝ =>
        meshWinding [jumpFace] (jumpPoint ε) - meshWinding [jumpFace] (jumpPoint (-ε)))
      = (fun ε : ℝ =>
        (solidAngle jumpA jumpB jumpC (jumpPoint ε) -
          solidAngle jumpA jumpB jumpC (jumpPoint (-ε))) / (4 * Real.pi)) := by
    funext ε
    simp [meshWinding, jumpFace]
    ring
  rw [heq]
  simpa [hconst] using hdiv

/-- Algebraic bridge for a general soup: if crossing face `f` contributes a
    solid-angle jump of exactly `±4π` and every other face's summed solid angle
    agrees at the two crossing points, then `meshWinding` jumps by `±1`.
    (The "other faces agree" hypothesis is supplied in the limit by
    `continuousAt_meshWinding_of_generic` when all other faces are regular at
    the crossing point.) -/
theorem meshWinding_cons_jump (f : Face) (rest : List Face) (pplus pminus : V3)
    (hface : solidAngle f.1 f.2.1 f.2.2 pplus - solidAngle f.1 f.2.1 f.2.2 pminus =
      -4 * Real.pi)
    (hrest : (rest.map fun g => solidAngle g.1 g.2.1 g.2.2 pplus).sum =
      (rest.map fun g => solidAngle g.1 g.2.1 g.2.2 pminus).sum) :
    meshWinding (f :: rest) pplus - meshWinding (f :: rest) pminus = (-1 : ℝ) := by
  simp only [meshWinding, List.map_cons, List.sum_cons]
  rw [hrest]
  field_simp [Real.pi_ne_zero]
  linarith

/-! ### Remaining walls for the unconditional degree theorem (status)

The two hypotheses isolated at the top of this module are now addressed as
follows.

* **Vanishing at infinity, uniform over directions.** `meshWinding` tends to
  `0` along the *norm filter* `comap (fun p => dot p p) atTop`, not merely along
  a fixed ray. The engine is the explicit finite-soup estimate
  `meshWinding_abs_le`: for `4 · faceM f ≤ ‖p‖`,
  `|solidAngle f p| ≤ 64 · faceM f² / ‖p‖²`, obtained from the denominator
  growth `faceDen_ge_cube` and the affine numerator bound `abs_faceNum_le_far`;
  summing over faces and squeezing gives `meshWinding_tendsto_zero_norm_atTop`.
  This is fully general (every finite soup, every direction).

* **The `±1` crossing jump, single-crossing-face tier.**
  `solidAngle_jump_along_of_den_neg` computes the `−4π` solid-angle jump for an
  *arbitrary* oriented triangle along an arbitrary transverse direction,
  assuming only that the crossing point lies in the plane (`faceNum f c = 0`)
  and in the negative-denominator region (`faceDen f c < 0`), with the crossing
  direction positively oriented. `meshWinding_single_face_crossing_general`
  adds the other faces' continuity. The canonical/right-triangle case is a
  corollary (`jumpFace_den_neg`), and `meshWinding_single_face_crossing_rigid`
  transports it by the landed translation/rotation invariance.

  **The interior geometric step is proved.** `interior_faceDen_neg` shows that
  a point in the relative interior of a nondegenerate oriented triangle (with
  the explicit nondegeneracy hypothesis `0 < dot n n`; the collinear case is
  genuinely false) has `faceDen f c < 0`, i.e. lies in the `atan2'` branch-cut
  region. The proof is purely algebraic: barycentric cancellation, the three
  cross-product identities, strict Cauchy–Schwarz and the Euler-type identity
  `2A′B′C′(1 + Σ cos) = −∏(B′+C′−A′)` with all factors positive. Choosing `nn`
  as the orientation normal and `c` as the interior crossing point therefore
  makes `meshWinding_single_face_crossing_general` unconditional for the unique
  crossing face; the canonical case is also discharged directly by
  `jumpFace_den_neg`.

  **The global assembly is now conditional on one geometric step.**
  `PathChain.sum_eq` proves, purely algebraically, that the winding-number
  change along a finite generic crossing chain is the integer sum of its
  crossing signs; `winding_eq_crossingSum_of_path` combines this with the
  far-field value `0`. Each crossing sign is discharged rigorously by
  `crossing_jump_of_generic_pos` (sign `-1`, from
  `meshWinding_single_face_crossing_general` plus local constancy on the two
  arcs) and `crossing_jump_of_generic_neg` (sign `+1`); the interior
  hypothesis `faceDen f c < 0` is supplied by `interior_faceDen_neg`, and
  `faceNum f c = 0` by `faceNum_eq_zero_of_barycentric`. Feeding the resulting
  integer-valuedness into `meshWinding_const_of_integer_on_preconnected`
  gives `closedMesh_winding_degree`: `meshWinding fs p ∈ ℤ` and constant on
  complement components, together with
  `closedMesh_winding_eq_crossingSum` (value = signed crossing count).

  **Remaining wall (isolated as an explicit hypothesis):** existence of the
  generic crossing chain `PathChain fs q p cs` with `meshWinding fs q = 0`
  for a combinatorially closed oriented mesh (`closedEdges`) and `p` off
  every face (`offFaces`). This is packaged as `GenericPathExists`, which
  the global theorem takes as a premise. Its geometric content -- a ray from
  far away meeting the triangles transversally, only in relative interiors,
  at finitely many points -- is not claimed here.

  **Progress on the remaining wall (rigorous sub-steps, proved at the end of
  this module).** `crossingParams_finite` proves that a finite soup has only
  finitely many crossing parameters along any line from a point off every
  face: each face contributes the singleton `{faceCrossingParam f p d}` (when
  the line is not parallel to the face plane) or nothing (when it is), and
  `crossingParams_subset_candidates` gives the explicit finite superset, one
  candidate per face. `segmentCrossingParams_finite` restricts this to a
  bounded segment. On the subclass side, `closedEdges_face_cancel` shows a
  soup together with its reverse is combinatorially closed, and
  `genericPathExists_face_cancel` (with `genericPathExists_empty` as its
  degenerate case) proves `GenericPathExists` unconditionally for that
  degree-zero closed subclass, using `meshWinding_face_cancel` (`= 0`
  everywhere off the faces). What is still open for a general closed mesh is
  therefore only the far point with winding exactly `0`, the choice of a
  direction avoiding all face edges, and the ordering/assembly of the
  finitely many crossings; the algebraic and finiteness walls are down.

  The direction-avoidance step has since been landed in the final section of
  this module (`exists_momentDir_avoid`, `exists_good_direction`,
  `exists_good_direction_of_general`): a finite set of bad directions is
  avoided by an explicit candidate on the moment curve. The far-point and
  crossing-ordering walls remain.
-/
/- ===== Norm-filter far field ===== -/

def faceM (f : Face) : ℝ := max (norm f.1) (max (norm f.2.1) (norm f.2.2))

lemma faceM_nonneg (f : Face) : 0 ≤ faceM f := by
  unfold faceM
  exact le_trans (norm_nonneg f.1) (le_max_left _ _)

lemma norm_le_faceM_A (f : Face) : norm f.1 ≤ faceM f := by
  unfold faceM
  exact le_max_left _ _

lemma norm_le_faceM_B (f : Face) : norm f.2.1 ≤ faceM f := by
  unfold faceM
  exact le_trans (le_max_left (norm f.2.1) (norm f.2.2))
    (le_max_right (norm f.1) (max (norm f.2.1) (norm f.2.2)))

lemma norm_le_faceM_C (f : Face) : norm f.2.2 ≤ faceM f := by
  unfold faceM
  exact le_trans (le_max_right (norm f.2.1) (norm f.2.2))
    (le_max_right (norm f.1) (max (norm f.2.1) (norm f.2.2)))

lemma dot_sub_sub (a b p : V3) : dot (sub a p) (sub b p) = dot a b - dot a p - dot b p + dot p p := by
  simp [sub, dot]
  ring

lemma dot_sub_self_self (a p : V3) : dot (sub a p) (sub a p) = dot a a - 2 * dot a p + dot p p := by
  rw [dot_sub_sub]
  ring

lemma dot_le_norm_mul (a b : V3) : dot a b ≤ norm a * norm b :=
  le_trans (le_abs_self _) (dot_abs_le a b)

lemma neg_norm_mul_le_dot (a b : V3) : -(norm a * norm b) ≤ dot a b := by
  exact le_trans (neg_le_neg (dot_abs_le a b)) (neg_abs_le _)

lemma norm_sub_ge (a p : V3) : norm p - norm a ≤ norm (sub a p) := by
  have hsq' : (norm p - norm a) ^ 2 ≤ dot (sub a p) (sub a p) := by
    have ha2 : (norm a) ^ 2 = dot a a := by rw [pow_two, norm_sq]
    have hp2 : (norm p) ^ 2 = dot p p := by rw [pow_two, norm_sq]
    rw [dot_sub_self_self, ← ha2, ← hp2]
    have hd := dot_le_norm_mul a p
    nlinarith
  calc
    norm p - norm a ≤ |norm p - norm a| := le_abs_self _
    _ = Real.sqrt ((norm p - norm a) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (dot (sub a p) (sub a p)) := Real.sqrt_le_sqrt hsq'
    _ = norm (sub a p) := rfl

lemma triple_eq_dot_cross (a b c : V3) : triple a b c = dot a (cross b c) := by
  rw [triple, Matrix.det_fin_three]
  simp [cols, dot, cross]
  ring

lemma norm_cross_le' (a b : V3) : norm (cross a b) ≤ norm a * norm b := by
  unfold V3.norm
  have h4 : Real.sqrt (dot a a * dot b b) = Real.sqrt (dot a a) * Real.sqrt (dot b b) :=
    Real.sqrt_mul (dot_self_nonneg _) _
  rw [← h4]
  exact Real.sqrt_le_sqrt (cross_norm_le a b)

lemma abs_triple_le (a b c : V3) : |triple a b c| ≤ norm a * norm b * norm c := by
  calc
    |triple a b c| = |dot a (cross b c)| := by rw [triple_eq_dot_cross]
    _ ≤ norm a * norm (cross b c) := dot_abs_le a (cross b c)
    _ ≤ norm a * (norm b * norm c) := mul_le_mul_of_nonneg_left (norm_cross_le' b c) (norm_nonneg a)
    _ = norm a * norm b * norm c := by ring

lemma abs_triple_le_of_le {a b c : V3} {ma mb mc : ℝ}
    (ha : norm a ≤ ma) (hb : norm b ≤ mb) (hc : norm c ≤ mc)
    (hma : 0 ≤ ma) (hmb : 0 ≤ mb) :
    |triple a b c| ≤ ma * mb * mc := by
  calc
    |triple a b c| ≤ norm a * norm b * norm c := abs_triple_le a b c
    _ ≤ ma * mb * mc := by
      have h1 : norm a * norm b ≤ ma * mb := mul_le_mul ha hb (norm_nonneg _) hma
      exact mul_le_mul h1 hc (norm_nonneg _) (mul_nonneg hma hmb)

lemma num_expand (A B C p : V3) :
    triple (sub A p) (sub B p) (sub C p) =
      triple A B C - triple p B C - triple A p C - triple A B p := by
  simp [triple_eq_dot_cross, dot, cross, sub]
  ring

lemma abs_faceNum_le (f : Face) (p : V3) :
    |faceNum f p| ≤ faceM f ^ 3 + 3 * norm p * faceM f ^ 2 := by
  rcases f with ⟨A, B, C⟩
  have hA := norm_le_faceM_A (A, B, C)
  have hB := norm_le_faceM_B (A, B, C)
  have hC := norm_le_faceM_C (A, B, C)
  have hM0 := faceM_nonneg (A, B, C)
  have hABC := abs_triple_le_of_le hA hB hC hM0 hM0
  have hpBC := abs_triple_le_of_le (le_refl (norm p)) hB hC (norm_nonneg p) hM0
  have hApC := abs_triple_le_of_le hA (le_refl (norm p)) hC hM0 (norm_nonneg p)
  have hABp := abs_triple_le_of_le hA hB (le_refl (norm p)) hM0 hM0
  rw [faceNum, num_expand]
  have h1 := abs_sub (triple A B C - triple p B C - triple A p C) (triple A B p)
  have h2 := abs_sub (triple A B C - triple p B C) (triple A p C)
  have h3 := abs_sub (triple A B C) (triple p B C)
  nlinarith

lemma abs_faceNum_le_far (f : Face) (p : V3) (hfar : 4 * faceM f ≤ norm p) :
    |faceNum f p| ≤ 4 * norm p * faceM f ^ 2 := by
  have h := abs_faceNum_le f p
  have hM0 := faceM_nonneg f
  have hMle : faceM f ≤ norm p := by linarith
  have hnonneg : 0 ≤ (norm p - faceM f) * faceM f ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hMle) (sq_nonneg _)
  nlinarith

lemma faceDen_ge_cube (f : Face) (p : V3) (hfar : 4 * faceM f ≤ norm p) :
    (norm p / 2) ^ 3 ≤ faceDen f p := by
  rcases f with ⟨A, B, C⟩
  let M := faceM (A, B, C)
  let R := norm p
  have hM0 : 0 ≤ M := faceM_nonneg _
  have hMleR : M ≤ R := by linarith
  have hA : norm A ≤ M := by simpa [M] using (norm_le_faceM_A (A, B, C))
  have hB : norm B ≤ M := by simpa [M] using (norm_le_faceM_B (A, B, C))
  have hC : norm C ≤ M := by simpa [M] using (norm_le_faceM_C (A, B, C))
  have hA2 : R / 2 ≤ norm (sub A p) := by
    have h := norm_sub_ge A p
    have : R - norm A ≥ R / 2 := by nlinarith
    linarith
  have hB2 : R / 2 ≤ norm (sub B p) := by
    have h := norm_sub_ge B p
    have : R - norm B ≥ R / 2 := by nlinarith
    linarith
  have hC2 : R / 2 ≤ norm (sub C p) := by
    have h := norm_sub_ge C p
    have : R - norm C ≥ R / 2 := by nlinarith
    linarith
  have hquad_nonneg : 0 ≤ R ^ 2 - 2 * M * R - M ^ 2 := by
    have hk : 0 ≤ M * (R - 4 * M) := mul_nonneg hM0 (sub_nonneg.mpr hfar)
    nlinarith [sq_nonneg M, sq_nonneg (R - 4 * M)]
  have hp2 : dot p p = R ^ 2 := by
    rw [pow_two]
    exact (norm_sq p).symm
  have hdotAB : 0 ≤ dot (sub A p) (sub B p) := by
    have hAB := neg_norm_mul_le_dot A B
    have hprod : norm A * norm B ≤ M * M := mul_le_mul hA hB (norm_nonneg _) hM0
    have hAB2 : -(M ^ 2) ≤ dot A B := by nlinarith
    have hAp' : dot A p ≤ M * R := by
      calc dot A p ≤ norm A * norm p := dot_le_norm_mul A p
        _ ≤ M * R := mul_le_mul hA (le_refl R) (norm_nonneg _) hM0
    have hBp' : dot B p ≤ M * R := by
      calc dot B p ≤ norm B * norm p := dot_le_norm_mul B p
        _ ≤ M * R := mul_le_mul hB (le_refl R) (norm_nonneg _) hM0
    rw [dot_sub_sub, hp2]
    nlinarith
  have hdotBC : 0 ≤ dot (sub B p) (sub C p) := by
    have hBC := neg_norm_mul_le_dot B C
    have hprod : norm B * norm C ≤ M * M := mul_le_mul hB hC (norm_nonneg _) hM0
    have hBC2 : -(M ^ 2) ≤ dot B C := by nlinarith
    have hBp' : dot B p ≤ M * R := by
      calc dot B p ≤ norm B * norm p := dot_le_norm_mul B p
        _ ≤ M * R := mul_le_mul hB (le_refl R) (norm_nonneg _) hM0
    have hCp' : dot C p ≤ M * R := by
      calc dot C p ≤ norm C * norm p := dot_le_norm_mul C p
        _ ≤ M * R := mul_le_mul hC (le_refl R) (norm_nonneg _) hM0
    rw [dot_sub_sub, hp2]
    nlinarith
  have hdotCA : 0 ≤ dot (sub C p) (sub A p) := by
    have hCA := neg_norm_mul_le_dot C A
    have hprod : norm C * norm A ≤ M * M := mul_le_mul hC hA (norm_nonneg _) hM0
    have hCA2 : -(M ^ 2) ≤ dot C A := by nlinarith
    have hCp' : dot C p ≤ M * R := by
      calc dot C p ≤ norm C * norm p := dot_le_norm_mul C p
        _ ≤ M * R := mul_le_mul hC (le_refl R) (norm_nonneg _) hM0
    have hAp' : dot A p ≤ M * R := by
      calc dot A p ≤ norm A * norm p := dot_le_norm_mul A p
        _ ≤ M * R := mul_le_mul hA (le_refl R) (norm_nonneg _) hM0
    rw [dot_sub_sub, hp2]
    nlinarith
  have hR0 : 0 ≤ R := by exact norm_nonneg p
  have hprod : (R / 2) * (R / 2) * (R / 2) ≤
      norm (sub A p) * norm (sub B p) * norm (sub C p) := by
    have hhalf : 0 ≤ R / 2 := by nlinarith
    have h1 : (R / 2) * (R / 2) ≤ norm (sub A p) * norm (sub B p) :=
      mul_le_mul hA2 hB2 hhalf (norm_nonneg _)
    exact mul_le_mul h1 hC2 hhalf
      (mul_nonneg (norm_nonneg (sub A p)) (norm_nonneg (sub B p)))
  change (R / 2) ^ 3 ≤
    norm (sub A p) * norm (sub B p) * norm (sub C p) +
      dot (sub A p) (sub B p) * norm (sub C p) +
      dot (sub B p) (sub C p) * norm (sub A p) +
      dot (sub C p) (sub A p) * norm (sub B p)
  calc
    (R / 2) ^ 3 = (R / 2) * (R / 2) * (R / 2) := by ring
    _ ≤ norm (sub A p) * norm (sub B p) * norm (sub C p) := hprod
    _ ≤ norm (sub A p) * norm (sub B p) * norm (sub C p) +
          dot (sub A p) (sub B p) * norm (sub C p) +
          dot (sub B p) (sub C p) * norm (sub A p) +
          dot (sub C p) (sub A p) * norm (sub B p) := by
      nlinarith [hdotAB, hdotBC, hdotCA, norm_nonneg (sub A p), norm_nonneg (sub B p),
        norm_nonneg (sub C p)]

lemma abs_solidAngle_le_far (f : Face) (p : V3) (hfar : 4 * faceM f ≤ norm p)
    (hp : 0 < norm p) :
    |solidAngle f.1 f.2.1 f.2.2 p| ≤ 64 * faceM f ^ 2 / dot p p := by
  let M := faceM f
  let R := norm p
  have hcube_lb : R ^ 3 / 8 ≤ faceDen f p := by
    have h := faceDen_ge_cube f p hfar
    have heq : (R / 2) ^ 3 = R ^ 3 / 8 := by ring
    simpa [R, heq] using h
  have hdenpos : 0 < faceDen f p := by
    have hR3 : 0 < R ^ 3 := by positivity
    nlinarith
  have hR2 : dot p p = R ^ 2 := by rw [pow_two, norm_sq]
  have hnum : |faceNum f p| ≤ 4 * R * M ^ 2 := by
    simpa [M, R] using abs_faceNum_le_far f p hfar
  have hratio : |faceNum f p / faceDen f p| ≤ 32 * M ^ 2 / R ^ 2 := by
    rw [abs_div, abs_of_pos hdenpos]
    have hM20 : 0 ≤ 4 * R * M ^ 2 := by positivity
    have hR3pos : 0 < R ^ 3 / 8 := by positivity
    have h1 : |faceNum f p| / faceDen f p ≤ (4 * R * M ^ 2) / (R ^ 3 / 8) :=
      div_le_div₀ hM20 hnum hR3pos hcube_lb
    calc
      |faceNum f p| / faceDen f p ≤ (4 * R * M ^ 2) / (R ^ 3 / 8) := h1
      _ = 32 * M ^ 2 / R ^ 2 := by field_simp [ne_of_gt hp]; ring
  rw [solidAngle_eq_face]
  simp [atan2', hdenpos]
  calc
    2 * |Real.arctan (faceNum f p / faceDen f p)|
        ≤ 2 * |faceNum f p / faceDen f p| :=
      mul_le_mul_of_nonneg_left Real.abs_arctan_le_abs (by norm_num)
    _ ≤ 2 * (32 * M ^ 2 / R ^ 2) := mul_le_mul_of_nonneg_left hratio (by norm_num)
    _ = 64 * faceM f ^ 2 / dot p p := by rw [hR2]; ring

def soupC (fs : List Face) : ℝ := (fs.map fun f => 64 * faceM f ^ 2).sum / (4 * Real.pi)

lemma solidAngle_sum_abs_le (fs : List Face) (p : V3)
    (hfar : ∀ f ∈ fs, 4 * faceM f ≤ norm p) (hp : 0 < norm p) :
    |(fs.map fun f => solidAngle f.1 f.2.1 f.2.2 p).sum| ≤
      (fs.map fun f => 64 * faceM f ^ 2).sum / dot p p := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
      have hf := hfar f (by simp)
      have hrs : ∀ g ∈ fs, 4 * faceM g ≤ norm p := by
        intro g hg; exact hfar g (by simp [hg])
      have h1 := abs_solidAngle_le_far f p hf hp
      have h2 := ih hrs
      simp only [List.map_cons, List.sum_cons]
      calc
        |solidAngle f.1 f.2.1 f.2.2 p + (fs.map fun f => solidAngle f.1 f.2.1 f.2.2 p).sum|
            ≤ |solidAngle f.1 f.2.1 f.2.2 p| +
                |(fs.map fun f => solidAngle f.1 f.2.1 f.2.2 p).sum| := abs_add_le _ _
        _ ≤ 64 * faceM f ^ 2 / dot p p +
              (fs.map fun f => 64 * faceM f ^ 2).sum / dot p p := add_le_add h1 h2
        _ = (64 * faceM f ^ 2 + (fs.map fun f => 64 * faceM f ^ 2).sum) / dot p p := by ring

lemma meshWinding_abs_le (fs : List Face) (p : V3)
    (hfar : ∀ f ∈ fs, 4 * faceM f ≤ norm p) (hp : 0 < norm p) :
    |meshWinding fs p| ≤ soupC fs / dot p p := by
  have h := solidAngle_sum_abs_le fs p hfar hp
  have h4pi : 0 < 4 * Real.pi := by positivity
  have hdotpos : 0 < dot p p := by
    rw [show dot p p = norm p * norm p from (norm_sq p).symm]
    positivity
  change |(fs.map fun f => solidAngle f.1 f.2.1 f.2.2 p).sum / (4 * Real.pi)| ≤
    soupC fs / dot p p
  rw [abs_div, abs_of_pos h4pi]
  calc
    |(fs.map fun f => solidAngle f.1 f.2.1 f.2.2 p).sum| / (4 * Real.pi)
        ≤ ((fs.map fun f => 64 * faceM f ^ 2).sum / dot p p) / (4 * Real.pi) :=
          div_le_div_of_nonneg_right h h4pi.le
    _ = soupC fs / dot p p := by
      simp [soupC]
      field_simp [Real.pi_ne_zero, ne_of_gt hdotpos]

def soupThresh (fs : List Face) : ℝ := 4 * (fs.map faceM).sum

lemma faceM_sum_nonneg (fs : List Face) : 0 ≤ (fs.map faceM).sum := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg (faceM_nonneg f) ih

lemma soupThresh_nonneg (fs : List Face) : 0 ≤ soupThresh fs := by
  unfold soupThresh
  exact mul_nonneg (by norm_num) (faceM_sum_nonneg fs)

lemma faceM_le_sum (f : Face) (fs : List Face) (hf : f ∈ fs) : faceM f ≤ (fs.map faceM).sum := by
  refine List.single_le_sum ?_ (faceM f) ?_
  · intro x hx
    rcases List.mem_map.mp hx with ⟨g, hg, rfl⟩
    exact faceM_nonneg g
  · exact List.mem_map.mpr ⟨f, hf, rfl⟩

lemma soupThresh_ge (fs : List Face) (f : Face) (hf : f ∈ fs) : 4 * faceM f ≤ soupThresh fs := by
  unfold soupThresh
  exact mul_le_mul_of_nonneg_left (faceM_le_sum f fs hf) (by norm_num)

lemma soupC_nonneg (fs : List Face) : 0 ≤ soupC fs := by
  unfold soupC
  have hsum : 0 ≤ (fs.map fun f => 64 * faceM f ^ 2).sum := by
    induction fs with
    | nil => simp
    | cons f fs ih =>
        simp only [List.map_cons, List.sum_cons]
        exact add_nonneg (by positivity) ih
  exact div_nonneg hsum (by positivity)

theorem meshWinding_tendsto_zero_norm_atTop (fs : List Face) :
    Tendsto (fun p : V3 => meshWinding fs p) (comap (fun p => dot p p) atTop) (𝓝 0) := by
  have hC : Tendsto (fun p : V3 => soupC fs / dot p p)
      (comap (fun p => dot p p) atTop) (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_comap
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Filter.Eventually.of_forall fun p => norm_nonneg _) ?_ hC
  change {p : V3 | ‖meshWinding fs p‖ ≤ soupC fs / dot p p} ∈ comap (fun p => dot p p) atTop
  rw [mem_comap]
  refine ⟨Set.Ici (max 1 (soupThresh fs ^ 2)), Filter.Ici_mem_atTop _, ?_⟩
  intro p hp
  have hdot1 : 1 ≤ dot p p := le_trans (le_max_left _ _) hp
  have hdotT : soupThresh fs ^ 2 ≤ dot p p := le_trans (le_max_right _ _) hp
  have hp_pos : 0 < V3.norm p := by
    change 0 < Real.sqrt (dot p p)
    exact Real.sqrt_pos.2 (lt_of_lt_of_le (by norm_num) hdot1)
  have hnorm_ge : soupThresh fs ≤ V3.norm p := by
    have hT0 := soupThresh_nonneg fs
    have hs := Real.sqrt_le_sqrt hdotT
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hT0] at hs
    simpa [V3.norm] using hs
  have hfar : ∀ f ∈ fs, 4 * faceM f ≤ V3.norm p := by
    intro f hf
    exact le_trans (soupThresh_ge fs f hf) hnorm_ge
  simpa [V3.norm] using (meshWinding_abs_le fs p hfar hp_pos)

/- ===== General single-face crossing ===== -/

def along (p nn : V3) (ε : ℝ) : V3 :=
  ⟨p.x + ε * nn.x, p.y + ε * nn.y, p.z + ε * nn.z⟩

def orientationNormal (f : Face) : V3 :=
  cross (sub f.2.1 f.1) (sub f.2.2 f.1)

set_option maxHeartbeats 800000 in
lemma faceNum_along (f : Face) (c nn : V3) (ε : ℝ) :
    faceNum f (along c nn ε) = faceNum f c - ε * dot (orientationNormal f) nn := by
  simp [faceNum, orientationNormal, along, triple_eq_dot_cross, dot, cross, sub]
  ring

set_option maxHeartbeats 800000 in
theorem solidAngle_jump_along_of_den_neg (f : Face) (c nn : V3)
    (hplane : faceNum f c = 0) (hden : faceDen f c < 0)
    (hN : 0 < dot (orientationNormal f) nn) :
    Tendsto (fun ε : ℝ =>
        solidAngle f.1 f.2.1 f.2.2 (along c nn ε) -
          solidAngle f.1 f.2.1 f.2.2 (along c nn (-ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-4 * Real.pi)) := by
  let K := dot (orientationNormal f) nn
  have halong_cont : Continuous (fun ε : ℝ => along c nn ε) := by
    rw [continuous_induced_rng]
    change Continuous (fun ε : ℝ => (c.x + ε * nn.x, c.y + ε * nn.y, c.z + ε * nn.z))
    fun_prop
  have halong_neg_cont : Continuous (fun ε : ℝ => along c nn (-ε)) :=
    halong_cont.comp continuous_neg
  have halong_zero : along c nn 0 = c := by
    apply V3.ext <;> simp [along]
  have halong_neg_zero : along c nn (-0) = c := by simpa using halong_zero
  have hden_cont_up : ContinuousAt (fun ε : ℝ => faceDen f (along c nn ε)) 0 :=
    (continuousAt_faceDen f c).comp_of_eq halong_cont.continuousAt halong_zero
  have hden_cont_dn : ContinuousAt (fun ε : ℝ => faceDen f (along c nn (-ε))) 0 :=
    (continuousAt_faceDen f c).comp_of_eq halong_neg_cont.continuousAt halong_neg_zero
  have hden_tend_up : Tendsto (fun ε : ℝ => faceDen f (along c nn ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (faceDen f c)) := by
    have htmp : Tendsto (fun ε : ℝ => faceDen f (along c nn ε))
        (𝓝[>] (0 : ℝ)) (𝓝 (faceDen f (along c nn 0))) :=
      hden_cont_up.tendsto.mono_left nhdsWithin_le_nhds
    simpa [halong_zero] using htmp
  have hden_tend_dn : Tendsto (fun ε : ℝ => faceDen f (along c nn (-ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (faceDen f c)) := by
    have htmp : Tendsto (fun ε : ℝ => faceDen f (along c nn (-ε)))
        (𝓝[>] (0 : ℝ)) (𝓝 (faceDen f (along c nn (-0)))) :=
      hden_cont_dn.tendsto.mono_left nhdsWithin_le_nhds
    rw [halong_neg_zero] at htmp
    exact htmp
  have hnum_up_eq : (fun ε : ℝ => faceNum f (along c nn ε)) = fun ε => (-K) * ε := by
    funext ε
    rw [faceNum_along, hplane]
    dsimp [K]
    ring
  have hnum_dn_eq : (fun ε : ℝ => faceNum f (along c nn (-ε))) = fun ε => K * ε := by
    funext ε
    rw [faceNum_along, hplane]
    dsimp [K]
    ring
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hnum_up : Tendsto (fun ε : ℝ => faceNum f (along c nn ε))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [hnum_up_eq]
    simpa using hid.const_mul (-K)
  have hnum_dn : Tendsto (fun ε : ℝ => faceNum f (along c nn (-ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [hnum_dn_eq]
    simpa using hid.const_mul K
  have hnum_up_pt : ∀ ε : ℝ, faceNum f (along c nn ε) = (-K) * ε :=
    fun ε => congrFun hnum_up_eq ε
  have hnum_dn_pt : ∀ ε : ℝ, faceNum f (along c nn (-ε)) = K * ε :=
    fun ε => congrFun hnum_dn_eq ε
  have hK : 0 < K := by simpa [K] using hN
  have hnum_up_neg : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), faceNum f (along c nn ε) < 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have heps : 0 < ε := hε
    have hprod : 0 < K * ε := mul_pos hK heps
    rw [hnum_up_pt]
    nlinarith
  have hnum_dn_pos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < faceNum f (along c nn (-ε)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have heps : 0 < ε := hε
    rw [hnum_dn_pt]
    exact mul_pos hK heps
  have hatan_up : Tendsto (fun ε : ℝ =>
      atan2' (faceNum f (along c nn ε)) (faceDen f (along c nn ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-Real.pi)) :=
    atan2'_tendsto_negPi_of hnum_up hden_tend_up hden hnum_up_neg
  have hatan_dn : Tendsto (fun ε : ℝ =>
      atan2' (faceNum f (along c nn (-ε))) (faceDen f (along c nn (-ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 Real.pi) :=
    atan2'_tendsto_posPi_of hnum_dn hden_tend_dn hden hnum_dn_pos
  have hsolid_up : Tendsto (fun ε : ℝ => solidAngle f.1 f.2.1 f.2.2 (along c nn ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * (-Real.pi))) := by
    simpa [solidAngle_eq_face] using hatan_up.const_mul (2 : ℝ)
  have hsolid_dn : Tendsto (fun ε : ℝ => solidAngle f.1 f.2.1 f.2.2 (along c nn (-ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * Real.pi)) := by
    simpa [solidAngle_eq_face] using hatan_dn.const_mul (2 : ℝ)
  have hdiff := hsolid_up.sub hsolid_dn
  simpa [show -(2 * Real.pi) - 2 * Real.pi = -4 * Real.pi by ring] using hdiff

set_option maxHeartbeats 800000 in
theorem meshWinding_single_face_crossing_general (f : Face) (rest : List Face) (c nn : V3)
    (hplane : faceNum f c = 0) (hden : faceDen f c < 0)
    (hN : 0 < dot (orientationNormal f) nn)
    (hrest : ∀ g ∈ rest, faceNum g c ≠ 0 ∧ faceDen g c ≠ 0) :
    Tendsto (fun ε : ℝ =>
        meshWinding (f :: rest) (along c nn ε) -
          meshWinding (f :: rest) (along c nn (-ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
  have halong_cont : Continuous (fun ε : ℝ => along c nn ε) := by
    rw [continuous_induced_rng]
    change Continuous (fun ε : ℝ => (c.x + ε * nn.x, c.y + ε * nn.y, c.z + ε * nn.z))
    fun_prop
  have halong_neg_cont : Continuous (fun ε : ℝ => along c nn (-ε)) :=
    halong_cont.comp continuous_neg
  have halong_zero : along c nn 0 = c := by
    apply V3.ext <;> simp [along]
  have halong_neg_zero : along c nn (-0) = c := by simpa using halong_zero
  have hrest_cont : ContinuousAt (meshWinding rest) c :=
    continuousAt_meshWinding_of_generic rest c hrest
  have hrest_plus : Tendsto (fun ε : ℝ => meshWinding rest (along c nn ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (meshWinding rest c)) := by
    have htmp : Tendsto (fun ε : ℝ => meshWinding rest (along c nn ε))
        (𝓝[>] (0 : ℝ)) (𝓝 (meshWinding rest (along c nn 0))) :=
      (hrest_cont.comp_of_eq halong_cont.continuousAt halong_zero).tendsto.mono_left
        nhdsWithin_le_nhds
    rw [halong_zero] at htmp
    exact htmp
  have hrest_minus : Tendsto (fun ε : ℝ => meshWinding rest (along c nn (-ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (meshWinding rest c)) := by
    have htmp : Tendsto (fun ε : ℝ => meshWinding rest (along c nn (-ε)))
        (𝓝[>] (0 : ℝ)) (𝓝 (meshWinding rest (along c nn (-0)))) :=
      (hrest_cont.comp_of_eq halong_neg_cont.continuousAt halong_neg_zero).tendsto.mono_left
        nhdsWithin_le_nhds
    rw [halong_neg_zero] at htmp
    exact htmp
  have hrest_diff : Tendsto (fun ε : ℝ =>
      meshWinding rest (along c nn ε) - meshWinding rest (along c nn (-ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hrest_plus.sub hrest_minus
  have hface := solidAngle_jump_along_of_den_neg f c nn hplane hden hN
  have hface_div : Tendsto (fun ε : ℝ =>
      solidAngle f.1 f.2.1 f.2.2 (along c nn ε) / (4 * Real.pi) -
        solidAngle f.1 f.2.1 f.2.2 (along c nn (-ε)) / (4 * Real.pi))
      (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
    have hd := hface.div_const (4 * Real.pi)
    have heq : (fun ε : ℝ =>
        (solidAngle f.1 f.2.1 f.2.2 (along c nn ε) -
          solidAngle f.1 f.2.1 f.2.2 (along c nn (-ε))) / (4 * Real.pi)) =
        (fun ε : ℝ =>
          solidAngle f.1 f.2.1 f.2.2 (along c nn ε) / (4 * Real.pi) -
            solidAngle f.1 f.2.1 f.2.2 (along c nn (-ε)) / (4 * Real.pi)) := by
      funext ε
      rw [sub_div]
    rw [← heq]
    have hcst : (-4 * Real.pi) / (4 * Real.pi) = (-1 : ℝ) := by
      field_simp [Real.pi_ne_zero]
    simpa [hcst] using hd
  have hsum := hface_div.add hrest_diff
  have heq : (fun ε : ℝ =>
        meshWinding (f :: rest) (along c nn ε) - meshWinding (f :: rest) (along c nn (-ε))) =
      (fun ε : ℝ =>
        (solidAngle f.1 f.2.1 f.2.2 (along c nn ε) / (4 * Real.pi) -
          solidAngle f.1 f.2.1 f.2.2 (along c nn (-ε)) / (4 * Real.pi)) +
        (meshWinding rest (along c nn ε) - meshWinding rest (along c nn (-ε)))) := by
    funext ε
    rw [show f :: rest = [f] ++ rest by rfl]
    rw [meshWinding_append, meshWinding_append]
    simp [meshWinding]
    ring
  rw [heq]
  simpa using hsum

/- ===== Canonical and rigid-motion specialisations ===== -/

lemma along_jumpPoint (ε : ℝ) :
    along (jumpPoint 0) ⟨0, 0, 1⟩ ε = jumpPoint ε := by
  apply V3.ext <;> simp [along, jumpPoint]

set_option maxHeartbeats 800000 in
theorem meshWinding_single_face_crossing_canonical (rest : List Face)
    (hrest : ∀ g ∈ rest, faceNum g (jumpPoint 0) ≠ 0 ∧ faceDen g (jumpPoint 0) ≠ 0) :
    Tendsto (fun ε : ℝ =>
        meshWinding (jumpFace :: rest) (jumpPoint ε) -
          meshWinding (jumpFace :: rest) (jumpPoint (-ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
  have hplane : faceNum jumpFace (jumpPoint 0) = 0 := by simpa using jumpFace_num 0
  have hden : faceDen jumpFace (jumpPoint 0) < 0 := jumpFace_den_neg
  have hN : 0 < dot (orientationNormal jumpFace) (⟨0, 0, 1⟩ : V3) := by
    simp [orientationNormal, jumpFace, jumpA, jumpB, jumpC, cross, dot, sub]
  have h := meshWinding_single_face_crossing_general jumpFace rest (jumpPoint 0)
    ⟨0, 0, 1⟩ hplane hden hN hrest
  simpa [along_jumpPoint] using h

set_option maxHeartbeats 800000 in
theorem meshWinding_single_face_crossing_rigid
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hO : Qᵀ * Q = 1) (hdet : Q.det = 1) (t : V3)
    (rest : List Face)
    (hrest : ∀ g ∈ rest, faceNum g (jumpPoint 0) ≠ 0 ∧ faceDen g (jumpPoint 0) ≠ 0) :
    Tendsto (fun ε : ℝ =>
        meshWinding (((jumpFace :: rest).map fun f =>
          (add (applyMat Q f.1) t, add (applyMat Q f.2.1) t, add (applyMat Q f.2.2) t)))
          (add (applyMat Q (jumpPoint ε)) t) -
        meshWinding (((jumpFace :: rest).map fun f =>
          (add (applyMat Q f.1) t, add (applyMat Q f.2.1) t, add (applyMat Q f.2.2) t)))
          (add (applyMat Q (jumpPoint (-ε))) t))
      (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
  have hcanon := meshWinding_single_face_crossing_canonical rest hrest
  let rotF : Face → Face := fun f => (applyMat Q f.1, applyMat Q f.2.1, applyMat Q f.2.2)
  let trF : Face → Face := fun f => (add f.1 t, add f.2.1 t, add f.2.2 t)
  let rigidF : Face → Face := fun f =>
    (add (applyMat Q f.1) t, add (applyMat Q f.2.1) t, add (applyMat Q f.2.2) t)
  have hmap : ((jumpFace :: rest).map rotF).map trF = (jumpFace :: rest).map rigidF := by
    rw [List.map_map]
    congr 1
  have htrans : ∀ p : V3,
      meshWinding ((jumpFace :: rest).map rigidF) (add (applyMat Q p) t) =
        meshWinding ((jumpFace :: rest).map rotF) (applyMat Q p) := by
    intro p
    rw [← hmap]
    exact meshWinding_translate t (applyMat Q p) ((jumpFace :: rest).map rotF)
  have hrot : ∀ p : V3,
      meshWinding ((jumpFace :: rest).map rotF) (applyMat Q p) =
        meshWinding (jumpFace :: rest) p := by
    intro p
    exact meshWinding_rotate Q hO hdet (jumpFace :: rest) p
  refine hcanon.congr' ?_
  filter_upwards [] with ε
  dsimp [rigidF, rotF] at htrans hrot ⊢
  rw [htrans (jumpPoint ε), hrot (jumpPoint ε),
      htrans (jumpPoint (-ε)), hrot (jumpPoint (-ε))]

set_option maxHeartbeats 800000 in
/-- **An interior point of a nondegenerate triangle lies in the negative-`faceDen`
branch.** If `c = αA + βB + γC` with `α, β, γ > 0` and `α + β + γ = 1`
(a relative-interior point), then the Van Oosterom–Strackee denominator is
strictly negative: `c` is inside the circumcircle, so the `atan2'` branch cut
is present. The proof uses the identity, with `r_A = |A-c|` and
`A' = α r_A` (cyclically),
```
  2 A' B' C' (1 + cos ⟨A-c,B-c⟩ + cos ⟨B-c,C-c⟩ + cos ⟨C-c,A-c⟩)
      = -(B'+C'-A')(C'+A'-B')(A'+B'-C'),
```
whose three factors are strictly positive by the triangle inequality
(applied to the side lengths `A', B', C'`, which form a nondegenerate triangle
because `c` is interior). Combined with `solidAngle_jump_along_of_den_neg`
this makes the `−4π` crossing jump unconditional for the crossing face. -/
theorem interior_faceDen_neg (f : Face) (c : V3)
    (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hsum : α + β + γ = 1)
    (hc : c = ⟨α*f.1.x + β*f.2.1.x + γ*f.2.2.x,
               α*f.1.y + β*f.2.1.y + γ*f.2.2.y,
               α*f.1.z + β*f.2.1.z + γ*f.2.2.z⟩)
    (hnd : 0 < dot (orientationNormal f) (orientationNormal f)) :
    faceDen f c < 0 := by
  rcases f with ⟨A, B, C⟩
  dsimp [orientationNormal] at hnd
  let u := sub A c
  let v := sub B c
  let w := sub C c
  let n := cross (sub B A) (sub C A)
  have hnd' : 0 < dot n n := by simpa [n] using hnd
  have hαe : α = 1 - β - γ := by linarith
  have hβe : β = 1 - α - γ := by linarith
  have hγe : γ = 1 - α - β := by linarith
  have hx : α * u.x + β * v.x + γ * w.x = 0 := by
    dsimp [u, v, w, sub]
    rw [hc]
    simp
    rw [hγe]
    ring
  have hy : α * u.y + β * v.y + γ * w.y = 0 := by
    dsimp [u, v, w, sub]
    rw [hc]
    simp
    rw [hγe]
    ring
  have hz : α * u.z + β * v.z + γ * w.z = 0 := by
    dsimp [u, v, w, sub]
    rw [hc]
    simp
    rw [hγe]
    ring
  have hcross_uv : cross u v = ⟨γ * n.x, γ * n.y, γ * n.z⟩ := by
    apply V3.ext <;> dsimp [cross, u, v, n, sub] <;> rw [hc] <;> simp <;> rw [hγe] <;> ring
  have hcross_vw : cross v w = ⟨α * n.x, α * n.y, α * n.z⟩ := by
    apply V3.ext <;> dsimp [cross, v, w, n, sub] <;> rw [hc] <;> simp <;> rw [hαe] <;> ring
  have hcross_wu : cross w u = ⟨β * n.x, β * n.y, β * n.z⟩ := by
    apply V3.ext <;> dsimp [cross, w, u, n, sub] <;> rw [hc] <;> simp <;> rw [hβe] <;> ring
  have hcu_pos : 0 < dot (cross u v) (cross u v) := by
    rw [hcross_uv]
    dsimp [dot] at hnd' ⊢
    nlinarith [mul_pos hγ hγ]
  have hcv_pos : 0 < dot (cross v w) (cross v w) := by
    rw [hcross_vw]
    dsimp [dot] at hnd' ⊢
    nlinarith [mul_pos hα hα]
  have hcw_pos : 0 < dot (cross w u) (cross w u) := by
    rw [hcross_wu]
    dsimp [dot] at hnd' ⊢
    nlinarith [mul_pos hβ hβ]
  let ra := Real.sqrt (dot u u)
  let rb := Real.sqrt (dot v v)
  let rc := Real.sqrt (dot w w)
  have hra2 : ra * ra = dot u u := by dsimp [ra]; exact Real.mul_self_sqrt (dot_self_nonneg u)
  have hrb2 : rb * rb = dot v v := by dsimp [rb]; exact Real.mul_self_sqrt (dot_self_nonneg v)
  have hrc2 : rc * rc = dot w w := by dsimp [rc]; exact Real.mul_self_sqrt (dot_self_nonneg w)
  have hduu_pos : 0 < dot u u := by
    have hlag := V3.lagrange u v
    rw [hcross_uv] at hlag
    have hcu_pos2 := hcu_pos
    rw [hcross_uv] at hcu_pos2
    nlinarith [hlag, hcu_pos2, dot_self_nonneg v, sq_nonneg (dot u v)]
  have hdvv_pos : 0 < dot v v := by
    have hlag := V3.lagrange v w
    rw [hcross_vw] at hlag
    have hcv_pos2 := hcv_pos
    rw [hcross_vw] at hcv_pos2
    nlinarith [hlag, hcv_pos2, dot_self_nonneg w, sq_nonneg (dot v w)]
  have hdww_pos : 0 < dot w w := by
    have hlag := V3.lagrange w u
    rw [hcross_wu] at hlag
    have hcw_pos2 := hcw_pos
    rw [hcross_wu] at hcw_pos2
    nlinarith [hlag, hcw_pos2, dot_self_nonneg u, sq_nonneg (dot w u)]
  have hra_pos : 0 < ra := by dsimp [ra]; exact Real.sqrt_pos.2 hduu_pos
  have hrb_pos : 0 < rb := by dsimp [rb]; exact Real.sqrt_pos.2 hdvv_pos
  have hrc_pos : 0 < rc := by dsimp [rc]; exact Real.sqrt_pos.2 hdww_pos
  let Ap := α * ra
  let Bp := β * rb
  let Cp := γ * rc
  have hAp_pos : 0 < Ap := by dsimp [Ap]; exact mul_pos hα hra_pos
  have hBp_pos : 0 < Bp := by dsimp [Bp]; exact mul_pos hβ hrb_pos
  have hCp_pos : 0 < Cp := by dsimp [Cp]; exact mul_pos hγ hrc_pos
  have hdu : α * dot u u + β * dot u v + γ * dot u w = 0 := by
    simp only [dot]
    calc
      α * (u.x * u.x + u.y * u.y + u.z * u.z) +
        β * (u.x * v.x + u.y * v.y + u.z * v.z) +
        γ * (u.x * w.x + u.y * w.y + u.z * w.z)
          = u.x * (α * u.x + β * v.x + γ * w.x) +
            u.y * (α * u.y + β * v.y + γ * w.y) +
            u.z * (α * u.z + β * v.z + γ * w.z) := by ring
      _ = 0 := by rw [hx, hy, hz]; ring
  have hdv : α * dot u v + β * dot v v + γ * dot v w = 0 := by
    simp only [dot]
    calc
      α * (u.x * v.x + u.y * v.y + u.z * v.z) +
        β * (v.x * v.x + v.y * v.y + v.z * v.z) +
        γ * (v.x * w.x + v.y * w.y + v.z * w.z)
          = v.x * (α * u.x + β * v.x + γ * w.x) +
            v.y * (α * u.y + β * v.y + γ * w.y) +
            v.z * (α * u.z + β * v.z + γ * w.z) := by ring
      _ = 0 := by rw [hx, hy, hz]; ring
  have hdw : α * dot u w + β * dot v w + γ * dot w w = 0 := by
    simp only [dot]
    calc
      α * (u.x * w.x + u.y * w.y + u.z * w.z) +
        β * (v.x * w.x + v.y * w.y + v.z * w.z) +
        γ * (w.x * w.x + w.y * w.y + w.z * w.z)
          = w.x * (α * u.x + β * v.x + γ * w.x) +
            w.y * (α * u.y + β * v.y + γ * w.y) +
            w.z * (α * u.z + β * v.z + γ * w.z) := by ring
      _ = 0 := by rw [hx, hy, hz]; ring
  let P := dot u v / (ra * rb)
  let Q := dot v w / (rb * rc)
  let S := dot u w / (ra * rc)
  have h1raw : α * ra + β * (dot u v / ra) + γ * (dot u w / ra) = 0 := by
    have htt := hdu
    rw [← hra2] at htt
    field_simp [ne_of_gt hra_pos] at htt ⊢
    ring_nf at htt ⊢
    exact htt
  have h2raw : α * (dot u v / rb) + β * rb + γ * (dot v w / rb) = 0 := by
    have htt := hdv
    rw [← hrb2] at htt
    field_simp [ne_of_gt hrb_pos] at htt ⊢
    ring_nf at htt ⊢
    exact htt
  have h3raw : α * (dot u w / rc) + β * (dot v w / rc) + γ * rc = 0 := by
    have htt := hdw
    rw [← hrc2] at htt
    field_simp [ne_of_gt hrc_pos] at htt ⊢
    ring_nf at htt ⊢
    exact htt
  have h1 : Ap + Bp * P + Cp * S = 0 := by
    dsimp [Ap, Bp, Cp, P, S]
    have hp' : β * rb * (dot u v / (ra * rb)) = β * (dot u v / ra) := by
      field_simp [ne_of_gt hra_pos, ne_of_gt hrb_pos]
    have hs' : γ * rc * (dot u w / (ra * rc)) = γ * (dot u w / ra) := by
      field_simp [ne_of_gt hra_pos, ne_of_gt hrc_pos]
    rw [hp', hs']
    exact h1raw
  have h2 : Ap * P + Bp + Cp * Q = 0 := by
    dsimp [Ap, Bp, Cp, P, Q]
    have hp' : α * ra * (dot u v / (ra * rb)) = α * (dot u v / rb) := by
      field_simp [ne_of_gt hra_pos, ne_of_gt hrb_pos]
    have hq' : γ * rc * (dot v w / (rb * rc)) = γ * (dot v w / rb) := by
      field_simp [ne_of_gt hrb_pos, ne_of_gt hrc_pos]
    rw [hp', hq']
    exact h2raw
  have h3 : Ap * S + Bp * Q + Cp = 0 := by
    dsimp [Ap, Bp, Cp, S, Q]
    have hs' : α * ra * (dot u w / (ra * rc)) = α * (dot u w / rc) := by
      field_simp [ne_of_gt hra_pos, ne_of_gt hrc_pos]
    have hq' : β * rb * (dot v w / (rb * rc)) = β * (dot v w / rc) := by
      field_simp [ne_of_gt hrb_pos, ne_of_gt hrc_pos]
    rw [hs', hq']
    exact h3raw
  have hPform : P = (Cp^2 - Ap^2 - Bp^2) / (2 * Ap * Bp) := by
    have hc1 : 2 * Ap * Bp * P = Cp^2 - Ap^2 - Bp^2 := by
      linear_combination Ap * h1 + Bp * h2 - Cp * h3
    field_simp [ne_of_gt hAp_pos, ne_of_gt hBp_pos]
    ring_nf at hc1 ⊢
    exact hc1
  have hQform : Q = (Ap^2 - Bp^2 - Cp^2) / (2 * Bp * Cp) := by
    have hc1 : 2 * Bp * Cp * Q = Ap^2 - Bp^2 - Cp^2 := by
      linear_combination -Ap * h1 + Bp * h2 + Cp * h3
    field_simp [ne_of_gt hBp_pos, ne_of_gt hCp_pos]
    ring_nf at hc1 ⊢
    exact hc1
  have hSform : S = (Bp^2 - Ap^2 - Cp^2) / (2 * Ap * Cp) := by
    have hc1 : 2 * Ap * Cp * S = Bp^2 - Ap^2 - Cp^2 := by
      linear_combination Ap * h1 - Bp * h2 + Cp * h3
    field_simp [ne_of_gt hAp_pos, ne_of_gt hCp_pos]
    ring_nf at hc1 ⊢
    exact hc1
  have hfinal : 2 * Ap * Bp * Cp * (1 + P + Q + S) =
      -((Bp + Cp - Ap) * (Cp + Ap - Bp) * (Ap + Bp - Cp)) := by
    rw [hPform, hQform, hSform]
    field_simp [ne_of_gt hAp_pos, ne_of_gt hBp_pos, ne_of_gt hCp_pos]
    ring
  have htri_vw : dot v w < rb * rc := by
    have hlag := V3.lagrange v w
    rw [hcross_vw] at hlag
    rw [← hrb2, ← hrc2] at hlag
    have hcv_pos2 := hcv_pos
    rw [hcross_vw] at hcv_pos2
    have hsq : (dot v w)^2 < (rb * rc)^2 := by nlinarith only [hlag, hcv_pos2]
    have habs : |dot v w| < |rb * rc| := sq_lt_sq.mp hsq
    rw [abs_of_pos (mul_pos hrb_pos hrc_pos)] at habs
    exact lt_of_le_of_lt (le_abs_self _) habs
  have htri_wu : dot w u < rc * ra := by
    have hlag := V3.lagrange w u
    rw [hcross_wu] at hlag
    rw [← hrc2, ← hra2] at hlag
    have hcw_pos2 := hcw_pos
    rw [hcross_wu] at hcw_pos2
    have hsq : (dot w u)^2 < (rc * ra)^2 := by nlinarith only [hlag, hcw_pos2]
    have habs : |dot w u| < |rc * ra| := sq_lt_sq.mp hsq
    rw [abs_of_pos (mul_pos hrc_pos hra_pos)] at habs
    exact lt_of_le_of_lt (le_abs_self _) habs
  have htri_uv : dot u v < ra * rb := by
    have hlag := V3.lagrange u v
    rw [hcross_uv] at hlag
    rw [← hra2, ← hrb2] at hlag
    have hcu_pos2 := hcu_pos
    rw [hcross_uv] at hcu_pos2
    have hsq : (dot u v)^2 < (ra * rb)^2 := by nlinarith only [hlag, hcu_pos2]
    have habs : |dot u v| < |ra * rb| := sq_lt_sq.mp hsq
    rw [abs_of_pos (mul_pos hra_pos hrb_pos)] at habs
    exact lt_of_le_of_lt (le_abs_self _) habs
  have hAp_sq : Ap^2 = Bp^2 + Cp^2 + 2 * β * γ * dot v w := by
    have hx' : α * u.x = -(β * v.x + γ * w.x) := by linarith only [hx]
    have hy' : α * u.y = -(β * v.y + γ * w.y) := by linarith only [hy]
    have hz' : α * u.z = -(β * v.z + γ * w.z) := by linarith only [hz]
    have hA2 : Ap^2 = α^2 * dot u u := by
      dsimp [Ap]
      rw [← hra2]
      ring
    have hscaled : α^2 * dot u u = β^2 * dot v v + γ^2 * dot w w + 2 * β * γ * dot v w := by
      calc
        α^2 * dot u u = (α*u.x)^2 + (α*u.y)^2 + (α*u.z)^2 := by simp [dot]; ring
        _ = (β*v.x + γ*w.x)^2 + (β*v.y + γ*w.y)^2 + (β*v.z + γ*w.z)^2 := by
          rw [hx', hy', hz']
          ring
        _ = β^2 * dot v v + γ^2 * dot w w + 2 * β * γ * dot v w := by
          simp [dot]
          ring
    have hB2 : Bp^2 = β^2 * dot v v := by dsimp [Bp]; rw [← hrb2]; ring
    have hC2 : Cp^2 = γ^2 * dot w w := by dsimp [Cp]; rw [← hrc2]; ring
    nlinarith only [hA2, hscaled, hB2, hC2]
  have hBp_sq : Bp^2 = Cp^2 + Ap^2 + 2 * γ * α * dot w u := by
    have hx' : β * v.x = -(γ * w.x + α * u.x) := by linarith only [hx]
    have hy' : β * v.y = -(γ * w.y + α * u.y) := by linarith only [hy]
    have hz' : β * v.z = -(γ * w.z + α * u.z) := by linarith only [hz]
    have hB2 : Bp^2 = β^2 * dot v v := by
      dsimp [Bp]
      rw [← hrb2]
      ring
    have hscaled : β^2 * dot v v = γ^2 * dot w w + α^2 * dot u u + 2 * γ * α * dot w u := by
      calc
        β^2 * dot v v = (β*v.x)^2 + (β*v.y)^2 + (β*v.z)^2 := by simp [dot]; ring
        _ = (γ*w.x + α*u.x)^2 + (γ*w.y + α*u.y)^2 + (γ*w.z + α*u.z)^2 := by
          rw [hx', hy', hz']
          ring
        _ = γ^2 * dot w w + α^2 * dot u u + 2 * γ * α * dot w u := by
          simp [dot]
          ring
    have hC2 : Cp^2 = γ^2 * dot w w := by dsimp [Cp]; rw [← hrc2]; ring
    have hA2 : Ap^2 = α^2 * dot u u := by dsimp [Ap]; rw [← hra2]; ring
    nlinarith only [hB2, hscaled, hC2, hA2]
  have hCp_sq : Cp^2 = Ap^2 + Bp^2 + 2 * α * β * dot u v := by
    have hx' : γ * w.x = -(α * u.x + β * v.x) := by linarith only [hx]
    have hy' : γ * w.y = -(α * u.y + β * v.y) := by linarith only [hy]
    have hz' : γ * w.z = -(α * u.z + β * v.z) := by linarith only [hz]
    have hC2 : Cp^2 = γ^2 * dot w w := by
      dsimp [Cp]
      rw [← hrc2]
      ring
    have hscaled : γ^2 * dot w w = α^2 * dot u u + β^2 * dot v v + 2 * α * β * dot u v := by
      calc
        γ^2 * dot w w = (γ*w.x)^2 + (γ*w.y)^2 + (γ*w.z)^2 := by simp [dot]; ring
        _ = (α*u.x + β*v.x)^2 + (α*u.y + β*v.y)^2 + (α*u.z + β*v.z)^2 := by
          rw [hx', hy', hz']
          ring
        _ = α^2 * dot u u + β^2 * dot v v + 2 * α * β * dot u v := by
          simp [dot]
          ring
    have hA2 : Ap^2 = α^2 * dot u u := by dsimp [Ap]; rw [← hra2]; ring
    have hB2 : Bp^2 = β^2 * dot v v := by dsimp [Bp]; rw [← hrb2]; ring
    nlinarith only [hC2, hscaled, hA2, hB2]
  have hAp_lt : Ap < Bp + Cp := by
    have hs : Ap^2 < (Bp + Cp)^2 := by
      dsimp [Ap, Bp, Cp] at hAp_sq htri_vw ⊢
      have hbgpos : 0 < β * γ := mul_pos hβ hγ
      nlinarith only [hAp_sq, htri_vw, hbgpos]
    have hh := sq_lt_sq.mp hs
    rw [abs_of_pos hAp_pos, abs_of_pos (add_pos hBp_pos hCp_pos)] at hh
    exact hh
  have hBp_lt : Bp < Cp + Ap := by
    have hs : Bp^2 < (Cp + Ap)^2 := by
      dsimp [Bp, Cp, Ap] at hBp_sq htri_wu ⊢
      have hgapos : 0 < γ * α := mul_pos hγ hα
      nlinarith only [hBp_sq, htri_wu, hgapos]
    have hh := sq_lt_sq.mp hs
    rw [abs_of_pos hBp_pos, abs_of_pos (add_pos hCp_pos hAp_pos)] at hh
    exact hh
  have hCp_lt : Cp < Ap + Bp := by
    have hs : Cp^2 < (Ap + Bp)^2 := by
      dsimp [Cp, Ap, Bp] at hCp_sq htri_uv ⊢
      have habpos : 0 < α * β := mul_pos hα hβ
      nlinarith only [hCp_sq, htri_uv, habpos]
    have hh := sq_lt_sq.mp hs
    rw [abs_of_pos hCp_pos, abs_of_pos (add_pos hAp_pos hBp_pos)] at hh
    exact hh
  have hfacpos : 0 < (Bp + Cp - Ap) * (Cp + Ap - Bp) * (Ap + Bp - Cp) := by
    exact mul_pos (mul_pos (by linarith [hAp_lt]) (by linarith [hBp_lt])) (by linarith [hCp_lt])
  have hsum_neg : 1 + P + Q + S < 0 := by
    have hlt : 2 * Ap * Bp * Cp * (1 + P + Q + S) < 0 := by
      rw [hfinal]
      linarith [hfacpos]
    have hcoef : 0 < 2 * Ap * Bp * Cp := by positivity
    nlinarith
  have hPinv : ra * rb * rc * P = dot u v * rc := by
    dsimp [P]
    have hne : ra * rb ≠ 0 := mul_ne_zero (ne_of_gt hra_pos) (ne_of_gt hrb_pos)
    field_simp [hne]
  have hQinv : ra * rb * rc * Q = dot v w * ra := by
    dsimp [Q]
    have hne : rb * rc ≠ 0 := mul_ne_zero (ne_of_gt hrb_pos) (ne_of_gt hrc_pos)
    field_simp [hne]
  have hSinv : ra * rb * rc * S = dot u w * rb := by
    dsimp [S]
    have hne : ra * rc ≠ 0 := mul_ne_zero (ne_of_gt hra_pos) (ne_of_gt hrc_pos)
    field_simp [hne]
  have hsum_eq : ra * rb * rc * (1 + P + Q + S) =
      ra * rb * rc + dot u v * rc + dot v w * ra + dot u w * rb := by
    calc
      ra * rb * rc * (1 + P + Q + S) =
          ra * rb * rc + ra * rb * rc * P + ra * rb * rc * Q + ra * rb * rc * S := by ring
      _ = ra * rb * rc + dot u v * rc + dot v w * ra + dot u w * rb := by
        rw [hPinv, hQinv, hSinv]
  have hfd_eq : faceDen (A, B, C) c =
      ra * rb * rc + dot u v * rc + dot v w * ra + dot u w * rb := by
    dsimp [faceDen, ra, rb, rc, u, v, w, dot]
    ring
  have hfd_eq' : faceDen (A, B, C) c = ra * rb * rc * (1 + P + Q + S) := by
    rw [hfd_eq, hsum_eq]
  rw [hfd_eq']
  exact mul_neg_of_pos_of_neg (mul_pos (mul_pos hra_pos hrb_pos) hrc_pos) hsum_neg

/- ===== Global closed-mesh degree assembly =====

The landed ingredients (norm-filter vanishing, the `±1` single-face jump and
the algebraic bridge `meshWinding_cons_jump`) are now assembled into the
global degree statement. The genuinely geometric part -- choosing a generic
path from far away to `p` that meets the mesh transversally, only in relative
interiors of faces, and only finitely often -- is isolated as the explicit
hypothesis `GenericPathExists`. Everything *downstream* of that hypothesis is
proved unconditionally: the telescoping lemma, the integer-valuedness, the
"equal to a signed crossing count" conclusion, and constancy on complement
components.
-/

/-- The three directed edges of an oriented face, in boundary orientation. -/
def faceEdges (f : Face) : List (V3 × V3) :=
  [(f.1, f.2.1), (f.2.1, f.2.2), (f.2.2, f.1)]

/-- Combinatorial closedness of a finite oriented soup: every directed edge
    also occurs with the opposite orientation. This is the formal counterpart
    of "closed oriented mesh" used in the degree statement. -/
def closedEdges (fs : List Face) : Prop :=
  ∀ f ∈ fs, ∀ u v : V3, (u, v) ∈ faceEdges f →
    ∃ g ∈ fs, (v, u) ∈ faceEdges g

/-- `p` is off every face of the soup (here: not coplanar with any face, which
    is the algebraic shadow of "not on the face"). This is the complement on
    which the degree is defined; it is the first conjunct of `regularSet`. -/
def offFaces (fs : List Face) (p : V3) : Prop :=
  ∀ f ∈ fs, faceNum f p ≠ 0

/-- One crossing of a generic path through the relative interior of a face.
    `before`/`after` are path sample points on either side of the crossing
    and `sign ∈ {+1, -1}` is its oriented contribution. -/
structure Crossing where
  face : Face
  before : V3
  after : V3
  sign : ℤ

/-- The total signed crossing count of a chain. -/
def crossingSum (cs : List Crossing) : ℤ :=
  (cs.map Crossing.sign).sum

/-- A finite generic crossing chain from `a` to `b`. Consecutive sample
    points not separated by a crossing lie on one arc of the complement on
    which the winding number is constant; each crossing contributes exactly
    its sign. The latter premise is discharged by the landed jump theorems
    (`crossing_jump_of_generic_pos` / `crossing_jump_of_generic_neg`, which in
    turn rest on `meshWinding_single_face_crossing_general` and
    `interior_faceDen_neg`). -/
def PathChain (fs : List Face) (a b : V3) : List Crossing → Prop
  | [] => b = a ∨ meshWinding fs b = meshWinding fs a
  | c :: rest =>
      meshWinding fs c.before = meshWinding fs a ∧
        (meshWinding fs c.after - meshWinding fs c.before = (c.sign : ℝ)) ∧
        PathChain fs c.after b rest

/-- Casting an integer crossing sum to `ℝ` distributes over the list sum. -/
lemma crossingSum_cast (cs : List Crossing) :
    (crossingSum cs : ℝ) = (cs.map (Int.cast ∘ Crossing.sign)).sum := by
  induction cs with
  | nil => simp [crossingSum]
  | cons c cs _ => simp [crossingSum]

/-- **Telescoping lemma.** The winding-number change along a finite generic
    crossing chain is exactly the integer sum of its crossing signs. -/
theorem PathChain.sum_eq (fs : List Face) (a b : V3) (cs : List Crossing)
    (h : PathChain fs a b cs) :
    meshWinding fs b - meshWinding fs a = (crossingSum cs : ℝ) := by
  induction cs generalizing a with
  | nil =>
      simp [PathChain, crossingSum] at h ⊢
      rcases h with rfl | h
      · ring
      · linarith
  | cons c rest ih =>
      simp only [PathChain] at h
      rcases h with ⟨hbarc, hcross, hrest⟩
      have hih := ih c.after hrest
      simp [crossingSum]
      rw [← crossingSum_cast rest]
      linarith

/-- **Integer-valuedness from a generic path.** If `cs` is a generic crossing
    chain from a far point `q` (`meshWinding fs q = 0`, justified by
    `meshWinding_tendsto_zero_norm_atTop`) to `p`, then `meshWinding fs p` is
    the integer `crossingSum cs`. -/
theorem winding_eq_crossingSum_of_path (fs : List Face) (p q : V3) (cs : List Crossing)
    (hpath : PathChain fs q p cs) (hfar : meshWinding fs q = 0) :
    ∃ d : ℤ, meshWinding fs p = (d : ℝ) ∧ d = crossingSum cs := by
  have hs := PathChain.sum_eq fs q p cs hpath
  refine ⟨crossingSum cs, ?_, rfl⟩
  linarith

/-- Negation of a vector (used to reverse a crossing direction; `V3` has no
    `Neg` instance). -/
def negV3 (v : V3) : V3 := ⟨-v.x, -v.y, -v.z⟩

lemma dot_negV3_right (a v : V3) : dot a (negV3 v) = - dot a v := by
  simp [negV3, dot]
  ring

lemma along_negV3 (c nn : V3) (ε : ℝ) : along c (negV3 nn) ε = along c nn (-ε) := by
  apply V3.ext <;> simp [along, negV3]

set_option maxHeartbeats 800000 in
/-- **Exact `−1` jump for a positively oriented interior crossing.** The
    landed theorem `meshWinding_single_face_crossing_general` gives the
    *limit* of the jump as `-1`; if the winding number is constant on each
    side near the crossing (hypotheses `hb`, `ha` -- the local form of
    "constant on a complement component"), the jump at the sample points is
    exactly `-1`. -/
theorem crossing_jump_of_generic_pos
    (f : Face) (rest : List Face) (c nn : V3)
    (hplane : faceNum f c = 0) (hden : faceDen f c < 0)
    (hN : 0 < dot (orientationNormal f) nn)
    (hrest : ∀ g ∈ rest, faceNum g c ≠ 0 ∧ faceDen g c ≠ 0)
    (before after : V3)
    (hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      meshWinding (f :: rest) (along c nn (-ε)) = meshWinding (f :: rest) before)
    (ha : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      meshWinding (f :: rest) (along c nn ε) = meshWinding (f :: rest) after) :
    meshWinding (f :: rest) after - meshWinding (f :: rest) before = (-1 : ℝ) := by
  have hlim := meshWinding_single_face_crossing_general f rest c nn hplane hden hN hrest
  have hev : (fun ε : ℝ =>
      meshWinding (f :: rest) (along c nn ε) - meshWinding (f :: rest) (along c nn (-ε)))
      =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ : ℝ => meshWinding (f :: rest) after - meshWinding (f :: rest) before) := by
    filter_upwards [hb, ha] with ε hbε haε
    linarith
  have hconstlim : Tendsto (fun _ : ℝ =>
      meshWinding (f :: rest) after - meshWinding (f :: rest) before)
      (𝓝[>] (0 : ℝ))
      (𝓝 (meshWinding (f :: rest) after - meshWinding (f :: rest) before)) :=
    tendsto_const_nhds
  have hlimconst : Tendsto (fun _ : ℝ =>
      meshWinding (f :: rest) after - meshWinding (f :: rest) before)
      (𝓝[>] (0 : ℝ)) (𝓝 (-1 : ℝ)) := hlim.congr' hev
  exact tendsto_nhds_unique hconstlim hlimconst

set_option maxHeartbeats 800000 in
/-- The matching `+1` jump for a crossing whose direction is opposite to the
    orientation normal. It follows from the positive case by reversing the
    crossing direction. -/
theorem crossing_jump_of_generic_neg
    (f : Face) (rest : List Face) (c nn : V3)
    (hplane : faceNum f c = 0) (hden : faceDen f c < 0)
    (hN : dot (orientationNormal f) nn < 0)
    (hrest : ∀ g ∈ rest, faceNum g c ≠ 0 ∧ faceDen g c ≠ 0)
    (before after : V3)
    (hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      meshWinding (f :: rest) (along c nn (-ε)) = meshWinding (f :: rest) before)
    (ha : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      meshWinding (f :: rest) (along c nn ε) = meshWinding (f :: rest) after) :
    meshWinding (f :: rest) after - meshWinding (f :: rest) before = (1 : ℝ) := by
  have hNpos : 0 < dot (orientationNormal f) (negV3 nn) := by
    rw [dot_negV3_right]
    linarith
  have hb' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      meshWinding (f :: rest) (along c (negV3 nn) (-ε)) =
        meshWinding (f :: rest) after := by
    filter_upwards [ha] with ε hε
    rw [along_negV3]
    simpa using hε
  have ha' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      meshWinding (f :: rest) (along c (negV3 nn) ε) =
        meshWinding (f :: rest) before := by
    filter_upwards [hb] with ε hε
    rw [along_negV3]
    exact hε
  have h := crossing_jump_of_generic_pos f rest c (negV3 nn) hplane hden hNpos hrest
    after before hb' ha'
  linarith

set_option maxHeartbeats 800000 in
/-- An affine (barycentric) point of a face is coplanar with it:
    `faceNum f c = 0`. This supplies the `hplane` premise of the jump
    theorems when the crossing point is in the relative interior. -/
lemma faceNum_eq_zero_of_barycentric (f : Face) (c : V3)
    (α β γ : ℝ) (hsum : α + β + γ = 1)
    (hc : c = ⟨α * f.1.x + β * f.2.1.x + γ * f.2.2.x,
               α * f.1.y + β * f.2.1.y + γ * f.2.2.y,
               α * f.1.z + β * f.2.1.z + γ * f.2.2.z⟩) :
    faceNum f c = 0 := by
  rcases f with ⟨A, B, C⟩
  dsimp at hc
  rw [hc]
  have hγe : γ = 1 - α - β := by linarith
  rw [hγe]
  rw [faceNum, triple, Matrix.det_fin_three]
  simp [cols, sub]
  ring_nf

set_option maxHeartbeats 800000 in
/-- **Interior crossing, exact `−1`.** For a crossing point in the relative
    interior of a nondegenerate face and a positively oriented crossing
    direction, the exact `−1` jump follows from the landed
    `interior_faceDen_neg` and `meshWinding_single_face_crossing_general`
    (the residual hypotheses `hb`, `ha` are local constancy of the winding
    number on the two arcs of the path). -/
theorem interior_crossing_jump_minus_one
    (f : Face) (rest : List Face) (c nn : V3)
    (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hsum : α + β + γ = 1)
    (hc : c = ⟨α * f.1.x + β * f.2.1.x + γ * f.2.2.x,
               α * f.1.y + β * f.2.1.y + γ * f.2.2.y,
               α * f.1.z + β * f.2.1.z + γ * f.2.2.z⟩)
    (hnd : 0 < dot (orientationNormal f) (orientationNormal f))
    (hN : 0 < dot (orientationNormal f) nn)
    (hrest : ∀ g ∈ rest, faceNum g c ≠ 0 ∧ faceDen g c ≠ 0)
    (before after : V3)
    (hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      meshWinding (f :: rest) (along c nn (-ε)) = meshWinding (f :: rest) before)
    (ha : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      meshWinding (f :: rest) (along c nn ε) = meshWinding (f :: rest) after) :
    meshWinding (f :: rest) after - meshWinding (f :: rest) before = (-1 : ℝ) := by
  have hplane := faceNum_eq_zero_of_barycentric f c α β γ hsum hc
  have hden := interior_faceDen_neg f c α β γ hα hβ hγ hsum hc hnd
  exact crossing_jump_of_generic_pos f rest c nn hplane hden hN hrest before after hb ha

/-- **The remaining geometric wall, isolated as an explicit hypothesis.**
    For `p` off every face, there is a far point `q` (winding number `0`) and
    a finite generic crossing chain from `q` to `p`. Its geometric content --
    a ray from far away meeting the triangles transversally, only in the
    relative interiors of faces, at finitely many points -- is *not* claimed
    here; it is supplied as a premise by the global theorem below. For a
    combinatorially closed oriented mesh this is the standard ray-casting
    picture; closedness is what rules out crossings at dangling boundary
    edges, and `meshWinding_tendsto_zero_norm_atTop` supplies the far value. -/
def GenericPathExists (fs : List Face) (p : V3) : Prop :=
  ∃ (q : V3) (cs : List Crossing),
    PathChain fs q p cs ∧ meshWinding fs q = 0

/-- **Global closed-mesh degree assembly (conditional on the geometric path
    hypothesis).** For a finite combinatorially closed oriented mesh and a
    point `p` off every face, if every such point admits a generic crossing
    chain from far away, then `meshWinding fs p` is an integer, and it is
    constant on every preconnected piece of the regular set (the complement
    of the mesh where every face is regular). -/
theorem closedMesh_winding_degree
    (fs : List Face) (hclosed : closedEdges fs)
    (p : V3) (hoff : offFaces fs p)
    (hgen : ∀ x : V3, offFaces fs x → GenericPathExists fs x)
    (s : Set V3) (hs : IsPreconnected s) (hsub : s ⊆ regularSet fs) :
    (∃ d : ℤ, meshWinding fs p = (d : ℝ)) ∧
      (∀ {x y : V3}, x ∈ s → y ∈ s → meshWinding fs x = meshWinding fs y) := by
  have _ := hclosed
  have hint : ∀ x ∈ s, ∃ d : ℤ, meshWinding fs x = (d : ℝ) := by
    intro x hx
    have hoffx : offFaces fs x := by
      intro f hf
      exact (hsub hx f hf).1
    rcases hgen x hoffx with ⟨q, cs, hpath, hfar⟩
    rcases winding_eq_crossingSum_of_path fs x q cs hpath hfar with ⟨d, hd, _⟩
    exact ⟨d, hd⟩
  have hpint : ∃ d : ℤ, meshWinding fs p = (d : ℝ) := by
    rcases hgen p hoff with ⟨q, cs, hpath, hfar⟩
    rcases winding_eq_crossingSum_of_path fs p q cs hpath hfar with ⟨d, hd, _⟩
    exact ⟨d, hd⟩
  have hcont : ContinuousOn (meshWinding fs) s := by
    intro z hz
    exact (continuousAt_meshWinding_of_generic fs z (hsub hz)).continuousWithinAt
  refine ⟨hpint, ?_⟩
  intro x y hx hy
  exact meshWinding_const_of_integer_on_preconnected fs s hs hcont hint hx hy

/-- Explicit form of "the winding number at `p` equals the signed crossing
    count along a path from infinity to `p`": the far point and the chain are
    produced by the generic-path hypothesis and the value is their
    `crossingSum`. -/
theorem closedMesh_winding_eq_crossingSum
    (fs : List Face) (p : V3) (hgenp : GenericPathExists fs p) :
    ∃ (q : V3) (cs : List Crossing),
      PathChain fs q p cs ∧ meshWinding fs q = 0 ∧
        meshWinding fs p = (crossingSum cs : ℝ) := by
  rcases hgenp with ⟨q, cs, hpath, hfar⟩
  refine ⟨q, cs, hpath, hfar, ?_⟩
  have hs := PathChain.sum_eq fs q p cs hpath
  linarith

/- ===== Rigorous sub-steps toward `GenericPathExists` =====

The ray-casting construction behind `GenericPathExists` (a far point of
winding `0` joined to `p` by a transversal chain meeting faces only in their
relative interiors) is not attempted in full here. What is proved in this
block is the part that is independent of any genericity choice:

  * along a fixed line `t ↦ along p d t`, each face of the soup is coplanar
    with the query point at **at most one** parameter (the line is not
    contained in the face plane because `p` is off every face); consequently
    the set of crossing parameters of a finite soup is finite and is contained
    in an explicit finite set of candidates, one per face;
  * the trivial closed subclass `fs ++ fs.map flipFace` (a soup together with
    its reverse) is combinatorially closed and admits `GenericPathExists`
    unconditionally, since its winding number is identically `0`.

These isolate two of the walls listed above as named, proved statements; the
remaining geometric choices are documented after `genericPathExists_face_cancel`.
-/

/-- The line parameterisation through `p` at parameter `0`. -/
lemma along_zero (p d : V3) : along p d 0 = p := by
  apply V3.ext <;> simp [along]

/-- The segment `t ↦ along p (sub q p) t` reaches `q` at parameter `1`. -/
lemma along_one_sub (p q : V3) : along p (sub q p) 1 = q := by
  apply V3.ext <;> simp [along, sub]

/-- The unique parameter at which the line through `p` in direction `d` can
    meet the plane of `f` (defined even when `d` is parallel to the plane). -/
def faceCrossingParam (f : Face) (p d : V3) : ℝ :=
  faceNum f p / dot (orientationNormal f) d

set_option maxHeartbeats 800000 in
/-- When the direction is not parallel to the face plane, the crossing
    parameter is uniquely determined: `faceNum f (along p d t) = 0 ↔ t =
    faceCrossingParam f p d`. This is the algebraic core of "each face is
    crossed at most once". -/
lemma faceNum_along_eq_zero_iff_crossingParam (f : Face) (p d : V3)
    (hperp : dot (orientationNormal f) d ≠ 0) (t : ℝ) :
    faceNum f (along p d t) = 0 ↔ t = faceCrossingParam f p d := by
  rw [faceNum_along]
  unfold faceCrossingParam
  constructor
  · intro h
    have hEq : faceNum f p = t * dot (orientationNormal f) d := by linarith
    field_simp [hperp]
    linarith
  · intro h
    rw [h]
    field_simp [hperp]
    ring

/-- If `d` is parallel to the plane of `f` and `p` is off that plane, then the
    entire line misses the plane: no crossing at any parameter. -/
lemma faceNum_along_ne_zero_of_parallel (f : Face) (p d : V3)
    (hp : faceNum f p ≠ 0) (hpar : dot (orientationNormal f) d = 0) (t : ℝ) :
    faceNum f (along p d t) ≠ 0 := by
  rw [faceNum_along, hpar]
  simpa using hp

/-- The set of parameters along the line `t ↦ along p d t` at which some face
    of the finite soup `fs` is coplanar with the query point. These are the
    candidate crossing parameters of a ray/segment cast from `p`. -/
def crossingParams (fs : List Face) (p d : V3) : Set ℝ :=
  {t | ∃ f ∈ fs, faceNum f (along p d t) = 0}

set_option maxHeartbeats 800000 in
/-- **Finiteness of crossings for one face.** A single face contributes at
    most one crossing parameter: it is the singleton `{faceCrossingParam f p d}`
    when the line is not parallel to the face plane, and the empty set when it
    is (since `p` is off the face). -/
lemma face_crossingSet_finite (f : Face) (p d : V3) (hp : faceNum f p ≠ 0) :
    ({t : ℝ | faceNum f (along p d t) = 0}).Finite := by
  by_cases hperp : dot (orientationNormal f) d = 0
  · have hempty : {t : ℝ | faceNum f (along p d t) = 0} = (∅ : Set ℝ) := by
      ext t
      simp [faceNum_along_ne_zero_of_parallel f p d hp hperp t]
    rw [hempty]
    exact Set.finite_empty
  · have heq : {t : ℝ | faceNum f (along p d t) = 0} =
        ({faceCrossingParam f p d} : Set ℝ) := by
      ext t
      change (faceNum f (along p d t) = 0) ↔ t = faceCrossingParam f p d
      exact faceNum_along_eq_zero_iff_crossingParam f p d hperp t
    rw [heq]
    exact Set.finite_singleton _

set_option maxHeartbeats 800000 in
/-- **Finiteness of crossings for a finite soup.** For `p` off every face,
    `crossingParams fs p d` is a finite subset of `ℝ`, with at most
    `fs.length` elements. This is the exact finiteness wall isolated above. -/
lemma crossingParams_finite (fs : List Face) (p d : V3) (hoff : offFaces fs p) :
    (crossingParams fs p d).Finite := by
  revert hoff
  induction fs with
  | nil =>
      intro hoff
      simp [crossingParams]
  | cons f fs ih =>
      intro hoff
      have hf : faceNum f p ≠ 0 := hoff f (by simp)
      have hrs : offFaces fs p := by intro g hg; exact hoff g (by simp [hg])
      have hfinf := face_crossingSet_finite f p d hf
      have hfinr := ih hrs
      rw [show crossingParams (f :: fs) p d =
          {t : ℝ | faceNum f (along p d t) = 0} ∪ crossingParams fs p d by
            ext t
            simp [crossingParams]]
      exact hfinf.union hfinr

set_option maxHeartbeats 800000 in
/-- An explicit finite superset of the crossing parameters: the image of the
    finite face list under `faceCrossingParam`. -/
lemma crossingParams_subset_candidates (fs : List Face) (p d : V3)
    (hoff : offFaces fs p) :
    crossingParams fs p d ⊆ (fun f : Face => faceCrossingParam f p d) '' ({g : Face | g ∈ fs} : Set Face) := by
  intro t ht
  rcases ht with ⟨f, hf, hzero⟩
  refine ⟨f, hf, ?_⟩
  by_cases hperp : dot (orientationNormal f) d = 0
  · exact False.elim (faceNum_along_ne_zero_of_parallel f p d (hoff f hf) hperp t hzero)
  · exact ((faceNum_along_eq_zero_iff_crossingParam f p d hperp t).mp hzero).symm

/-- Restricting to the open segment `(0,1)` preserves finiteness: a finite
    soup has finitely many crossings on any bounded segment. -/
lemma segmentCrossingParams_finite (fs : List Face) (p q : V3) (hoff : offFaces fs p) :
    (crossingParams fs p (sub q p) ∩ Set.Ioo 0 1).Finite :=
  (crossingParams_finite fs p (sub q p) hoff).subset (by intro t ht; exact ht.1)

/-- The empty soup is combinatorially closed. -/
theorem closedEdges_empty : closedEdges ([] : List Face) := by
  intro f hf
  simp at hf

/-- Flipping twice returns the original face. -/
lemma flipFace_flipFace (f : Face) : flipFace (flipFace f) = f := by
  rcases f with ⟨A, B, C⟩
  rfl

set_option maxHeartbeats 800000 in
/-- Reversing the orientation of a face also reverses each of its directed
    edges (which is what combinatorial closedness needs). -/
lemma faceEdges_flipFace (f : Face) (u v : V3) (h : (u, v) ∈ faceEdges f) :
    (v, u) ∈ faceEdges (flipFace f) := by
  rcases f with ⟨A, B, C⟩
  simp [faceEdges, flipFace] at h ⊢
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

set_option maxHeartbeats 800000 in
/-- A soup together with its reverse is combinatorially closed. -/
theorem closedEdges_face_cancel (fs : List Face) : closedEdges (fs ++ fs.map flipFace) := by
  intro f hf u v huv
  rcases List.mem_append.mp hf with hf | hf
  · refine ⟨flipFace f, ?_, ?_⟩
    · rw [List.mem_append]
      exact Or.inr (List.mem_map.mpr ⟨f, hf, rfl⟩)
    exact faceEdges_flipFace f u v huv
  · rcases List.mem_map.mp hf with ⟨g, hg, rfl⟩
    refine ⟨g, by simp [hg], ?_⟩
    have h := faceEdges_flipFace (flipFace g) u v huv
    simpa [flipFace_flipFace] using h

/-- **Subclass (empty mesh).** The empty soup has winding `0` everywhere, so
    the empty chain from `p` to itself witnesses `GenericPathExists`. -/
theorem genericPathExists_empty (p : V3) : GenericPathExists [] p := by
  refine ⟨p, [], ?_, ?_⟩
  · simp [PathChain]
  · exact meshWinding_empty p

/-- **Subclass (soup plus its reverse).** For a combinatorially closed mesh of
    the form `fs ++ fs.map flipFace`, `meshWinding_face_cancel` gives winding
    `0` at every point off the faces, so the empty chain witnesses
    `GenericPathExists` unconditionally. This is a genuine (degree-zero)
    closed-mesh subclass, not the empty soup. -/
theorem genericPathExists_face_cancel (fs : List Face) (p : V3)
    (hoff : ∀ f ∈ fs, faceNum f p ≠ 0) :
    GenericPathExists (fs ++ fs.map flipFace) p := by
  refine ⟨p, [], ?_, ?_⟩
  · simp [PathChain]
  · exact meshWinding_face_cancel fs p hoff

/- What remains for the fully general `GenericPathExists` (and is NOT claimed
   here) is the choice of the far point and the ordering of the crossings:

   1. a far point `q` with `meshWinding fs q = 0` exactly (the far-field
      theorem gives only a limit `→ 0`; exact vanishing is the very degree
      statement being proved);
   2. a direction `d` (equivalently a perturbation of the ray) avoiding all
      edges of all faces, so that every crossing lies in a face's relative
      interior and no two crossings share a parameter;
   3. assembling the finitely many parameters of `crossingParams` (whose
      finiteness is proved above) in increasing order and discharging each
      sign with `interior_crossing_jump_minus_one` /
      `crossing_jump_of_generic_neg`, with local constancy of `meshWinding`
      on the arcs between consecutive crossings.

   Items 1--3 are precisely the geometric ray-casting content that
   `GenericPathExists` packages as a hypothesis. -/

/- ===== Exact zero at a shared exterior point (structural tier) =====

The norm-filter far-field theorem gives only a *limit* `meshWinding fs p → 0`;
upgrading that to an exact zero at a far point would (for a general mesh) need
integer-valuedness, which is the degree statement being proved. The tier proved
here takes the independent structural route instead: at a query point `q` that
is coplanar with every face of the soup and lies outside every face's
circumcircle, the Van Oosterom numerator is `0` and the denominator is positive,
so `atan2'(0, den) = 0` and every solid angle — hence the whole winding number —
is *exactly* `0`, with no limit and no degree theory involved. This covers any
single nondegenerate triangle and any soup of faces admitting a common such
exterior point (in particular a coplanar soup with a far exterior point). -/

set_option maxHeartbeats 800000 in
/-- A single face's solid angle is exactly `0` at a coplanar query point
    outside its circumcircle. This is the exact counterpart of the far-field
    limit: numerator `0` plus positive denominator kills `atan2'` outright. -/
theorem solidAngle_eq_zero_of_coplanar_of_den_pos (f : Face) (q : V3)
    (hnum : faceNum f q = 0) (hden : 0 < faceDen f q) :
    solidAngle f.1 f.2.1 f.2.2 q = 0 := by
  rw [solidAngle_eq_face, hnum]
  simp [atan2', hden]

set_option maxHeartbeats 800000 in
/-- A finite soup whose faces share a coplanar outside point has winding number
    **exactly** `0` there. This is the structural exact-far-value tier: it
    supplies the `hfar = 0` premise of the degree-reduction theorems without a
    limit argument. -/
theorem meshWinding_eq_zero_of_common_exterior_point (fs : List Face) (q : V3)
    (h : ∀ f ∈ fs, faceNum f q = 0 ∧ 0 < faceDen f q) :
    meshWinding fs q = 0 := by
  have hsum : (fs.map fun f => solidAngle f.1 f.2.1 f.2.2 q).sum = 0 := by
    induction fs with
    | nil => simp
    | cons f fs ih =>
        have hf := h f (by simp)
        have hrs : ∀ g ∈ fs, faceNum g q = 0 ∧ 0 < faceDen g q := by
          intro g hg
          exact h g (by simp [hg])
        simp only [List.map_cons, List.sum_cons]
        rw [solidAngle_eq_zero_of_coplanar_of_den_pos f q hf.1 hf.2, ih hrs]
        ring
  rw [meshWinding, hsum]
  simp

set_option maxHeartbeats 800000 in
/-- The canonical face is coplanar with `(t, t, 0)` for every `t`. -/
lemma jumpFace_num_at (t : ℝ) : faceNum jumpFace (⟨t, t, 0⟩ : V3) = 0 := by
  rw [faceNum, triple, Matrix.det_fin_three]
  simp [jumpFace, jumpA, jumpB, jumpC, sub]

set_option maxHeartbeats 800000 in
/-- For `t > 1` the point `(t, t, 0)` lies in the canonical face's plane and
    outside its circumcircle: every pairwise dot product of the three vectors
    from the query point to the vertices is strictly positive, so the Van
    Oosterom denominator is strictly positive. -/
lemma jumpFace_den_pos_at (t : ℝ) (ht : 1 < t) :
    0 < faceDen jumpFace (⟨t, t, 0⟩ : V3) := by
  let q : V3 := ⟨t, t, 0⟩
  have ht0 : 0 < t := by linarith
  change 0 <
    Real.sqrt (dot (sub jumpA q) (sub jumpA q)) *
        Real.sqrt (dot (sub jumpB q) (sub jumpB q)) *
          Real.sqrt (dot (sub jumpC q) (sub jumpC q))
      + dot (sub jumpA q) (sub jumpB q) * Real.sqrt (dot (sub jumpC q) (sub jumpC q))
      + dot (sub jumpB q) (sub jumpC q) * Real.sqrt (dot (sub jumpA q) (sub jumpA q))
      + dot (sub jumpC q) (sub jumpA q) * Real.sqrt (dot (sub jumpB q) (sub jumpB q))
  have hAA : 0 < dot (sub jumpA q) (sub jumpA q) := by
    simp [jumpA, q, sub, dot]
    nlinarith [sq_pos_of_pos ht0]
  have hBB : 0 < dot (sub jumpB q) (sub jumpB q) := by
    simp [jumpB, q, sub, dot]
    nlinarith [sq_nonneg (1 - t), sq_pos_of_pos ht0]
  have hCC : 0 < dot (sub jumpC q) (sub jumpC q) := by
    simp [jumpC, q, sub, dot]
    nlinarith [sq_nonneg (1 - t), sq_pos_of_pos ht0]
  have hAB : 0 < dot (sub jumpA q) (sub jumpB q) := by
    simp [jumpA, jumpB, q, sub, dot]
    have hpos : 0 < t * (2 * t - 1) := mul_pos ht0 (by linarith)
    nlinarith
  have hBC : 0 < dot (sub jumpB q) (sub jumpC q) := by
    simp [jumpB, jumpC, q, sub, dot]
    have hpos : 0 < 2 * t * (t - 1) := mul_pos (mul_pos (by norm_num) ht0) (by linarith)
    nlinarith
  have hCA : 0 < dot (sub jumpC q) (sub jumpA q) := by
    simp [jumpC, jumpA, q, sub, dot]
    have hpos : 0 < t * (2 * t - 1) := mul_pos ht0 (by linarith)
    nlinarith
  have hsA : 0 < Real.sqrt (dot (sub jumpA q) (sub jumpA q)) := Real.sqrt_pos.2 hAA
  have hsB : 0 < Real.sqrt (dot (sub jumpB q) (sub jumpB q)) := Real.sqrt_pos.2 hBB
  have hsC : 0 < Real.sqrt (dot (sub jumpC q) (sub jumpC q)) := Real.sqrt_pos.2 hCC
  nlinarith [mul_pos (mul_pos hsA hsB) hsC, mul_pos hAB hsC, mul_pos hBC hsA, mul_pos hCA hsB]

set_option maxHeartbeats 800000 in
/-- **Unconditional exact far value for a concrete soup.** The canonical
    oriented triangle has winding number exactly `0` at the arbitrarily far
    point `(t, t, 0)` (`t > 1`) — no limit, no degree theory. -/
theorem meshWinding_jumpFace_eq_zero_far (t : ℝ) (ht : 1 < t) :
    meshWinding [jumpFace] (⟨t, t, 0⟩ : V3) = 0 := by
  apply meshWinding_eq_zero_of_common_exterior_point
  intro f hf
  have hf' : f = jumpFace := by simpa using hf
  subst f
  exact ⟨jumpFace_num_at t, jumpFace_den_pos_at t ht⟩

set_option maxHeartbeats 800000 in
/-- The canonical triangle soup at such a far point itself witnesses
    `GenericPathExists` (the empty chain suffices, since the far point is the
    endpoint and its winding is already exactly `0`). -/
theorem genericPathExists_jumpFace_far (t : ℝ) (ht : 1 < t) :
    GenericPathExists [jumpFace] (⟨t, t, 0⟩ : V3) := by
  refine ⟨⟨t, t, 0⟩, [], ?_, ?_⟩
  · simp [PathChain]
  · exact meshWinding_jumpFace_eq_zero_far t ht

/- **Why the fully general exact-far-point remains open.** For an arbitrary
   finite soup there is in general no single point coplanar with all faces and
   outside all circumcircles, so the structural tier does not apply. The only
   other known route is: winding is integer-valued off the mesh (degree theory)
   and `meshWinding → 0` at infinity, so a far point has `|winding| < 1/2` and,
   being an integer, is `0`. But integer-valuedness is precisely the conclusion
   of `closedMesh_winding_degree`, which *assumes* the exact far value through
   `GenericPathExists` — that is the circularity. Breaking it requires either
   an independent integrality proof (Gauss-map/holonomy degree) or the generic
   ray-casting construction; neither is landed here. What *is* unconditional is
   exact vanishing for every soup admitting a shared coplanar exterior point
   (`meshWinding_eq_zero_of_common_exterior_point`), instantiated above for the
   canonical triangle family. -/

/- ===== Generic direction avoidance (algebraic tier) =====

This block lands the direction-existence step of generic ray casting. It is
fully rigorous: a finite list of nonzero linear functionals on `V3` is avoided
by one member of an explicit finite family of directions (the affine moment
curve `t ↦ (1, t, t²)`, with `t` a natural number), via a product-polynomial
degree argument. The three geometric degeneracies of a ray cast -- parallel to
a face plane, two crossing parameters coinciding, a crossing on a face edge --
are such functionals, so a single direction avoids them all. -/

open Polynomial

def quadPoly (a b c : ℝ) : ℝ[X] := C a + C b * X + C c * X ^ 2
lemma quadPoly_eval (a b c t : ℝ) : (quadPoly a b c).eval t = a + b * t + c * t ^ 2 := by simp [quadPoly]
lemma quadPoly_eq_zero_iff (a b c : ℝ) : quadPoly a b c = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun p : ℝ[X] => p.coeff 0) h
    have h1 := congrArg (fun p : ℝ[X] => p.coeff 1) h
    have h2 := congrArg (fun p : ℝ[X] => p.coeff 2) h
    simp [quadPoly] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp [quadPoly]
lemma quadPoly_natDegree_le (a b c : ℝ) : (quadPoly a b c).natDegree ≤ 2 := by
  rw [quadPoly]; compute_degree

def momentDir (t : ℝ) : V3 := ⟨1, t, t ^ 2⟩
def dirPoly (w : V3) : ℝ[X] := quadPoly w.x w.y w.z
lemma dirPoly_eval (w : V3) (t : ℝ) : (dirPoly w).eval t = dot w (momentDir t) := by
  rw [dirPoly, quadPoly_eval]
  simp [momentDir, dot]
lemma dirPoly_ne_zero (w : V3) (hw : w ≠ ⟨0,0,0⟩) : dirPoly w ≠ 0 := by
  intro h
  have hc := (quadPoly_eq_zero_iff w.x w.y w.z).mp h
  rcases hc with ⟨hx, hy, hz⟩
  apply hw
  apply V3.ext <;> assumption
lemma dirPoly_natDegree_le (w : V3) : (dirPoly w).natDegree ≤ 2 := by
  exact quadPoly_natDegree_le w.x w.y w.z

set_option maxHeartbeats 800000 in
lemma exists_momentDir_avoid (ws : List V3) (hnz : ∀ w ∈ ws, w ≠ ⟨0,0,0⟩) :
    ∃ k : ℕ, k < 2 * ws.length + 1 ∧ ∀ w ∈ ws, dot w (momentDir (k : ℝ)) ≠ 0 := by
  classical
  let P : ℝ[X] := ∏ i : Fin ws.length, dirPoly (ws.get i)
  have hPnz : P ≠ 0 := by
    dsimp [P]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact dirPoly_ne_zero (ws.get i) (hnz (ws.get i) (List.get_mem ws i))
  have hdeg : P.natDegree ≤ 2 * ws.length := by
    dsimp [P]
    calc
      (∏ i : Fin ws.length, dirPoly (ws.get i)).natDegree
          ≤ ∑ i ∈ (Finset.univ : Finset (Fin ws.length)), (dirPoly (ws.get i)).natDegree :=
            Polynomial.natDegree_prod_le (Finset.univ) (fun i : Fin ws.length => dirPoly (ws.get i))
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin ws.length)), 2 := by
            apply Finset.sum_le_sum
            intro i hi
            exact dirPoly_natDegree_le (ws.get i)
      _ = 2 * ws.length := by simp; omega
  by_contra hno
  push Not at hno
  have hinj : Function.Injective (fun i : Fin (2 * ws.length + 1) => (i : ℝ)) := by
    intro i j h
    apply Fin.ext
    exact Nat.cast_injective h
  have hPzero : P = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (f := fun i : Fin (2 * ws.length + 1) => (i : ℝ)) hinj
    · intro i
      dsimp [P]
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero_iff.mpr
      rcases hno i.val i.isLt with ⟨w, hw, hzero⟩
      rcases List.get_of_mem hw with ⟨j, rfl⟩
      refine ⟨j, Finset.mem_univ _, ?_⟩
      rw [dirPoly_eval]
      exact hzero
    · simpa using (lt_of_le_of_lt hdeg (by omega : 2 * ws.length < 2 * ws.length + 1))
  exact hPnz hPzero

/-- Bad vector: two faces cross at the same parameter. -/
def badCoincideVec (f g : Face) (p : V3) : V3 :=
  let nf := orientationNormal f
  let ng := orientationNormal g
  ⟨ faceNum f p * ng.x - faceNum g p * nf.x,
    faceNum f p * ng.y - faceNum g p * nf.y,
    faceNum f p * ng.z - faceNum g p * nf.z ⟩

lemma dot_badCoincideVec (f g : Face) (p d : V3) :
    dot (badCoincideVec f g p) d =
      faceNum f p * dot (orientationNormal g) d - faceNum g p * dot (orientationNormal f) d := by
  simp [badCoincideVec, dot]
  ring

set_option maxHeartbeats 800000 in
lemma badCoincideVec_ne_zero (f g : Face) (p : V3)
    (hf : faceNum f p ≠ 0)
    (hpar : cross (orientationNormal f) (orientationNormal g) ≠ ⟨0,0,0⟩) :
    badCoincideVec f g p ≠ ⟨0,0,0⟩ := by
  intro hz
  have hx := congrArg V3.x hz
  have hy := congrArg V3.y hz
  have hz' := congrArg V3.z hz
  simp [badCoincideVec] at hx hy hz'
  apply hpar
  apply V3.ext <;> simp [cross]
  · have : faceNum f p * ((orientationNormal f).y * (orientationNormal g).z - (orientationNormal f).z * (orientationNormal g).y) = 0 := by
      calc
        faceNum f p * ((orientationNormal f).y * (orientationNormal g).z - (orientationNormal f).z * (orientationNormal g).y)
            = (orientationNormal f).y * (faceNum f p * (orientationNormal g).z - faceNum g p * (orientationNormal f).z)
              - (orientationNormal f).z * (faceNum f p * (orientationNormal g).y - faceNum g p * (orientationNormal f).y) := by ring
        _ = 0 := by rw [hz', hy]; ring
    exact (mul_eq_zero.mp this).resolve_left hf
  · have : faceNum f p * ((orientationNormal f).z * (orientationNormal g).x - (orientationNormal f).x * (orientationNormal g).z) = 0 := by
      calc
        faceNum f p * ((orientationNormal f).z * (orientationNormal g).x - (orientationNormal f).x * (orientationNormal g).z)
            = (orientationNormal f).z * (faceNum f p * (orientationNormal g).x - faceNum g p * (orientationNormal f).x)
              - (orientationNormal f).x * (faceNum f p * (orientationNormal g).z - faceNum g p * (orientationNormal f).z) := by ring
        _ = 0 := by rw [hx, hz']; ring
    exact (mul_eq_zero.mp this).resolve_left hf
  · have : faceNum f p * ((orientationNormal f).x * (orientationNormal g).y - (orientationNormal f).y * (orientationNormal g).x) = 0 := by
      calc
        faceNum f p * ((orientationNormal f).x * (orientationNormal g).y - (orientationNormal f).y * (orientationNormal g).x)
            = (orientationNormal f).x * (faceNum f p * (orientationNormal g).y - faceNum g p * (orientationNormal f).y)
              - (orientationNormal f).y * (faceNum f p * (orientationNormal g).x - faceNum g p * (orientationNormal f).x) := by ring
        _ = 0 := by rw [hy, hx]; ring
    exact (mul_eq_zero.mp this).resolve_left hf

/-- Bad vector: the crossing of face `f` with edge `(u,v)`. -/
def badEdgeVec (f : Face) (u v : V3) (p : V3) : V3 :=
  let n := orientationNormal f
  let e := sub v u
  let K := triple n (sub p u) e
  let α := faceNum f p
  let ce := cross e n
  ⟨ K * n.x + α * ce.x, K * n.y + α * ce.y, K * n.z + α * ce.z ⟩

set_option maxHeartbeats 800000 in
lemma dot_badEdgeVec (f : Face) (u v p d : V3) :
    dot (badEdgeVec f u v p) d =
      dot (orientationNormal f) d * triple (orientationNormal f) (sub p u) (sub v u)
        + faceNum f p * dot (cross (sub v u) (orientationNormal f)) d := by
  simp [badEdgeVec, dot, triple_eq_dot_cross]
  ring

lemma dot_cross_cyclic' (a b c : V3) : dot (cross a b) c = dot b (cross c a) := by
  simp [dot, cross]
  ring

set_option maxHeartbeats 800000 in
lemma dot_cross_sub_along (f : Face) (u v p d : V3) (s : ℝ) :
    dot (orientationNormal f) (cross (sub (along p d s) u) (sub v u)) =
      triple (orientationNormal f) (sub p u) (sub v u) +
        s * dot (orientationNormal f) (cross d (sub v u)) := by
  simp [along, cross, sub, dot, triple_eq_dot_cross]
  ring

set_option maxHeartbeats 800000 in
lemma dot_badEdgeVec_eq (f : Face) (u v p d : V3)
    (hden : dot (orientationNormal f) d ≠ 0) :
    dot (badEdgeVec f u v p) d =
      dot (orientationNormal f) d *
        dot (orientationNormal f) (cross (sub (along p d (faceCrossingParam f p d)) u) (sub v u)) := by
  rw [dot_badEdgeVec]
  rw [dot_cross_cyclic' (sub v u) (orientationNormal f) d]
  rw [dot_cross_sub_along]
  unfold faceCrossingParam
  field_simp [hden]

lemma edge_cross_imp_dot_badEdgeVec_zero (f : Face) (u v p d : V3)
    (hden : dot (orientationNormal f) d ≠ 0)
    (hcross : cross (sub (along p d (faceCrossingParam f p d)) u) (sub v u) = ⟨0,0,0⟩) :
    dot (badEdgeVec f u v p) d = 0 := by
  rw [dot_badEdgeVec_eq f u v p d hden, hcross]
  simp [dot]

set_option maxHeartbeats 800000 in
lemma dot_edge_normal (f : Face) (u v : V3) (huv : (u,v) ∈ faceEdges f) :
    dot (sub v u) (orientationNormal f) = 0 := by
  rcases f with ⟨A,B,C⟩
  simp [faceEdges] at huv
  rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp [orientationNormal, dot, cross, sub]; ring

set_option maxHeartbeats 800000 in
lemma badEdgeVec_ne_zero (f : Face) (u v : V3) (p : V3)
    (huv : (u,v) ∈ faceEdges f)
    (hn : 0 < dot (orientationNormal f) (orientationNormal f))
    (he : 0 < dot (sub v u) (sub v u))
    (hp : faceNum f p ≠ 0) :
    badEdgeVec f u v p ≠ ⟨0,0,0⟩ := by
  intro hz
  let n := orientationNormal f
  let e := sub v u
  let K := triple n (sub p u) e
  let α := faceNum f p
  have hx := congrArg V3.x hz
  have hy := congrArg V3.y hz
  have hz' := congrArg V3.z hz
  simp [badEdgeVec] at hx hy hz'
  have hnedot : dot e n = 0 := by simpa [e, n] using dot_edge_normal f u v huv
  have hdot : dot (badEdgeVec f u v p) n = 0 := by rw [hz]; simp [dot]
  have hcn_n : dot (cross e n) n = 0 := by simp [dot, cross]; ring
  have hdot_expand : dot (badEdgeVec f u v p) n = K * dot n n + α * dot (cross e n) n := by
    simp [badEdgeVec, dot]; ring
  have hdot_expand' : dot (badEdgeVec f u v p) n = K * dot n n := by
    rw [hdot_expand, hcn_n, mul_zero, add_zero]
  have hKd : K * dot n n = 0 := by rw [← hdot_expand', hdot]
  have hK : K = 0 := (mul_eq_zero.mp hKd).resolve_right (ne_of_gt hn)
  have hKu : triple (orientationNormal f) (sub p u) (sub v u) = 0 := by simpa [K] using hK
  have hcex : (cross e n).x = 0 := by
    have hx0 := hx
    rw [hKu] at hx0
    have hx1 : faceNum f p * (cross e n).x = 0 := by simpa [e, n] using hx0
    exact (mul_eq_zero.mp hx1).resolve_left hp
  have hcey : (cross e n).y = 0 := by
    have hy0 := hy
    rw [hKu] at hy0
    have hy1 : faceNum f p * (cross e n).y = 0 := by simpa [e, n] using hy0
    exact (mul_eq_zero.mp hy1).resolve_left hp
  have hcez : (cross e n).z = 0 := by
    have hz0 := hz'
    rw [hKu] at hz0
    have hz1 : faceNum f p * (cross e n).z = 0 := by simpa [e, n] using hz0
    exact (mul_eq_zero.mp hz1).resolve_left hp
  have hce0 : dot (cross e n) (cross e n) = 0 := by simp [dot, hcex, hcey, hcez]
  have hl := V3.lagrange e n
  nlinarith [hl, hnedot, hce0, he, hn]

/-- The finite list of bad-direction vectors for a soup at `p`. -/
def badVectors (fs : List Face) (p : V3) : List V3 :=
  (fs.map fun f => orientationNormal f) ++
    (fs.flatMap fun f => fs.flatMap fun g =>
      if f = g then [] else [badCoincideVec f g p]) ++
    (fs.flatMap fun f => (faceEdges f).map fun e => badEdgeVec f e.1 e.2 p)

lemma mem_badVectors_parallel (fs : List Face) (p : V3) (f : Face) (hf : f ∈ fs) :
    orientationNormal f ∈ badVectors fs p := by
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  exact List.mem_map.mpr ⟨f, hf, rfl⟩

lemma mem_badVectors_coincide (fs : List Face) (p : V3) (f g : Face)
    (hf : f ∈ fs) (hg : g ∈ fs) (hfg : f ≠ g) :
    badCoincideVec f g p ∈ badVectors fs p := by
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  right
  exact List.mem_flatMap.mpr ⟨f, hf, List.mem_flatMap.mpr ⟨g, hg, by simp [hfg]⟩⟩

lemma mem_badVectors_edge (fs : List Face) (p : V3) (f : Face) (e : V3 × V3)
    (hf : f ∈ fs) (he : e ∈ faceEdges f) :
    badEdgeVec f e.1 e.2 p ∈ badVectors fs p := by
  apply List.mem_append.mpr
  right
  exact List.mem_flatMap.mpr ⟨f, hf, List.mem_map.mpr ⟨e, he, rfl⟩⟩

set_option maxHeartbeats 800000 in
theorem exists_good_direction (fs : List Face) (p : V3)
    (hnz : ∀ w ∈ badVectors fs p, w ≠ ⟨0,0,0⟩) :
    ∃ k : ℕ, k < 2 * (badVectors fs p).length + 1 ∧
      (∀ f ∈ fs, dot (orientationNormal f) (momentDir (k : ℝ)) ≠ 0) ∧
      (∀ f ∈ fs, ∀ g ∈ fs, f ≠ g →
        faceCrossingParam f p (momentDir (k : ℝ)) ≠ faceCrossingParam g p (momentDir (k : ℝ))) ∧
      (∀ f ∈ fs, ∀ e ∈ faceEdges f,
        cross (sub (along p (momentDir (k : ℝ)) (faceCrossingParam f p (momentDir (k : ℝ)))) e.1) (sub e.2 e.1) ≠ ⟨0,0,0⟩) := by
  rcases exists_momentDir_avoid (badVectors fs p) hnz with ⟨k, hk, hgood⟩
  refine ⟨k, hk, ?_⟩
  let d := momentDir (k : ℝ)
  have hpar : ∀ f ∈ fs, dot (orientationNormal f) d ≠ 0 := by
    intro f hf
    exact hgood (orientationNormal f) (mem_badVectors_parallel fs p f hf)
  have hcoin : ∀ f ∈ fs, ∀ g ∈ fs, f ≠ g → dot (badCoincideVec f g p) d ≠ 0 := by
    intro f hf g hg hfg
    exact hgood (badCoincideVec f g p) (mem_badVectors_coincide fs p f g hf hg hfg)
  have hedge : ∀ f ∈ fs, ∀ e ∈ faceEdges f, dot (badEdgeVec f e.1 e.2 p) d ≠ 0 := by
    intro f hf e he
    exact hgood (badEdgeVec f e.1 e.2 p) (mem_badVectors_edge fs p f e hf he)
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    simpa [d] using hpar f hf
  · intro f hf g hg hfg hEq
    have hdf : dot (orientationNormal f) (momentDir (k : ℝ)) ≠ 0 := by simpa [d] using hpar f hf
    have hdg : dot (orientationNormal g) (momentDir (k : ℝ)) ≠ 0 := by simpa [d] using hpar g hg
    have hbc := hcoin f hf g hg hfg
    rw [dot_badCoincideVec] at hbc
    have hbc' : faceNum f p * dot (orientationNormal g) (momentDir (k : ℝ)) -
        faceNum g p * dot (orientationNormal f) (momentDir (k : ℝ)) ≠ 0 := by
      simpa [d] using hbc
    unfold faceCrossingParam at hEq
    field_simp [hdf, hdg] at hEq
    have hzero : faceNum f p * dot (orientationNormal g) (momentDir (k : ℝ)) -
        faceNum g p * dot (orientationNormal f) (momentDir (k : ℝ)) = 0 := by
      nlinarith
    exact hbc' hzero
  · intro f hf e he hcross
    exact (hedge f hf e he) (edge_cross_imp_dot_badEdgeVec_zero f e.1 e.2 p d (hpar f hf) (by simpa [d] using hcross))
set_option maxHeartbeats 800000 in
lemma badVectors_nonzero_of_general (fs : List Face) (p : V3)
    (hoff : offFaces fs p)
    (hnd : ∀ f ∈ fs, 0 < dot (orientationNormal f) (orientationNormal f))
    (hnpar : ∀ f ∈ fs, ∀ g ∈ fs, f ≠ g →
      cross (orientationNormal f) (orientationNormal g) ≠ ⟨0,0,0⟩)
    (hedge : ∀ f ∈ fs, ∀ e ∈ faceEdges f, 0 < dot (sub e.2 e.1) (sub e.2 e.1)) :
    ∀ w ∈ badVectors fs p, w ≠ ⟨0,0,0⟩ := by
  classical
  intro w hw
  rw [badVectors] at hw
  simp only [List.mem_append, List.mem_map, List.mem_flatMap] at hw
  rcases hw with (⟨f, hf, hwpar⟩ | ⟨f, hf, ⟨g, hg, hwcoin⟩⟩) | ⟨f, hf, ⟨e, he, hwedge⟩⟩
  · rw [← hwpar]
    have hn := hnd f hf
    intro hz
    have hx := congrArg V3.x hz
    have hy := congrArg V3.y hz
    have hz' := congrArg V3.z hz
    simp at hx hy hz'
    have hdot0 : dot (orientationNormal f) (orientationNormal f) = 0 := by
      simp [dot, hx, hy, hz']
    linarith
  · by_cases hfg : f = g
    · subst g
      simp at hwcoin
    · simp [hfg] at hwcoin
      rw [hwcoin]
      exact badCoincideVec_ne_zero f g p (hoff f hf) (hnpar f hf g hg hfg)
  · rw [← hwedge]
    exact badEdgeVec_ne_zero f e.1 e.2 p he (hnd f hf) (hedge f hf e he) (hoff f hf)
set_option maxHeartbeats 800000 in
/-- **Generic ray direction exists (rigorous avoidance tier).** Under the
    explicit generality assumptions below -- every face nondegenerate, every
    two distinct faces having non-parallel planes, every edge nondegenerate,
    and `p` off every face -- there is a candidate direction
    `momentDir k = (1, k, k²)` with `k < 2·#bad + 1` for which no face is
    parallel, no two crossing parameters coincide, and no crossing lies on a
    face edge line. This is the direction-existence step of generic ray
    casting; the remaining walls (exact far value `0`, and the ordering of the
    finitely many crossings into a `PathChain`) are documented after it. -/
theorem exists_good_direction_of_general (fs : List Face) (p : V3)
    (hoff : offFaces fs p)
    (hnd : ∀ f ∈ fs, 0 < dot (orientationNormal f) (orientationNormal f))
    (hnpar : ∀ f ∈ fs, ∀ g ∈ fs, f ≠ g →
      cross (orientationNormal f) (orientationNormal g) ≠ ⟨0,0,0⟩)
    (hedge : ∀ f ∈ fs, ∀ e ∈ faceEdges f, 0 < dot (sub e.2 e.1) (sub e.2 e.1)) :
    ∃ k : ℕ, k < 2 * (badVectors fs p).length + 1 ∧
      (∀ f ∈ fs, dot (orientationNormal f) (momentDir (k : ℝ)) ≠ 0) ∧
      (∀ f ∈ fs, ∀ g ∈ fs, f ≠ g →
        faceCrossingParam f p (momentDir (k : ℝ)) ≠ faceCrossingParam g p (momentDir (k : ℝ))) ∧
      (∀ f ∈ fs, ∀ e ∈ faceEdges f,
        cross (sub (along p (momentDir (k : ℝ)) (faceCrossingParam f p (momentDir (k : ℝ)))) e.1) (sub e.2 e.1) ≠ ⟨0,0,0⟩) := by
  exact exists_good_direction fs p (badVectors_nonzero_of_general fs p hoff hnd hnpar hedge)

/- **What this avoidance tier does and does not establish.**

   Established unconditionally above:

     * `exists_momentDir_avoid`: a single algebraic fact. A finite list of
       nonzero vectors `w₁, …, w_m` in `V3` gives `m` nonzero quadratics
       `eval t (dirPoly wᵢ) = dot wᵢ (momentDir t)`. Their product has degree
       `≤ 2m`, so it cannot vanish at all `2m+1` distinct points
       `t = 0, …, 2m`; one candidate `momentDir k` makes every functional
       nonzero. (This is the "finite union of great circles is not
       everything" argument, made constructive over an explicit candidate
       set.)
     * `exists_good_direction` / `exists_good_direction_of_general`: the three
       geometric degeneracies are each a linear functional of `d`:
       parallel-to-a-plane (`orientationNormal f`), coincident crossing
       parameters (`badCoincideVec f g p`), and a crossing on an edge line
       (`badEdgeVec f u v p`). The direction returned avoids all of them.
       Combined with `faceNum_along_eq_zero_iff_crossingParam`, each face is
       crossed at most once and with a distinct parameter, and no crossing is
       on a boundary edge.

   Not established here (still hypotheses of `GenericPathExists`):

     * an exact far point `q` with `meshWinding fs q = 0` for a general soup
       (only the limit `meshWinding_tendsto_zero_norm_atTop` is unconditional;
       exact vanishing for the structural subclasses is landed separately);
     * ordering the finitely many parameters of `crossingParams` into a
       `PathChain` and discharging the local-constancy hypotheses on the arcs
       between consecutive crossings.

   The `hnpar` hypothesis excludes two distinct faces lying in the same plane
   (which would force their crossing parameters to coincide for every
   direction); the `hnd`/`hedge` hypotheses exclude degenerate faces/edges.
   These are genuine geometric generality assumptions, not artifacts of the
   proof. -/

/- ===== Ordering half of `GenericPathExists` (conditional assembly) =====

The ordering/local-constancy step of the generic ray-casting construction is
isolated here, independently of the circular exact-far-point question.  What is
proved is a *conditional* assembly theorem, not `GenericPathExists` itself:

  * `meshWinding_perm` (permutation invariance of a finite soup) lets a
    crossing face be moved to the head, so the landed jump theorems apply to an
    arbitrary soup.  `crossing_jump_of_mem_pos` / `crossing_jump_of_mem_neg`
    are those jumps for a face at any position; their `hplane`/`hden` premises
    are supplied by `faceNum_eq_zero_of_barycentric` and `interior_faceDen_neg`
    (equivalently `interior_crossing_jump_minus_one` in the head case), and the
    sign `hN` by the generic direction of `exists_good_direction_of_general`.

  * `GoodCrossing` packages one crossing: the sample parameters `lo < t < hi`
    bracket the crossing parameter `t`, and the exact `±1` jump holds at the
    sample points.  Its jump component is discharged by the two lemmas above;
    the bracketing is arithmetic on the midpoint sample parameters.

  * `recsOfParams` turns a strictly increasing list of crossing parameters in
    `(0,1)` into crossing records with shared midpoint sample points: the
    `after` sample of one record *is* the `before` sample of the next (and the
    first/last samples are `a`/`b`), so the arc-constancy clauses between
    consecutive crossings of `PathChain` hold by reflexivity.  The only local
    constancy still needed is on the two crossing-free sub-arcs immediately
    around each crossing -- the `hb`/`ha` premises of the jump theorems, which
    are discharged with `continuousAt_meshWinding_of_generic` plus
    `meshWinding_const_of_locallyConstant` on those arcs.  `chainFrom_of_sorted`
    proves the records form a `ChainFrom`; and `pathChain_of_chainFrom` converts
    a `ChainFrom` into exactly the `PathChain` consumed by `PathChain.sum_eq` /
    `winding_eq_crossingSum_of_path`.
    `genericPath_ordering_half` is the resulting theorem, and its
    `genericPath_ordering_half_finset` form consumes the finite set supplied by
    `segmentCrossingParams_finite` after sorting with `Finset.sort`
    (`sortedParams_of_finset`).

The two geometric inputs that remain hypotheses in this tier are precisely the
ones documented as open above: an exact far value `0` (circular for a general
soup), and local constancy of `meshWinding` on each crossing-free open arc
(equivalently, integer-valuedness there -- the very degree conclusion that the
assembled `PathChain` feeds into).  The ordering/combinatorial half itself is
unconditional given those inputs.
-/

/-- The winding number is invariant under reordering of the (finite) soup. -/
theorem meshWinding_perm (fs gs : List Face) (p : V3) (hperm : fs.Perm gs) :
    meshWinding fs p = meshWinding gs p := by
  let g : Face → ℝ := fun f => solidAngle f.1 f.2.1 f.2.2 p
  have hsum : (fs.map g).sum = (gs.map g).sum := (hperm.map g).sum_eq
  change (fs.map g).sum / (4 * Real.pi) = (gs.map g).sum / (4 * Real.pi)
  rw [hsum]

set_option maxHeartbeats 800000 in
/-- The `-1` jump for a crossing face occurring anywhere in the soup.  Move
    `f` to the head by permutation and apply `crossing_jump_of_generic_pos`
    (equivalently the interior-specialisation `interior_crossing_jump_minus_one`
    when `hplane`/`hden` come from a relative-interior crossing point). -/
theorem crossing_jump_of_mem_pos
    (fs : List Face) (f : Face) (hf : f ∈ fs) (c nn : V3)
    (hplane : faceNum f c = 0) (hden : faceDen f c < 0)
    (hN : 0 < dot (orientationNormal f) nn)
    (hrest : ∀ g ∈ fs.erase f, faceNum g c ≠ 0 ∧ faceDen g c ≠ 0)
    (before after : V3)
    (hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      meshWinding fs (along c nn (-ε)) = meshWinding fs before)
    (ha : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      meshWinding fs (along c nn ε) = meshWinding fs after) :
    meshWinding fs after - meshWinding fs before = (-1 : ℝ) := by
  classical
  let rest := fs.erase f
  have hperm : fs.Perm (f :: rest) := List.perm_cons_erase hf
  have hpermEq : ∀ q : V3, meshWinding fs q = meshWinding (f :: rest) q := by
    intro q
    exact meshWinding_perm fs (f :: rest) q hperm
  have hb' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      meshWinding (f :: rest) (along c nn (-ε)) = meshWinding (f :: rest) before := by
    filter_upwards [hb] with ε hε
    rw [← hpermEq (along c nn (-ε)), ← hpermEq before]
    exact hε
  have ha' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      meshWinding (f :: rest) (along c nn ε) = meshWinding (f :: rest) after := by
    filter_upwards [ha] with ε hε
    rw [← hpermEq (along c nn ε), ← hpermEq after]
    exact hε
  have hj := crossing_jump_of_generic_pos f rest c nn hplane hden hN hrest before after hb' ha'
  rw [hpermEq after, hpermEq before]
  exact hj

set_option maxHeartbeats 800000 in
/-- The `+1` jump for a crossing face occurring anywhere in the soup.  This is
    the general-soup counterpart of `crossing_jump_of_generic_neg`. -/
theorem crossing_jump_of_mem_neg
    (fs : List Face) (f : Face) (hf : f ∈ fs) (c nn : V3)
    (hplane : faceNum f c = 0) (hden : faceDen f c < 0)
    (hN : dot (orientationNormal f) nn < 0)
    (hrest : ∀ g ∈ fs.erase f, faceNum g c ≠ 0 ∧ faceDen g c ≠ 0)
    (before after : V3)
    (hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      meshWinding fs (along c nn (-ε)) = meshWinding fs before)
    (ha : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      meshWinding fs (along c nn ε) = meshWinding fs after) :
    meshWinding fs after - meshWinding fs before = (1 : ℝ) := by
  classical
  let rest := fs.erase f
  have hperm : fs.Perm (f :: rest) := List.perm_cons_erase hf
  have hpermEq : ∀ q : V3, meshWinding fs q = meshWinding (f :: rest) q := by
    intro q
    exact meshWinding_perm fs (f :: rest) q hperm
  have hb' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      meshWinding (f :: rest) (along c nn (-ε)) = meshWinding (f :: rest) before := by
    filter_upwards [hb] with ε hε
    rw [← hpermEq (along c nn (-ε)), ← hpermEq before]
    exact hε
  have ha' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      meshWinding (f :: rest) (along c nn ε) = meshWinding (f :: rest) after := by
    filter_upwards [ha] with ε hε
    rw [← hpermEq (along c nn ε), ← hpermEq after]
    exact hε
  have hj := crossing_jump_of_generic_neg f rest c nn hplane hden hN hrest before after hb' ha'
  rw [hpermEq after, hpermEq before]
  exact hj

/-- One crossing record on the segment `t ↦ along p d t`: crossing at
    parameter `t`, sampled at `lo < t < hi`, on `face`, contributing `sign`. -/
structure CrossingRec where
  t : ℝ
  lo : ℝ
  hi : ℝ
  face : Face
  sign : ℤ

/-- Turn a record into a `Crossing` using the segment sample points. -/
def CrossingRec.toCrossing (p d : V3) (r : CrossingRec) : Crossing :=
  { face := r.face, before := along p d r.lo, after := along p d r.hi, sign := r.sign }

/-- `ChainFrom fs p d lo hi recs`: the records form an ordered crossing chain
    on the segment from parameter `lo` to parameter `hi`.  Consecutive records
    share their sample parameter, and each record's jump is exact.  Defined by
    structural recursion on `recs` (rather than as an inductive family) so the
    recursion does not carry the heavy `meshWinding` term in its motive. -/
def ChainFrom (fs : List Face) (p d : V3) (lo hi : ℝ) : List CrossingRec → Prop
  | [] => meshWinding fs (along p d hi) = meshWinding fs (along p d lo)
  | r :: rs => r.lo = lo ∧
      meshWinding fs (along p d r.hi) - meshWinding fs (along p d r.lo) = (r.sign : ℝ) ∧
      ChainFrom fs p d r.hi hi rs

set_option maxHeartbeats 800000 in
/-- A `ChainFrom` is already a `PathChain` on the segment sample points. -/
theorem pathChain_of_chainFrom_aux (fs : List Face) (p d : V3) (lo hi : ℝ)
    (recs : List CrossingRec) (h : ChainFrom fs p d lo hi recs) :
    PathChain fs (along p d lo) (along p d hi) (recs.map (CrossingRec.toCrossing p d)) := by
  induction recs generalizing lo with
  | nil =>
      simpa [ChainFrom, PathChain] using (Or.inr h :
        along p d hi = along p d lo ∨ meshWinding fs (along p d hi) = meshWinding fs (along p d lo))
  | cons r rs ih =>
      simp only [ChainFrom] at h
      rcases h with ⟨hlo, hjump, hrest⟩
      simp only [List.map_cons, PathChain, CrossingRec.toCrossing]
      exact ⟨by rw [hlo], hjump, ih r.hi hrest⟩

/-- **Ordering half (assembly).** A `ChainFrom` on `[0,1]` gives a `PathChain`
    from `a = along p d 0` to `b = along p d 1`. -/
theorem pathChain_of_chainFrom (fs : List Face) (p d : V3) (recs : List CrossingRec)
    (h : ChainFrom fs p d 0 1 recs) :
    ∃ cs : List Crossing, PathChain fs (along p d 0) (along p d 1) cs :=
  ⟨recs.map (CrossingRec.toCrossing p d), pathChain_of_chainFrom_aux fs p d 0 1 recs h⟩

/-- A crossing record is *good* if its sample parameters bracket the crossing
    and the exact winding jump holds there.  The jump component is the premise
    discharged by `crossing_jump_of_mem_pos` / `crossing_jump_of_mem_neg`. -/
def GoodCrossing (fs : List Face) (p d : V3) (r : CrossingRec) : Prop :=
  r.lo < r.t ∧ r.t < r.hi ∧
    meshWinding fs (along p d r.hi) - meshWinding fs (along p d r.lo) = (r.sign : ℝ)

/-- Build crossing records with midpoint sample parameters from a list of
    crossing parameters: the upper sample of one record is the lower sample
    of the next, so consecutive crossings share a sample point. -/
def recsOfParams (mkFace : ℝ → Face) (mkSign : ℝ → ℤ) (lo : ℝ) : List ℝ → List CrossingRec
  | [] => []
  | [t] => [{ t := t, lo := lo, hi := 1, face := mkFace t, sign := mkSign t }]
  | t :: u :: rest =>
      { t := t, lo := lo, hi := (t + u) / 2, face := mkFace t, sign := mkSign t } ::
        recsOfParams mkFace mkSign ((t + u) / 2) (u :: rest)

set_option maxHeartbeats 800000 in
/-- From a strictly increasing list of crossing parameters in `(0,1)`, with a
    good crossing datum at each one, build the ordered `ChainFrom`. -/
theorem chainFrom_of_sorted (fs : List Face) (p d : V3)
    (mkFace : ℝ → Face) (mkSign : ℝ → ℤ)
    (ts : List ℝ) (lo : ℝ)
    (hsorted : ts.Pairwise (fun a b => a < b))
    (hlo : ∀ t ∈ ts, lo < t)
    (hhi : ∀ t ∈ ts, t < 1)
    (hmk : ∀ t ∈ ts, ∀ l h : ℝ, l < t → t < h →
      GoodCrossing fs p d { t := t, lo := l, hi := h, face := mkFace t, sign := mkSign t })
    (hconst : ts = [] → meshWinding fs (along p d 1) = meshWinding fs (along p d lo)) :
    ChainFrom fs p d lo 1 (recsOfParams mkFace mkSign lo ts) := by
  induction ts generalizing lo with
  | nil =>
      change meshWinding fs (along p d 1) = meshWinding fs (along p d lo)
      exact hconst rfl
  | cons t ts' ih =>
      simp only [List.pairwise_cons] at hsorted
      rcases hsorted with ⟨hhead, htail⟩
      cases ts' with
      | nil =>
          simp only [recsOfParams, ChainFrom]
          have htlo : lo < t := hlo t (by simp)
          have ht1 : t < 1 := hhi t (by simp)
          have hg := hmk t (by simp) lo 1 htlo ht1
          simp only [GoodCrossing] at hg
          exact ⟨trivial, hg.2.2, trivial⟩
      | cons u rest =>
          simp only [recsOfParams, ChainFrom]
          have htu : t < u := hhead u (by simp)
          have htlo : lo < t := hlo t (by simp)
          have hmid : t < (t + u) / 2 := by linarith
          have hg := hmk t (by simp) lo ((t + u) / 2) htlo hmid
          simp only [GoodCrossing] at hg
          refine ⟨trivial, hg.2.2, ?_⟩
          apply ih ((t + u) / 2)
          · exact htail
          · intro x hx
            have hux : u ≤ x := by
              rcases List.mem_cons.mp hx with hxu | hxr
              · subst x
                exact le_rfl
              · exact le_of_lt ((List.pairwise_cons.mp htail).1 x hxr)
            have hlou : (t + u) / 2 < u := by linarith
            exact lt_of_lt_of_le hlou hux
          · intro x hx
            exact hhi x (by simp [hx])
          · intro x hx l h hlx hxhi
            exact hmk x (by simp [hx]) l h hlx hxhi
          · simp

/-- The sorted finset of crossing parameters satisfies the strict-order
    hypothesis of `chainFrom_of_sorted`. -/
lemma sortedParams_of_finset (S : Finset ℝ) :
    (S.sort (fun a b : ℝ => a ≤ b)).Pairwise (fun a b => a < b) :=
  (Finset.sortedLT_sort S).pairwise

/-- **Ordering half of `GenericPathExists` (conditional assembly).** Given a
    strictly increasing list of crossing parameters in `(0,1)` and a good
    crossing datum at each one (jump discharged by the landed jump theorems,
    local constancy on the crossing-free arcs supplied as `GoodCrossing`),
    there is a `PathChain` from `a = along p d 0` to `b = along p d 1`. -/
theorem genericPath_ordering_half (fs : List Face) (p d : V3)
    (mkFace : ℝ → Face) (mkSign : ℝ → ℤ)
    (ts : List ℝ)
    (hsorted : ts.Pairwise (fun a b => a < b))
    (hpos : ∀ t ∈ ts, 0 < t) (hlt : ∀ t ∈ ts, t < 1)
    (hmk : ∀ t ∈ ts, ∀ l h : ℝ, l < t → t < h →
      GoodCrossing fs p d { t := t, lo := l, hi := h, face := mkFace t, sign := mkSign t })
    (hconst : ts = [] → meshWinding fs (along p d 1) = meshWinding fs (along p d 0)) :
    ∃ cs : List Crossing, PathChain fs (along p d 0) (along p d 1) cs := by
  exact pathChain_of_chainFrom fs p d (recsOfParams mkFace mkSign 0 ts)
    (chainFrom_of_sorted fs p d mkFace mkSign ts 0 hsorted hpos hlt hmk hconst)

/-- Finite-set form: sort the (finite) crossing-parameter set with `Finset.sort`
    and apply the ordering lemma.  This is the form that consumes
    `segmentCrossingParams_finite`. -/
theorem genericPath_ordering_half_finset (fs : List Face) (p d : V3) (S : Finset ℝ)
    (mkFace : ℝ → Face) (mkSign : ℝ → ℤ)
    (hmem : ∀ t ∈ S, 0 < t ∧ t < 1)
    (hmk : ∀ t ∈ S, ∀ l h : ℝ, l < t → t < h →
      GoodCrossing fs p d { t := t, lo := l, hi := h, face := mkFace t, sign := mkSign t })
    (hconst : S = ∅ → meshWinding fs (along p d 1) = meshWinding fs (along p d 0)) :
    ∃ cs : List Crossing, PathChain fs (along p d 0) (along p d 1) cs := by
  apply genericPath_ordering_half fs p d mkFace mkSign (S.sort (fun a b : ℝ => a ≤ b))
  · exact sortedParams_of_finset S
  · intro t ht
    exact (hmem t ((Finset.mem_sort (s := S) (fun a b : ℝ => a ≤ b) (a := t)).mp ht)).1
  · intro t ht
    exact (hmem t ((Finset.mem_sort (s := S) (fun a b : ℝ => a ≤ b) (a := t)).mp ht)).2
  · intro t ht l h hl hh
    exact hmk t ((Finset.mem_sort (s := S) (fun a b : ℝ => a ≤ b) (a := t)).mp ht) l h hl hh
  · intro hnil
    apply hconst
    apply Finset.card_eq_zero.mp
    rw [← Finset.length_sort (s := S) (r := fun a b : ℝ => a ≤ b)]
    simp [hnil]

/- ===== Breaking the far-point circularity without integrality: the far-ray tier =====

The exact-far-point step used by `GenericPathExists` is circular: the far point
is pinned to `0` by integrality plus `meshWinding_tendsto_zero_norm_atTop`,
while integrality is proved from a path chain starting at such a far point.
This section takes the alternative route suggested by the topology of the
complement.  We use the *ray* version (option (b)) rather than a sphere: a
half-line in `V3` is preconnected for elementary reasons (it is the image of
`Set.Ici T` under a continuous map), so the preconnectedness wall is solved
unconditionally here.

What survives unconditionally:

  * `farRegion fs = {p | soupThresh fs < norm p}` is crossed by no face in the
    branch-cut sense: every face has `faceDen f p > 0` there, so each solid
    angle is an ordinary `arctan` branch and `meshWinding fs` is continuous on
    the whole region (`continuousOn_meshWinding_farRegion`);
  * constancy on a preconnected far ray forces the value `0`, by comparison
    with `meshWinding_ray_tendsto_zero` (`farRay_meshWinding_eq_zero`).

The one ingredient that is **not** supplied is local constancy of
`meshWinding` along the far ray; it is isolated as the precisely named
hypothesis `FarRayLocallyConstant`.  This is the honest wall: continuity alone
does *not* give local constancy (for a single triangle the winding number is a
nonconstant continuous function on any far ray, decaying like `‖p‖⁻²`), and
for a general soup local constancy is equivalent to the degree-theoretic
integrality that this exercise is meant to avoid.  Thus the route proves the
implication "branch stability on the far ray ⇒ exact far value `0`" with no
circularity, but branch stability itself remains an explicit hypothesis. -/

/-- The crossing-free far region: beyond the threshold at which every face's
    Van Oosterom denominator is strictly positive. -/
def farRegion (fs : List Face) : Set V3 := {p | soupThresh fs < norm p}

lemma mem_farRegion_norm_pos {fs : List Face} {p : V3} (hp : p ∈ farRegion fs) :
    0 < norm p :=
  lt_of_le_of_lt (soupThresh_nonneg fs) hp

set_option maxHeartbeats 800000 in
lemma faceDen_pos_of_mem_farRegion (fs : List Face) (f : Face) (hf : f ∈ fs)
    {p : V3} (hp : p ∈ farRegion fs) : 0 < faceDen f p := by
  have h4 : 4 * faceM f ≤ norm p := le_trans (soupThresh_ge fs f hf) hp.le
  have hcube := faceDen_ge_cube f p h4
  have hnormp : 0 < norm p := mem_farRegion_norm_pos hp
  have hhalf : 0 < norm p / 2 := by nlinarith
  have hpos : 0 < (norm p / 2) ^ 3 := pow_pos hhalf 3
  exact lt_of_lt_of_le hpos hcube

set_option maxHeartbeats 800000 in
/-- `atan2'` is continuous wherever the denominator is positive, even when the
    numerator vanishes: there it is the ordinary `arctan (y/x)` branch. This
    is why crossing the *plane* of a face at large distance causes no jump. -/
lemma atan2'_continuousAt_of_den_pos (y x : ℝ) (hx : 0 < x) :
    ContinuousAt (fun z : ℝ × ℝ => atan2' z.1 z.2) (y, x) := by
  have hz2 : ∀ᶠ z in 𝓝 (y, x), 0 < z.2 :=
    continuousAt_snd.eventually (eventually_gt_nhds hx)
  have heq : (fun z : ℝ × ℝ => atan2' z.1 z.2) =ᶠ[𝓝 (y, x)]
      (fun z => Real.arctan (z.1 / z.2)) := by
    filter_upwards [hz2] with z hz
    simp [atan2', hz]
  have hrhs : ContinuousAt (fun z : ℝ × ℝ => Real.arctan (z.1 / z.2)) (y, x) :=
    Real.continuousAt_arctan.comp (continuousAt_fst.div continuousAt_snd (ne_of_gt hx))
  exact hrhs.congr heq.symm

set_option maxHeartbeats 800000 in
lemma continuousAt_solidAngle_of_den_pos (f : Face) (p : V3)
    (hden : 0 < faceDen f p) :
    ContinuousAt (fun q => solidAngle f.1 f.2.1 f.2.2 q) p := by
  rw [show (fun q => solidAngle f.1 f.2.1 f.2.2 q) =
      (fun q => 2 * atan2' (faceNum f q) (faceDen f q)) by
        funext q
        exact solidAngle_eq_face f q]
  have hpair : ContinuousAt (fun q => (faceNum f q, faceDen f q)) p :=
    (continuousAt_faceNum f p).prodMk (continuousAt_faceDen f p)
  have hatan : ContinuousAt (fun q => atan2' (faceNum f q) (faceDen f q)) p := by
    change ContinuousAt ((fun z : ℝ × ℝ => atan2' z.1 z.2) ∘
      (fun q : V3 => (faceNum f q, faceDen f q))) p
    exact (atan2'_continuousAt_of_den_pos (faceNum f p) (faceDen f p) hden).comp
      (x := p) hpair
  exact continuousAt_const.mul hatan

set_option maxHeartbeats 800000 in
/-- Continuity of `meshWinding fs` at every point of the far region, with no
    `faceNum ≠ 0` requirement (unlike `continuousAt_meshWinding_of_generic`). -/
lemma continuousAt_meshWinding_of_mem_farRegion (fs : List Face) {p : V3}
    (hp : p ∈ farRegion fs) : ContinuousAt (meshWinding fs) p := by
  have hden : ∀ f ∈ fs, 0 < faceDen f p := by
    intro f hf
    exact faceDen_pos_of_mem_farRegion fs f hf hp
  have hsum : ContinuousAt
      (fun q => (fs.map fun f => solidAngle f.1 f.2.1 f.2.2 q).sum) p := by
    induction fs with
    | nil =>
        simpa using (continuousAt_const : ContinuousAt (fun _ : V3 => (0 : ℝ)) p)
    | cons f fs ih =>
        have hptail : p ∈ farRegion fs := by
          change soupThresh fs < norm p
          have hst : soupThresh fs ≤ soupThresh (f :: fs) := by
            simp [soupThresh]
            nlinarith [faceM_nonneg f, faceM_sum_nonneg fs]
          exact lt_of_le_of_lt hst hp
        have hdentail : ∀ g ∈ fs, 0 < faceDen g p := by
          intro g hg
          exact hden g (by simp [hg])
        simp only [List.map_cons, List.sum_cons]
        exact (continuousAt_solidAngle_of_den_pos f p (hden f (by simp))).add
          (ih hptail hdentail)
  change ContinuousAt
    (fun q => (fs.map fun f => solidAngle f.1 f.2.1 f.2.2 q).sum / (4 * Real.pi)) p
  exact hsum.div_const (4 * Real.pi)

lemma continuousOn_meshWinding_farRegion (fs : List Face) :
    ContinuousOn (meshWinding fs) (farRegion fs) := by
  intro p hp
  exact (continuousAt_meshWinding_of_mem_farRegion fs hp).continuousWithinAt

/-- The ray norm grows linearly for nonnegative parameters. -/
lemma dot_ray_ray (t : ℝ) (d : V3) : dot (ray t d) (ray t d) = t ^ 2 * dot d d := by
  simp [ray, dot]
  ring

lemma norm_ray_of_nonneg (t : ℝ) (d : V3) (ht : 0 ≤ t) :
    norm (ray t d) = t * norm d := by
  unfold V3.norm
  rw [dot_ray_ray]
  rw [Real.sqrt_mul (sq_nonneg t)]
  simp [Real.sqrt_sq_eq_abs, abs_of_nonneg ht]

lemma continuous_ray (d : V3) : Continuous (fun t : ℝ => ray t d) := by
  rw [continuous_induced_rng]
  change Continuous (fun t : ℝ => (t * d.x, t * d.y, t * d.z))
  fun_prop

/-- The preconnectedness wall, solved unconditionally for a half-line: the
    image of a preconnected interval under a continuous map. -/
lemma isPreconnected_farRay (d : V3) (T : ℝ) :
    IsPreconnected ((fun t : ℝ => ray t d) '' Set.Ici T) :=
  isPreconnected_Ici.image (fun t : ℝ => ray t d) (continuous_ray d).continuousOn

/-- **Named branch-stability hypothesis.** Along the crossing-free far ray the
    winding number is locally constant as a function of the ray parameter:
    near each `t ≥ T` there is an open neighbourhood on which, for all `s ≥ T`,
    `meshWinding fs (ray s d) = meshWinding fs (ray t d)`. This is exactly the
    step that continuity alone does not supply and that degree theory would
    supply via integrality. It is stated on the ambient real line (not on the
    subtype) so it can be plugged into `IsLocallyConstant.apply_eq_of_isPreconnected`. -/
def FarRayLocallyConstant (fs : List Face) (d : V3) (T : ℝ) : Prop :=
  ∀ t : ℝ, T ≤ t → ∃ u : Set ℝ, u ∈ 𝓝 t ∧
    ∀ s : ℝ, s ∈ u → T ≤ s → meshWinding fs (ray s d) = meshWinding fs (ray t d)

set_option maxHeartbeats 800000 in
/-- Extend a ray-locally-constant function to a globally locally constant
    function by freezing its value below `T`. -/
lemma FarRayLocallyConstant.patched_isLocallyConstant (fs : List Face) (d : V3) (T : ℝ)
    (h : FarRayLocallyConstant fs d T) :
    IsLocallyConstant (fun t : ℝ =>
      if T ≤ t then meshWinding fs (ray t d) else meshWinding fs (ray T d)) := by
  intro S
  rw [isOpen_iff_mem_nhds]
  intro t ht
  by_cases htT : T ≤ t
  · have htt : meshWinding fs (ray t d) ∈ S := by simpa [htT] using ht
    rcases h t htT with ⟨u, hu, hconst⟩
    by_cases hlt : T < t
    · have hv : u ∩ Set.Ioi T ∈ 𝓝 t := Filter.inter_mem hu (Ioi_mem_nhds hlt)
      apply Filter.mem_of_superset hv
      intro s hs
      have hslt : T < s := by simpa using hs.2
      have hsle : T ≤ s := le_of_lt hslt
      have hcs := hconst s hs.1 hsle
      change (if T ≤ s then meshWinding fs (ray s d) else meshWinding fs (ray T d)) ∈ S
      rw [ite_eq_left hsle, hcs]
      exact htt
    · have htEq : t = T := le_antisymm (le_of_not_gt hlt) htT
      apply Filter.mem_of_superset hu
      intro s hs
      by_cases hsT : T ≤ s
      · have hcs := hconst s hs hsT
        change (if T ≤ s then meshWinding fs (ray s d) else meshWinding fs (ray T d)) ∈ S
        rw [ite_eq_left hsT, hcs]
        exact htt
      · change (if T ≤ s then meshWinding fs (ray s d) else meshWinding fs (ray T d)) ∈ S
        rw [ite_eq_right hsT]
        simpa [htEq] using htt
  · have htt : meshWinding fs (ray T d) ∈ S := by simpa [htT] using ht
    have hv : Set.Iio T ∈ 𝓝 t := isOpen_Iio.mem_nhds (lt_of_not_ge htT)
    apply Filter.mem_of_superset hv
    intro s hs
    have hsT : ¬ T ≤ s := not_le.mpr hs
    change (if T ≤ s then meshWinding fs (ray s d) else meshWinding fs (ray T d)) ∈ S
    rw [ite_eq_right hsT]
    exact htt

set_option maxHeartbeats 800000 in
/-- Branch stability plus preconnectedness of the half-line give exact
    constancy along the far ray, with no integrality premise. -/
lemma FarRayLocallyConstant.eq_on_farRay (fs : List Face) (d : V3) (T : ℝ)
    (h : FarRayLocallyConstant fs d T) (t : ℝ) (ht : T ≤ t) :
    meshWinding fs (ray t d) = meshWinding fs (ray T d) := by
  let g : ℝ → ℝ := fun s => if T ≤ s then meshWinding fs (ray s d)
    else meshWinding fs (ray T d)
  have hg : IsLocallyConstant g := h.patched_isLocallyConstant fs d T
  have hconn : IsPreconnected (Set.Ici T) := isPreconnected_Ici
  have htmem : t ∈ Set.Ici T := ht
  have hTmem : T ∈ Set.Ici T := by simp
  have heq : g t = g T := hg.apply_eq_of_isPreconnected hconn htmem hTmem
  simpa [g, ht] using heq

set_option maxHeartbeats 800000 in
/-- **Exact far value from branch stability.** If `meshWinding fs` is locally
    constant along a far ray (all of whose points lie in `farRegion fs`), then
    its value there is `0`: constancy transports the unconditional ray limit
    `meshWinding fs (ray t d) → 0` back to every ray point. No integrality and
    no `GenericPathExists` are used. -/
theorem farRay_meshWinding_eq_zero (fs : List Face) (d : V3) (hd : d ≠ ⟨0, 0, 0⟩)
    (T : ℝ) (_hT0 : 0 ≤ T)
    (_hfar : ∀ t : ℝ, T ≤ t → ray t d ∈ farRegion fs)
    (hloc : FarRayLocallyConstant fs d T) :
    ∀ t : ℝ, T ≤ t → meshWinding fs (ray t d) = 0 := by
  have hdotpos : 0 < dot d d := by
    have hnn : 0 ≤ dot d d := dot_self_nonneg d
    rcases lt_or_eq_of_le hnn with hpos | hzero
    · exact hpos
    · exfalso
      apply hd
      apply V3.ext
      · simp [dot] at hzero ⊢
        nlinarith [sq_nonneg d.x, sq_nonneg d.y, sq_nonneg d.z]
      · simp [dot] at hzero ⊢
        nlinarith [sq_nonneg d.x, sq_nonneg d.y, sq_nonneg d.z]
      · simp [dot] at hzero ⊢
        nlinarith [sq_nonneg d.x, sq_nonneg d.y, sq_nonneg d.z]
  have hev : (fun t : ℝ => meshWinding fs (ray t d)) =ᶠ[atTop]
      (fun _ : ℝ => meshWinding fs (ray T d)) := by
    filter_upwards [Filter.Ici_mem_atTop T] with t ht
    exact hloc.eq_on_farRay fs d T t ht
  have hlim := meshWinding_ray_tendsto_zero fs d hdotpos
  have hlimconst : Tendsto (fun _ : ℝ => meshWinding fs (ray T d)) atTop
      (𝓝 (meshWinding fs (ray T d))) := tendsto_const_nhds
  have hz : meshWinding fs (ray T d) = 0 :=
    tendsto_nhds_unique hlimconst (hlim.congr' hev)
  intro t ht
  rw [hloc.eq_on_farRay fs d T t ht, hz]

set_option maxHeartbeats 800000 in
/-- **Far-point zero from branch stability, no circularity.** For any `q` in
    the crossing-free far region, if `meshWinding fs` is locally constant along
    the outward ray through `q` from parameter `1`, then `meshWinding fs q = 0`.
    The hypothesis is named precisely (`FarRayLocallyConstant`) and is the sole
    remaining wall of this route. -/
theorem meshWinding_eq_zero_of_far_of_locallyConstant (fs : List Face) (q : V3)
    (hq : q ∈ farRegion fs) (hloc : FarRayLocallyConstant fs q 1) :
    meshWinding fs q = 0 := by
  have hqdot : 0 < dot q q := by
    have hqnorm : 0 < norm q := mem_farRegion_norm_pos hq
    rw [← norm_sq q]
    nlinarith
  have hq0 : q ≠ ⟨0, 0, 0⟩ := by
    intro hzero
    subst q
    simp [dot] at hqdot
  have hfar : ∀ t : ℝ, 1 ≤ t → ray t q ∈ farRegion fs := by
    intro t ht
    change soupThresh fs < norm (ray t q)
    rw [norm_ray_of_nonneg t q (by linarith)]
    have hmul : norm q ≤ t * norm q := by
      simpa using (mul_le_mul_of_nonneg_right ht (norm_nonneg q))
    exact lt_of_lt_of_le hq hmul
  have hz := farRay_meshWinding_eq_zero fs q hq0 1 (by norm_num) hfar hloc 1 le_rfl
  simpa [ray] using hz

end

end Vdb
