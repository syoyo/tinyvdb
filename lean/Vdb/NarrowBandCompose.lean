/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Narrow-band composition (plan §5.4): the mesh→level-set pipeline produces
  a candidate grid; `tvdb_signed_flood_fill` (dense, `src/tinyvdb_ops.c`)
  then floods the far (`|v| ≥ band`) voxels from the grid boundary and writes
  `+band` to the reachable (exterior) ones and `−band` to the rest;
  `tvdb_grid_prune` then collapses the uniform subtrees into tiles. The claim
  this module verifies is the composition statement:

      denote(prune(floodFill(candidate))) = clamp(signedDist, −in, ext)

  where `signedDist` is the true signed distance field on the band and
  `±width` is the flood-fill's constant off-band fill. The hypothesis is the
  one the pipeline actually relies on — a *correct sign oracle*: the flood
  fill's exterior is exactly the region `0 < signedDist`.

  What is proved here (all over the `nx × ny × nz` lattice, mirroring the
  `FloodFill.lean` model):

  * `signedFill` — the dense `tvdb_signed_flood_fill` as a definition;
  * its exact postcondition (`signedFill_far`/`signedFill_near`): band values
    are preserved; far voxels carry `±w`;
  * **`signedFill_eq_clamp`** — under the three hypotheses (exact measurement
    on the band, the generator's far set covering `d`'s far set, and the sign
    oracle), the filled field is exactly `clamp(signedDist, −w, +w)`;
  * **prune preservation** — `PruneStep`/`PruneClosed` model uniform-subtree
    collapsing (and deletion of background-equal inactive tiles drops out as a
    no-op at the value level); both preserve the denoted function pointwise
    (`PruneStep_denote`, `PruneClosed_denote`);
  * **`pruneClosed_pruneClosed_clamp`** — the final field is exactly
    `clamp(signedDist, −w, +w)`: the composed denote the plan asks for.

  What is *not* modelled: the sparse/tree variant's active-voxel graph and
  the tree `tvdb_grid_signed_flood_fill` propagation (they share the sign
  semantics but iterate over the sparse tree, not the lattice); the
  winding-number/ray-parity oracles that discharge the sign-oracle hypothesis
  (see `Vdb/WindingNumber.lean` / `Vdb/MeshRay.lean`).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.FloodFill
import Mathlib.Tactic

namespace Vdb

open Finset

variable {nx ny nz : ℕ}

/-- The grid-boundary voxels (the flood-fill's seeds for "infinity"). -/
noncomputable def boundaryOf (nx ny nz : ℕ) : Finset (GPoint nx ny nz) :=
  Finset.univ.filter fun p =>
    p.1.val = 0 ∨ p.1.val = nx - 1 ∨ p.2.1.val = 0 ∨ p.2.1.val = ny - 1 ∨
    p.2.2.val = 0 ∨ p.2.2.val = nz - 1

/-- The flood-fill's seed set: far voxels on the grid boundary. -/
noncomputable def boundaryFar (g : GPoint nx ny nz → ℝ) (w : ℝ) : Finset (GPoint nx ny nz) :=
  (boundaryOf nx ny nz).filter (fun p => w ≤ |g p|)

/-- The far predicate as a decidable boolean (the C code tests it on every
    visit). -/
noncomputable def farBool (g : GPoint nx ny nz → ℝ) (w : ℝ) (p : GPoint nx ny nz) : Bool :=
  decide (w ≤ |g p|)

theorem boundaryFar_far {g : GPoint nx ny nz → ℝ} {w : ℝ} {p : GPoint nx ny nz}
    (hp : p ∈ boundaryFar g w) : farBool g w p = true := by
  unfold boundaryFar at hp
  simp only [Finset.mem_filter] at hp
  exact (decide_eq_true_iff ..).mpr hp.2

/-- The dense `tvdb_signed_flood_fill` end state:

    * band voxels (`|g v| < w`) keep their value;
    * far voxels on the boundary-connected component are set to `+w`, the
      rest to `−w`. -/
noncomputable def signedFill (g : GPoint nx ny nz → ℝ) (w : ℝ)
    (v : GPoint nx ny nz) : ℝ :=
  if w ≤ |g v| then
    (if v ∈ exteriorFar (farBool g w) (boundaryFar g w) then w else -w)
  else g v

/-- The fill writes exactly `±w` to far voxels (the clamp postcondition). -/
theorem signedFill_far {g : GPoint nx ny nz → ℝ} {w : ℝ} {v : GPoint nx ny nz}
    (h : w ≤ |g v|) : signedFill g w v = w ∨ signedFill g w v = -w := by
  unfold signedFill
  rw [ite_eq_left h]
  by_cases hv : v ∈ exteriorFar (farBool g w) (boundaryFar g w)
  · simp [hv]
  · simp [hv]

/-- Band values are preserved by the fill. -/
theorem signedFill_near {g : GPoint nx ny nz → ℝ} {w : ℝ} {v : GPoint nx ny nz}
    (h : |g v| < w) : signedFill g w v = g v := by
  unfold signedFill
  rw [ite_eq_right (not_le.mpr h)]

/-- Every boundary far voxel ends up `+w` after the fill (the seeds). -/
theorem signedFill_boundary {g : GPoint nx ny nz → ℝ} {w : ℝ} {v : GPoint nx ny nz}
    (hb : v ∈ boundaryFar g w) : signedFill g w v = w := by
  have hvf : w ≤ |g v| := by
    unfold boundaryFar at hb
    simp only [Finset.mem_filter] at hb
    simpa using hb.2
  unfold signedFill
  rw [ite_eq_left hvf]
  have hvf' : v ∈ exteriorFar (farBool g w) (boundaryFar g w) := by
    unfold exteriorFar
    have h0 : v ∈ fillIter (farBool g w) (boundaryFar g w) 0 := hb
    exact fillIter_mono' (farBool g w) (boundaryFar g w)
      (show 0 ≤ nx * (ny * nz) + 1 by omega) h0
  simp [hvf']

/-- **Composition (denote of flood fill)**: under the three hypotheses the
    pipeline actually relies on, the filled field is exactly the clamped
    signed distance field.

    * `hband` — the band carries the true field (`|d v| < w → g v = d v`);
    * `hdfar` — the generator's far set covers `d`'s (`w ≤ |d v| → w ≤ |g v|`):
      the candidate grid's band never misses a voxel the clamp would pin at
      `±w`;
    * `H` — the *sign oracle*: the flood fill's exterior is exactly the
      region `0 < d v` (this is what the winding-number/ray-parity oracles
      supply for closed oriented meshes; it is *not* provable in general). -/
theorem signedFill_eq_clamp (d g : GPoint nx ny nz → ℝ) (w : ℝ) (hw : 0 < w)
    (hband : ∀ v, |d v| < w → g v = d v)
    (hdfar : ∀ v, w ≤ |d v| → w ≤ |g v|)
    (H : ∀ v, w ≤ |g v| →
      (v ∈ exteriorFar (farBool g w) (boundaryFar g w) ↔ 0 < d v)) :
    signedFill g w = fun v => max (-w) (min (d v) w) := by
  funext v
  by_cases hb : |d v| < w
  · have hgv := hband v hb
    have hgn : |g v| < w := by
      rw [hgv]; exact hb
    rw [signedFill_near hgn, hgv]
    have hclamp : d v ≤ w := by linarith [abs_lt.mp hb, hb]
    have hclamp' : -w ≤ d v := by linarith [abs_lt.mp hb, hb]
    rw [min_eq_left hclamp, max_eq_right hclamp']
  · have hw' : w ≤ |d v| := not_lt.mp hb
    have hgfar := hdfar v hw'
    rw [signedFill]
    rw [ite_eq_left hgfar]
    have horacle := H v hgfar
    by_cases hv : v ∈ exteriorFar (farBool g w) (boundaryFar g w)
    · have hpos : 0 < d v := horacle.mp hv
      have hclamp : d v ≥ w := by
        have habs := abs_of_nonneg hpos.le
        linarith [hw', habs, hpos]
      simp [hv, min_eq_right hclamp, max_eq_right (by linarith : -w ≤ w)]
    · have hneg : d v ≤ 0 := not_lt.mp (mt horacle.mpr hv)
      have hclamp : d v ≤ -w := by
        have habs := abs_of_nonpos hneg
        linarith [hw', habs, hneg]
      have hle : d v ≤ w := by linarith [hw, hneg]
      simp [hv, min_eq_left hle, max_eq_left hclamp]

/-! ### Prune: uniform-subtree collapse preserves the denoted function -/

open Classical

/-- One prune step: a region on which the field is constant is collapsed to a
    constant tile (the C `tvdb_grid_prune` turns uniform subtrees into root
    tiles, and inactive background-equal uniform tiles are dropped). -/
inductive PruneStep : (GPoint nx ny nz → ℝ) → (GPoint nx ny nz → ℝ) → Prop
  | collapse (s : Set (GPoint nx ny nz)) (c : ℝ) (f : GPoint nx ny nz → ℝ)
      (h : ∀ v, v ∈ s → f v = c) :
      PruneStep f (fun v => if v ∈ s then c else f v)

/-- A prune step does not change the denoted value anywhere. -/
theorem pruneStep_denote {f g : GPoint nx ny nz → ℝ} (h : PruneStep f g) (v) :
    g v = f v := by
  cases h with
  | collapse s c f hc =>
      by_cases hv : v ∈ s
      · simp [hv, hc v hv]
      · simp [hv]

/-- The transitive closure of prune steps (the C `tvdb_grid_prune` applies
    collapsing bottom-up over the whole tree). -/
inductive PruneClosed : (GPoint nx ny nz → ℝ) → (GPoint nx ny nz → ℝ) → Prop
  | refl (f : GPoint nx ny nz → ℝ) : PruneClosed f f
  | step {f g h : GPoint nx ny nz → ℝ} : PruneStep f g → PruneClosed g h → PruneClosed f h

/-- Pruning never changes the denoted value anywhere (any number of steps). -/
theorem pruneClosed_denote {f g : GPoint nx ny nz → ℝ} (h : PruneClosed f g) (v) :
    g v = f v := by
  induction h with
  | refl => rfl
  | step h1 h2 ih =>
      exact ih.trans (pruneStep_denote h1 v)

/-- **Composition (denote of flood fill + prune)**: the final field is exactly
    the clamped signed distance field — the theorem plan-lean.md §5.4 asks
    for. Follows from `signedFill_eq_clamp` plus pointwise preservation
    through any number of prune steps. -/
theorem pruned_pruneClosed_clamp {d g final : GPoint nx ny nz → ℝ} (w : ℝ) (hw : 0 < w)
    (hband : ∀ v, |d v| < w → g v = d v)
    (hdfar : ∀ v, w ≤ |d v| → w ≤ |g v|)
    (H : ∀ v, w ≤ |g v| →
      (v ∈ exteriorFar (farBool g w) (boundaryFar g w) ↔ 0 < d v))
    (hp : PruneClosed (signedFill g w) final) :
    final = fun v => max (-w) (min (d v) w) := by
  funext v
  rw [pruneClosed_denote hp v]
  exact congrFun (signedFill_eq_clamp d g w hw hband hdfar H) v
