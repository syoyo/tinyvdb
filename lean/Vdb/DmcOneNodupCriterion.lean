/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  **Global DMC-1 `Nodup` criterion (lane VS-2, first slice).** For every
  grid size `n` and shell-pinned sign field `s`, the assembled DMC-1
  directed mesh has no repeated edge exactly when no interior face of the
  padded grid is a bad-face configuration (`badFaceConfig`, the local
  obstruction enumerated in `Vdb/DmcOneNodupFailure.lean`). Consequently
  the Euler identity `χ = V − F` holds with the `Nodup` premise discharged
  by the criterion; finding F19 is the negative witness (its field has a
  bad face).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.DmcOneNodupFailure
import Vdb.DmcOneQuadInject
import Vdb.DmcOneAssemble
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Vdb
namespace DmcOneStitch

open Vdb.DmcOneEuler
open Vdb.DmcOnePad
open Vdb.PadGrid

local instance {α β : Type} (f : α → List β) :
    Std.Symm (fun x y : α => List.Disjoint (f x) (f y)) :=
  ⟨fun _ _ h => h.symm⟩

/-- An interior face of the `n^3` cell grid: its normal coordinate is
    strictly positive (`FaceBaseOK`) and the `+` cell lies strictly inside
    the cell grid (hence so does the `−` cell). -/
def InteriorFace (n : Nat) (na : Nat) (p : Lat) : Prop :=
  FaceBaseOK na p ∧ InCells n (facePlusCell na p)

/-- The global no-bad-face criterion: no interior face has a bad-face
    configuration (the case-pair obstruction of finding F19). -/
def NoBadFace (n : Nat) (s : Lat → Bool) : Prop :=
  ∀ (na : Nat) (hna : na < 3) (pF : Lat), InteriorFace n na pF →
    badFaceConfig na (cellCase s (facePlusCell na pF))
      (cellCase s (faceMinusCell na pF)) = false

/-! ### Local bridges -/

set_option maxHeartbeats 800000 in
lemma boundaryEdges_inLattice (n : Nat) (na : Nat) (hna : na < 3) (pF : Lat)
    (hin : InCells n pF) :
    ∀ j : Nat, j < 4 →
      InLattice n ((faceBoundaryEdges na pF).getD j (pF, 0)).1 ∧
      InLattice n (succN ((faceBoundaryEdges na pF).getD j (pF, 0)).1
        ((faceBoundaryEdges na pF).getD j (pF, 0)).2) := by
  intro j hj
  interval_cases na <;> interval_cases j <;>
    simp [faceBoundaryEdges, iaOf, ibOf, succN, InLattice, InCells] at hin ⊢ <;> omega

set_option maxHeartbeats 800000 in
lemma faceBase_inCells_of_crossed {n : Nat} (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false)
    {na : Nat} (hna : na < 3) {pF : Lat} (hx : FaceBaseOK na pF)
    {i : Nat} (hi : i < 4) {e : PadEdge}
    (heq : e = (faceBoundaryEdges na pF).getD i (pF, 0))
    (hlat : InLattice n e.1) (hlatsucc : InLattice n (succN e.1 e.2))
    (hcross : s e.1 ≠ s (succN e.1 e.2)) : InCells n pF := by
  subst e
  have ht := pinned_transverse n s hpin hlat hcross
  interval_cases na <;> interval_cases i <;>
    simp [faceBoundaryEdges, iaOf, ibOf, succN, InLattice, InCells] at hlat hlatsucc ht ⊢ <;> omega

set_option maxHeartbeats 800000 in
lemma cfgCrossed_signChange (s : Lat → Bool) {na : Nat} (hna : na < 3)
    {pF : Lat} (hx : FaceBaseOK na pF) {i : Nat} (hi : i < 4) :
    cfgCrossed (cellCase s (facePlusCell na pF)) na i = true →
    s ((faceBoundaryEdges na pF).getD i (pF, 0)).1 ≠
      s (succN ((faceBoundaryEdges na pF).getD i (pF, 0)).1
        ((faceBoundaryEdges na pF).getD i (pF, 0)).2) := by
  intro hc
  unfold cfgCrossed at hc
  let naF : Fin 3 := ⟨na, hna⟩
  let sideF : Fin 2 := ⟨0, by decide⟩
  let iF : Fin 4 := ⟨i, hi⟩
  have hbnd : if naF.val = 0 then 1 ≤ pF.1 else if naF.val = 1 then 1 ≤ pF.2.1 else 1 ≤ pF.2.2 := by
    simpa [FaceBaseOK, naF] using hx
  have hs := bitOf_start_sign naF sideF iF s pF.1 pF.2.1 pF.2.2 hbnd
  have he := endBitOf_start_sign naF sideF iF s pF.1 pF.2.1 pF.2.2 hbnd
  dsimp [naF, sideF, iF] at hs he ⊢
  rw [hs, he] at hc
  cases h1 : s ((faceBoundaryEdges na pF).getD i (pF, 0)).1 <;>
    cases h2 : s (succN ((faceBoundaryEdges na pF).getD i (pF, 0)).1
                    ((faceBoundaryEdges na pF).getD i (pF, 0)).2) <;> simp_all

set_option maxHeartbeats 800000 in
lemma boundaryEdge_dir_lt_three (na : Nat) (hna : na < 3) {pF : Lat}
    {i : Nat} (hi : i < 4) :
    ((faceBoundaryEdges na pF).getD i (pF, 0)).2 < 3 := by
  interval_cases na <;> interval_cases i <;> simp [faceBoundaryEdges, iaOf, ibOf]

/-! ### Classification of a mesh edge emitted by a *known* crossed edge

    This is the analogue of `classify_mesh_edge`, but the emitting crossed
    edge is an explicit argument rather than reconstructed from the mesh
    membership. Hence the returned edge `eB` is provably that crossed edge. -/

set_option maxHeartbeats 800000 in
lemma classify_crossed_mem (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false)
    {e : PadEdge} (he : e ∈ PadGrid.crossed n s)
    {a b : V} (hm : (a, b) ∈ quadDirectedEdges (dmcOneQuadN s e)) :
    ∃ (na : Nat) (hna : na < 3) (pF : Lat) (hx : FaceBaseOK na pF)
      (hlat : ∀ j : Nat, j < 4 →
        InLattice n ((faceBoundaryEdges na pF).getD j (pF, 0)).1 ∧
        InLattice n (succN ((faceBoundaryEdges na pF).getD j (pF, 0)).1
          ((faceBoundaryEdges na pF).getD j (pF, 0)).2))
      (i : Nat) (hi : i < 4) (eB : PadEdge)
      (heq : eB = (faceBoundaryEdges na pF).getD i (pF, 0))
      (hBe : eB = e) (dir : Bool),
      s eB.1 ≠ s (succN eB.1 eB.2) ∧
      flipDir i (s eB.1) = dir ∧
      (a, b) = if dir then
          (cellPatchVertex s (facePlusCell na pF) eB.1 eB.2,
           cellPatchVertex s (faceMinusCell na pF) eB.1 eB.2)
        else
          (cellPatchVertex s (faceMinusCell na pF) eB.1 eB.2,
           cellPatchVertex s (facePlusCell na pF) eB.1 eB.2) := by
  obtain ⟨hd3, hp3, hpSucc, hne0⟩ := PadGrid.crossed_spec n s he
  rcases e with ⟨⟨x, y, z⟩, d⟩
  have hne' : s (x, y, z) ≠ s (succN (x, y, z) d) := by simpa using hne0
  have hm' : (a, b) ∈ quadDirectedEdges (dmcOneQuadN s ((x, y, z), d)) := by simpa using hm
  have hb := pinned_transverse n s hpin hp3 hne'
  interval_cases d
  all_goals simp at hp3 hpSucc hne0 hm' hb
  ·
    have hpSucc0 := hpSucc
    simp [InLattice, succN] at hpSucc
    rcases hb with ⟨hb1, hb2, hb3, hb4⟩
    rcases hpSucc with ⟨hpS1, hpS2, hpS3⟩
    have hx0 : 0 ≤ x := Nat.zero_le x
    have hy : 1 ≤ y := by omega
    have hz : 1 ≤ z := by omega
    have hxN : x < n := by omega
    have hyN : y < n := by omega
    have hzN : z < n := by omega
    by_cases hs : s (x, y, z) = false
    ·
      have hR := ring_pair_0_false s x y z hx0 hy hz hs hne' a b hm'
      rcases hR with hcase | hcase | hcase | hcase
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_0_false_0 n s x y z hx0 hy hz hp3 hpSucc0 hxN hyN hzN
            hs hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_0_false_1 n s x y z hx0 hy hz hp3 hpSucc0 hxN hyN hzN
            hs hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_0_false_2 n s x y z hx0 hy hz hp3 hpSucc0 hxN hyN hzN
            hs hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_0_false_3 n s x y z hx0 hy hz hp3 hpSucc0 hxN hyN hzN
            hs hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
    ·
      have hsT : s (x, y, z) = true := by cases hh : s (x, y, z) <;> simp_all
      have hR := ring_pair_0_true s x y z hx0 hy hz hsT hne' a b hm'
      rcases hR with hcase | hcase | hcase | hcase
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_0_true_0 n s x y z hx0 hy hz hp3 hpSucc0 hxN hyN hzN
            hsT hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_0_true_1 n s x y z hx0 hy hz hp3 hpSucc0 hxN hyN hzN
            hsT hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_0_true_2 n s x y z hx0 hy hz hp3 hpSucc0 hxN hyN hzN
            hsT hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_0_true_3 n s x y z hx0 hy hz hp3 hpSucc0 hxN hyN hzN
            hsT hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
  ·
    have hpSucc0 := hpSucc
    simp [InLattice, succN] at hpSucc
    rcases hb with ⟨hb1, hb2, hb3, hb4⟩
    rcases hpSucc with ⟨hpS1, hpS2, hpS3⟩
    have hx : 1 ≤ x := by omega
    have hy0 : 0 ≤ y := Nat.zero_le y
    have hz : 1 ≤ z := by omega
    have hxN : x < n := by omega
    have hyN : y < n := by omega
    have hzN : z < n := by omega
    by_cases hs : s (x, y, z) = false
    ·
      have hR := ring_pair_1_false s x y z hx hy0 hz hs hne' a b hm'
      rcases hR with hcase | hcase | hcase | hcase
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_1_false_0 n s x y z hx hy0 hz hp3 hpSucc0 hxN hyN hzN
            hs hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_1_false_1 n s x y z hx hy0 hz hp3 hpSucc0 hxN hyN hzN
            hs hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_1_false_2 n s x y z hx hy0 hz hp3 hpSucc0 hxN hyN hzN
            hs hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_1_false_3 n s x y z hx hy0 hz hp3 hpSucc0 hxN hyN hzN
            hs hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
    ·
      have hsT : s (x, y, z) = true := by cases hh : s (x, y, z) <;> simp_all
      have hR := ring_pair_1_true s x y z hx hy0 hz hsT hne' a b hm'
      rcases hR with hcase | hcase | hcase | hcase
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_1_true_0 n s x y z hx hy0 hz hp3 hpSucc0 hxN hyN hzN
            hsT hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_1_true_1 n s x y z hx hy0 hz hp3 hpSucc0 hxN hyN hzN
            hsT hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_1_true_2 n s x y z hx hy0 hz hp3 hpSucc0 hxN hyN hzN
            hsT hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_1_true_3 n s x y z hx hy0 hz hp3 hpSucc0 hxN hyN hzN
            hsT hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
  ·
    have hpSucc0 := hpSucc
    simp [InLattice, succN] at hpSucc
    rcases hb with ⟨hb1, hb2, hb3, hb4⟩
    rcases hpSucc with ⟨hpS1, hpS2, hpS3⟩
    have hx : 1 ≤ x := by omega
    have hy : 1 ≤ y := by omega
    have hz0 : 0 ≤ z := Nat.zero_le z
    have hxN : x < n := by omega
    have hyN : y < n := by omega
    have hzN : z < n := by omega
    by_cases hs : s (x, y, z) = false
    ·
      have hR := ring_pair_2_false s x y z hx hy hz0 hs hne' a b hm'
      rcases hR with hcase | hcase | hcase | hcase
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_2_false_0 n s x y z hx hy hz0 hp3 hpSucc0 hxN hyN hzN
            hs hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_2_false_1 n s x y z hx hy hz0 hp3 hpSucc0 hxN hyN hzN
            hs hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_2_false_2 n s x y z hx hy hz0 hp3 hpSucc0 hxN hyN hzN
            hs hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_2_false_3 n s x y z hx hy hz0 hp3 hpSucc0 hxN hyN hzN
            hs hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
    ·
      have hsT : s (x, y, z) = true := by cases hh : s (x, y, z) <;> simp_all
      have hR := ring_pair_2_true s x y z hx hy hz0 hsT hne' a b hm'
      rcases hR with hcase | hcase | hcase | hcase
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_2_true_0 n s x y z hx hy hz0 hp3 hpSucc0 hxN hyN hzN
            hsT hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_2_true_1 n s x y z hx hy hz0 hp3 hpSucc0 hxN hyN hzN
            hsT hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_2_true_2 n s x y z hx hy hz0 hp3 hpSucc0 hxN hyN hzN
            hsT hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩
      · rcases hcase with ⟨ha, hbS⟩
        obtain ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩ :=
          classify_2_true_3 n s x y z hx hy hz0 hp3 hpSucc0 hxN hyN hzN
            hsT hne' a b ha hbS
        exact ⟨na, hna, pF, hx', hlat, i, hi, eB, heq, heqraw, dir, hcross, hdir, hpair⟩

/-! ### Distinct crossed edges cannot emit the same directed edge
    unless an interior face is bad. -/

set_option maxHeartbeats 800000 in
lemma no_shared_pair (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false) (hnb : NoBadFace n s)
    {e e' : PadEdge} (he : e ∈ PadGrid.crossed n s) (he' : e' ∈ PadGrid.crossed n s)
    (hnee : e ≠ e') {a b : V}
    (hm : (a, b) ∈ quadDirectedEdges (dmcOneQuadN s e))
    (hm' : (a, b) ∈ quadDirectedEdges (dmcOneQuadN s e')) : False := by
  obtain ⟨na, hna, pF, hx, hlat, i, hi, eB, heq, hBe, dir, hcross, hdir, hpair⟩ :=
    classify_crossed_mem n s hpin he hm
  obtain ⟨na', hna', pF', hxF', hlat', i', hi', eB', heq', hBe', dir', hcross', hdir', hpair'⟩ :=
    classify_crossed_mem n s hpin he' hm'
  have hc1 := congrArg (fun v : V => v.1) (congrArg Prod.fst (hpair.symm.trans hpair'))
  have hc2 := congrArg (fun v : V => v.1) (congrArg Prod.snd (hpair.symm.trans hpair'))
  dsimp [cellPatchVertex] at hc1 hc2
  have hcells : (facePlusCell na pF = facePlusCell na' pF' ∧ faceMinusCell na pF = faceMinusCell na' pF')
      ∨ (facePlusCell na pF = faceMinusCell na' pF' ∧ faceMinusCell na pF = facePlusCell na' pF') := by
    by_cases hd : dir <;> by_cases hd' : dir'
    · left; simpa [hd, hd'] using And.intro hc1 hc2
    · right; simpa [hd, hd'] using And.intro hc1 hc2
    · right; simpa [hd, hd'] using And.intro hc2 hc1
    · left; simpa [hd, hd'] using And.intro hc2 hc1
  have hface := facePair_unique hna hna' hx hxF' hcells
  rcases hface with ⟨hnaeq, hpFeq⟩
  subst na'
  subst pF'
  by_cases hii : i = i'
  · have heBeB' : eB = eB' := by rw [heq, heq', hii]
    have hee : e = e' := by rw [← hBe, ← hBe', heBeB']
    exact hnee hee
  · have hcA : s ((faceBoundaryEdges na pF).getD i (pF, 0)).1 ≠
        s (succN ((faceBoundaryEdges na pF).getD i (pF, 0)).1
          ((faceBoundaryEdges na pF).getD i (pF, 0)).2) := by
      simpa [heq] using hcross
    have hcB : s ((faceBoundaryEdges na pF).getD i' (pF, 0)).1 ≠
        s (succN ((faceBoundaryEdges na pF).getD i' (pF, 0)).1
          ((faceBoundaryEdges na pF).getD i' (pF, 0)).2) := by
      simpa [heq'] using hcross'
    have hdA : flipDir i (s ((faceBoundaryEdges na pF).getD i (pF, 0)).1) = dir := by
      simpa [heq] using hdir
    have hdB : flipDir i' (s ((faceBoundaryEdges na pF).getD i' (pF, 0)).1) = dir' := by
      simpa [heq'] using hdir'
    have hpA : (a, b) = if dir then
        (cellPatchVertex s (facePlusCell na pF) ((faceBoundaryEdges na pF).getD i (pF, 0)).1
           ((faceBoundaryEdges na pF).getD i (pF, 0)).2,
         cellPatchVertex s (faceMinusCell na pF) ((faceBoundaryEdges na pF).getD i (pF, 0)).1
           ((faceBoundaryEdges na pF).getD i (pF, 0)).2)
      else
        (cellPatchVertex s (faceMinusCell na pF) ((faceBoundaryEdges na pF).getD i (pF, 0)).1
           ((faceBoundaryEdges na pF).getD i (pF, 0)).2,
         cellPatchVertex s (facePlusCell na pF) ((faceBoundaryEdges na pF).getD i (pF, 0)).1
           ((faceBoundaryEdges na pF).getD i (pF, 0)).2) := by
      simpa [heq] using hpair
    have hpB : (a, b) = if dir' then
        (cellPatchVertex s (facePlusCell na pF) ((faceBoundaryEdges na pF).getD i' (pF, 0)).1
           ((faceBoundaryEdges na pF).getD i' (pF, 0)).2,
         cellPatchVertex s (faceMinusCell na pF) ((faceBoundaryEdges na pF).getD i' (pF, 0)).1
           ((faceBoundaryEdges na pF).getD i' (pF, 0)).2)
      else
        (cellPatchVertex s (faceMinusCell na pF) ((faceBoundaryEdges na pF).getD i' (pF, 0)).1
           ((faceBoundaryEdges na pF).getD i' (pF, 0)).2,
         cellPatchVertex s (facePlusCell na pF) ((faceBoundaryEdges na pF).getD i' (pF, 0)).1
           ((faceBoundaryEdges na pF).getD i' (pF, 0)).2) := by
      simpa [heq'] using hpair'
    have hif : InteriorFace n na pF := by
      refine ⟨hx, ?_⟩
      have hli := hlat i hi
      have hlat_e : InLattice n eB.1 := by simpa [heq] using hli.1
      have hlats_e : InLattice n (succN eB.1 eB.2) := by simpa [heq] using hli.2
      exact faceBase_inCells_of_crossed s hpin hna hx hi heq hlat_e hlats_e hcross
    rcases lt_or_gt_of_ne hii with hlt | hlt
    · have hbad := same_pair_badFace hna hx hi hi' hlt (hcross := hcA) (hcross' := hcB) hdA hdB hpA hpB
      simp [hnb na hna pF hif] at hbad
    · have hbad := same_pair_badFace hna hx hi' hi hlt (hcross := hcB) (hcross' := hcA) hdB hdA hpB hpA
      simp [hnb na hna pF hif] at hbad

/-! ### A bad interior face makes two crossed edges share a directed edge. -/

set_option maxHeartbeats 800000 in
lemma faceBoundaryEdges_getD_inj {na : Nat} (hna : na < 3) {pF : Lat}
    {i j : Nat} (hi : i < 4) (hj : j < 4) (hij : i < j) :
    (faceBoundaryEdges na pF).getD i (pF, 0) ≠ (faceBoundaryEdges na pF).getD j (pF, 0) := by
  intro h
  rcases pF with ⟨x, y, z⟩
  interval_cases na <;> interval_cases i <;> interval_cases j <;>
    simp [faceBoundaryEdges, iaOf, ibOf, succN] at h ⊢ <;> omega

set_option maxHeartbeats 800000 in
lemma badFace_shared_pair (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false)
    {na : Nat} (hna : na < 3) {pF : Lat} (hif : InteriorFace n na pF)
    (hbad : badFaceConfig na (cellCase s (facePlusCell na pF))
      (cellCase s (faceMinusCell na pF)) = true) :
    ∃ (e e' : PadEdge), e ∈ PadGrid.crossed n s ∧ e' ∈ PadGrid.crossed n s ∧ e ≠ e' ∧
      ∃ (a b : V), (a, b) ∈ quadDirectedEdges (dmcOneQuadN s e) ∧
        (a, b) ∈ quadDirectedEdges (dmcOneQuadN s e') := by
  have hx : FaceBaseOK na pF := hif.1
  have hlatAll := boundaryEdges_inLattice n na hna pF hif.2
  let be := fun t : Nat => (faceBoundaryEdges na pF).getD t (pF, 0)
  let cA : Cell := facePlusCell na pF
  let cB : Cell := faceMinusCell na pF
  unfold badFaceConfig at hbad
  rw [List.any_eq_true] at hbad
  rcases hbad with ⟨i, hi_mem, hbad_i⟩
  rw [List.any_eq_true] at hbad_i
  rcases hbad_i with ⟨j, hj_mem, hbad_ij⟩
  have hi : i < 4 := List.mem_range.mp hi_mem
  have hj : j < 4 := List.mem_range.mp hj_mem
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hbad_ij
  rcases hbad_ij with ⟨⟨⟨⟨⟨hij, hci⟩, hcj⟩, hpatchAeq⟩, hpatchBeq⟩, hdirEq⟩
  have hpatchA : cfgPatch (cellCase s cA) na 0 i = cfgPatch (cellCase s cA) na 0 j := by
    simpa [cA] using hpatchAeq
  have hpatchB : cfgPatch (cellCase s cB) na 1 i = cfgPatch (cellCase s cB) na 1 j := by
    simpa [cB] using hpatchBeq
  have hsign_i : s (be i).1 ≠ s (succN (be i).1 (be i).2) :=
    cfgCrossed_signChange s hna hx hi (by simpa [be] using hci)
  have hsign_j : s (be j).1 ≠ s (succN (be j).1 (be j).2) :=
    cfgCrossed_signChange s hna hx hj (by simpa [be] using hcj)
  have hcb_i : crossedB n s (be i) = true := by
    unfold crossedB
    rw [decide_eq_true_eq.mpr (hlatAll i hi).1, decide_eq_true_eq.mpr (hlatAll i hi).2]
    cases h1 : s (be i).1 <;> cases h2 : s (succN (be i).1 (be i).2) <;> simp_all
  have hcb_j : crossedB n s (be j) = true := by
    unfold crossedB
    rw [decide_eq_true_eq.mpr (hlatAll j hj).1, decide_eq_true_eq.mpr (hlatAll j hj).2]
    cases h1 : s (be j).1 <;> cases h2 : s (succN (be j).1 (be j).2) <;> simp_all
  have hcrossed_i : be i ∈ PadGrid.crossed n s :=
    crossed_of_crossedB n s hcb_i (List.mem_range.mpr (by simpa [be] using boundaryEdge_dir_lt_three na hna hi))
  have hcrossed_j : be j ∈ PadGrid.crossed n s :=
    crossed_of_crossedB n s hcb_j (List.mem_range.mpr (by simpa [be] using boundaryEdge_dir_lt_three na hna hj))
  have heij : be i ≠ be j := by
    dsimp [be]
    exact faceBoundaryEdges_getD_inj hna hi hj hij
  have hsd_i := edge_dir_p na hna i hi s pF
    (edgeBaseOK_of_crossed n s hpin pF.1 pF.2.1 pF.2.2 na i hna hi (by simpa [be] using hsign_i))
  have hsd_j := edge_dir_p na hna j hj s pF
    (edgeBaseOK_of_crossed n s hpin pF.1 pF.2.1 pF.2.2 na j hna hj (by simpa [be] using hsign_j))
  have hm_i := side_of_sideDir s (be i) cA cB (flipDir i (s (be i).1))
    (by simpa [be] using hsign_i) (by simpa [be] using hsd_i)
  have hm_j := side_of_sideDir s (be j) cA cB (flipDir j (s (be j).1))
    (by simpa [be] using hsign_j) (by simpa [be] using hsd_j)
  have hbi : cfgDir (cellCase s cA) na i = flipDir i (s (be i).1) := by
    have := cfgDir_eq_dir s hna hx hi (rfl : flipDir i (s (be i).1) = flipDir i (s (be i).1))
    simpa [be] using this
  have hbj : cfgDir (cellCase s cA) na j = flipDir j (s (be j).1) := by
    have := cfgDir_eq_dir s hna hx hj (rfl : flipDir j (s (be j).1) = flipDir j (s (be j).1))
    simpa [be] using this
  have hflipEq : flipDir i (s (be i).1) = flipDir j (s (be j).1) := by
    rw [← hbi, ← hbj]
    simpa [cA] using hdirEq
  have hvA : cellPatchVertex s cA (be i).1 (be i).2 = cellPatchVertex s cA (be j).1 (be j).2 := by
    have hi' := patchAt_boundary s hna hx hi 0 (by decide : 0 < 2)
    have hj' := patchAt_boundary s hna hx hj 0 (by decide : 0 < 2)
    have hpAeq : (cellPatchVertex s cA (be i).1 (be i).2).2 =
        (cellPatchVertex s cA (be j).1 (be j).2).2 := by
      simpa [be, cA] using hi'.trans (hpatchA.trans hj'.symm)
    unfold cellPatchVertex
    exact Prod.ext rfl (by simpa [cellPatchVertex] using hpAeq)
  have hvB : cellPatchVertex s cB (be i).1 (be i).2 = cellPatchVertex s cB (be j).1 (be j).2 := by
    have hi' := patchAt_boundary s hna hx hi 1 (by decide : 1 < 2)
    have hj' := patchAt_boundary s hna hx hj 1 (by decide : 1 < 2)
    have hpBeq : (cellPatchVertex s cB (be i).1 (be i).2).2 =
        (cellPatchVertex s cB (be j).1 (be j).2).2 := by
      simpa [be, cB] using hi'.trans (hpatchB.trans hj'.symm)
    unfold cellPatchVertex
    exact Prod.ext rfl (by simpa [cellPatchVertex] using hpBeq)
  let pi := if flipDir i (s (be i).1) then
      (cellPatchVertex s cA (be i).1 (be i).2, cellPatchVertex s cB (be i).1 (be i).2)
    else
      (cellPatchVertex s cB (be i).1 (be i).2, cellPatchVertex s cA (be i).1 (be i).2)
  let pj := if flipDir j (s (be j).1) then
      (cellPatchVertex s cA (be j).1 (be j).2, cellPatchVertex s cB (be j).1 (be j).2)
    else
      (cellPatchVertex s cB (be j).1 (be j).2, cellPatchVertex s cA (be j).1 (be j).2)
  have hpij : pi = pj := by
    dsimp [pi, pj]
    rw [hflipEq, hvA, hvB]
  have hmi : pi ∈ quadDirectedEdges (dmcOneQuadN s (be i)) := by simpa [pi, cA, cB] using hm_i
  have hmj : pj ∈ quadDirectedEdges (dmcOneQuadN s (be j)) := by simpa [pj, cA, cB] using hm_j
  exact ⟨be i, be j, hcrossed_i, hcrossed_j, heij, pi.1, pi.2,
    by simpa using hmi, by simpa [hpij] using hmj⟩

/-! ### The global criterion -/

set_option maxHeartbeats 800000 in
theorem mesh_nodup_iff_noBadFace (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false) :
    (Vdb.DmcOneEuler.dmcOneMeshEdges n s).Nodup ↔ NoBadFace n s := by
  constructor
  · intro hnod na hna pF hif
    by_contra hnot
    have hbad : badFaceConfig na (cellCase s (facePlusCell na pF))
        (cellCase s (faceMinusCell na pF)) = true := by
      cases hcf : badFaceConfig na (cellCase s (facePlusCell na pF))
          (cellCase s (faceMinusCell na pF)) <;> simp_all
    obtain ⟨e, e', he, he', heij, a, b, hm, hm'⟩ := badFace_shared_pair n s hpin hna hif hbad
    have hnod' : ((PadGrid.crossed n s).flatMap
        (fun e => quadDirectedEdges (dmcOneQuadN s e))).Nodup := by
      simpa [Vdb.DmcOneEuler.dmcOneMeshEdges, Vdb.DmcOneEuler.dmcOneQuads_eq_map_crossed,
        List.flatMap_map, Function.comp_def] using hnod
    have hpair := (List.nodup_flatMap.mp hnod').2
    have hdisj := hpair.forall he he' heij
    exact (List.disjoint_left.mp hdisj) hm hm'
  · intro hnb
    have hnod' : ((PadGrid.crossed n s).flatMap
        (fun e => quadDirectedEdges (dmcOneQuadN s e))).Nodup := by
      apply (List.nodup_flatMap).2
      constructor
      · intro e he
        obtain ⟨hd, hp, hpS, hne⟩ := PadGrid.crossed_spec n s he
        have hq := quad_ok n s hpin e.1 e.2 hd hp hne
        exact quadDirectedEdges_nodup (by simpa using hq.2) (by simpa using hq.1)
      · refine List.pairwise_iff_getElem.mpr ?_
        intro i j hi hj hij
        let ei := (PadGrid.crossed n s)[i]
        let ej := (PadGrid.crossed n s)[j]
        have hei : ei ∈ PadGrid.crossed n s := by
          dsimp [ei]
          exact List.getElem_mem hi
        have hej : ej ∈ PadGrid.crossed n s := by
          dsimp [ej]
          exact List.getElem_mem hj
        have hneij : ei ≠ ej := by
          intro heq
          have hijeq : i = j := (PadGrid.nodup_crossed n s).getElem_inj_iff.mp heq
          omega
        change List.Disjoint (quadDirectedEdges (dmcOneQuadN s ei))
          (quadDirectedEdges (dmcOneQuadN s ej))
        rw [List.disjoint_left]
        intro x hx hx'
        exact no_shared_pair n s hpin hnb hei hej hneij hx hx'
    simpa [Vdb.DmcOneEuler.dmcOneMeshEdges, Vdb.DmcOneEuler.dmcOneQuads_eq_map_crossed,
      List.flatMap_map, Function.comp_def] using hnod'

/-- **Euler characteristic with the `Nodup` premise discharged.** Under
    shell pinning and the criterion `NoBadFace`, `χ = V − F` for every `n`. -/
theorem euler_general_dmc1_of_noBadFace (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false) (hnb : NoBadFace n s) :
    ((QuadEuler.vertices (Vdb.DmcOneEuler.dmcOneMeshEdges n s)).card : Int)
        - (QuadEuler.undirected (Vdb.DmcOneEuler.dmcOneMeshEdges n s)).card
        + (PadGrid.crossed n s).length
      = (QuadEuler.vertices (Vdb.DmcOneEuler.dmcOneMeshEdges n s)).card - (PadGrid.crossed n s).length :=
  euler_general_dmc1_of_nodup n s hpin ((mesh_nodup_iff_noBadFace n s hpin).2 hnb)

/-- Finding F19 as a negative witness: its field has a bad interior face,
    so its mesh repeats an edge and the Euler identity fails. -/
theorem nodupFailure_noBadFace_fails : ¬ NoBadFace 4 nodupFailureField := by
  intro hnb
  exact nodupFailure_not_nodup ((mesh_nodup_iff_noBadFace 4 nodupFailureField
    nodupFailure_shellPinned).2 hnb)

end DmcOneStitch
end Vdb
