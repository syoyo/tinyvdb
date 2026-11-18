/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  **The DMC-1 no-repeat condition is not automatic.** A concrete
  shell-pinned sign field on the `n = 4` padded grid whose assembled
  DMC-1 mesh is `EdgeClosed` (hence watertight) but has a repeated
  directed edge. Consequently `2·|E| ≠ 4·F` and the Euler identity
  `χ = V − F` genuinely fails for this field, so the `Nodup`
  hypothesis of `DmcOneEuler.euler_general_dmc1` (and of
  `DmcOneAssemble.euler_general_dmc1_unconditional`) cannot be removed.

  The field is the local configuration found by enumerating the two
  cell cases `62` (plus cell at `(2,1,1)`) and `61` (minus cell at
  `(1,1,1)`): two crossed edges of their shared face carry the same
  patch id in both cells and emit the same direction, producing one
  duplicated directed edge and its reverse.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.DmcOneEuler
import Vdb.DmcOneAssemble
import Vdb.DmcOnePad
import Vdb.DmcOneStitchEnum
import Vdb.PadGrid
import Vdb.QuadEuler
import Mathlib.Tactic

set_option linter.unusedSimpArgs false

namespace Vdb
namespace DmcOneEuler

abbrev Lat4 := Nat × Nat × Nat

/-- The Bourke bit `j` of the case `k`, as a sign. -/
def caseBitB (k j : Nat) : Bool := k / 2 ^ j % 2 = 1

/-- The lattice corner of the cell `c` at Bourke bit `j`. -/
def cornerSign4 (c : Lat4) (j : Nat) : Lat4 :=
  match j with
  | 0 => c
  | 1 => (c.1 + 1, c.2.1, c.2.2)
  | 2 => (c.1 + 1, c.2.1 + 1, c.2.2)
  | 3 => (c.1, c.2.1 + 1, c.2.2)
  | 4 => (c.1, c.2.1, c.2.2 + 1)
  | 5 => (c.1 + 1, c.2.1, c.2.2 + 1)
  | 6 => (c.1 + 1, c.2.1 + 1, c.2.2 + 1)
  | _ => (c.1, c.2.1 + 1, c.2.2 + 1)

/-- The counterexample field: the cell `(2,1,1)` carries case `62`,
    the cell `(1,1,1)` carries case `61` (the minus cell's assignment
    wins on their four shared corners), every other lattice point is
    `false`. The two cells lie strictly inside the `n = 4` grid, so
    the field is shell-pinned. -/
def nodupFailureField (p : Lat4) : Bool :=
  let cA : Lat4 := (2, 1, 1)
  let cB : Lat4 := (1, 1, 1)
  match (List.range 8).find? (fun j => cornerSign4 cB j == p) with
  | some j => caseBitB 61 j
  | none => match (List.range 8).find? (fun j => cornerSign4 cA j == p) with
            | some j => caseBitB 62 j
            | none => false

/-- The field pins the shell to `false`. -/
theorem nodupFailure_shellPinned :
    ∀ p, PadGrid.isShell 4 p = true → nodupFailureField p = false := by
  intro p hp
  unfold nodupFailureField
  dsimp only
  rcases hf : List.find? (fun j => cornerSign4 (1, 1, 1) j == p) (List.range 8) with _ | j
  · rcases hf2 : List.find? (fun j => cornerSign4 (2, 1, 1) j == p) (List.range 8) with _ | j
    · rfl
    · have hmem : j ∈ List.range 8 := List.mem_of_find?_eq_some hf2
      have heq : (cornerSign4 (2, 1, 1) j == p) = true := List.find?_some (p := fun j => cornerSign4 (2, 1, 1) j == p) (l := List.range 8) hf2
      have hp_eq : cornerSign4 (2, 1, 1) j = p := by simpa using heq
      subst p
      have hnot : PadGrid.isShell 4 (cornerSign4 (2, 1, 1) j) = false := by
        have hjlt : j < 8 := List.mem_range.mp hmem
        interval_cases j <;> native_decide
      simp [hnot] at hp
  · have hmem : j ∈ List.range 8 := List.mem_of_find?_eq_some hf
    have heq : (cornerSign4 (1, 1, 1) j == p) = true := List.find?_some (p := fun j => cornerSign4 (1, 1, 1) j == p) (l := List.range 8) hf
    have hp_eq : cornerSign4 (1, 1, 1) j = p := by simpa using heq
    subst p
    have hnot : PadGrid.isShell 4 (cornerSign4 (1, 1, 1) j) = false := by
      have hjlt : j < 8 := List.mem_range.mp hmem
      interval_cases j <;> native_decide
    simp [hnot] at hp

/-- The two cells carry the announced cases. -/
theorem nodupFailure_cases :
    DmcOnePad.cellCase nodupFailureField (2, 1, 1) = 62 ∧
    DmcOnePad.cellCase nodupFailureField (1, 1, 1) = 61 := by
  native_decide

/-- The assembled mesh is watertight (this is the general theorem,
    not a computation). -/
theorem nodupFailure_edgeClosed :
    EdgeClosed (dmcOneMeshEdges 4 nodupFailureField) :=
  Vdb.DmcOneStitch.edgeClosed_general 4 nodupFailureField nodupFailure_shellPinned

/-- **The failure**: the directed edge list repeats an edge. -/
theorem nodupFailure_not_nodup :
    ¬ (dmcOneMeshEdges 4 nodupFailureField).Nodup := by
  native_decide

/-- The repeated pair, explicitly: `((1,1,1),0) → ((2,1,1),0)` and its
    reverse each occur twice (they are the only repeated edges). -/
theorem nodupFailure_dupEdges :
    (dmcOneMeshEdges 4 nodupFailureField).countP
        (fun e => e = ((((1, 1, 1), 0), ((2, 1, 1), 0)) : DmcOnePad.V × DmcOnePad.V)) = 2 ∧
    (dmcOneMeshEdges 4 nodupFailureField).countP
        (fun e => e = ((((2, 1, 1), 0), ((1, 1, 1), 0)) : DmcOnePad.V × DmcOnePad.V)) = 2 := by
  native_decide

/-- Every individual quad still has four pairwise-distinct corners. -/
theorem nodupFailure_quads_ok :
    (dmcOneQuads 4 nodupFailureField).all (fun q => q.Nodup ∧ q.length = 4) = true := by
  native_decide

/-- The counts: `V = 32`, `E = 63`, `F = 32`, and `|mesh| = 128 = 4·F`. -/
theorem nodupFailure_counts :
    (QuadEuler.vertices (dmcOneMeshEdges 4 nodupFailureField)).card = 32 ∧
    (QuadEuler.undirected (dmcOneMeshEdges 4 nodupFailureField)).card = 63 ∧
    (PadGrid.crossed 4 nodupFailureField).length = 32 ∧
    (dmcOneMeshEdges 4 nodupFailureField).length = 128 := by
  native_decide

/-- Consequently `2·|E| = 126 ≠ 128 = |mesh|`: the count identity that
    `QuadEuler.euler_eq_vertices_sub_faces` needs is false here. -/
theorem nodupFailure_euler_count_fails :
    2 * (QuadEuler.undirected (dmcOneMeshEdges 4 nodupFailureField)).card ≠
      (dmcOneMeshEdges 4 nodupFailureField).length := by
  native_decide

/-- And the Euler characteristic itself differs: `V − E + F = 1`
    while `V − F = 0` (integers). -/
theorem nodupFailure_euler_fails :
    ((QuadEuler.vertices (dmcOneMeshEdges 4 nodupFailureField)).card : Int)
        - (QuadEuler.undirected (dmcOneMeshEdges 4 nodupFailureField)).card
        + (PadGrid.crossed 4 nodupFailureField).length
      ≠ ((QuadEuler.vertices (dmcOneMeshEdges 4 nodupFailureField)).card : Int)
        - (PadGrid.crossed 4 nodupFailureField).length := by
  native_decide


/-! ### The local obstruction (machine-checked enumeration)

    A directed DMC-1 edge is a pair of cell-patch vertices `((C,p),(D,q))`,
    so two crossed boundary edges of the face shared by `C` and `D` emit
    the same directed edge exactly when they carry the same patch id in
    both cells and emit the same direction. The enumeration below counts
    those local configurations over all `256 × 256` compatible cell-case
    pairs (for each normal axis). Finding F19's field realizes one of
    them; no `n = 3` field realizes any (`fin3_mesh_nodup`).
-/

end DmcOneEuler

-- namespace Vdb already open
namespace DmcOneStitch

/-- Crossedness of the `i`-th boundary edge of a `+na` face, from the
    case's corner bits. -/
def cfgCrossed (k na i : Nat) : Bool :=
  caseBit k (startCornerId na 0 i) != caseBit k (endCornerId na 0 i)

/-- The patch id at the `i`-th boundary edge, in the `+na` / `-na` frame. -/
def cfgPatch (k na side i : Nat) : Nat :=
  (patchesUsing k ((if side = 0 then localFacePlus na else localFaceMinus na).getD i 0)).headD 0

/-- The emitted direction token, from the `+na` frame. -/
def cfgDir (k na i : Nat) : Bool := if i ≤ 1 then caseBit k (startCornerId na 0 i) = 1
  else caseBit k (startCornerId na 0 i) = 0

/-- The local duplicate configuration: two distinct crossed boundary
    edges with the same patch id in both cells and the same direction. -/
def badFaceConfig (na kA kB : Nat) : Bool :=
  (List.range 4).any fun i => (List.range 4).any fun j =>
    i < j && cfgCrossed kA na i && cfgCrossed kA na j &&
    cfgPatch kA na 0 i == cfgPatch kA na 0 j &&
    cfgPatch kB na 1 i == cfgPatch kB na 1 j &&
    cfgDir kA na i == cfgDir kA na j

/-- All bad configurations (`kA`, `kB`, `i*4+j`) for compatible case pairs. -/
def badFaceConfigs (na : Nat) : List (Nat × Nat × Nat) :=
  (List.range 256).flatMap fun kA => (List.range 256).flatMap fun kB =>
    if maskPlus na kA == maskMinus na kB then
      (List.range 4).flatMap fun i => (List.range 4).filterMap fun j =>
        if i < j && cfgCrossed kA na i && cfgCrossed kA na j &&
           cfgPatch kA na 0 i == cfgPatch kA na 0 j &&
           cfgPatch kB na 1 i == cfgPatch kB na 1 j &&
           cfgDir kA na i == cfgDir kA na j
        then some (kA, kB, i * 4 + j) else none
    else []

theorem badFaceConfigs_length :
    (badFaceConfigs 0).length = 36 ∧
    (badFaceConfigs 1).length = 36 ∧
    (badFaceConfigs 2).length = 36 := by
  native_decide

/-- The `n = 4` counterexample's two cell cases form a bad configuration. -/
theorem badFaceConfig_counterexample : badFaceConfig 0 62 61 = true := by
  native_decide


/-- The patch component of the plus/minus cell's vertex at the i-th boundary
    edge equals the case-level patch id used by `badFaceConfig`. -/
lemma patchAt_boundary (s : Lat → Bool) {na : Nat} (hna : na < 3) {p : Lat}
    (hx : FaceBaseOK na p) {i : Nat} (hi : i < 4) (side : Nat) (hside : side < 2) :
    (DmcOnePad.cellPatchVertex s
      (if side = 0 then facePlusCell na p else faceMinusCell na p)
      ((faceBoundaryEdges na p).getD i (p, 0)).1
      ((faceBoundaryEdges na p).getD i (p, 0)).2).2 =
      (Vdb.patchesUsing (DmcOnePad.cellCase s
        (if side = 0 then facePlusCell na p else faceMinusCell na p))
        ((if side = 0 then localFacePlus na else localFaceMinus na).getD i 0)).headD 0 := by
  unfold DmcOnePad.cellPatchVertex
  dsimp
  rw [localEdge_faceEdges na side p i hna hi hx hside]
  rfl

lemma cfgDir_eq_dir (s : Lat → Bool) {na : Nat} (hna : na < 3) {p : Lat}
    (hx : FaceBaseOK na p) {i : Nat} (hi : i < 4) {dir : Bool}
    (hdir : flipDir i (s ((faceBoundaryEdges na p).getD i (p, 0)).1) = dir) :
    (cfgDir (DmcOnePad.cellCase s (facePlusCell na p)) na i == dir) = true := by
  unfold cfgDir
  let naF : Fin 3 := ⟨na, hna⟩
  let sideF : Fin 2 := ⟨0, by decide⟩
  let iF : Fin 4 := ⟨i, hi⟩
  have hbnd : if naF.val = 0 then 1 ≤ p.1 else if naF.val = 1 then 1 ≤ p.2.1 else 1 ≤ p.2.2 := by
    simpa [FaceBaseOK, naF] using hx
  have hsi := bitOf_start_sign naF sideF iF s p.1 p.2.1 p.2.2 hbnd
  dsimp [naF, sideF, iF] at hsi ⊢
  rw [hsi]
  unfold flipDir at hdir
  by_cases hi1 : i ≤ 1 <;>
    cases hsg : s ((faceBoundaryEdges na p).getD i (p, 0)).1 <;>
    simp [hi1, hsg] at hdir ⊢ <;> simp_all

lemma same_pair_badFace {s : Lat → Bool}
    {na : Nat} (hna : na < 3) {pF : Lat} (hx' : FaceBaseOK na pF)
    {i i' : Nat} (hi : i < 4) (hi' : i' < 4) (hiilt : i < i')
    {hcross : s ((faceBoundaryEdges na pF).getD i (pF, 0)).1 ≠
      s (PadGrid.succN ((faceBoundaryEdges na pF).getD i (pF, 0)).1
                       ((faceBoundaryEdges na pF).getD i (pF, 0)).2)}
    {hcross' : s ((faceBoundaryEdges na pF).getD i' (pF, 0)).1 ≠
      s (PadGrid.succN ((faceBoundaryEdges na pF).getD i' (pF, 0)).1
                       ((faceBoundaryEdges na pF).getD i' (pF, 0)).2)}
    {dir dir' : Bool}
    (hdir : flipDir i (s ((faceBoundaryEdges na pF).getD i (pF, 0)).1) = dir)
    (hdir' : flipDir i' (s ((faceBoundaryEdges na pF).getD i' (pF, 0)).1) = dir')
    {a b : V}
    (hpair : (a, b) = if dir then
          (DmcOnePad.cellPatchVertex s (facePlusCell na pF)
            ((faceBoundaryEdges na pF).getD i (pF, 0)).1
            ((faceBoundaryEdges na pF).getD i (pF, 0)).2,
           DmcOnePad.cellPatchVertex s (faceMinusCell na pF)
            ((faceBoundaryEdges na pF).getD i (pF, 0)).1
            ((faceBoundaryEdges na pF).getD i (pF, 0)).2)
        else
          (DmcOnePad.cellPatchVertex s (faceMinusCell na pF)
            ((faceBoundaryEdges na pF).getD i (pF, 0)).1
            ((faceBoundaryEdges na pF).getD i (pF, 0)).2,
           DmcOnePad.cellPatchVertex s (facePlusCell na pF)
            ((faceBoundaryEdges na pF).getD i (pF, 0)).1
            ((faceBoundaryEdges na pF).getD i (pF, 0)).2))
    (hpair' : (a, b) = if dir' then
          (DmcOnePad.cellPatchVertex s (facePlusCell na pF)
            ((faceBoundaryEdges na pF).getD i' (pF, 0)).1
            ((faceBoundaryEdges na pF).getD i' (pF, 0)).2,
           DmcOnePad.cellPatchVertex s (faceMinusCell na pF)
            ((faceBoundaryEdges na pF).getD i' (pF, 0)).1
            ((faceBoundaryEdges na pF).getD i' (pF, 0)).2)
        else
          (DmcOnePad.cellPatchVertex s (faceMinusCell na pF)
            ((faceBoundaryEdges na pF).getD i' (pF, 0)).1
            ((faceBoundaryEdges na pF).getD i' (pF, 0)).2,
           DmcOnePad.cellPatchVertex s (facePlusCell na pF)
            ((faceBoundaryEdges na pF).getD i' (pF, 0)).1
            ((faceBoundaryEdges na pF).getD i' (pF, 0)).2)) :
    badFaceConfig na (DmcOnePad.cellCase s (facePlusCell na pF))
      (DmcOnePad.cellCase s (faceMinusCell na pF)) = true := by
  have hpm_ne : facePlusCell na pF ≠ faceMinusCell na pF := by
    rcases pF with ⟨x,y,z⟩
    interval_cases na <;> simp [facePlusCell, faceMinusCell, FaceBaseOK] at hx' ⊢ <;> omega
  have hdirs : dir = dir' := by
    by_cases hd : dir <;> by_cases hd' : dir'
    · simp [hd, hd']
    · have hf : facePlusCell na pF = faceMinusCell na pF := by
        have h12 := congrArg Prod.fst (congrArg Prod.fst (hpair.symm.trans hpair'))
        dsimp [DmcOnePad.cellPatchVertex] at h12
        simpa [hd, hd'] using h12
      exact False.elim (hpm_ne hf)
    · have hf : faceMinusCell na pF = facePlusCell na pF := by
        have h12 := congrArg Prod.fst (congrArg Prod.fst (hpair.symm.trans hpair'))
        dsimp [DmcOnePad.cellPatchVertex] at h12
        simpa [hd, hd'] using h12
      exact False.elim (hpm_ne hf.symm)
    · simp [hd, hd']
  rw [← hdirs] at hpair'
  have hpatchA : (DmcOnePad.cellPatchVertex s (facePlusCell na pF)
      ((faceBoundaryEdges na pF).getD i (pF, 0)).1
      ((faceBoundaryEdges na pF).getD i (pF, 0)).2).2 =
      (DmcOnePad.cellPatchVertex s (facePlusCell na pF)
      ((faceBoundaryEdges na pF).getD i' (pF, 0)).1
      ((faceBoundaryEdges na pF).getD i' (pF, 0)).2).2 := by
    have hp1 := hpair
    have hp2 := hpair'
    by_cases hd : dir
    · simp [hd] at hp1 hp2
      exact congrArg Prod.snd (hp1.1.symm.trans hp2.1)
    · simp [hd] at hp1 hp2
      exact congrArg Prod.snd (hp1.2.symm.trans hp2.2)
  have hpatchB : (DmcOnePad.cellPatchVertex s (faceMinusCell na pF)
      ((faceBoundaryEdges na pF).getD i (pF, 0)).1
      ((faceBoundaryEdges na pF).getD i (pF, 0)).2).2 =
      (DmcOnePad.cellPatchVertex s (faceMinusCell na pF)
      ((faceBoundaryEdges na pF).getD i' (pF, 0)).1
      ((faceBoundaryEdges na pF).getD i' (pF, 0)).2).2 := by
    have hp1 := hpair
    have hp2 := hpair'
    by_cases hd : dir
    · simp [hd] at hp1 hp2
      exact congrArg Prod.snd (hp1.2.symm.trans hp2.2)
    · simp [hd] at hp1 hp2
      exact congrArg Prod.snd (hp1.1.symm.trans hp2.1)
  have hcrossB : cfgCrossed (DmcOnePad.cellCase s (facePlusCell na pF)) na i = true := by
    unfold cfgCrossed
    let naF : Fin 3 := ⟨na, hna⟩
    let sideF : Fin 2 := ⟨0, by decide⟩
    let iF : Fin 4 := ⟨i, hi⟩
    have hbnd : if naF.val = 0 then 1 ≤ pF.1 else if naF.val = 1 then 1 ≤ pF.2.1 else 1 ≤ pF.2.2 := by
      simpa [FaceBaseOK, naF] using hx'
    have hs := bitOf_start_sign naF sideF iF s pF.1 pF.2.1 pF.2.2 hbnd
    have he := endBitOf_start_sign naF sideF iF s pF.1 pF.2.1 pF.2.2 hbnd
    dsimp [naF, sideF, iF] at hs he ⊢
    rw [hs, he]
    cases h1 : s ((faceBoundaryEdges na pF).getD i (pF, 0)).1 <;>
      cases h2 : s (PadGrid.succN ((faceBoundaryEdges na pF).getD i (pF, 0)).1
                                   ((faceBoundaryEdges na pF).getD i (pF, 0)).2) <;> simp_all
  have hcrossB' : cfgCrossed (DmcOnePad.cellCase s (facePlusCell na pF)) na i' = true := by
    unfold cfgCrossed
    let naF : Fin 3 := ⟨na, hna⟩
    let sideF : Fin 2 := ⟨0, by decide⟩
    let iF : Fin 4 := ⟨i', hi'⟩
    have hbnd : if naF.val = 0 then 1 ≤ pF.1 else if naF.val = 1 then 1 ≤ pF.2.1 else 1 ≤ pF.2.2 := by
      simpa [FaceBaseOK, naF] using hx'
    have hs := bitOf_start_sign naF sideF iF s pF.1 pF.2.1 pF.2.2 hbnd
    have he := endBitOf_start_sign naF sideF iF s pF.1 pF.2.1 pF.2.2 hbnd
    dsimp [naF, sideF, iF] at hs he ⊢
    rw [hs, he]
    cases h1 : s ((faceBoundaryEdges na pF).getD i' (pF, 0)).1 <;>
      cases h2 : s (PadGrid.succN ((faceBoundaryEdges na pF).getD i' (pF, 0)).1
                                   ((faceBoundaryEdges na pF).getD i' (pF, 0)).2) <;> simp_all
  have hpA : cfgPatch (DmcOnePad.cellCase s (facePlusCell na pF)) na 0 i =
             cfgPatch (DmcOnePad.cellCase s (facePlusCell na pF)) na 0 i' := by
    unfold cfgPatch
    have hb := hpatchA
    dsimp [DmcOnePad.cellPatchVertex] at hb
    simp at hb
    have hle := localEdge_faceEdges na 0 pF i hna hi hx' (by decide)
    have hle' := localEdge_faceEdges na 0 pF i' hna hi' hx' (by decide)
    simp at hle hle'
    rw [hle, hle'] at hb
    simpa [localEdgeAt, edgeId, enumFaceEdges] using hb
  have hpB : cfgPatch (DmcOnePad.cellCase s (faceMinusCell na pF)) na 1 i =
             cfgPatch (DmcOnePad.cellCase s (faceMinusCell na pF)) na 1 i' := by
    unfold cfgPatch
    have hb := hpatchB
    dsimp [DmcOnePad.cellPatchVertex] at hb
    simp at hb
    have hle := localEdge_faceEdges na 1 pF i hna hi hx' (by decide)
    have hle' := localEdge_faceEdges na 1 pF i' hna hi' hx' (by decide)
    simp at hle hle'
    rw [hle, hle'] at hb
    simpa [localEdgeAt, edgeId, enumFaceEdges] using hb
  have hdirEq : cfgDir (DmcOnePad.cellCase s (facePlusCell na pF)) na i =
                cfgDir (DmcOnePad.cellCase s (facePlusCell na pF)) na i' := by
    have hdi := cfgDir_eq_dir s hna hx' hi hdir
    have hdj := cfgDir_eq_dir s hna hx' hi' hdir'
    cases hdirs
    simp at hdi hdj
    rw [hdi, hdj]
  unfold badFaceConfig
  rw [List.any_eq_true]
  refine ⟨i, by simp [hi], ?_⟩
  rw [List.any_eq_true]
  refine ⟨i', by simp [hi'], ?_⟩
  simp [hiilt, hcrossB, hcrossB', hpA, hpB, hdirEq]
end DmcOneStitch
end Vdb
