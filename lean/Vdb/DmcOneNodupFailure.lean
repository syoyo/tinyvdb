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
import Vdb.PadGrid
import Vdb.QuadEuler
import Mathlib.Tactic

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

end DmcOneEuler
end Vdb
