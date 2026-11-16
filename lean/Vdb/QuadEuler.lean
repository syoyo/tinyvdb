/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  Edge counting for assembled quad meshes. `Vdb/Assembly.lean` proves only
  that the directed dual edge list of a balanced assembly is reverse-closed
  (`EdgeClosed`, a *set* statement). The Euler characteristic needs the
  number of *undirected* edges, which depends on multiplicities: a
  reverse-closed list can use a directed edge several times (the bounded
  model in `Vdb/Cuberille.lean` has such fields, `badEdgeCount ≠ 0`).

  This module proves the clean multiplicity statement: a reverse-closed,
  duplicate-free, loop-free directed edge list has exactly half as many
  undirected edges as directed ones. For a quad mesh (four directed edges
  per quad) this gives `E = 2 F`, hence `χ = V - E + F = V - F`.

  Nothing here asserts `χ = 2`: that claim is false in general (see
  `Cuberille.bounded_chi_manifold_not_chi2`, whose fields embed unchanged
  into every padded grid with `n ≥ 3`).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Mathlib.Data.Sym.Sym2
import Vdb.Assembly

namespace Vdb

namespace QuadEuler

variable {ι : Type} [DecidableEq ι]

/-- The unordered edge of a directed edge. -/
abbrev unord (e : ι × ι) : Sym2 ι := s(e.1, e.2)

/-- The undirected edges of a directed edge list. -/
def undirected (es : List (ι × ι)) : Finset (Sym2 ι) :=
  (es.map unord).toFinset

/-- **Half-edge count**: a reverse-closed, duplicate-free, loop-free directed
    edge list has exactly twice as many directed edges as undirected ones. -/
theorem two_mul_card_undirected (es : List (ι × ι)) (hnd : es.Nodup)
    (hcl : EdgeClosed es) (hloop : ∀ a b, (a, b) ∈ es → a ≠ b) :
    2 * (undirected es).card = es.length := by
  have hlen : es.length = es.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
  have hmap : ∀ x ∈ es.toFinset, unord x ∈ undirected es := by
    intro x hx
    simp only [undirected, List.mem_toFinset, List.mem_map]
    exact ⟨x, List.mem_toFinset.mp hx, rfl⟩
  have hfib := Finset.card_eq_sum_card_fiberwise hmap
  have h2 : ∀ t ∈ undirected es,
      (es.toFinset.filter fun x => unord x = t).card = 2 := by
    intro t ht
    simp only [undirected, List.mem_toFinset, List.mem_map] at ht
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := ht
    have hba : (b, a) ∈ es := (hcl a b).mp hab
    have hne : a ≠ b := hloop a b hab
    have hset : es.toFinset.filter (fun x => unord x = unord (a, b))
        = {(a, b), (b, a)} := by
      ext ⟨c, d⟩
      simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_insert,
        Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨_, h⟩
        have h' := Sym2.eq_iff.mp h
        tauto
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨hab, rfl⟩
        · exact ⟨hba, Sym2.eq_swap⟩
    rw [hset, Finset.card_pair]
    intro h
    exact hne (congrArg Prod.fst h)
  rw [hlen, hfib, Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul]
  ring

/-- For a mesh of quads (`4 F` directed edges), `E = 2 F`. -/
theorem undirected_card_eq_two_mul (es : List (ι × ι)) (F : Nat) (hnd : es.Nodup)
    (hcl : EdgeClosed es) (hloop : ∀ a b, (a, b) ∈ es → a ≠ b)
    (hF : es.length = 4 * F) :
    (undirected es).card = 2 * F := by
  have := two_mul_card_undirected es hnd hcl hloop
  omega

/-- The vertices of a directed edge list (tails). -/
def vertices (es : List (ι × ι)) : Finset ι := (es.map Prod.fst).toFinset

/-- **Euler characteristic of a manifold-edge quad mesh**: `χ = V - F`. -/
theorem euler_eq_vertices_sub_faces (es : List (ι × ι)) (F : Nat) (hnd : es.Nodup)
    (hcl : EdgeClosed es) (hloop : ∀ a b, (a, b) ∈ es → a ≠ b)
    (hF : es.length = 4 * F) :
    ((vertices es).card : Int) - (undirected es).card + F
      = (vertices es).card - F := by
  have := undirected_card_eq_two_mul es F hnd hcl hloop hF
  omega

end QuadEuler

end Vdb
