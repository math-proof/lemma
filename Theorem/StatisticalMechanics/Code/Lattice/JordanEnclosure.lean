/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

namespace EvenDegree

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem sum_degree_component_even (C : G.ConnectedComponent) :
    Even (∑ x ∈ C.supp.toFinset, G.degree x) := by
  classical
  have hdeg : ∀ x : (C.supp : Set V), (G.induce (C.supp : Set V)).degree x = G.degree x := by
    intro x
    apply degree_induce_of_neighborSet_subset
    intro y hy
    rw [SimpleGraph.mem_neighborSet] at hy
    show G.connectedComponentMk y = C
    have hx : G.connectedComponentMk (x : V) = C := x.2
    rw [← hx]
    exact ConnectedComponent.connectedComponentMk_eq_of_adj hy.symm
  have hhand := SimpleGraph.sum_degrees_eq_twice_card_edges (G.induce (C.supp : Set V))
  have key : ∑ x : (C.supp : Set V), G.degree (x : V)
      = 2 * #(G.induce (C.supp : Set V)).edgeFinset := by
    rw [← hhand]
    exact (Finset.sum_congr rfl (fun x _ => (hdeg x).symm))
  have hconv : ∑ x ∈ C.supp.toFinset, G.degree x = ∑ x : (C.supp : Set V), G.degree (x : V) := by
    rw [← Finset.sum_coe_sort C.supp.toFinset (fun x => G.degree x)]
    apply Finset.sum_bij (fun (x : C.supp.toFinset) _ => (⟨x.1, by
      have := x.2; rwa [Set.mem_toFinset] at this⟩ : (C.supp : Set V)))
    · intro a _; exact Finset.mem_univ _
    · intro a _ b _ h; ext; simpa using congrArg Subtype.val h
    · intro b _; exact ⟨⟨b.1, by rw [Set.mem_toFinset]; exact b.2⟩, Finset.mem_univ _, rfl⟩
    · intro a _; rfl
  rw [hconv, key]
  exact even_two_mul _


theorem degree_deleteEdges_of_ne {v w x : V} (hxv : x ≠ v) (hxw : x ≠ w) :
    (G.deleteEdges {s(v, w)}).degree x = G.degree x := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  congr 1
  apply Finset.ext
  intro y
  simp only [mem_neighborFinset, deleteEdges_adj, Set.mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    intro hcontra
    rw [Sym2.eq_iff] at hcontra
    rcases hcontra with ⟨hxv', _⟩ | ⟨hxw', _⟩
    · exact hxv hxv'
    · exact hxw hxw'


theorem degree_deleteEdges_self {v w : V} (hadj : G.Adj v w) :
    (G.deleteEdges {s(v, w)}).degree v + 1 = G.degree v := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have hsub : (G.deleteEdges {s(v, w)}).neighborFinset v =
      (G.neighborFinset v).erase w := by
    apply Finset.ext
    intro y
    simp only [mem_neighborFinset, deleteEdges_adj, Set.mem_singleton_iff, Finset.mem_erase]
    constructor
    · rintro ⟨hxy, hne⟩
      refine ⟨?_, hxy⟩
      intro hyw; subst hyw; exact hne rfl
    · rintro ⟨hyw, hxy⟩
      refine ⟨hxy, ?_⟩
      intro hcontra
      rw [Sym2.eq_iff] at hcontra
      rcases hcontra with ⟨_, hyw'⟩ | ⟨hvw, _⟩
      · exact hyw hyw'
      · exact (hadj.ne) hvw
  rw [hsub, Finset.card_erase_of_mem (by rw [mem_neighborFinset]; exact hadj)]
  have hpos : 0 < #(G.neighborFinset v) := by
    rw [card_neighborFinset_eq_degree]
    exact hadj.degree_pos_left
  omega


theorem reachable_deleteEdges_of_even (heven : ∀ x, Even (G.degree x))
    {v w : V} (hadj : G.Adj v w) :
    (G.deleteEdges {s(v, w)}).Reachable v w := by
  classical
  by_contra hnr
  set H := G.deleteEdges {s(v, w)} with hH
  set C := H.connectedComponentMk v with hC
  have hwC : w ∉ (C.supp : Set V) := by
    intro hw
    apply hnr
    have hwmk : H.connectedComponentMk w = C := hw
    rw [hC] at hwmk
    exact (ConnectedComponent.eq.mp hwmk).symm
  have hHeven := sum_degree_component_even H C
  have hvC : v ∈ C.supp.toFinset := by
    rw [Set.mem_toFinset]; show H.connectedComponentMk v = C; rw [hC]
  have hxne_w : ∀ x ∈ C.supp.toFinset, x ≠ w := by
    intro x hx hxw
    rw [Set.mem_toFinset] at hx
    exact hwC (hxw ▸ hx)
  have hsplit : (∑ x ∈ C.supp.toFinset, H.degree x) + 1 =
      ∑ x ∈ C.supp.toFinset, G.degree x := by
    rw [← Finset.add_sum_erase _ _ hvC, ← Finset.add_sum_erase _ (fun x => G.degree x) hvC]
    have hrest : ∑ x ∈ C.supp.toFinset.erase v, H.degree x
        = ∑ x ∈ C.supp.toFinset.erase v, G.degree x := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxv : x ≠ v := Finset.ne_of_mem_erase hx
      have hxw : x ≠ w := hxne_w x (Finset.mem_of_mem_erase hx)
      exact degree_deleteEdges_of_ne G hxv hxw
    have hvdeg : H.degree v + 1 = G.degree v := degree_deleteEdges_self G hadj
    rw [hrest]
    omega
  have hGeven : Even (∑ x ∈ C.supp.toFinset, G.degree x) :=
    Finset.even_sum _ (fun x _ => heven x)
  rw [← hsplit] at hGeven
  exact (Nat.even_add_one.mp hGeven) hHeven


theorem exists_cycle_through_edge_of_even (heven : ∀ x, Even (G.degree x))
    {v w : V} (hadj : G.Adj v w) :
    ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s(v, w) ∈ p.edges :=
  adj_and_reachable_delete_edges_iff_exists_cycle.mp
    ⟨hadj, reachable_deleteEdges_of_even G heven hadj⟩

end EvenDegree

namespace EvenDegree

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [LocallyFinite G]


theorem exists_cycle_through_edge_of_even_of_finite_support
    (T : Finset V) (hsupp : G.support ⊆ (T : Set V))
    (heven : ∀ x, Even (G.degree x)) {v w : V} (hadj : G.Adj v w) :
    ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s(v, w) ∈ p.edges := by
  classical
  set H := G.induce (T : Set V) with hH
  haveI : Fintype (T : Set V) := FinsetCoe.fintype T
  haveI : DecidableRel H.Adj := Classical.decRel _
  have hvT : v ∈ (T : Set V) := hsupp hadj.mem_support_left
  have hwT : w ∈ (T : Set V) := hsupp hadj.mem_support_right
  have hdegH : ∀ x : (T : Set V), H.degree x = G.degree (x : V) := by
    intro x
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
    refine Fintype.card_congr ?_
    refine ⟨fun y => ⟨(y.1 : V), y.2⟩, fun y => ⟨⟨y.1, hsupp y.2.symm.mem_support_left⟩, y.2⟩,
      ?_, ?_⟩
    · intro y; ext; rfl
    · intro y; ext; rfl
  have hHeven : ∀ x : (T : Set V), Even (H.degree x) := by
    intro x; rw [hdegH x]; exact heven _
  have hadjH : H.Adj ⟨v, hvT⟩ ⟨w, hwT⟩ := hadj
  obtain ⟨u, p, hpcyc, hpe⟩ := exists_cycle_through_edge_of_even H hHeven hadjH
  let emb : H ↪g G := SimpleGraph.Embedding.induce (T : Set V)
  refine ⟨(u : V), p.map emb.toHom, hpcyc.map emb.injective, ?_⟩
  have hmem : s((⟨v, hvT⟩ : (T : Set V)), (⟨w, hwT⟩ : (T : Set V))) ∈ p.edges := hpe
  have hmap := SimpleGraph.Walk.edges_map (f := emb.toHom) (p := p)
  have hgoal : s(v, w)
      = Sym2.map emb.toHom s((⟨v, hvT⟩ : (T : Set V)), (⟨w, hwT⟩ : (T : Set V))) := by
    simp only [Sym2.map_mk]; rfl
  have hin : s(v, w) ∈ List.map (Sym2.map emb.toHom) p.edges := by
    rw [List.mem_map]; exact ⟨_, hmem, hgoal.symm⟩
  rwa [← hmap] at hin

end EvenDegree
end Lattice
end StatMech
