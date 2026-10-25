/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arccontiguity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.atsattachsurgery.Part4
import Theorem.StatisticalMechanics.Code.Walls.arrreroute.Part5
import Theorem.StatisticalMechanics.Code.Walls.cycboundary.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


section AbstractCycle

variable {V : Type*} {G : SimpleGraph V}


theorem arc_reachable_induce_of_avoidWalk {S : Set V} {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) (p : G.Walk x y) (hp : ∀ w ∈ p.support, w ∈ S) :
    (G.induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  classical
  
  set T : Set V := {v | v ∈ p.support} with hT
  have hTS : T ⊆ S := fun v hv => hp v hv
  
  have hconn := p.connected_induce_support
  have hxT : x ∈ T := by simp [hT, p.start_mem_support]
  have hyT : y ∈ T := by simp [hT, p.end_mem_support]
  have hreachT : (G.induce T).Reachable ⟨x, hxT⟩ ⟨y, hyT⟩ := hconn ⟨x, hxT⟩ ⟨y, hyT⟩
  
  have hmap := hreachT.map (G.induceHomOfLE hTS).toHom
  simpa using hmap


theorem arc_reachable_induce_compl_singleton [Finite V]
    (hcyc : G.IsCycles) {v a b : V} (hab : a ≠ b)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (ha : a ∈ ({v}ᶜ : Set V)) (hb : b ∈ ({v}ᶜ : Set V)) :
    (G.induce ({v}ᶜ : Set V)).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  classical
  
  have hav : a ≠ v := hva.ne'
  have hbv : b ≠ v := hvb.ne'
  set p : G.Walk a b := Walk.cons hva.symm (Walk.cons hvb Walk.nil) with hp
  have hppath : p.IsPath := by
    rw [hp, Walk.cons_isPath_iff, Walk.cons_isPath_iff]
    refine ⟨⟨Walk.IsPath.nil, ?_⟩, ?_⟩
    · simp only [Walk.support_nil, List.mem_singleton]; exact fun h => hbv h.symm
    · simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false]
      push_neg
      exact ⟨hav, hab⟩
  
  have hsdiff := hcyc.reachable_sdiff_toSubgraph_spanningCoe p hppath
  
  
  
  obtain ⟨q⟩ := hsdiff.symm  
  
  have hv_nbrs : ∀ w, G.Adj v w → w = a ∨ w = b := by
    intro w hvw
    
    have h2 := hcyc (⟨a, hva⟩ : (G.neighborSet v).Nonempty)
    obtain ⟨x, y, hxy, hset⟩ := Set.ncard_eq_two.mp h2
    have hmem : ∀ z, G.Adj v z → z ∈ ({x, y} : Set V) := by
      intro z hz; rw [← hset]; exact hz
    have hxa := hmem a hva; have hxb := hmem b hvb; have hxw := hmem w hvw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxa hxb hxw
    
    rcases hxa with rfl | rfl <;> rcases hxb with rfl | rfl <;> rcases hxw with h | h <;>
      simp_all
  
  have hnoV : ∀ w, ¬ (G \ p.toSubgraph.spanningCoe).Adj v w := by
    intro w hadj
    rw [sdiff_adj] at hadj
    obtain ⟨hgadj, hnotp⟩ := hadj
    
    apply hnotp
    simp only [Subgraph.spanningCoe_adj]
    rcases hv_nbrs w hgadj with rfl | rfl
    · 
      rw [hp]; simp [Walk.toSubgraph, Subgraph.sup_adj, subgraphOfAdj_adj]
    · rw [hp]; simp [Walk.toSubgraph, Subgraph.sup_adj, subgraphOfAdj_adj]
  
  have hqavoid : ∀ w ∈ q.support, w ∈ ({v}ᶜ : Set V) := by
    intro w hw
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hwv
    subst hwv
    
    obtain ⟨n, hgv, hnl⟩ := Walk.mem_support_iff_exists_getVert.mp hw
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · 
      rw [hn0, Walk.getVert_zero] at hgv
      exact hva.ne' hgv
    · 
      have hlt : n - 1 < q.length := by lia
      have hadj := q.adj_getVert_succ hlt
      rw [Nat.sub_add_cancel hnpos, hgv] at hadj
      exact hnoV _ hadj.symm
  
  
  have hle : (G \ p.toSubgraph.spanningCoe) ≤ G := sdiff_le
  have hGavoid : ∀ w ∈ (q.mapLe hle).support, w ∈ ({v}ᶜ : Set V) := by
    intro w hw
    rw [Walk.support_mapLe_eq_support] at hw
    exact hqavoid w hw
  exact arc_reachable_induce_of_avoidWalk ha hb (q.mapLe hle) hGavoid


theorem arc_reachable_induce_compl_pathInterior [Finite V]
    (hcyc : G.IsCycles) {x y : V} (hxy : x ≠ y)
    (p : G.Walk x y) (hp : p.IsPath)
    (hx : x ∈ ({w | w ∈ p.support ∧ w ≠ x ∧ w ≠ y}ᶜ : Set V))
    (hy : y ∈ ({w | w ∈ p.support ∧ w ≠ x ∧ w ≠ y}ᶜ : Set V)) :
    (G.induce ({w | w ∈ p.support ∧ w ≠ x ∧ w ≠ y}ᶜ : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  classical
  set D : Set V := {w | w ∈ p.support ∧ w ≠ x ∧ w ≠ y} with hD
  
  have hsdiff := hcyc.reachable_sdiff_toSubgraph_spanningCoe p hp
  obtain ⟨q⟩ := hsdiff.symm  
  
  have hnoInt : ∀ w ∈ D, ∀ z, ¬ (G \ p.toSubgraph.spanningCoe).Adj w z := by
    intro w hw z hadj
    rw [sdiff_adj] at hadj
    obtain ⟨hgadj, hnotp⟩ := hadj
    apply hnotp
    
    
    obtain ⟨hwsupp, hwx, hwy⟩ := hw
    
    obtain ⟨n, hgv, hnl⟩ := Walk.mem_support_iff_exists_getVert.mp hwsupp
    have hn0 : n ≠ 0 := by
      intro h; rw [h, Walk.getVert_zero] at hgv; exact hwx hgv.symm
    have hnlen : n ≠ p.length := by
      intro h; rw [h, Walk.getVert_length] at hgv; exact hwy hgv.symm
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hnlt : n < p.length := lt_of_le_of_ne hnl hnlen
    
    have hprev : p.toSubgraph.Adj (p.getVert (n-1)) w := by
      have := p.toSubgraph_adj_getVert (i := n-1) (by lia)
      rw [Nat.sub_add_cancel hnpos, hgv] at this; exact this
    have hnext : p.toSubgraph.Adj w (p.getVert (n+1)) := by
      have := p.toSubgraph_adj_getVert (i := n) hnlt
      rw [hgv] at this; exact this
    
    have hprevG : G.Adj w (p.getVert (n-1)) := hprev.adj_sub.symm
    have hnextG : G.Adj w (p.getVert (n+1)) := hnext.adj_sub
    
    have hpne : p.getVert (n-1) ≠ p.getVert (n+1) := by
      
      have h1 : p.getVert (n-1) ∈ p.support := Walk.getVert_mem_support _ _
      have h2 : p.getVert (n+1) ∈ p.support := Walk.getVert_mem_support _ _
      intro heq
      have := hp.getVert_injOn (by lia : n - 1 ≤ p.length) (by lia : n + 1 ≤ p.length) heq
      lia
    have h2 := hcyc (⟨p.getVert (n-1), hprevG⟩ : (G.neighborSet w).Nonempty)
    
    have hsub : ({p.getVert (n-1), p.getVert (n+1)} : Set V) ⊆ G.neighborSet w := by
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl
      · exact hprevG
      · exact hnextG
    have hpairncard : ({p.getVert (n-1), p.getVert (n+1)} : Set V).ncard = 2 :=
      Set.ncard_pair hpne
    have hseteq : ({p.getVert (n-1), p.getVert (n+1)} : Set V) = G.neighborSet w :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [h2, hpairncard]) (G.neighborSet w).toFinite
    
    have hzmem : z ∈ ({p.getVert (n-1), p.getVert (n+1)} : Set V) := by
      rw [hseteq]; exact hgadj
    have hz2 : z = p.getVert (n-1) ∨ z = p.getVert (n+1) := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzmem
    simp only [Subgraph.spanningCoe_adj]
    rcases hz2 with rfl | rfl
    · exact hprev.symm
    · exact hnext
  
  have hqavoid : ∀ w ∈ q.support, w ∈ (Dᶜ : Set V) := by
    intro w hw hwD
    obtain ⟨n, hgv, hnl⟩ := Walk.mem_support_iff_exists_getVert.mp hw
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [hn0, Walk.getVert_zero] at hgv
      
      exact (hwD.2.1) hgv.symm
    · have hlt : n - 1 < q.length := by lia
      have hadj := q.adj_getVert_succ hlt
      rw [Nat.sub_add_cancel hnpos, hgv] at hadj
      exact hnoInt w hwD _ hadj.symm
  have hle : (G \ p.toSubgraph.spanningCoe) ≤ G := sdiff_le
  have hGavoid : ∀ w ∈ (q.mapLe hle).support, w ∈ (Dᶜ : Set V) := by
    intro w hw
    rw [Walk.support_mapLe_eq_support] at hw
    exact hqavoid w hw
  exact arc_reachable_induce_of_avoidWalk hx hy (q.mapLe hle) hGavoid


theorem arc_reachable_induce_mono_of_avoidWalk {S : Set V} {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) (p : G.Walk x y) (hp : ∀ w ∈ p.support, w ∈ S) :
    (G.induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩ :=
  arc_reachable_induce_of_avoidWalk hx hy p hp

end AbstractCycle


section BoundaryArc

variable {K : Finset (Site 2)} {c a₀ : Site 2}


theorem arc_noncontig_can_disconnect :
    ∃ (W : Type) (H : SimpleGraph W) (_ : H.IsCycles) (D : Set W) (a c : W)
      (ha : a ∈ Dᶜ) (hc : c ∈ Dᶜ),
      ¬ (H.induce (Dᶜ)).Reachable ⟨a, ha⟩ ⟨c, hc⟩ := by
  classical
  
  have ha0 : (0 : Fin 4) ∈ (({1, 3} : Set (Fin 4))ᶜ) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]; decide
  have hc2 : (2 : Fin 4) ∈ (({1, 3} : Set (Fin 4))ᶜ) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]; decide
  refine ⟨Fin 4, cycleGraph 4, ?_, {1, 3}, 0, 2, ha0, hc2, ?_⟩
  · 
    intro v _
    rw [cycleGraph_neighborSet (n := 2)]
    refine Set.ncard_pair ?_
    
    fin_cases v <;> decide
  · 
    rintro ⟨w⟩
    
    have hnoedge : ∀ (p q : ((({1, 3} : Set (Fin 4))ᶜ) : Set (Fin 4))),
        ¬ ((cycleGraph 4).induce ((({1, 3} : Set (Fin 4))ᶜ) : Set (Fin 4))).Adj p q := by
      rintro ⟨p, hp⟩ ⟨q, hq⟩ hadj
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
      have hadj' : (cycleGraph 4).Adj p q := hadj
      rw [cycleGraph_adj'] at hadj'
      fin_cases p <;> fin_cases q <;> simp_all <;> revert hadj' <;> decide
    
    match w with
    | Walk.cons hadj _ => exact hnoedge _ _ hadj


end BoundaryArc
end Walls
end StatMech
