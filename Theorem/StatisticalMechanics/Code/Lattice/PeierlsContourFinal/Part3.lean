/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part7
import Instance.StatisticalMechanics.Code.Lattice.PeierlsContourFinal
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn crossEdges contourLen connClusterFamily
  bondFinsetTouch)

attribute [local instance] Classical.propDecidable


theorem componentGraph_degree_even (K : Set (Site 2)) (f a : Site 2) :
    Even ((componentGraph K f).degree a) := by
  classical
  by_cases ha : (faceBoundaryGraph K).Reachable f a
  · 
    rw [← SimpleGraph.card_neighborSet_eq_degree]
    have hcard : Fintype.card ((componentGraph K f).neighborSet a)
        = (faceBoundaryGraph K).degree a := by
      rw [← SimpleGraph.card_neighborSet_eq_degree]
      exact Fintype.card_congr (Equiv.setCongr (componentGraph_neighborSet_eq ha))
    rw [hcard]; exact degree_faceBoundaryGraph_even K a
  · rw [← SimpleGraph.card_neighborSet_eq_degree]
    have hempty : (componentGraph K f).neighborSet a = ∅ := componentGraph_neighborSet_empty ha
    have hcard : Fintype.card ((componentGraph K f).neighborSet a) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun x => (hempty ▸ x.2 : (x : Site 2) ∈ (∅ : Set (Site 2)))⟩
    rw [hcard]; exact Even.zero


theorem componentGraph_support_subset {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2))) (f : Site 2) :
    (componentGraph K f).support ⊆ (componentSupport K T f : Set (Site 2)) := by
  intro a ha
  rw [SimpleGraph.mem_support] at ha
  obtain ⟨b, hadj, hra, _⟩ := ha
  rw [Finset.mem_coe, mem_componentSupport]
  exact ⟨hsupp hadj.mem_support_left, hra⟩


theorem componentGraph_walk_in_componentSupport {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2))) {f : Site 2} (hf : f ∈ T)
    {g : Site 2} (p : (componentGraph K f).Walk f g) :
    ∀ v ∈ p.support, v ∈ componentSupport K T f := by
  
  intro v hv
  have hmem : v ∈ (p.mapLe (componentGraph_le K f)).support := by
    rw [SimpleGraph.Walk.support_mapLe_eq_support]; exact hv
  exact componentSupport_walk_subset hsupp hf (p.mapLe (componentGraph_le K f)) v hmem


theorem componentGraph_edge_of_walk_from_base {K : Set (Site 2)} {f g : Site 2}
    (q : (faceBoundaryGraph K).Walk f g) {e : Sym2 (Site 2)} (he : e ∈ q.edges) :
    e ∈ (componentGraph K f).edgeSet := by
  induction e with
  | h x y =>
    have hxadj : (faceBoundaryGraph K).Adj x y := q.adj_of_mem_edges he
    
    have hx : x ∈ q.support := q.fst_mem_support_of_mem_edges he
    have hy : y ∈ q.support := q.snd_mem_support_of_mem_edges he
    have hrx : (faceBoundaryGraph K).Reachable f x := ⟨q.takeUntil x hx⟩
    have hry : (faceBoundaryGraph K).Reachable f y := ⟨q.takeUntil y hy⟩
    rw [SimpleGraph.mem_edgeSet]
    exact ⟨hxadj, hrx, hry⟩


theorem componentGraph_reachable_of_reachable {K : Set (Site 2)} {f g : Site 2}
    (h : (faceBoundaryGraph K).Reachable f g) : (componentGraph K f).Reachable f g := by
  obtain ⟨p⟩ := h
  exact ⟨p.transfer (componentGraph K f)
    (fun e he => componentGraph_edge_of_walk_from_base p he)⟩


theorem reachable_induce_of_walk_in_set {V : Type*} {G : SimpleGraph V} {S : Set V}
    {a b : V} (p : G.Walk a b) (hsub : ∀ v ∈ p.support, v ∈ S) (ha : a ∈ S) :
    (G.induce S).Reachable ⟨a, ha⟩ ⟨b, hsub b p.end_mem_support⟩ := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y z hxy q ih =>
    have hyS : y ∈ S := hsub y (by
      rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ q.start_mem_support)
    have hqsub : ∀ v ∈ q.support, v ∈ S := fun v hv =>
      hsub v (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hv)
    have hadjI : (G.induce S).Adj ⟨x, ha⟩ ⟨y, hyS⟩ := by rw [SimpleGraph.induce_adj]; exact hxy
    exact (SimpleGraph.Adj.reachable hadjI).trans (ih hqsub hyS)


theorem componentGraph_support_walk {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2))) {f : Site 2} (hf : f ∈ T)
    {a b : Site 2} (ha : a ∈ componentSupport K T f) (hb : b ∈ componentSupport K T f) :
    ∃ p : (componentGraph K f).Walk a b, ∀ v ∈ p.support, v ∈ componentSupport K T f := by
  rw [mem_componentSupport] at ha hb
  
  obtain ⟨pa⟩ := componentGraph_reachable_of_reachable ha.2
  obtain ⟨pb⟩ := componentGraph_reachable_of_reachable hb.2
  
  refine ⟨pa.reverse.append pb, ?_⟩
  intro v hv
  rw [SimpleGraph.Walk.support_append] at hv
  rcases List.mem_append.mp hv with hva | hvb
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hva
    exact componentGraph_walk_in_componentSupport hsupp hf pa v hva
  · exact componentGraph_walk_in_componentSupport hsupp hf pb v (List.mem_of_mem_tail hvb)


theorem componentGraph_induce_connected {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2))) {f : Site 2} (hf : f ∈ T) :
    ((componentGraph K f).induce (componentSupport K T f : Set (Site 2))).Connected := by
  have hself : f ∈ componentSupport K T f := self_mem_componentSupport hf
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨f, hself⟩⟩⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  have ha' : a ∈ componentSupport K T f := Finset.mem_coe.mp ha
  have hb' : b ∈ componentSupport K T f := Finset.mem_coe.mp hb
  obtain ⟨p, hp⟩ := componentGraph_support_walk hsupp hf ha' hb'
  
  have hrec := reachable_induce_of_walk_in_set p (fun v hv => hp v hv) ha
  convert hrec using 2


theorem componentEulerCircuit {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2))) {f : Site 2} (hf : f ∈ T) :
    ∃ c : (componentGraph K f).Walk f f,
      c.IsTrail ∧ ∀ e ∈ (componentGraph K f).edgeSet, e ∈ c.edges := by
  refine EulerianExistence.exists_closed_eulerian_of_finite_support (componentGraph K f)
    (componentSupport K T f) (componentGraph_support_subset hsupp f)
    (componentGraph_induce_connected hsupp hf) (componentGraph_degree_even K f) ?_
  exact Finset.mem_coe.mpr (self_mem_componentSupport hf)


theorem dualCircuit_of_componentCovers {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2))) {f : Site 2} (hf : f ∈ T)
    (hcov : ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ (componentGraph K f).edgeSet) :
    ∃ c : (faceBoundaryGraph K).Walk f f,
      c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ c.edges := by
  obtain ⟨c, htrail, hccov⟩ := componentEulerCircuit hsupp hf
  refine ⟨c.mapLe (componentGraph_le K f),
    SimpleGraph.Walk.map_isTrail_of_injective (Function.injective_id) ?_, ?_⟩
  · 
    exact htrail
  · intro e he
    have hcomp : e ∈ (componentGraph K f).edgeSet := hcov e he
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
    exact hccov e hcomp


end Lattice
end StatMech
