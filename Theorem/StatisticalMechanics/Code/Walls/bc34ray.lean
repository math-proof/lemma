/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc33escaping.Part2
import Def.StatisticalMechanics.Code.Walls.bc34ray
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


@[simp]
theorem ray34_mem_avoidCluster {V : Type*} {G : SimpleGraph V} {S : Set V} {v w : V} :
    w ∈ ray34_AvoidCluster G S v ↔ ray34_AvoidReach G S v w := Iff.rfl


theorem ray34_avoidReach_refl {V : Type*} (G : SimpleGraph V) (S : Set V) {v : V}
    (hv : v ∉ S) : ray34_AvoidReach G S v v :=
  ⟨Walk.nil, by intro u hu; rw [Walk.support_nil, List.mem_singleton] at hu; exact hu ▸ hv⟩


theorem ray34_avoidReach_symm {V : Type*} {G : SimpleGraph V} {S : Set V} {v w : V}
    (h : ray34_AvoidReach G S v w) : ray34_AvoidReach G S w v := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.reverse, ?_⟩
  intro u hu
  rw [Walk.support_reverse, List.mem_reverse] at hu
  exact hp u hu


theorem ray34_avoidReach_trans {V : Type*} {G : SimpleGraph V} {S : Set V} {u v w : V}
    (huv : ray34_AvoidReach G S u v) (hvw : ray34_AvoidReach G S v w) :
    ray34_AvoidReach G S u w := by
  obtain ⟨p, hp⟩ := huv
  obtain ⟨q, hq⟩ := hvw
  refine ⟨p.append q, ?_⟩
  intro x hx
  rw [Walk.support_append, List.mem_append] at hx
  rcases hx with hx | hx
  · exact hp x hx
  · exact hq x (List.mem_of_mem_tail hx)


theorem ray34_avoidCluster_avoids {V : Type*} {G : SimpleGraph V} {S : Set V} {v w : V}
    (h : w ∈ ray34_AvoidCluster G S v) : w ∉ S := by
  obtain ⟨p, hp⟩ := h
  exact hp w p.end_mem_support


theorem ray34_self_mem_avoidCluster {V : Type*} (G : SimpleGraph V) (S : Set V) {v : V}
    (hv : v ∉ S) : v ∈ ray34_AvoidCluster G S v :=
  ray34_avoidReach_refl G S hv


theorem ray34_notMem_of_avoidCluster_nonempty {V : Type*} {G : SimpleGraph V} {S : Set V} {v : V}
    (h : (ray34_AvoidCluster G S v).Nonempty) : v ∉ S := by
  obtain ⟨w, p, hp⟩ := h
  exact hp v p.start_mem_support


theorem ray34_avoidCluster_eq_of_reach {V : Type*} {G : SimpleGraph V} {S : Set V} {v w : V}
    (h : ray34_AvoidReach G S v w) : ray34_AvoidCluster G S v = ray34_AvoidCluster G S w := by
  ext z
  simp only [ray34_mem_avoidCluster]
  exact ⟨fun hz => ray34_avoidReach_trans (ray34_avoidReach_symm h) hz,
    fun hz => ray34_avoidReach_trans h hz⟩


theorem ray34_avoidCluster_mono {V : Type*} {G : SimpleGraph V} {S T : Set V} (hST : S ⊆ T)
    (v : V) : ray34_AvoidCluster G T v ⊆ ray34_AvoidCluster G S v := by
  intro w hw
  obtain ⟨p, hp⟩ := hw
  exact ⟨p, fun u hu hus => hp u hu (hST hus)⟩


theorem ray34_avoidCluster_diff_subset_biUnion {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [LocallyFinite G] {S : Set V} [DecidablePred (· ∉ S)] (v : V) :
    ray34_AvoidCluster G S v \ {v} ⊆
      ⋃ w ∈ (G.neighborFinset v).filter (· ∉ S), ray34_AvoidCluster G (insert v S) w := by
  intro z hz
  obtain ⟨hzc, hzv⟩ := hz
  simp only [Set.mem_singleton_iff] at hzv
  
  obtain ⟨p, hp⟩ := hzc
  set q := p.toPath with hq
  have hqsub : (q : G.Walk v z).support ⊆ p.support := p.support_toPath_subset
  have hqpath : (q : G.Walk v z).IsPath := q.2
  have hqavoid : ∀ u ∈ (q : G.Walk v z).support, u ∉ S := fun u hu => hp u (hqsub hu)
  
  obtain ⟨w, hadj, q', hcons⟩ := Walk.exists_eq_cons_of_ne (Ne.symm hzv) (q : G.Walk v z)
  have hqcons : (q : G.Walk v z) = Walk.cons hadj q' := hcons
  
  have hwS : w ∉ S := by
    apply hqavoid w
    rw [hqcons, Walk.support_cons]
    exact List.mem_cons.mpr (Or.inr q'.start_mem_support)
  
  have hqpath' : (Walk.cons hadj q').IsPath := hqcons ▸ hqpath
  have hvnotin : v ∉ q'.support := ((Walk.cons_isPath_iff hadj q').mp hqpath').2
  have hq'avoid : ∀ u ∈ q'.support, u ∉ insert v S := by
    intro u hu
    rw [Set.mem_insert_iff]; push Not
    refine ⟨?_, ?_⟩
    · rintro rfl; exact hvnotin hu
    · apply hqavoid u
      rw [hqcons, Walk.support_cons]
      exact List.mem_cons.mpr (Or.inr hu)
  rw [Set.mem_iUnion₂]
  refine ⟨w, ?_, ⟨q', hq'avoid⟩⟩
  rw [Finset.mem_filter, mem_neighborFinset]
  exact ⟨hadj, hwS⟩


theorem ray34_konig_step {V : Type*} [DecidableEq V] {G : SimpleGraph V} [LocallyFinite G]
    {S : Set V} {v : V} (hv : v ∉ S) (hinf : (ray34_AvoidCluster G S v).Infinite) :
    ∃ w, G.Adj v w ∧ w ∉ S ∧ w ∈ ray34_AvoidCluster G S v ∧
      (ray34_AvoidCluster G (insert v S) w).Infinite := by
  classical
  
  have hdiff : (ray34_AvoidCluster G S v \ {v}).Infinite :=
    hinf.diff (Set.finite_singleton v)
  
  have hcover := ray34_avoidCluster_diff_subset_biUnion (G := G) (S := S) v
  
  by_contra hcon
  push Not at hcon
  have hfin : ∀ w ∈ (((G.neighborFinset v).filter (· ∉ S) : Finset V) : Set V),
      (ray34_AvoidCluster G (insert v S) w).Finite := by
    intro w hw
    rw [Finset.mem_coe, Finset.mem_filter, mem_neighborFinset] at hw
    
    have hwc : w ∈ ray34_AvoidCluster G S v := by
      refine ⟨Walk.cons hw.1 Walk.nil, ?_⟩
      intro u hu
      rw [Walk.support_cons, Walk.support_nil] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact hv
      · exact hw.2
    exact hcon w hw.1 hw.2 hwc
  
  have hunionfin :
      (⋃ w ∈ (((G.neighborFinset v).filter (· ∉ S) : Finset V) : Set V),
        ray34_AvoidCluster G (insert v S) w).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) hfin
  
  exact hdiff (hunionfin.subset hcover)


end StatMech.Walls
