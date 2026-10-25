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
import Instance.StatisticalMechanics.Code.Walls.bc34ray
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem ray34_avoidCluster_empty_eq_cluster (ω : ConfigSpace (Sym2 (Site d))) (v : Site d) :
    ray34_AvoidCluster (openSubgraph d ω) ∅ v = cluster d ω v := by
  ext w
  simp only [ray34_mem_avoidCluster, mem_cluster]
  constructor
  · rintro ⟨p, _⟩; exact p.reachable
  · rintro ⟨p⟩; exact ⟨p, fun u _ => Set.notMem_empty u⟩


theorem ray34_connected_of_avoidReach {ω : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)}
    {v w : Site d} (h : ray34_AvoidReach (openSubgraph d ω) S v w) : Connected d ω v w :=
  h.choose.reachable


theorem ray34_Tavoiding_ray_of_infinite_cluster (ω : ConfigSpace (Sym2 (Site d))) {v : Site d}
    (hinf : (cluster d ω v).Infinite) (T : Finset (Site d)) :
    ∃ b : Site d, Connected d ω v b ∧
      ∃ r : ℕ → Site d, r 0 = b ∧ Function.Injective r ∧
        (∀ k, (openSubgraph d ω).Adj (r k) (r (k + 1))) ∧
        (∀ k, r k ∉ T) := by
  classical
  
  have hinf' : (ray34_AvoidCluster (openSubgraph d ω) ∅ v).Infinite := by
    rw [ray34_avoidCluster_empty_eq_cluster]; exact hinf
  
  obtain ⟨b, hbmem, hbinf⟩ := ray34_infinite_avoidCluster_of_finset hinf' T
  have hbconn : Connected d ω v b := by
    rw [ray34_avoidCluster_empty_eq_cluster] at hbmem
    exact hbmem
  
  have hbT : b ∉ (↑T : Set (Site d)) := ray34_notMem_of_avoidCluster_nonempty hbinf.nonempty
  
  obtain ⟨r, hr0, hinj, hadj, hravoid⟩ :=
    ray34_konig (openSubgraph d ω) hbT hbinf
  refine ⟨b, hbconn, r, hr0, hinj, hadj, ?_⟩
  intro k
  have := hravoid k
  rwa [Finset.mem_coe] at this


theorem ray34_adj_removeSite_of_adj {ω : ConfigSpace (Sym2 (Site d))} {x a c : Site d}
    (hadj : (openSubgraph d ω).Adj a c) (ha : a ≠ x) (hc : c ≠ x) :
    (openSubgraph d (removeSite x ω)).Adj a c := by
  obtain ⟨hlat, hopen⟩ := hadj
  refine ⟨hlat, ?_⟩
  have hxnotin : x ∉ s(a, c) := by
    rw [Sym2.mem_iff]; push Not; exact ⟨fun h => ha h.symm, fun h => hc h.symm⟩
  rw [removeSite_apply_of_notMem hxnotin]; exact hopen


theorem ray34_removeSite_Tavoiding_ray_of_trif (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (hinf : (cluster d ω x).Infinite) (T : Finset (Site d)) :
    ∃ b : Site d, Connected d ω x b ∧
      ∃ r : ℕ → Site d, r 0 = b ∧ Function.Injective r ∧
        (∀ k, (openSubgraph d (removeSite x ω)).Adj (r k) (r (k + 1))) ∧
        (∀ k, r k ∉ T) := by
  classical
  set G := openSubgraph d ω with hG
  
  have hinf' : (ray34_AvoidCluster G ∅ x).Infinite := by
    rw [hG, ray34_avoidCluster_empty_eq_cluster]; exact hinf
  
  obtain ⟨b, hbmem, hbinf⟩ := ray34_infinite_avoidCluster_of_finset hinf' (insert x T)
  have hbconn : Connected d ω x b := by
    rw [hG, ray34_avoidCluster_empty_eq_cluster] at hbmem; exact hbmem
  have hbnot : b ∉ (↑(insert x T) : Set (Site d)) :=
    ray34_notMem_of_avoidCluster_nonempty hbinf.nonempty
  
  obtain ⟨r, hr0, hinj, hadj, hravoid⟩ := ray34_konig G hbnot hbinf
  
  have hrx : ∀ k, r k ≠ x := by
    intro k hk
    have := hravoid k
    rw [Finset.coe_insert, Set.mem_insert_iff] at this
    push Not at this
    exact this.1 hk
  have hrT : ∀ k, r k ∉ T := by
    intro k
    have := hravoid k
    rw [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at this
    push Not at this
    exact this.2
  refine ⟨b, hbconn, r, hr0, hinj, ?_, hrT⟩
  intro k
  exact ray34_adj_removeSite_of_adj (hadj k) (hrx k) (hrx (k + 1))


end StatMech.Walls
