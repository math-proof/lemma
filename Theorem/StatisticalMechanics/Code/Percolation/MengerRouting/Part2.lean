/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part4
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
import Def.StatisticalMechanics.Code.Percolation.MengerRouting
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

namespace DisjointPaths

variable {d : ℕ}


theorem mng_disjointRouting_of_mengerCore (ω : ConfigSpace (Sym2 (Site d)))
    (h : MengerCore ω) : DisjointCorridorRouting ω := by
  obtain ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, hne, hadj,
    ⟨hc1, hc2, hc3⟩, ⟨hw1, hw2, hw3⟩, hd12, hd13, hd23⟩ := h
  set ϱ := removeSite (0 : Site d) (forceOpenFinset G ω) with hϱ
  
  refine ⟨a₁, a₂, a₃, G, w₁, w₂, w₃,
    cluster d ϱ w₁, cluster d ϱ w₂, cluster d ϱ w₃,
    hne, hadj, ⟨hc1, hc2, hc3⟩, ⟨hw1, hw2, hw3⟩, ?_, ?_, ?_⟩
  · 
    exact ⟨mng_corridor_mem_destCluster ω G hc1,
      mng_corridor_mem_destCluster ω G hc2,
      mng_corridor_mem_destCluster ω G hc3⟩
  · 
    exact ⟨fun u v hu hadj => mng_cluster_adjClosed ϱ w₁ hu hadj,
      fun u v hu hadj => mng_cluster_adjClosed ϱ w₂ hu hadj,
      fun u v hu hadj => mng_cluster_adjClosed ϱ w₃ hu hadj⟩
  · 
    exact ⟨mng_disjoint_of_cluster_ne ϱ w₁ w₂ hd12,
      mng_disjoint_of_cluster_ne ϱ w₁ w₃ hd13,
      mng_disjoint_of_cluster_ne ϱ w₂ w₃ hd23⟩


theorem mng_forceOpenFinset_empty (ω : ConfigSpace (Sym2 (Site d))) :
    forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := by
  funext e; simp [forceOpenFinset]


theorem mng_mengerCore_of_neighborClusters (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hinf : (cluster d (removeSite 0 ω) a₁).Infinite ∧
      (cluster d (removeSite 0 ω) a₂).Infinite ∧
      (cluster d (removeSite 0 ω) a₃).Infinite)
    (hdist : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧
      cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧
      cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
    MengerCore ω := by
  refine ⟨a₁, a₂, a₃, ∅, a₁, a₂, a₃, hne, hadj,
    ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩,
    ?_, ?_⟩
  · rw [mng_forceOpenFinset_empty]; exact hinf
  · rw [mng_forceOpenFinset_empty]; exact hdist


end DisjointPaths
end Percolation
end StatMech
