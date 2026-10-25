/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bcl2close.Part2
import Theorem.StatisticalMechanics.Code.Walls.bcorcorridors.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc117mergeproof.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation
open StatMech.Ising StatMech.IsingFK


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


theorem bins_cluster_subset_of_openClosed (ω : ConfigSpace (Sym2 (Site 2)))
    {a : Site 2} {S : Set (Site 2)} (ha : a ∈ S)
    (hclosed : ∀ u v : Site 2, u ∈ S → IsOpenEdge 2 (removeSite 0 ω) u v → v ∈ S) :
    cluster 2 (removeSite 0 ω) a ⊆ S := by
  intro y hy
  obtain ⟨w⟩ := (hy : (openSubgraph 2 (removeSite 0 ω)).Reachable a y)
  exact bpt2_walk_invariant ω hclosed w ha


theorem bins_precursor_of_sides (ω : ConfigSpace (Sym2 (Site 2))) (a₁ a₂ a₃ : Site 2)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
      (hypercubicLattice 2).Adj 0 a₃)
    (S₁ S₂ S₃ : Set (Site 2))
    (ha : a₁ ∈ S₁ ∧ a₂ ∈ S₂ ∧ a₃ ∈ S₃)
    (hd : Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃)
    (hc : (∀ u v : Site 2, u ∈ S₁ → IsOpenEdge 2 (removeSite 0 ω) u v → v ∈ S₁) ∧
      (∀ u v : Site 2, u ∈ S₂ → IsOpenEdge 2 (removeSite 0 ω) u v → v ∈ S₂) ∧
      (∀ u v : Site 2, u ∈ S₃ → IsOpenEdge 2 (removeSite 0 ω) u v → v ∈ S₃))
    (hinf : (cluster 2 (removeSite 0 ω) a₁).Infinite ∧
      (cluster 2 (removeSite 0 ω) a₂).Infinite ∧
      (cluster 2 (removeSite 0 ω) a₃).Infinite) :
    ω ∈ NeighborTrifPrecursor 2 a₁ a₂ a₃ := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hd12, hd13, hd23⟩ := hd
  obtain ⟨hc1, hc2, hc3⟩ := hc
  have hsub1 : cluster 2 (removeSite 0 ω) a₁ ⊆ S₁ :=
    bins_cluster_subset_of_openClosed ω ha1 hc1
  have hsub2 : cluster 2 (removeSite 0 ω) a₂ ⊆ S₂ :=
    bins_cluster_subset_of_openClosed ω ha2 hc2
  have hsub3 : cluster 2 (removeSite 0 ω) a₃ ⊆ S₃ :=
    bins_cluster_subset_of_openClosed ω ha3 hc3
  refine ⟨hne, hadj, hinf, ?_, ?_, ?_⟩
  · intro hconn; exact (Set.disjoint_left.mp hd12) (hsub1 (mem_cluster.mpr hconn)) ha2
  · intro hconn; exact (Set.disjoint_left.mp hd13) (hsub1 (mem_cluster.mpr hconn)) ha3
  · intro hconn; exact (Set.disjoint_left.mp hd23) (hsub2 (mem_cluster.mpr hconn)) ha3


end StatMech.Walls
