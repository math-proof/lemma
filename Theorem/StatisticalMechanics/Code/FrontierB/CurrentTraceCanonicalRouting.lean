/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceClusterUniqueness
import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part4
import Theorem.StatisticalMechanics.Code.Percolation.MengerRouting.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence.Part4
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierB

open Lattice ConfigSpace Percolation

open Percolation.DisjointPaths

variable {d : ℕ}


theorem latticeEdgePart_subset_edgeSet (G : Finset (Sym2 (Site d))) :
    (↑(latticeEdgePart d G) : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet :=
  latticeEdgePart_lattice d G

theorem forceOpenFinset_latticeEdgePart_apply
    (G : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    {e : Sym2 (Site d)} (he : e ∈ (hypercubicLattice d).edgeSet) :
    forceOpenFinset (latticeEdgePart d G) ω e = forceOpenFinset G ω e := by
  simp [forceOpenFinset, latticeEdgePart, he]


theorem corridorStep_latticeEdgePart_iff
    (G : Finset (Sym2 (Site d))) (x y : Site d) :
    CorridorStep (latticeEdgePart d G) x y ↔ CorridorStep G x y := by
  constructor
  · rintro ⟨hadj, hmem, hzero⟩
    exact ⟨hadj, latticeEdgePart_subset d G hmem, hzero⟩
  · rintro ⟨hadj, hmem, hzero⟩
    refine ⟨hadj, ?_, hzero⟩
    change s(x, y) ∈ G.filter
      (fun e => e ∈ (hypercubicLattice d).edgeSet)
    rw [Finset.mem_filter]
    refine ⟨hmem, ?_⟩
    rw [SimpleGraph.mem_edgeSet]
    exact hadj


theorem corridor_latticeEdgePart_iff
    (G : Finset (Sym2 (Site d))) (x y : Site d) :
    Relation.ReflTransGen (CorridorStep (latticeEdgePart d G)) x y ↔
      Relation.ReflTransGen (CorridorStep G) x y := by
  constructor
  · apply Relation.ReflTransGen.mono fun _ _ h =>
      (corridorStep_latticeEdgePart_iff G _ _).mp h
  · apply Relation.ReflTransGen.mono fun _ _ h =>
      (corridorStep_latticeEdgePart_iff G _ _).mpr h


theorem openSubgraph_forceOpenFinset_latticeEdgePart
    (G : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))) :
    openSubgraph d (forceOpenFinset (latticeEdgePart d G) ω) =
      openSubgraph d (forceOpenFinset G ω) := by
  ext x y
  simp only [openSubgraph_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    have hedge : s(x, y) ∈ (hypercubicLattice d).edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact hadj
    exact ⟨hadj, by
      rwa [forceOpenFinset_latticeEdgePart_apply G ω hedge] at hopen⟩
  · rintro ⟨hadj, hopen⟩
    have hedge : s(x, y) ∈ (hypercubicLattice d).edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact hadj
    exact ⟨hadj, by
      rwa [forceOpenFinset_latticeEdgePart_apply G ω hedge]⟩

theorem removeSite_forceOpenFinset_latticeEdgePart_apply
    (z : Site d) (G : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) {e : Sym2 (Site d)}
    (he : e ∈ (hypercubicLattice d).edgeSet) :
    removeSite z (forceOpenFinset (latticeEdgePart d G) ω) e =
      removeSite z (forceOpenFinset G ω) e := by
  unfold removeSite
  by_cases hz : z ∈ e
  · simp [hz]
  · simp only [hz, if_false]
    exact forceOpenFinset_latticeEdgePart_apply G ω he


theorem openSubgraph_removeSite_forceOpenFinset_latticeEdgePart
    (z : Site d) (G : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) :
    openSubgraph d
        (removeSite z (forceOpenFinset (latticeEdgePart d G) ω)) =
      openSubgraph d (removeSite z (forceOpenFinset G ω)) := by
  ext x y
  simp only [openSubgraph_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    have hedge : s(x, y) ∈ (hypercubicLattice d).edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact hadj
    exact ⟨hadj, by
      rwa [removeSite_forceOpenFinset_latticeEdgePart_apply z G ω hedge] at hopen⟩
  · rintro ⟨hadj, hopen⟩
    have hedge : s(x, y) ∈ (hypercubicLattice d).edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact hadj
    exact ⟨hadj, by
      rwa [removeSite_forceOpenFinset_latticeEdgePart_apply z G ω hedge]⟩

theorem cluster_removeSite_forceOpenFinset_latticeEdgePart
    (z x : Site d) (G : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) :
    cluster d (removeSite z (forceOpenFinset (latticeEdgePart d G) ω)) x =
      cluster d (removeSite z (forceOpenFinset G ω)) x := by
  ext y
  simp only [mem_cluster]
  change
    (openSubgraph d
      (removeSite z (forceOpenFinset (latticeEdgePart d G) ω))).Reachable x y ↔
    (openSubgraph d (removeSite z (forceOpenFinset G ω))).Reachable x y
  rw [openSubgraph_removeSite_forceOpenFinset_latticeEdgePart]


theorem corridorWorks_latticeEdgePart
    (a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d))) :
    CorridorWorks a₁ a₂ a₃ (latticeEdgePart d G) =
      CorridorWorks a₁ a₂ a₃ G := by
  ext ω
  simp only [CorridorWorks, Set.mem_setOf_eq]
  rw [cluster_removeSite_forceOpenFinset_latticeEdgePart,
    cluster_removeSite_forceOpenFinset_latticeEdgePart,
    cluster_removeSite_forceOpenFinset_latticeEdgePart]


end StatMech.FrontierB
