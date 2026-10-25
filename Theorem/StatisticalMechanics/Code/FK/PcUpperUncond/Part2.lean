/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FK.CriticalPoint.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.FK.PcUpperUncond.Part2
open MeasureTheory Filter Topology Finset Set SimpleGraph
open scoped NNReal ENNReal BigOperators Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation


theorem exists_closed_latticeCircuit_of_finite_cluster
    {ω : ConfigSpace (Sym2 (Site 2))} (o : Site 2) (hfin : (cluster 2 ω o).Finite) :
    ∃ (u : Site 2) (c : (hypercubicLattice 2).Walk u u), c.IsCycle ∧
      ω ∈ closedCircuitEvent c := by
  obtain ⟨z, hreach, hzout⟩ := exists_walk_exterior o hfin
  obtain ⟨w⟩ := hreach
  obtain ⟨u, c0, hc0cyc⟩ := exists_dualCircuit_of_finite_cluster o hfin w hzout
  refine ⟨u, c0.mapLe (faceBoundaryGraph_le _), hc0cyc.mapLe _, ?_⟩
  intro f g hfg
  rw [Walk.edges_mapLe_eq_edges] at hfg
  have hadj : (faceBoundaryGraph (cluster 2 ω o)).Adj f g := c0.adj_of_mem_edges hfg
  have hbd : bdEdge (cluster 2 ω o) (sharedPrimalEdge f g) := hadj.2
  obtain ⟨p, q, hpq, hadjpq⟩ := sharedPrimalEdge_isLatticeEdge hadj.1
  rw [hpq] at hbd ⊢
  rw [bdEdge_mk] at hbd
  exact cluster_edgeBoundary_isClosed o ((mem_edgeBoundary).mpr ⟨hadjpq, hbd⟩)


theorem exists_enclosing_closed_latticeCircuit_of_finite_cluster
    {ω : ConfigSpace (Sym2 (Site 2))} (o : Site 2) (hfin : (cluster 2 ω o).Finite) :
    ∃ z : Site 2,
      (∃ (u : Site 2) (c : (hypercubicLattice 2).Walk u u), c.IsCycle ∧ ω ∈ closedCircuitEvent c)
        ∧ ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable o z
        ∧ ∀ γ : (hypercubicLattice 2).Walk o z, ¬ Even (crossCount (cluster 2 ω o) γ) := by
  obtain ⟨z, hreach, hzout⟩ := exists_walk_exterior o hfin
  obtain ⟨w⟩ := hreach
  obtain ⟨_, hsep, hwind⟩ := cluster_enclosed_with_winding o hfin w hzout
  exact ⟨z, exists_closed_latticeCircuit_of_finite_cluster o hfin, hsep, hwind⟩


theorem finiteCluster_subset_iUnion_closedCircuit (o : Site 2) :
    {ω : ConfigSpace (Sym2 (Site 2)) | (cluster 2 ω o).Finite}
      ⊆ ⋃ (u : Site 2) (c : (hypercubicLattice 2).Walk u u) (_ : c.IsCycle),
          closedCircuitEvent c := by
  intro ω hω
  obtain ⟨u, c, hcyc, hmem⟩ := exists_closed_latticeCircuit_of_finite_cluster o hω
  exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hcyc, hmem⟩⟩⟩


theorem compl_percolationEvent_eq_finiteCluster :
    (percolationEvent 2)ᶜ
      = {ω : ConfigSpace (Sym2 (Site 2)) | (cluster 2 ω (origin 2)).Finite} := by
  ext ω
  rw [Set.mem_compl_iff, mem_percolationEvent, Set.mem_setOf_eq, Set.not_infinite]


end FK
end StatMech
