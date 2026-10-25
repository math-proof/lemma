/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Def.StatisticalMechanics.Code.Lattice.JordanContour
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem cluster_reachable_in_barrier (o : Site 2) {x y : Site 2}
    (hx : x ∈ cluster 2 ω o) (hy : y ∈ cluster 2 ω o) :
    (latticeMinusBarrier (cluster 2 ω o)).Reachable x y := by
  obtain ⟨wx⟩ := (mem_cluster.mp hx)
  obtain ⟨wy⟩ := (mem_cluster.mp hy)
  have rx := walk_induce_reachable (openSubgraph 2 ω) (cluster 2 ω o) wx
    (openWalk_support_mem_cluster o wx) (self_mem_cluster ω o) hx
  have ry := walk_induce_reachable (openSubgraph 2 ω) (cluster 2 ω o) wy
    (openWalk_support_mem_cluster o wy) (self_mem_cluster ω o) hy
  have hmap := (rx.symm.trans ry).map (clusterOpenToBarrierHom (ω := ω) o)
  simpa [clusterOpenToBarrierHom] using hmap


theorem insideComponent_supp_subset_cluster (o : Site 2) :
    ((latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk o).supp ⊆ cluster 2 ω o := by
  intro z hz
  rw [ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq] at hz
  obtain ⟨w⟩ := hz
  exact (latticeMinusBarrier_sameSide (cluster 2 ω o) w).mpr (self_mem_cluster ω o)


theorem insideComponent_finite (o : Site 2) (hfin : (cluster 2 ω o).Finite) :
    ((latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk o).supp.Finite :=
  hfin.subset (insideComponent_supp_subset_cluster (ω := ω) o)


end Lattice
end StatMech
