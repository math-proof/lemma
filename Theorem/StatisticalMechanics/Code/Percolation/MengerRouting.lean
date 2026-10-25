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
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

namespace DisjointPaths

variable {d : ℕ}


theorem mng_cluster_adjClosed (ϱ : ConfigSpace (Sym2 (Site d))) (w : Site d)
    {u v : Site d} (hu : u ∈ cluster d ϱ w) (hadj : (openSubgraph d ϱ).Adj u v) :
    v ∈ cluster d ϱ w := by
  rw [mem_cluster] at hu ⊢
  exact hu.trans hadj.reachable


theorem mng_corridor_mem_destCluster (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {a w : Site d}
    (hc : Relation.ReflTransGen (CorridorStep G) a w) :
    a ∈ cluster d (removeSite 0 (forceOpenFinset G ω)) w := by
  rw [mem_cluster]
  exact (connected_removeSite_forceOpen_of_corridor ω G hc).symm


theorem mng_disjoint_of_cluster_ne (ϱ : ConfigSpace (Sym2 (Site d))) (w₁ w₂ : Site d)
    (h : cluster d ϱ w₁ ≠ cluster d ϱ w₂) :
    Disjoint (cluster d ϱ w₁) (cluster d ϱ w₂) := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  rw [mem_cluster] at hz1 hz2
  exact h (cluster_eq_of_connected (hz1.trans hz2.symm))


end DisjointPaths
end Percolation
end StatMech
