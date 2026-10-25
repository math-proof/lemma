/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorSidesFromClusters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part4


namespace StatMech.Percolation

open StatMech.Lattice StatMech.ConfigSpace SimpleGraph

open StatMech.Percolation.DisjointPaths

variable {d : ℕ}


theorem csc_cluster_adjClosed (ω' : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    ∀ u v, u ∈ cluster d ω' x → (openSubgraph d ω').Adj u v → v ∈ cluster d ω' x := by
  intro u v hu hadj
  rw [mem_cluster] at hu ⊢
  exact hu.trans hadj.reachable


theorem csc_clusters_disjoint (ω' : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (h : ¬ Connected d ω' x y) : Disjoint (cluster d ω' x) (cluster d ω' y) := by
  rw [Set.disjoint_left]
  intro w hwx hwy
  rw [mem_cluster] at hwx hwy
  exact h (hwx.trans hwy.symm)


end StatMech.Percolation
