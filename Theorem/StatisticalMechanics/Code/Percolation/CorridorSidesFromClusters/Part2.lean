/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorSidesFromClusters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part4
import Def.StatisticalMechanics.Code.Percolation.CorridorSidesFromClusters


namespace StatMech.Percolation

open StatMech.Lattice StatMech.ConfigSpace SimpleGraph

open StatMech.Percolation.DisjointPaths

variable {d : ℕ}


theorem csc_disjointCorridorRouting_of_distinctClusters (ω : ConfigSpace (Sym2 (Site d)))
    (h : csc_DistinctClusterCorridors ω) : DisjointCorridorRouting ω := by
  obtain ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, hne, hadj, hcorr, hinf, hsep⟩ := h
  set ω' : ConfigSpace (Sym2 (Site d)) := removeSite 0 (forceOpenFinset G ω) with hω'
  refine ⟨a₁, a₂, a₃, G, w₁, w₂, w₃,
    cluster d ω' a₁, cluster d ω' a₂, cluster d ω' a₃,
    hne, hadj, hcorr, hinf, ?_, ?_, ?_⟩
  · exact ⟨mem_cluster.mpr (connected_refl ω' a₁), mem_cluster.mpr (connected_refl ω' a₂),
      mem_cluster.mpr (connected_refl ω' a₃)⟩
  · exact ⟨csc_cluster_adjClosed ω' a₁, csc_cluster_adjClosed ω' a₂, csc_cluster_adjClosed ω' a₃⟩
  · exact ⟨csc_clusters_disjoint ω' hsep.1, csc_clusters_disjoint ω' hsep.2.1,
      csc_clusters_disjoint ω' hsep.2.2⟩


theorem csc_corridorCover_of_distinctClusters {n : ℕ}
    (h : ∀ ω ∈ threeMeetBox d n, csc_DistinctClusterCorridors ω) :
    threeMeetBox d n ⊆
      ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))),
        CorridorWorks a₁ a₂ a₃ G :=
  corridorCover_of_routing (fun ω hω => csc_disjointCorridorRouting_of_distinctClusters ω (h ω hω))

end StatMech.Percolation
