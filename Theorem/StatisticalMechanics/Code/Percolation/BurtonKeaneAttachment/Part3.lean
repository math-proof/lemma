/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.CorridorConfinement.Part2
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
import Def.StatisticalMechanics.Code.Percolation.BurtonKeaneAttachment.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

open DisjointPaths

variable {d : ℕ}


theorem bka_distinct_clusters_of_clusterRespecting (ω : ConfigSpace (Sym2 (Site d)))
    (h : bka_ClusterRespectingRouting ω) : DisjointCorridorRouting ω := by
  obtain ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, R₁, R₂, R₃, hne, hadj, ⟨hc1, hc2, hc3⟩,
    ⟨hw1, hw2, hw3⟩, ⟨hm1, hm2, hm3⟩, ⟨ho1, ho2, ho3⟩, ⟨hg1, hg2, hg3⟩,
    hd12, hd13, hd23⟩ := h
  
  refine ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, R₁, R₂, R₃, hne, hadj, ⟨hc1, hc2, hc3⟩,
    ⟨hw1, hw2, hw3⟩, ⟨hm1, hm2, hm3⟩,
    ⟨bka_region_rhoAdjClosed ω G R₁ ho1 hg1, bka_region_rhoAdjClosed ω G R₂ ho2 hg2,
      bka_region_rhoAdjClosed ω G R₃ ho3 hg3⟩, hd12, hd13, hd23⟩


end Percolation
end StatMech
