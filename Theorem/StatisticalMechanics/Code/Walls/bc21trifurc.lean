/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc21trifurc.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc20mengerroute.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc12core.Part2
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
open Set SimpleGraph MeasureTheory
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech.Walls

variable {d : ℕ}


theorem bc21_mengerCore_of_canonicalTrifurcation (ω : ConfigSpace (Sym2 (Site d)))
    (htri : IsCanonicalTrifurcation d ω 0) : MengerCore ω := by
  obtain ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩ := htri
  exact mng_mengerCore_of_neighborClusters ω a₁ a₂ a₃ hne
    ⟨hadj.1.1, hadj.2.1.1, hadj.2.2.1⟩ hinf
    ⟨bc12_cluster_ne_of_not_connected hsep.1,
      bc12_cluster_ne_of_not_connected hsep.2.1,
      bc12_cluster_ne_of_not_connected hsep.2.2⟩


end StatMech.Walls
