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
import Def.StatisticalMechanics.Code.FrontierB.CurrentTraceCanonicalRouting.Part2
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierB

open Lattice ConfigSpace Percolation

open Percolation.DisjointPaths

variable {d : ℕ}


theorem hubCorridorWorks_latticeEdgePart
    (z a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d))) :
    HubCorridorWorks z a₁ a₂ a₃ (latticeEdgePart d G) =
      HubCorridorWorks z a₁ a₂ a₃ G := by
  ext ω
  simp only [HubCorridorWorks, Set.mem_setOf_eq]
  rw [cluster_removeSite_forceOpenFinset_latticeEdgePart,
    cluster_removeSite_forceOpenFinset_latticeEdgePart,
    cluster_removeSite_forceOpenFinset_latticeEdgePart]


end StatMech.FrontierB
