/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part8
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part6
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingDobrushinDomain

variable {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]

variable (D : FKIsingDobrushinDomain P M)

namespace CaseThreeEastSouthExplorationSwitchingLaw

variable (L : D.CaseThreeEastSouthExplorationSwitchingLaw)

theorem crossingEdge_mem : L.crossingEdge ∈ P.G.edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  exact L.crossing_adj

theorem clusterCountEq (omega : ConfigSpace (Sym2 P.V)) :
    numClustersBC P.G D.wiring (setOpen L.crossingEdge omega) =
      numClustersBC P.G D.wiring (setClosed L.crossingEdge omega) := by
  exact D.numClustersBC_setOpen_eq_setClosed_of_reachable
    L.crossingA L.crossingB L.crossing_adj omega
      (L.closed_endpoints_reachable omega)

end CaseThreeEastSouthExplorationSwitchingLaw
end FKIsingDobrushinDomain
end
end StatMech.Universality
