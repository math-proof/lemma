/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part8
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part9
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingDobrushinDomain

variable {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]

variable (D : FKIsingDobrushinDomain P M)

namespace CaseThreeExplorationSwitchingLaw

variable (L : D.CaseThreeExplorationSwitchingLaw)

def localSwitchingTable : D.BalancedLocalSwitchingTable :=
  balancedLocalSwitchingTableOfClosedOpen D L.crossingEdge L.edges
    L.paired_balance

end CaseThreeExplorationSwitchingLaw
end FKIsingDobrushinDomain
end
end StatMech.Universality
