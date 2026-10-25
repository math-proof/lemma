/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part8
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part8
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingDobrushinDomain

variable {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]

variable (D : FKIsingDobrushinDomain P M)

def balancedLocalSwitchingTableOfClosedOpen
    (crossingEdge : Sym2 P.V) (edges : Fin 4 -> M)
    (hbalance : D.ClosedOpenPairedBalance crossingEdge edges) :
    D.BalancedLocalSwitchingTable where
  edges := edges
  toggle := localEdgeFlipEquiv crossingEdge
  pairedBalance := by
    intro omega
    rw [pair_with_localEdgeFlip_eq_closed_add_open crossingEdge
        (fun rho => D.fermionicSummand rho (edges 0)) omega,
      pair_with_localEdgeFlip_eq_closed_add_open crossingEdge
        (fun rho => D.fermionicSummand rho (edges 1)) omega,
      pair_with_localEdgeFlip_eq_closed_add_open crossingEdge
        (fun rho => D.fermionicSummand rho (edges 2)) omega,
      pair_with_localEdgeFlip_eq_closed_add_open crossingEdge
        (fun rho => D.fermionicSummand rho (edges 3)) omega]
    exact hbalance omega

namespace CaseTwoExplorationSwitchingLaw

variable (L : D.CaseTwoExplorationSwitchingLaw)


def localSwitchingTable : D.BalancedLocalSwitchingTable :=
  balancedLocalSwitchingTableOfClosedOpen D L.crossingEdge L.edges
    L.paired_balance

end CaseTwoExplorationSwitchingLaw
end FKIsingDobrushinDomain
end
end StatMech.Universality
