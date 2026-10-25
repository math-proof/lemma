/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part8
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part5
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingDobrushinDomain

variable {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]

variable (D : FKIsingDobrushinDomain P M)

namespace ExhaustiveExplorationSwitchingLaw

variable (L : D.ExhaustiveExplorationSwitchingLaw)


def localSwitchingTable : D.BalancedLocalSwitchingTable where
  edges := L.edges
  toggle := localEdgeFlipEquiv L.crossingEdge
  pairedBalance := by
    intro omega
    have hpair (k : Fin 4) :
        D.fermionicSummand omega (L.edges k) +
            D.fermionicSummand
              (localEdgeFlipEquiv L.crossingEdge omega) (L.edges k) =
          D.fermionicSummand (setClosed L.crossingEdge omega) (L.edges k) +
            D.fermionicSummand (setOpen L.crossingEdge omega) (L.edges k) :=
      pair_with_localEdgeFlip_eq_closed_add_open L.crossingEdge
        (fun rho => D.fermionicSummand rho (L.edges k)) omega
    cases hcase : L.caseAt omega with
    | caseOne hclosed hopen =>
        rw [hpair 0, hpair 1, hpair 2, hpair 3]
        simp [fermionicSummand, hclosed, hopen]
    | caseTwo hbalanced =>
        rw [hpair 0, hpair 1, hpair 2, hpair 3]
        exact hbalanced
    | caseThree hbalanced =>
        rw [hpair 0, hpair 1, hpair 2, hpair 3]
        exact hbalanced

end ExhaustiveExplorationSwitchingLaw
end FKIsingDobrushinDomain
end
end StatMech.Universality
