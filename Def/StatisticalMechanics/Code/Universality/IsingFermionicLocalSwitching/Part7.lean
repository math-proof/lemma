/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part8
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part3
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingDobrushinDomain

variable {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]

variable (D : FKIsingDobrushinDomain P M)

namespace CaseOneExplorationSwitchingLaw

variable (L : D.CaseOneExplorationSwitchingLaw)

def crossingEdge : Sym2 P.V := s(L.crossingA, L.crossingB)

def localSwitchingTable : D.LocalSwitchingTable where
  edges := L.edges
  toggle := localEdgeFlipEquiv L.crossingEdge
  pairedContribution := by
    intro omega
    refine ⟨0, ?_⟩
    intro k
    calc
      D.fermionicSummand omega (L.edges k) +
          D.fermionicSummand (localEdgeFlipEquiv L.crossingEdge omega) (L.edges k) =
        D.fermionicSummand (setClosed L.crossingEdge omega) (L.edges k) +
          D.fermionicSummand (setOpen L.crossingEdge omega) (L.edges k) :=
        pair_with_localEdgeFlip_eq_closed_add_open L.crossingEdge
          (fun rho => D.fermionicSummand rho (L.edges k)) omega
      _ = 0 := by
        unfold crossingEdge
        simp [fermionicSummand, L.closed_not_mem omega k,
          L.open_not_mem omega k]
      _ = isingF k 0 := by
        fin_cases k <;> simp [isingF]

end CaseOneExplorationSwitchingLaw
end FKIsingDobrushinDomain
end
end StatMech.Universality
