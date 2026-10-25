/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part8
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Inductive.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingDobrushinDomain

variable {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]

variable (D : FKIsingDobrushinDomain P M)

namespace CaseTwoExplorationSwitchingLaw

def pointwiseCase (L : D.CaseTwoExplorationSwitchingLaw)
    (omega : ConfigSpace (Sym2 P.V)) :
    D.PointwiseExplorationSwitchingCase L.crossingEdge L.edges omega :=
  .caseTwo (L.paired_balance omega)

end CaseTwoExplorationSwitchingLaw

namespace CaseThreeExplorationSwitchingLaw


def pointwiseCase (L : D.CaseThreeExplorationSwitchingLaw)
    (omega : ConfigSpace (Sym2 P.V)) :
    D.PointwiseExplorationSwitchingCase L.crossingEdge L.edges omega :=
  .caseThree (L.paired_balance omega)

end CaseThreeExplorationSwitchingLaw

namespace CaseThreeEastSouthExplorationSwitchingLaw


def pointwiseCase (L : D.CaseThreeEastSouthExplorationSwitchingLaw)
    (omega : ConfigSpace (Sym2 P.V)) :
    D.PointwiseExplorationSwitchingCase L.crossingEdge L.edges omega :=
  .caseThree (L.paired_balance omega)

end CaseThreeEastSouthExplorationSwitchingLaw

namespace CaseOneExplorationSwitchingLaw


def pointwiseCase (L : D.CaseOneExplorationSwitchingLaw)
    (omega : ConfigSpace (Sym2 P.V)) :
    D.PointwiseExplorationSwitchingCase L.crossingEdge L.edges omega :=
  .caseOne (L.closed_not_mem omega) (L.open_not_mem omega)

end CaseOneExplorationSwitchingLaw
end FKIsingDobrushinDomain
end
end StatMech.Universality
