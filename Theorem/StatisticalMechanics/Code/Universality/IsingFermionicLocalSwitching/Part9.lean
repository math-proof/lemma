/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part8
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part8
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingDobrushinDomain

variable {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]

variable (D : FKIsingDobrushinDomain P M)

namespace CaseTwoExplorationSwitchingLaw

variable (L : D.CaseTwoExplorationSwitchingLaw)


theorem fermionicObservable_contour_relation :
    D.fermionicObservable (L.edges 0) - D.fermionicObservable (L.edges 1) =
      Complex.I * (D.fermionicObservable (L.edges 2) -
        D.fermionicObservable (L.edges 3)) :=
  (L.localSwitchingTable D).fermionicObservable_contour_relation D

end CaseTwoExplorationSwitchingLaw
end FKIsingDobrushinDomain
end
end StatMech.Universality
