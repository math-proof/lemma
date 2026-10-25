/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part8
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part7
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingDobrushinDomain

variable {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]

variable (D : FKIsingDobrushinDomain P M)

structure BalancedLocalSwitchingTable where
  edges : Fin 4 -> M
  toggle : ConfigSpace (Sym2 P.V) ≃ ConfigSpace (Sym2 P.V)
  pairedBalance : forall omega,
    (D.fermionicSummand omega (edges 0) +
        D.fermionicSummand (toggle omega) (edges 0)) -
      (D.fermionicSummand omega (edges 1) +
        D.fermionicSummand (toggle omega) (edges 1)) =
    Complex.I *
      ((D.fermionicSummand omega (edges 2) +
          D.fermionicSummand (toggle omega) (edges 2)) -
        (D.fermionicSummand omega (edges 3) +
          D.fermionicSummand (toggle omega) (edges 3)))

end FKIsingDobrushinDomain
end
end StatMech.Universality
