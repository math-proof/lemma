/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingSHolo.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part5
open Finset Complex
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

variable (P : PlanarZ2Subgraph) (M : Type*) [Fintype M] [DecidableEq M]


namespace FKIsingDobrushinDomain

variable {P M} (D : FKIsingDobrushinDomain P M)


structure LocalSwitchingTable where
  edges : Fin 4 -> M
  toggle : ConfigSpace (Sym2 P.V) ≃ ConfigSpace (Sym2 P.V)
  pairedContribution : forall omega,
    ∃ X : Complex, forall k : Fin 4,
      D.fermionicSummand omega (edges k) +
          D.fermionicSummand (toggle omega) (edges k) =
        isingF k X

end FKIsingDobrushinDomain
end
end StatMech.Universality
