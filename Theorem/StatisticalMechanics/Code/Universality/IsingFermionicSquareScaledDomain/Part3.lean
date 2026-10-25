/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareScaledDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWindowRealization.Part3
import Theorem.StatisticalMechanics.Code.Universality.FiniteInjectivePerturbation
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareScaledDomain.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareWiredPerturbedDobrushinDomain_fermionicObservable
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh)
    (a : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredPerturbedDobrushinDomain n hn mesh hmesh).fermionicObservable
        a =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable a := rfl


end
end StatMech.Universality
