/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareScaledDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWindowRealization.Part3
import Theorem.StatisticalMechanics.Code.Universality.FiniteInjectivePerturbation
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareScaledDomain


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareWiredScaledDobrushinDomain_medialPosition
    (n : Nat) (hn : 0 < n) (mesh : Real)
    (a : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredScaledDobrushinDomain n hn mesh).medialPosition a =
      (mesh : Complex) * fkIsingSquareWiredCarrierPosition n hn a := rfl


@[simp] theorem fkIsingSquareWiredScaledDobrushinDomain_fermionicObservable
    (n : Nat) (hn : 0 < n) (mesh : Real)
    (a : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredScaledDobrushinDomain n hn mesh).fermionicObservable a =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable a := rfl


@[simp] theorem
    fkIsingSquareWiredScaledDobrushinDomain_normalizedFermionicObservable
    (n : Nat) (hn : 0 < n) (mesh : Real)
    (a : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredScaledDobrushinDomain n hn mesh).normalizedFermionicObservable
        mesh a =
      (fkIsingSquareWiredDobrushinDomain n hn).normalizedFermionicObservable
        mesh a := rfl


end
end StatMech.Universality
