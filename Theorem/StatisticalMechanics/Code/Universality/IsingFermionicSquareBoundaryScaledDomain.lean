/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryScaledDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareScaledDomain.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer.Part8
import Theorem.StatisticalMechanics.Code.Universality.FiniteHolomorphicInterpolation
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryScaledDomain


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareBoundaryPerturbedDobrushinDomain_fermionicObservable
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh)
    (a : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareBoundaryPerturbedDobrushinDomain n hn mesh hmesh).fermionicObservable
        a =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        a := rfl


end
end StatMech.Universality
