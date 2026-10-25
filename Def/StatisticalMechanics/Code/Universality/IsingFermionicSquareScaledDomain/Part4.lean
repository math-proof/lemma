/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareScaledDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWindowRealization.Part3
import Theorem.StatisticalMechanics.Code.Universality.FiniteInjectivePerturbation
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareScaledDomain.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareWiredPerturbedRawInterpolant
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh)
    (z : Complex) : Complex :=
  if h : ∃ a : FKIsingSquareWiredCarrier n,
      fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a = z then
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
      (Classical.choose h)
  else 0

end
end StatMech.Universality
