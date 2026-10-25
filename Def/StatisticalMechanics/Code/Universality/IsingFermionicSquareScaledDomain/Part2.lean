/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareScaledDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWindowRealization.Part3
import Theorem.StatisticalMechanics.Code.Universality.FiniteInjectivePerturbation
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareScaledDomain


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareWiredPerturbedCarrierPosition
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh) :
    FKIsingSquareWiredCarrier n → Complex :=
  Classical.choose (exists_injective_perturbation
    (fun a : FKIsingSquareWiredCarrier n ↦
      (mesh : Complex) * fkIsingSquareWiredCarrierPosition n hn a)
    (show 0 < mesh / 10 by positivity))

end
end StatMech.Universality
