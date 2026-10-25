/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareScaledDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWindowRealization.Part3
import Theorem.StatisticalMechanics.Code.Universality.FiniteInjectivePerturbation
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareScaledDomain.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredPerturbedCarrierPosition_injective
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh) :
    Function.Injective
      (fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh) :=
  (Classical.choose_spec (exists_injective_perturbation
    (fun a : FKIsingSquareWiredCarrier n ↦
      (mesh : Complex) * fkIsingSquareWiredCarrierPosition n hn a)
    (show 0 < mesh / 10 by positivity))).1

theorem fkIsingSquareWiredPerturbedCarrierPosition_dist_lt
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh)
    (a : FKIsingSquareWiredCarrier n) :
    dist (fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a)
        ((mesh : Complex) * fkIsingSquareWiredCarrierPosition n hn a) <
      mesh / 10 :=
  (Classical.choose_spec (exists_injective_perturbation
    (fun a : FKIsingSquareWiredCarrier n ↦
      (mesh : Complex) * fkIsingSquareWiredCarrierPosition n hn a)
    (show 0 < mesh / 10 by positivity))).2 a


end
end StatMech.Universality
