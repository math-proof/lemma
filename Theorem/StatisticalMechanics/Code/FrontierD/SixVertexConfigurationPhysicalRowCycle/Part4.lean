/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem natCard_natGradedPairFiber
    {A B : Type*} [Finite A] [Finite B]
    (gradeA : A → Nat) (gradeB : B → Nat) (total : Nat) :
    Nat.card {pair : A × B // gradeA pair.1 + gradeB pair.2 = total} =
      ∑ k : Fin (total + 1),
        Nat.card {a : A // gradeA a = k.val} *
          Nat.card {b : B // gradeB b = total - k.val} := by
  rw [Nat.card_congr (natGradedPairFiberEquivSigma gradeA gradeB total),
    Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.card_congr
    (natGradedPairFiberAtEquivProd gradeA gradeB total k), Nat.card_prod]

end
end StatMech.FrontierD
