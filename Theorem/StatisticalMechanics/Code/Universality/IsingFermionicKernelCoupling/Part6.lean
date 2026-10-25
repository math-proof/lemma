/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part8


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem natCard_killedChoiceFirstHitFamily_eq_surviving
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    Nat.card (IsingLeapfrogKilledChoiceFirstHitFamily R t p q level) =
      Nat.card (SurvivingFirstHitFamily R (isingLeapfrogBoxInt p) level t
        (isingLeapfrogBoxInt q)) :=
  Nat.card_congr (killedChoiceFirstHitFamilyEquiv R t p q level)


end
end StatMech.Universality
