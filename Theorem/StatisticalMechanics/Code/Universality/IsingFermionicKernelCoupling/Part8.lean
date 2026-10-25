/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part12


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem natCard_killedChoiceNoHitAll_eq_sum
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    Nat.card (IsingLeapfrogKilledChoiceNoHitAll R t p level) =
      ∑ q, Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) := by
  rw [Nat.card_congr (killedChoiceNoHitAllEquivSigma R t p level),
    Nat.card_sigma]


end
end StatMech.Universality
