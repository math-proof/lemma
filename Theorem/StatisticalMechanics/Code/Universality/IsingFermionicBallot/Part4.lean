/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part4


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem natCard_horizontalHitBelow_eq_firstHitBelow
    (t : Nat) (start level : Int) :
    Nat.card (HorizontalHitBelow t start level) =
      Nat.card (HorizontalFirstHitBelow t start level) := by
  apply le_antisymm
  · exact Nat.card_le_card_of_injective
      (horizontalHitBelowToFirstHitBelow t start level)
      (horizontalHitBelowToFirstHitBelow_injective t start level)
  · exact Nat.card_le_card_of_injective
      (horizontalFirstHitBelowToHitBelow t start level)
      (horizontalFirstHitBelowToHitBelow_injective t start level)

end
end StatMech.Universality
