/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part8


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem natCard_horizontalFirstHitBelow_lower_eq_upper
    (t : Nat) (level : Int) :
    Nat.card (HorizontalFirstHitBelow t (level - 1) level) =
      Nat.card (HorizontalFirstHitBelow t (level + 1) level) := by
  apply le_antisymm
  · have hle := Nat.card_le_card_of_injective
        (horizontalFirstHitBelowReflect t (level - 1) level)
        (horizontalFirstHitBelowReflect_injective t (level - 1) level)
    simpa only [show 2 * level - (level - 1) = level + 1 by ring] using hle
  · have hle := Nat.card_le_card_of_injective
        (horizontalFirstHitBelowReflect t (level + 1) level)
        (horizontalFirstHitBelowReflect_injective t (level + 1) level)
    simpa only [show 2 * level - (level + 1) = level - 1 by ring] using hle

theorem natCard_horizontalHitBelow_lower_eq_upper
    (t : Nat) (level : Int) :
    Nat.card (HorizontalHitBelow t (level - 1) level) =
      Nat.card (HorizontalHitBelow t (level + 1) level) := by
  rw [natCard_horizontalHitBelow_eq_firstHitBelow,
    natCard_horizontalHitBelow_eq_firstHitBelow,
    natCard_horizontalFirstHitBelow_lower_eq_upper]

end
end StatMech.Universality
