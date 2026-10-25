/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part10


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem natCard_horizontalFreeBelow_upper_eq_deepLower
    (t : Nat) (level : Int) :
    Nat.card (HorizontalFreeBelow t (level + 1) level) =
      Nat.card (HorizontalFreeBelow t (level - 1) (level - 2)) :=
  Nat.card_congr (horizontalFreeBelowUpperEquivDeepLower t level)


end
end StatMech.Universality
