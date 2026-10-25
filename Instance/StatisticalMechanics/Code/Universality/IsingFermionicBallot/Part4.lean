/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part3


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable instance horizontalFirstHitBelow_finite
    (t : Nat) (start level : Int) :
    Finite (HorizontalFirstHitBelow t start level) :=
  Finite.of_injective (horizontalFirstHitBelowToHitBelow t start level)
    (horizontalFirstHitBelowToHitBelow_injective t start level)

end
end StatMech.Universality
