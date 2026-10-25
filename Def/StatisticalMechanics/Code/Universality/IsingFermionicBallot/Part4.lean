/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part2


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def HorizontalNoHitBelow (t : Nat) (start level : Int) :=
  {w : HorizontalFreeBelow t start level //
    ¬ isingDiagonalWalkFirstHitSplit? (start, 0) level
      (horizontalChoiceSteps w.val) ≠ none}

end
end StatMech.Universality
