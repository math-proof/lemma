/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part5


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem horizontalHitBelowSplit_spec
    {t : Nat} {start level : Int}
    (z : HorizontalHitBelow t start level) :
    isingDiagonalWalkFirstHitSplit? (start, 0) level
      (horizontalChoiceSteps z.1.1) = some (horizontalHitBelowSplit z) :=
  (Option.some_get (Option.ne_none_iff_isSome.mp z.2)).symm

end
end StatMech.Universality
