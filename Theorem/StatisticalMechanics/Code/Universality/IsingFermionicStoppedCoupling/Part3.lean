/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part3


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem couplingChoiceTransform_steps
    (t : Nat) (start : Int × Int) (level : Int)
    (w : IsingLeapfrogChoiceStringFamily t) :
    isingLeapfrogChoiceSteps
        (isingLeapfrogCouplingChoiceTransform t start level w).1 =
      isingDiagonalWalkCouplingReflectSteps start level
        (isingLeapfrogChoiceSteps w.1) := by
  exact choiceSteps_encodeSteps_of_valid _
    (couplingReflectSteps_valid start level _
      (isingLeapfrogChoiceSteps_valid w.1))

theorem couplingChoiceTransform_involutive
    (t : Nat) (start : Int × Int) (level : Int) :
    Function.LeftInverse
      (isingLeapfrogCouplingChoiceTransform t (reflectedEndpoint level start)
        level)
      (isingLeapfrogCouplingChoiceTransform t start level) := by
  intro w
  apply Subtype.ext
  unfold isingLeapfrogCouplingChoiceTransform
  dsimp only
  have hdecode := choiceSteps_encodeSteps_of_valid
    (isingDiagonalWalkCouplingReflectSteps start level
      (isingLeapfrogChoiceSteps w.1))
    (couplingReflectSteps_valid start level _
      (isingLeapfrogChoiceSteps_valid w.1))
  rw [hdecode]
  rw [couplingReflectSteps_involutive]
  exact encodeSteps_choiceSteps w.1


end
end StatMech.Universality
