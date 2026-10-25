/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def isingLeapfrogCouplingChoiceTransform
    (t : Nat) (start : Int × Int) (level : Int) :
    IsingLeapfrogChoiceStringFamily t → IsingLeapfrogChoiceStringFamily t :=
  fun w => ⟨isingLeapfrogEncodeSteps
    (isingDiagonalWalkCouplingReflectSteps start level
      (isingLeapfrogChoiceSteps w.1)), by
    simp [isingLeapfrogEncodeSteps, couplingReflectSteps_length,
      isingLeapfrogChoiceSteps, w.2]⟩

end
end StatMech.Universality
