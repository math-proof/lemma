/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part3


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def isingLeapfrogCouplingChoiceEquiv
    (t : Nat) (start : Int × Int) (level : Int) :
    IsingLeapfrogChoiceStringFamily t ≃ IsingLeapfrogChoiceStringFamily t where
  toFun := isingLeapfrogCouplingChoiceTransform t start level
  invFun := isingLeapfrogCouplingChoiceTransform t
    (reflectedEndpoint level start) level
  left_inv := couplingChoiceTransform_involutive t start level
  right_inv := by
    intro w
    have h := couplingChoiceTransform_involutive t
      (reflectedEndpoint level start) level w
    simpa [reflectedEndpoint] using h

end
end StatMech.Universality
