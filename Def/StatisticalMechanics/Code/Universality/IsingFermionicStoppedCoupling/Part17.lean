/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part13


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def isingLeapfrogStoppedChoicePathFiberEquiv
    (R t : Nat) (p q : IsingLeapfrogBox R) :
    IsingLeapfrogStoppedChoicePathFamily R t p q ≃
      {w : IsingLeapfrogChoiceStringFamily t //
        isingLeapfrogChoiceRun R p w.1 = q} where
  toFun w := ⟨⟨w.1, w.2.1⟩, w.2.2⟩
  invFun w := ⟨w.1.1, w.1.2, w.2⟩
  left_inv w := by rfl
  right_inv w := by rfl


def IsingLeapfrogStoppedCouplingBadFamily
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    isingLeapfrogChoiceRun R p w.1 ≠
      isingLeapfrogChoiceRun R p'
        (isingLeapfrogCouplingChoiceTransform t
          (isingLeapfrogBoxInt p) level w).1}

end
end StatMech.Universality
