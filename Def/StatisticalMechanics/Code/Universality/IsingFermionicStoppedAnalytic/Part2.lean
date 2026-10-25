/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part22
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedAnalytic


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def isingLeapfrogBoxSwapEquiv (R : Nat) :
    IsingLeapfrogBox R ≃ IsingLeapfrogBox R where
  toFun := isingLeapfrogBoxSwap R
  invFun := isingLeapfrogBoxSwap R
  left_inv := isingLeapfrogBoxSwap_involutive R
  right_inv := isingLeapfrogBoxSwap_involutive R

end
end StatMech.Universality
