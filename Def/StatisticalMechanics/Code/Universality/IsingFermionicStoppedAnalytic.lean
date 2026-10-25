/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part22


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def isingLeapfrogBoxSwap (R : Nat) (p : IsingLeapfrogBox R) :
    IsingLeapfrogBox R :=
  (p.2, p.1)

end
end StatMech.Universality
