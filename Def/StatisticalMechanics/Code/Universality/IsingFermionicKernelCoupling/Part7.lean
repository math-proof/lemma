/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part5


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def IsingLeapfrogKilledChoiceFirstHitFamily (R t : Nat)
    (p q : IsingLeapfrogBox R) (level : Int) :=
  {z : IsingLeapfrogKilledChoicePathFamily R t p q ×
      IsingDiagonalWalkHitSplit (isingLeapfrogBoxInt p) level //
    isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level
      (isingLeapfrogChoiceSteps z.1.1) = some z.2}

end
end StatMech.Universality
