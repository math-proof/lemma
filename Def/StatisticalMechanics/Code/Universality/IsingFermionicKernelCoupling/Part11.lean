/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part7


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def IsingLeapfrogKilledChoiceNoHitAll (R t : Nat)
    (p : IsingLeapfrogBox R) (level : Int) :=
  {w : {bs : List (Bool × Bool) //
      bs.length = t ∧ IsingLeapfrogKilledChoiceValid R p bs} //
    isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level
      (isingLeapfrogChoiceSteps w.1) = none}

end
end StatMech.Universality
