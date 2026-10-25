/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def IsingLeapfrogKilledChoiceValid (R : Nat) :
    IsingLeapfrogBox R → List (Bool × Bool) → Prop
  | p, [] => ¬ isingLeapfrogBoxBoundary R p
  | p, b :: bs =>
      ¬ isingLeapfrogBoxBoundary R p ∧
        IsingLeapfrogKilledChoiceValid R
          (isingLeapfrogChoiceNext R p b) bs

def IsingLeapfrogKilledChoicePathFamily (R t : Nat)
    (p q : IsingLeapfrogBox R) :=
  {bs : List (Bool × Bool) //
    bs.length = t ∧ IsingLeapfrogKilledChoiceValid R p bs ∧
      isingLeapfrogChoiceRun R p bs = q}

end
end StatMech.Universality
