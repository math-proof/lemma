/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part12


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def IsingLeapfrogChoiceExecValid (R : Nat) (p : IsingLeapfrogBox R)
    (bs : List (Bool × Bool)) : Prop :=
  ∀ j, j < bs.length →
    ¬ isingLeapfrogBoxBoundary R
      (isingLeapfrogChoiceRun R p (bs.take j))

end
end StatMech.Universality
