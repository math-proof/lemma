/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part2


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem IsingLeapfrogKilledChoiceValid.start_not_boundary
    (R : Nat) (p : IsingLeapfrogBox R) (bs : List (Bool × Bool))
    (h : IsingLeapfrogKilledChoiceValid R p bs) :
    ¬ isingLeapfrogBoxBoundary R p := by
  cases bs with
  | nil => exact h
  | cons b bs => exact h.1

theorem IsingLeapfrogKilledChoiceValid.endpoint_not_boundary
    (R : Nat) (p : IsingLeapfrogBox R) (bs : List (Bool × Bool))
    (h : IsingLeapfrogKilledChoiceValid R p bs) :
    ¬ isingLeapfrogBoxBoundary R (isingLeapfrogChoiceRun R p bs) := by
  induction bs generalizing p with
  | nil => exact h
  | cons b bs ih =>
      exact ih (isingLeapfrogChoiceNext R p b) h.2

end
end StatMech.Universality
