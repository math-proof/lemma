/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part13


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem horizontalFirstHitSplit_eq_none_of_avoids
    (t : Nat) (start level : Int) (bs : List Bool)
    (hlen : bs.length = t)
    (havoid : ∀ k, k ≤ t →
      lineFreeEndpoint start (bs.take k) ≠ level) :
    isingDiagonalWalkFirstHitSplit? (start, 0) level
      (horizontalChoiceSteps bs) = none := by
  cases hsplit : isingDiagonalWalkFirstHitSplit? (start, 0) level
      (horizontalChoiceSteps bs) with
  | none => rfl
  | some split =>
      exfalso
      have hsteps := firstHitSplit_steps hsplit
      have hk : split.before.length ≤ t := by
        calc
          split.before.length ≤ split.steps.length := by
            simp [IsingDiagonalWalkHitSplit.steps]
          _ = (horizontalChoiceSteps bs).length := congrArg List.length hsteps
          _ = t := by rw [horizontalChoiceSteps_length, hlen]
      exact (havoid split.before.length hk) (by
        calc
          lineFreeEndpoint start (bs.take split.before.length) =
              (isingDiagonalWalkEndpoint (start, 0)
                (horizontalChoiceSteps (bs.take split.before.length))).1 :=
            lineFreeEndpoint_horizontalChoiceSteps _ _
          _ = (isingDiagonalWalkEndpoint (start, 0)
                ((horizontalChoiceSteps bs).take split.before.length)).1 := by
            simp [horizontalChoiceSteps, List.map_take]
          _ = (isingDiagonalWalkEndpoint (start, 0) split.before).1 := by
            rw [← hsteps]
            simp [IsingDiagonalWalkHitSplit.steps]
          _ = level := split.hit)

end
end StatMech.Universality
