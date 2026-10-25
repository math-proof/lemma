/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part6


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def horizontalFreeBelowUpperEquivHitBelowUpper
    (t : Nat) (level : Int) :
    HorizontalFreeBelow t (level + 1) level ≃
      HorizontalHitBelow t (level + 1) level where
  toFun w := ⟨w, by
    intro hnone
    have hvalid := horizontalChoiceSteps_valid w.1
    have hend :
        (isingDiagonalWalkEndpoint (level + 1, 0)
          (horizontalChoiceSteps w.1)).1 ≤ level := by
      exact (show (isingDiagonalWalkEndpoint (level + 1, 0)
          (horizontalChoiceSteps w.1)).1 < level from by
        rw [← lineFreeEndpoint_horizontalChoiceSteps]
        exact w.2.2).le
    rcases exists_prefix_fst_eq_of_ge_of_gt
        (horizontalChoiceSteps w.1) (level + 1, 0) level
        hvalid (by omega) hend with ⟨k, hk, heq⟩
    exact (firstHitSplit_none_endpoint_fst_ne hnone k hk) heq⟩
  invFun w := w.1
  left_inv _ := rfl
  right_inv w := Subtype.ext rfl

end
end StatMech.Universality
