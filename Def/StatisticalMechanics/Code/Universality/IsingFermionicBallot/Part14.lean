/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part10


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def horizontalNoHitToNoHitBelow
    (t : Nat) (level : Int) :
    IsingHorizontalNoHitFamily t (level - 1) level →
      HorizontalNoHitBelow t (level - 1) level := fun w => by
  have hnone := horizontalFirstHitSplit_eq_none_of_avoids t (level - 1)
    level w.1 w.2.1 w.2.2
  have hbelow : lineFreeEndpoint (level - 1) w.1 < level := by
    by_contra hnot
    have hend : level ≤
        (isingDiagonalWalkEndpoint (level - 1, 0)
          (horizontalChoiceSteps w.1)).1 := by
      rw [← lineFreeEndpoint_horizontalChoiceSteps]
      omega
    rcases exists_prefix_fst_eq_of_lt_of_le
        (horizontalChoiceSteps w.1) (level - 1, 0) level
        (horizontalChoiceSteps_valid w.1) (by omega) hend with
      ⟨k, hk, heq⟩
    exact (firstHitSplit_none_endpoint_fst_ne hnone k hk) heq
  exact ⟨⟨w.1, w.2.1, hbelow⟩, fun hne => hne hnone⟩

end
end StatMech.Universality
