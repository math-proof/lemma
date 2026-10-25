/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise.Part3
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot.Part2


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def noHitEndpointToLocalNoHit
    (t : Nat) (level target : Int) :
    IsingHorizontalNoHitEndpointFamily t level target →
      LocalHorizontalNoHitFiber t (level - 1) level target := fun w => by
  refine ⟨⟨w.1.1, w.1.2.1, w.2⟩, ?_⟩
  change ¬ isingDiagonalWalkFirstHitSplit? (level - 1, 0) level
    (localHorizontalSteps w.1.1) ≠ none
  intro hne
  let split := (isingDiagonalWalkFirstHitSplit? (level - 1, 0) level
    (localHorizontalSteps w.1.1)).get (Option.ne_none_iff_isSome.mp hne)
  have hsplit : isingDiagonalWalkFirstHitSplit? (level - 1, 0) level
      (localHorizontalSteps w.1.1) = some split :=
    (Option.some_get (Option.ne_none_iff_isSome.mp hne)).symm
  have hk : split.before.length ≤ t := by
    have hlen := congrArg List.length (firstHitSplit_steps hsplit)
    simp [IsingDiagonalWalkHitSplit.steps, localHorizontalSteps, w.1.2.1] at hlen
    omega
  apply w.1.2.2 split.before.length hk
  calc
    lineFreeEndpoint (level - 1) (w.1.1.take split.before.length) =
        (isingDiagonalWalkEndpoint (level - 1, 0)
          (localHorizontalSteps (w.1.1.take split.before.length))).1 :=
      lineFreeEndpoint_localHorizontalSteps _ _
    _ = (isingDiagonalWalkEndpoint (level - 1, 0)
          ((localHorizontalSteps w.1.1).take split.before.length)).1 := by
      simp [localHorizontalSteps, List.map_take]
    _ = (isingDiagonalWalkEndpoint (level - 1, 0) split.before).1 := by
      rw [← firstHitSplit_steps hsplit]
      simp [IsingDiagonalWalkHitSplit.steps]
    _ = level := split.hit

end
end StatMech.Universality
