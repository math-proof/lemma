/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part2


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable def horizontalHitBelowToFirstHitBelow
    (t : Nat) (start level : Int) :
    HorizontalHitBelow t start level →
      HorizontalFirstHitBelow t start level := fun z => by
    let split := horizontalHitBelowSplit z
    have hsplit := horizontalHitBelowSplit_spec z
    let q := split.endpoint
    have hsteps := firstHitSplit_steps hsplit
    have hfirst := firstHitSplit_firstHit hsplit
    have hvalid : split.Valid := by
      unfold IsingDiagonalWalkHitSplit.Valid
      rw [hsteps]
      exact horizontalChoiceSteps_valid z.1.1
    have hlength : split.steps.length = t := by
      rw [hsteps, horizontalChoiceSteps_length]
      exact z.1.2.1
    have hbelow : q.1 < level := by
      change split.endpoint.1 < level
      rw [show split.endpoint.1 = lineFreeEndpoint start z.1.1 by
        unfold IsingDiagonalWalkHitSplit.endpoint
        rw [hsteps]
        exact (lineFreeEndpoint_horizontalChoiceSteps z.1.1 start).symm]
      exact z.1.2.2
    exact ⟨split, hfirst, hvalid, hlength, hbelow, by
        intro d hd
        rw [hsteps] at hd
        exact horizontalChoiceSteps_vertical z.1.1 d hd⟩

noncomputable def horizontalFirstHitBelowToHitBelow
    (t : Nat) (start level : Int) :
    HorizontalFirstHitBelow t start level →
      HorizontalHitBelow t start level := fun z => by
    let split := z.1
    let bs := split.steps.map horizontalStepCode
    have hdecode : horizontalChoiceSteps bs = split.steps :=
      horizontalChoiceSteps_stepCodes_of_valid split.steps
        z.2.2.1 z.2.2.2.2.2
    have hlength : bs.length = t := by
      simpa [bs] using z.2.2.2.1
    have hbelow : lineFreeEndpoint start bs < level := by
      rw [lineFreeEndpoint_horizontalChoiceSteps, hdecode]
      exact z.2.2.2.2.1
    refine ⟨⟨bs, hlength, hbelow⟩, ?_⟩
    rw [hdecode, firstHitSplit_eq_some split z.2.1]
    exact Option.some_ne_none split

end
end StatMech.Universality
