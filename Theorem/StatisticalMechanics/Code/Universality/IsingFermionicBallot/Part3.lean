/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part6


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem horizontalHitBelowToFirstHitBelow_injective
    (t : Nat) (start level : Int) :
    Function.Injective
      (horizontalHitBelowToFirstHitBelow t start level) := by
  intro a b h
  have hsplits : horizontalHitBelowSplit a = horizontalHitBelowSplit b :=
    congrArg (fun z : HorizontalFirstHitBelow t start level => z.1) h
  have ha := firstHitSplit_steps (horizontalHitBelowSplit_spec a)
  have hb := firstHitSplit_steps (horizontalHitBelowSplit_spec b)
  have hpaths : horizontalChoiceSteps a.1.1 =
      horizontalChoiceSteps b.1.1 := by
    rw [← ha, ← hb, hsplits]
  have hbits := congrArg (List.map horizontalStepCode) hpaths
  rw [horizontalStepCodes_choiceSteps,
    horizontalStepCodes_choiceSteps] at hbits
  exact Subtype.ext (Subtype.ext hbits)

theorem horizontalFirstHitBelowToHitBelow_injective
    (t : Nat) (start level : Int) :
    Function.Injective
      (horizontalFirstHitBelowToHitBelow t start level) := by
  intro a b h
  apply Subtype.ext
  have hbits : a.1.steps.map horizontalStepCode =
      b.1.steps.map horizontalStepCode := congrArg
    (fun z : HorizontalHitBelow t start level => z.1.1) h
  have ha := horizontalChoiceSteps_stepCodes_of_valid a.1.steps
    a.2.2.1 a.2.2.2.2.2
  have hb := horizontalChoiceSteps_stepCodes_of_valid b.1.steps
    b.2.2.1 b.2.2.2.2.2
  apply Option.some.inj
  rw [← firstHitSplit_eq_some a.1 a.2.1,
    ← firstHitSplit_eq_some b.1 b.2.1, ← ha, ← hb, hbits]

end
end StatMech.Universality
