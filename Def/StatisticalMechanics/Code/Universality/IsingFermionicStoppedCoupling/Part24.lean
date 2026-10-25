/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part19


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def sourceFailureReflectX
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Nat)
    (hlevelR : level ≤ R) :
    IsingStoppedCouplingSourceFailureFamily R t p (level : Int) →
      IsingStoppedCouplingSourceFailureFamily R t
        (isingLeapfrogBoxReflectX R p) ((R - level : Nat) : Int) := fun w => by
  let w' : IsingLeapfrogChoiceStringFamily t :=
    ⟨isingLeapfrogFlipXChoices w.1.1, by
      simp [isingLeapfrogFlipXChoices, w.1.2]⟩
  refine ⟨w', ?_⟩
  rcases w.2 with ⟨split, hsplit, hnot⟩
  let split' := globalReflectHitSplit R split
  unfold IsingStoppedCouplingSourceFailure
  have hlevel : ((R - level : Nat) : Int) = (R : Int) - level := by
    rw [Nat.cast_sub hlevelR]
  rw [boxInt_reflectX, hlevel]
  refine ⟨split', ?_, ?_⟩
  · have hpath : isingLeapfrogChoiceSteps w'.1 = split'.steps := by
      dsimp [w']
      rw [choiceSteps_flipX, globalReflectHitSplit_steps,
        firstHitSplit_steps hsplit]
    rw [hpath]
    exact firstHitSplit_eq_some split'
      (globalReflectHitSplit_firstHit R split (firstHitSplit_firstHit hsplit))
  · have hlen : split'.before.length = split.before.length := by
      simp [split', globalReflectHitSplit]
    rw [hlen]
    intro hvalid
    apply hnot
    apply (choiceExecValid_reflectX_iff R p (w.1.1.take split.before.length)).mp
    simpa [w', isingLeapfrogFlipXChoices, List.map_take] using hvalid

end
end StatMech.Universality
