/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part20


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def mirrorFailureToSource
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint level (isingLeapfrogBoxInt p)) :
    IsingStoppedCouplingMirrorFailureFamily R t p p' level →
      IsingStoppedCouplingSourceFailureFamily R t p' level := fun w => by
  let w' := isingLeapfrogCouplingChoiceTransform t
    (isingLeapfrogBoxInt p) level w.1
  refine ⟨w', ?_⟩
  rcases w.2 with ⟨split, hsplit, hnot⟩
  unfold IsingStoppedCouplingSourceFailure
  rw [hmirror]
  refine ⟨split.reflectPrefix, ?_, ?_⟩
  · have hpath : isingLeapfrogChoiceSteps w'.1 = split.reflectPrefix.steps := by
      dsimp [w']
      have hsteps : isingLeapfrogChoiceSteps
          (isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p)
            level w.1).1 =
          isingDiagonalWalkCouplingReflectSteps (isingLeapfrogBoxInt p) level
            (isingLeapfrogChoiceSteps w.1.1) := by
        exact choiceSteps_encodeSteps_of_valid _
          (couplingReflectSteps_valid (isingLeapfrogBoxInt p) level _
            (isingLeapfrogChoiceSteps_valid w.1.1))
      rw [hsteps]
      unfold isingDiagonalWalkCouplingReflectSteps
      rw [hsplit]
    rw [hpath]
    exact firstHitSplit_eq_some split.reflectPrefix
      (reflectPrefix_firstHit split (firstHitSplit_firstHit hsplit))
  · simpa [w', reflectPrefix] using hnot

end
end StatMech.Universality
