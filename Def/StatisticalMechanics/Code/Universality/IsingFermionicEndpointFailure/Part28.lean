/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicOrderedEndpointConvolution
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part24


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def mirrorNoHitOutputReflectX
    (R t level : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level <= R) :
    IsingMirrorChoiceNoHitOutputAtFamily R t p p' q (level : Int) ->
      IsingSourceChoiceNoHitOutputAtFamily R t
        (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
        ((R - level : Nat) : Int) := fun w => by
  have hp'x : (isingLeapfrogBoxInt p').1 = (level : Int) + 1 := by
    rw [hmirror]
    unfold reflectedEndpoint
    dsimp
    omega
  have hrefStart :
      (isingLeapfrogBoxInt (isingLeapfrogBoxReflectX R p')).1 + 1 =
        (R - level : Nat) := by
    rw [boxInt_reflectX]
    dsimp
    have hcast : ((R - level : Nat) : Int) = (R : Int) - level := by
      rw [Nat.cast_sub hlevelR]
    rw [hcast, hp'x]
    omega
  refine ⟨w.1, ?_, ?_⟩
  · intro k hk hnewHit
    apply w.2.1 k hk
    have htranslate := lineFreeEndpoint_translate
      ((w.1.1.map Prod.fst).take k) (isingLeapfrogBoxInt p).1
      (isingLeapfrogBoxInt (isingLeapfrogBoxReflectX R p')).1
    rw [hnewHit] at htranslate
    linarith
  · have hflip := couplingChoiceTransform_flipX_eq_of_noHit t
      (isingLeapfrogBoxInt p) (level : Int) w.1 w.2.1
    change isingLeapfrogChoiceRun R (isingLeapfrogBoxReflectX R p') w.1.1 =
      isingLeapfrogBoxReflectX R q
    rw [← hflip, choiceRun_reflectX, w.2.2]

end
end StatMech.Universality
