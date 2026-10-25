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
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part2


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def mirrorFailureOutputReflectX
    (R t level : Nat) (p p' q : IsingLeapfrogBox R)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level <= R) :
    IsingMirrorFailureOutputAtFamily R t p p' q (level : Int) ->
      IsingSourceFailureOutputAtFamily R t
        (isingLeapfrogBoxReflectX R p') (isingLeapfrogBoxReflectX R q)
        ((R - level : Nat) : Int) := fun w => by
  refine ⟨mirrorFailureReflectX R t level p p' hmirror hlevelR w.1, ?_⟩
  change isingLeapfrogChoiceRun R (isingLeapfrogBoxReflectX R p')
      (isingLeapfrogFlipXChoices
        (isingLeapfrogCouplingChoiceTransform t
          (isingLeapfrogBoxInt p) (level : Int) w.1.1).1) =
    isingLeapfrogBoxReflectX R q
  rw [choiceRun_reflectX, w.2]

end
end StatMech.Universality
