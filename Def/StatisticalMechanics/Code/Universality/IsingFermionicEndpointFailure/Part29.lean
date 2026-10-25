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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part25


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable def choiceNoHitAtOutputCover
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    IsingLeapfrogChoiceNoHitAtFamily R t p p' q level ->
      Sum (IsingSourceChoiceNoHitOutputAtFamily R t p q level)
        (IsingMirrorChoiceNoHitOutputAtFamily R t p p' q level) := fun w => by
  classical
  by_cases hs : isingLeapfrogChoiceRun R p w.1.1 = q
  · exact Sum.inl ⟨w.1, w.2.1, hs⟩
  · exact Sum.inr ⟨w.1, w.2.1, w.2.2.resolve_left hs⟩

def choiceNoHitAtOutputCoverValue
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Sum (IsingSourceChoiceNoHitOutputAtFamily R t p q level)
        (IsingMirrorChoiceNoHitOutputAtFamily R t p p' q level) ->
      IsingLeapfrogChoiceStringFamily t :=
  Sum.elim (fun w => w.1) (fun w => w.1)

end
end StatMech.Universality
