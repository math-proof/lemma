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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part9


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable def sourceFailureAtAlignedCover_of_rightHalf
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level < R) (hhalf : R <= 2 * level) :
    IsingStoppedCouplingSourceFailureAtFamily R t p p' q (level : Int) ->
      Sum (IsingSourceFailureOutputAtFamily R t p q (level : Int))
        (IsingMirrorFailureOutputAtFamily R t p p' q (level : Int)) := fun w =>
  Classical.choose (exists_sourceFailureAtAlignedCover_of_rightHalf R level t
    p p' q hstart hmirror hlevelR hhalf w)

end
end StatMech.Universality
