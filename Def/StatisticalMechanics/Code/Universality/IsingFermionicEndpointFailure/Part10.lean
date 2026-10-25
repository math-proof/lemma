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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part8


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def alignedFailureOutputValue
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Sum (IsingSourceFailureOutputAtFamily R t p q level)
      (IsingMirrorFailureOutputAtFamily R t p p' q level) ->
      IsingLeapfrogChoiceStringFamily t
  | Sum.inl w => w.1.1
  | Sum.inr w => w.1.1

end
end StatMech.Universality
