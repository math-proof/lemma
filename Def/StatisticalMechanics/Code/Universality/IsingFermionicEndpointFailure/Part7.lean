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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part6


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable def sourceFailureOutputFarCover
    (R level t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hqLeft : q.1.1 = 0) :
    IsingSourceFailureOutputAtFamily R t p q (level : Int) →
      IsingEndpointFarEscapeWitnessFamily level t
        (isingLeapfrogBoxInt p).2 (isingLeapfrogBoxInt q).2 := fun w =>
  Classical.choose
    (exists_sourceFailureOutputFarCover R level t p q hstart hqLeft w)

end
end StatMech.Universality
