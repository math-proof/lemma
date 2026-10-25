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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part15


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable def mirrorFailureAtAlignedOrResidualCover
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level ->
      Sum (IsingSourceFailureOutputAtFamily R t p q level)
        (Sum (IsingMirrorFailureOutputAtFamily R t p p' q level)
          (IsingMirrorOnlySourceOutputAtFamily R t p p' q level)) := fun w =>
  Classical.choose
    (exists_mirrorFailureAtAlignedOrResidualCover R t p p' q level w)

end
end StatMech.Universality
