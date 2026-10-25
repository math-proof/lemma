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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part17


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable def mirrorOnlyOrderedCover
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hlevelR : level <= R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q) :
    IsingMirrorOnlySourceOutputAtFamily R t p p' q (level : Int) ->
      IsingOrderedFarEndpointFamily (R - level) R t p.2 q.2
        (2 * (level : Int) - R) (q.1 : Int) := fun w =>
  Classical.choose
    (exists_mirrorOnlyOrderedCover R level t p p' q hlevelR hstart hmirror hq w)

end
end StatMech.Universality
