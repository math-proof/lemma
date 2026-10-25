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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part20


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable def mirrorOnlyOrderedHorizontalCover
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hlevelR : level <= R) (hhalf : R <= 2 * level)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hq : isingLeapfrogBoxBoundary R q) :
    IsingMirrorOnlySourceOutputAtFamily R t p p' q (level : Int) ->
      IsingOrderedFarHorizontalEndpointFamily (R - level) R t
        ⟨2 * level - R, by omega⟩ q.1 (p.2.1 : Int) (q.2.1 : Int) := fun w =>
  Classical.choose ((Classical.choose_spec
    (exists_mirrorOnlyOrderedCover R level t p p' q
      hlevelR hstart hmirror hq w)).2 hhalf)

end
end StatMech.Universality
