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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part4


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable def sourceFailureOutputTransverseCover
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 \/ q.2.1 = R) :
    IsingSourceFailureOutputAtFamily R t p q (level : Int) ->
      IsingTailDependentEndpointRaceFamily rho t (level : Int)
        (sourceEndpointRaceTarget R t rho p q) := fun w =>
  Classical.choose (exists_sourceFailureOutputTransverseCover R level rho t
    p q hstart hρ hbottom htop hqVertical w)

end
end StatMech.Universality
