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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part2


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable def sourceEndpointRaceTarget
    (R t rho : Nat) (p q : IsingLeapfrogBox R)
    (j : Fin (t + 1)) (pref : IsingLineFirstBoundaryFamily rho j)
    (tail : IsingEndpointRaceTail t j) : Int :=
  let ys := pref.1 ++ tail.1.map Prod.snd
  let stop := firstVerticalBoundaryTimeEndpointFailure
    R (isingLeapfrogBoxInt p).2 ys
  (isingLeapfrogBoxInt q).1 -
    lineFreeEndpoint 0 ((tail.1.map Prod.fst).take (stop - (j : Nat)))

end
end StatMech.Universality
