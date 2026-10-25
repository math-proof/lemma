/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTailEndpointRace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part4
import Abbrev.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace


namespace StatMech.Universality

open Finset

noncomputable section

def IsingTailDependentEndpointRaceFamily
    (m t : Nat) (level : Int)
    (target : (j : Fin (t + 1)) ->
      IsingLineFirstBoundaryFamily m j -> IsingEndpointRaceTail t j -> Int) :=
  Σ j : Fin (t + 1),
    Σ pref : IsingLineFirstBoundaryFamily m j,
      Σ tail : IsingEndpointRaceTail t j,
        IsingHorizontalNoHitEndpointFamily j level (target j pref tail)

end
end StatMech.Universality
