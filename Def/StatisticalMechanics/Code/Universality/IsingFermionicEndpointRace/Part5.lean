/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFourthMoment
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part3


namespace StatMech.Universality

open Finset

noncomputable section

def IsingEndpointTransverseRaceWitnessFamily
    (m t : Nat) (level target : Int) :=
  Σ j : Fin (t + 1),
    IsingHorizontalNoHitEndpointFamily j level target ×
      IsingLineFirstBoundaryFamily m j ×
        {tail : List (Bool × Bool) // tail.length = t - j}

end
end StatMech.Universality
