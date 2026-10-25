/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointEscape.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part3


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def IsingEndpointFarEscapeWitnessFamily
    (m t : Nat) (start target : Int) :=
  Σ j : Fin (t + 1),
    IsingLineFarFirstBoundaryFamily m j ×
      VerticalChoicePathFamily j start target ×
        {tail : List (Bool × Bool) // tail.length = t - j}

end
end StatMech.Universality
