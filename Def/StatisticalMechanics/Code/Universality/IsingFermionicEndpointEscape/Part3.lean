/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointEscape.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def FarFirstBoundaryExtension (m K : Nat) :=
  Σ j : Fin (K + 1),
    IsingLineFarFirstBoundaryFamily m j ×
      {tail : List Bool // tail.length = K - j}

end
end StatMech.Universality
