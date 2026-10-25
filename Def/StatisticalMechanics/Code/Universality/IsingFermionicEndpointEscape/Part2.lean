/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointEscape.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def IsingLineFarFirstBoundaryFamily (m k : Nat) :=
  {ys : List Bool // ys.length = k ∧
    isingLineChoiceRun m ⟨m - 1, by omega⟩ ys = ⟨0, by omega⟩ ∧
    ∀ j, j < k → ¬ isingLineBoxBoundary m
      (isingLineChoiceRun m ⟨m - 1, by omega⟩ (ys.take j))}

end
end StatMech.Universality
