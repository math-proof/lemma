/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFourthMoment
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part2


namespace StatMech.Universality

open Finset

noncomputable section

def EndpointBoundaryStringFamily (m K : Nat) :=
  {ys : List Bool // ys.length = K ∧
    isingLineBoxBoundary (2 * m)
      (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ ys)}

end
end StatMech.Universality
