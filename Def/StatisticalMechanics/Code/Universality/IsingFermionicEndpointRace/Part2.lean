/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFourthMoment
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace


namespace StatMech.Universality

open Finset

noncomputable section

def endpointFirstBoundaryExtend (m K : Nat) :
    EndpointFirstBoundaryExtension m K →
      {ys : List Bool // ys.length = K ∧
        isingLineBoxBoundary (2 * m)
          (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ ys)} := fun w =>
  ⟨w.2.1.1 ++ w.2.2.1, by
      rw [List.length_append, w.2.1.2.1, w.2.2.2]
      omega,
    by
      rw [isingLineChoiceRun_append_endpointRace]
      rw [isingLineChoiceRun_of_boundary_endpointRace
        (2 * m) _ w.2.1.2.2.1]
      exact w.2.1.2.2.1⟩

end
end StatMech.Universality
