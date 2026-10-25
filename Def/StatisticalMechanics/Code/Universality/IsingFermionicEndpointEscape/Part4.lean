/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointEscape.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part2


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def farFirstBoundaryExtend (m K : Nat) :
    FarFirstBoundaryExtension m K →
      IsingLineChoicePathFamily m K ⟨m - 1, by omega⟩ ⟨0, by omega⟩ :=
  fun w => ⟨w.2.1.1 ++ w.2.2.1, by
      rw [List.length_append, w.2.1.2.1, w.2.2.2]
      omega,
    by
      rw [isingLineChoiceRun_append_endpointEscape, w.2.1.2.2.1]
      exact isingLineChoiceRun_boundary_endpointEscape m ⟨0, by omega⟩
        (by simp [isingLineBoxBoundary]) _⟩

end
end StatMech.Universality
