/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFourthMoment
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part5


namespace StatMech.Universality

open Finset

noncomputable section

noncomputable instance isingEndpointTransverseRaceWitnessFamily_finite
    (m t : Nat) (level target : Int) :
    Finite (IsingEndpointTransverseRaceWitnessFamily m t level target) := by
  letI (j : Fin (t + 1)) :
      Fintype (IsingHorizontalNoHitEndpointFamily j level target) :=
    Fintype.ofFinite _
  letI (j : Fin (t + 1)) :
      Fintype (IsingLineFirstBoundaryFamily m j) := Fintype.ofFinite _
  letI (j : Fin (t + 1)) :
      Fintype {tail : List (Bool × Bool) // tail.length = t - j} :=
    (List.finite_length_eq (Bool × Bool) (t - j)).fintype
  change Finite (Σ j : Fin (t + 1),
    IsingHorizontalNoHitEndpointFamily j level target ×
      IsingLineFirstBoundaryFamily m j ×
        {tail : List (Bool × Bool) // tail.length = t - j})
  infer_instance


end
end StatMech.Universality
