/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTailEndpointRace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace


namespace StatMech.Universality

open Finset

noncomputable section

noncomputable instance isingTailDependentEndpointRaceFamily_finite
    (m t : Nat) (level : Int)
    (target : (j : Fin (t + 1)) ->
      IsingLineFirstBoundaryFamily m j -> IsingEndpointRaceTail t j -> Int) :
    Finite (IsingTailDependentEndpointRaceFamily m t level target) := by
  letI (j : Fin (t + 1)) : Fintype (IsingLineFirstBoundaryFamily m j) :=
    Fintype.ofFinite _
  letI (j : Fin (t + 1)) : Fintype (IsingEndpointRaceTail t j) :=
    (List.finite_length_eq (Bool × Bool) (t - j)).fintype
  letI (j : Fin (t + 1))
      (pref : IsingLineFirstBoundaryFamily m j)
      (tail : IsingEndpointRaceTail t j) :
      Fintype (IsingHorizontalNoHitEndpointFamily
        j level (target j pref tail)) :=
    Fintype.ofFinite _
  unfold IsingTailDependentEndpointRaceFamily
  infer_instance


end
end StatMech.Universality
