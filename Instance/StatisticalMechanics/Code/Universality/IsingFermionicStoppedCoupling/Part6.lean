/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part13


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable instance isingTransverseRaceWitnessFamily_finite
    (m t : Nat) (level : Int) :
    Finite (IsingTransverseRaceWitnessFamily m t level) := by
  letI (j : Fin (t + 1)) :
      Fintype (IsingHorizontalNoHitFamily j (level - 1) level) :=
    Fintype.ofFinite _
  letI (j : Fin (t + 1)) :
      Fintype (IsingLineFirstBoundaryFamily m j) := Fintype.ofFinite _
  letI (j : Fin (t + 1)) :
      Fintype {tail : List (Bool × Bool) // tail.length = t - j} :=
    (List.finite_length_eq (Bool × Bool) (t - j)).fintype
  change Finite (Σ j : Fin (t + 1),
    IsingHorizontalNoHitFamily j (level - 1) level ×
      IsingLineFirstBoundaryFamily m j ×
        {tail : List (Bool × Bool) // tail.length = t - j})
  infer_instance

end
end StatMech.Universality
