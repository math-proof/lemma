/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part10


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def IsingTransverseRaceWitnessFamily (m t : Nat) (level : Int) :=
  Σ j : Fin (t + 1),
    IsingHorizontalNoHitFamily j (level - 1) level ×
      IsingLineFirstBoundaryFamily m j ×
        {tail : List (Bool × Bool) // tail.length = t - j}

end
end StatMech.Universality
