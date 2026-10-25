/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot.Part2


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

abbrev LocalHorizontalFreeFiber
    (t : Nat) (start target : Int) :=
  VerticalChoicePathFamily t start target

end
end StatMech.Universality
