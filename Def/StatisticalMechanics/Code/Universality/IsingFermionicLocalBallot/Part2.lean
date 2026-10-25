/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise.Part3
import Abbrev.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def LocalHorizontalHitFiber
    (t : Nat) (start level target : Int) :=
  {w : LocalHorizontalFreeFiber t start target //
    isingDiagonalWalkFirstHitSplit? (start, 0) level
      (localHorizontalSteps w.1) ≠ none}

def LocalHorizontalNoHitFiber
    (t : Nat) (start level target : Int) :=
  {w : LocalHorizontalFreeFiber t start target //
    ¬ isingDiagonalWalkFirstHitSplit? (start, 0) level
      (localHorizontalSteps w.1) ≠ none}

end
end StatMech.Universality
