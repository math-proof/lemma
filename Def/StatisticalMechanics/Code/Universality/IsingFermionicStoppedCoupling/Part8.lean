/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part7


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def IsingLineFirstBoundaryFamily (m k : Nat) :=
  {ys : List Bool // ys.length = k ∧
    isingLineBoxBoundary (2 * m)
      (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ ys) ∧
    ∀ j, j < k → ¬ isingLineBoxBoundary (2 * m)
      (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ (ys.take j))}

end
end StatMech.Universality
