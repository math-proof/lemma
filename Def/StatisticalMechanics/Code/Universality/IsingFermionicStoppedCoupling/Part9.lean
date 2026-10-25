/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part3


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def IsingLineFirstBoundaryExtension (m K : Nat) :=
  Σ j : Fin (K + 1),
    IsingLineFirstBoundaryFamily m j ×
      {tail : List Bool // tail.length = K - j}


def lineFirstBoundaryExtend (m K : Nat) :
    IsingLineFirstBoundaryExtension m K →
      {ys : List Bool // ys.length = K ∧
        isingLineBoxBoundary (2 * m)
          (isingLineChoiceRun (2 * m) ⟨m, by omega⟩ ys)} := fun w =>
  ⟨w.2.1.1 ++ w.2.2.1, by
      rw [List.length_append, w.2.1.2.1, w.2.2.2]
      omega,
    by
      rw [isingLineChoiceRun_append]
      rw [isingLineChoiceRun_of_boundary (2 * m) _ w.2.1.2.2.1]
      exact w.2.1.2.2.1⟩

end
end StatMech.Universality
