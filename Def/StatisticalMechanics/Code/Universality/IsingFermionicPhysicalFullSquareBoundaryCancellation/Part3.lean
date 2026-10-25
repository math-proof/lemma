/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryGeometry
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part2


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquarePerimeterMarkedCut (n : Nat)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) : Prop :=
  (side = .bottom ∧ k.1 = 0) ∨
    (side = .top ∧ k.1 + 1 = 2 * n)


def FKIsingSquarePerimeterCancellationAt (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) : Prop :=
  ¬ fkIsingSquarePerimeterMarkedCut n side k ∧
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
      (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquarePerimeterCancelledSide side)) = 0


def FKIsingSquarePerimeterCancellation (n : Nat) (hn : 0 < n) : Prop :=
  ∀ side k, ¬ fkIsingSquarePerimeterMarkedCut n side k →
    FKIsingSquarePerimeterCancellationAt n hn side k


end
end StatMech.Universality
