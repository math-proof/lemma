/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCappedTent
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerGreen


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def fullVertexDirectionIncrement
    (n : Nat) (F : FKIsingSquareFullVertexNode n -> Real)
    (x : FKIsingSquareFullVertexNode n) (d : FKIsingSquareDirection) : Real := by
  classical
  exact if h : fkIsingSquareDirectionAvailable n x d then
      F (fkIsingSquareNeighbor n x d h) - F x
    else 0


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
