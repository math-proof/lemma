module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCappedTent
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerGreen.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem fullVertexGhostRate_split
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    isingFermionicGhostRate (fullVertexRightGhostMultiplicity n) x +
        isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) x =
      isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x := by
  unfold isingFermionicGhostRate fullVertexRightGhostMultiplicity
    fullVertexVerticalGhostMultiplicity
    fkIsingSquareFullVertexGhostMultiplicity
  push_cast
  ring


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
