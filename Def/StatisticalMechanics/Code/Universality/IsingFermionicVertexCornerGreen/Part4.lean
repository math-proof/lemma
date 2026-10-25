/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCappedTent
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerGreen.Part3


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def fullVertexRightGhostMultiplicity
    (n : Nat) (x : FKIsingSquareFullVertexNode n) : Nat :=
  if x.1 0 = (n : Int) then 1 else 0


def fullVertexVerticalGhostMultiplicity
    (n : Nat) (x : FKIsingSquareFullVertexNode n) : Nat :=
  (if x.1 1 = -(n : Int) then 1 else 0) +
    (if x.1 1 = (n : Int) then 1 else 0)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
