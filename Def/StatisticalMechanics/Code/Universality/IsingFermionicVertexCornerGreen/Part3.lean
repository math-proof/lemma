/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCappedTent
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerGreen.Part2


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def fullVertexColumnIndex
    (n : Nat) (x : FKIsingSquareFullVertexNode n) : Nat :=
  (x.1 0 + (n : Int)).toNat


def fullVertexRowIndex
    (n : Nat) (x : FKIsingSquareFullVertexNode n) : Nat :=
  (x.1 1 + (n : Int)).toNat

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
