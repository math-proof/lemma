/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCappedTent
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerGreen.Part4


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def vertexLeftColumnCap
    {n : Nat} (source x : FKIsingSquareFullVertexNode n) : Real :=
  isingNatCappedTent (fullVertexColumnIndex n source)
    (fullVertexColumnIndex n x)


noncomputable def vertexBottomRowRobinCap
    {n : Nat} (source x : FKIsingSquareFullVertexNode n) : Real :=
  isingNatCappedRobinTent isingFermionicGhostCoefficient
    (fullVertexRowIndex n source) (fullVertexRowIndex n x)


noncomputable def isingNatReverseCappedRobinTent
    (coefficient : Real) (top source i : Nat) : Real :=
  isingNatReverseCappedTent top source i + 1 / coefficient

noncomputable def vertexTopRowRobinCap
    (n : Nat) (source x : FKIsingSquareFullVertexNode n) : Real :=
  isingNatReverseCappedRobinTent isingFermionicGhostCoefficient (2 * n)
    (fullVertexRowIndex n source) (fullVertexRowIndex n x)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
