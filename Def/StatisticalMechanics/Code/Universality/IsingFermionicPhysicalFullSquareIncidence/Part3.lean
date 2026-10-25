/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidenceFiber
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGhost.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def FKIsingSquareFullRadiallyAdjacent
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (c : FKIsingSquareFullFaceNode n) : Prop :=
  fkIsingSquareFullFaceCoordinate n c =
      ((fkIsingSquareFullVertexCoordinate n x).1 + 1,
        (fkIsingSquareFullVertexCoordinate n x).2) ∨
    fkIsingSquareFullFaceCoordinate n c =
      ((fkIsingSquareFullVertexCoordinate n x).1,
        (fkIsingSquareFullVertexCoordinate n x).2 + 1) ∨
    fkIsingSquareFullFaceCoordinate n c =
      ((fkIsingSquareFullVertexCoordinate n x).1 - 1,
        (fkIsingSquareFullVertexCoordinate n x).2) ∨
    fkIsingSquareFullFaceCoordinate n c =
      ((fkIsingSquareFullVertexCoordinate n x).1,
        (fkIsingSquareFullVertexCoordinate n x).2 - 1)

noncomputable def fkIsingSquareFullIncidenceOfAdjacent
    (n : Nat) (hn : 0 < n)
    (x : FKIsingSquareFullVertexNode n)
    (c : FKIsingSquareFullFaceNode n)
    (h : FKIsingSquareFullRadiallyAdjacent n x c) :
    FKIsingSquareInteriorRadialIncidence n hn :=
  Classical.choose
    (fkIsingSquareFull_exists_incidence_of_radiallyAdjacent n hn x c h)

end
end StatMech.Universality
