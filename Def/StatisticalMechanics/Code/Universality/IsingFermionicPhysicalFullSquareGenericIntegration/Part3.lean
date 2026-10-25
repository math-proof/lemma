/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGenericIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGenericIntegration.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullCoordinateOneForm

noncomputable def vertexPrimitive {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n)
    (x : FKIsingSquareFullVertexNode n) : Real :=
  A.coordinatePrimitive (fkIsingSquareFullVertexCoordinate n x) -
    A.coordinatePrimitive
      (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))

noncomputable def facePrimitive {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n)
    (c : FKIsingSquareFullFaceNode n) : Real :=
  A.coordinatePrimitive (fkIsingSquareFullFaceCoordinate n c) -
    A.coordinatePrimitive
      (fkIsingSquareFullVertexCoordinate n (fkIsingSquareMarkedB n))

end FKIsingSquareFullCoordinateOneForm


noncomputable def fkIsingSquareFullBoxCoordinateOneForm
    (n : Nat) (hn : 0 < n) : FKIsingSquareFullCoordinateOneForm n where
  horizontal := fkIsingSquareFullHorizontalIncrement n hn
  vertical := fkIsingSquareFullVerticalIncrement n hn
  closed := fkIsingSquareFull_increment_closed n hn

end
end StatMech.Universality
