/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGenericIntegration.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareFullCoordinateOneFormOf
    (n : Nat) (hn : 0 < n)
    (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
    (hinc : forall C : FKIsingSquareInteriorRadialCell n,
      inc (fkIsingSquareInteriorRadialCellIncidence n hn C .west) +
          inc (fkIsingSquareInteriorRadialCellIncidence n hn C .east) =
        inc (fkIsingSquareInteriorRadialCellIncidence n hn C .south) +
          inc (fkIsingSquareInteriorRadialCellIncidence n hn C .north)) :
    FKIsingSquareFullCoordinateOneForm n where
  horizontal := fkIsingSquareFullHorizontalIncrementOf n hn
    inc
  vertical := fkIsingSquareFullVerticalIncrementOf n hn
    inc
  closed := fkIsingSquareFull_increment_closed_of n hn inc hinc


noncomputable def fkIsingSquareBoundaryLayerCoordinateOneForm
    (n : Nat) (hn : 0 < n) : FKIsingSquareFullCoordinateOneForm n :=
  fkIsingSquareFullCoordinateOneFormOf n hn
    (fkIsingSquareBoundaryLayerRadialIncrement n hn)
    (fkIsingSquareBoundaryLayerRadialCell_increment_closed n hn)


end
end StatMech.Universality
