/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialRectangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidence.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalEnergy
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveFiniteIntegration
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareInteriorRadialRectanglePlacement

variable {n : Nat} {hn : 0 < n}

theorem increment_closed
    (P : FKIsingSquareInteriorRadialRectanglePlacement n hn) :
    IsingRectangleClosedOneForm P.horizontalIncrement P.verticalIncrement := by
  intro i j
  rw [show P.verticalIncrement i j =
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn (P.cell i j) .west) by
        exact congrArg _ (P.west i j),
    show P.horizontalIncrement i (j + 1) =
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn (P.cell i j) .east) by
        exact congrArg _ (P.east i j),
    show P.horizontalIncrement i j =
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn (P.cell i j) .south) by
        exact congrArg _ (P.south i j),
    show P.verticalIncrement (i + 1) j =
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn (P.cell i j) .north) by
        exact congrArg _ (P.north i j)]
  exact fkIsingSquareInteriorRadialCell_increment_closed n hn (P.cell i j)


end FKIsingSquareInteriorRadialRectanglePlacement
end
end StatMech.Universality
