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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part5


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareInteriorRadialFiniteRectanglePlacement

variable {n width height : Nat} {hn : 0 < n}


theorem increment_closed_on
    (P : FKIsingSquareInteriorRadialFiniteRectanglePlacement
      n hn width height) :
    IsingRectangleClosedOneFormOn P.horizontalIncrement P.verticalIncrement
      width height := by
  intro i hi j hj
  let ii : Fin width := ⟨i, hi⟩
  let jj : Fin height := ⟨j, hj⟩
  rw [show P.verticalIncrement i j =
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn (P.cell ii jj) .west) by
        exact congrArg _ (P.west ii jj),
    show P.horizontalIncrement i (j + 1) =
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn (P.cell ii jj) .east) by
        exact congrArg _ (P.east ii jj),
    show P.horizontalIncrement i j =
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn (P.cell ii jj) .south) by
        exact congrArg _ (P.south ii jj),
    show P.verticalIncrement (i + 1) j =
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn (P.cell ii jj) .north) by
        exact congrArg _ (P.north ii jj)]
  exact fkIsingSquareInteriorRadialCell_increment_closed n hn (P.cell ii jj)

end FKIsingSquareInteriorRadialFiniteRectanglePlacement
end
end StatMech.Universality
