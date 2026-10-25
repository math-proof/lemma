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
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareInteriorRadialFiniteRectanglePlacement

variable {n width height : Nat} {hn : 0 < n}


noncomputable def singleton
    (e : FKIsingSquareInteriorRadialCell n) :
    FKIsingSquareInteriorRadialFiniteRectanglePlacement n hn 1 1 where
  horizontal i j :=
    if j = 0 then fkIsingSquareInteriorRadialCellIncidence n hn e .south
    else fkIsingSquareInteriorRadialCellIncidence n hn e .east
  vertical i j :=
    if i = 0 then fkIsingSquareInteriorRadialCellIncidence n hn e .west
    else fkIsingSquareInteriorRadialCellIncidence n hn e .north
  cell _ _ := e
  west i _ := by simp [i.eq_zero]
  east _ j := by simp [j.eq_zero]
  south _ j := by simp [j.eq_zero]
  north i _ := by simp [i.eq_zero]

def horizontalIncrement
    (P : FKIsingSquareInteriorRadialFiniteRectanglePlacement
      n hn width height) : Nat → Nat → Real :=
  fun i j ↦ fkIsingSquareInteriorRadialIncrement n hn (P.horizontal i j)

def verticalIncrement
    (P : FKIsingSquareInteriorRadialFiniteRectanglePlacement
      n hn width height) : Nat → Nat → Real :=
  fun i j ↦ fkIsingSquareInteriorRadialIncrement n hn (P.vertical i j)

end FKIsingSquareInteriorRadialFiniteRectanglePlacement
end
end StatMech.Universality
