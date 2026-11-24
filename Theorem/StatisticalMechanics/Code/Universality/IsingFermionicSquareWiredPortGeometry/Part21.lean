module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part22


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

@[simp] theorem fkIsingSquareWiredUnitDiagonalTangentCode_zero :
    fkIsingSquareWiredUnitDiagonalTangentCode 0 = 5 := rfl

@[simp] theorem fkIsingSquareWiredUnitDiagonalTangentCode_one :
    fkIsingSquareWiredUnitDiagonalTangentCode 1 = 3 := rfl

@[simp] theorem fkIsingSquareWiredUnitDiagonalTangentCode_two :
    fkIsingSquareWiredUnitDiagonalTangentCode 2 = 7 := rfl

@[simp] theorem fkIsingSquareWiredUnitDiagonalTangentCode_three :
    fkIsingSquareWiredUnitDiagonalTangentCode 3 = 1 := rfl


end
end StatMech.Universality
