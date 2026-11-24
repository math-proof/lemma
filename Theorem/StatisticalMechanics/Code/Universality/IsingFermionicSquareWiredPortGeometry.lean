module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry


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

theorem fkIsingSquareWiredUnitDiagonalStep_injective :
    Function.Injective fkIsingSquareWiredUnitDiagonalStep := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [fkIsingSquareWiredUnitDiagonalStep, Prod.ext_iff] at h ⊢

theorem fkIsingSquareWiredUnitDiagonalStep_add_reverse (a : Fin 4) :
    fkIsingSquareWiredUnitDiagonalStep a +
      fkIsingSquareWiredUnitDiagonalStep
        (fkIsingSquareWiredUnitDiagonalReverse a) = 0 := by
  fin_cases a <;> decide


end
end StatMech.Universality
