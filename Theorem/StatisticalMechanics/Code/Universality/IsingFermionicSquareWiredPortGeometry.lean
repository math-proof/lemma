/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry


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
