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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part26


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

@[simp] theorem fkIsingSquareWiredRingStepIndex_zero :
    fkIsingSquareWiredRingStepIndex 0 = 3 := rfl

@[simp] theorem fkIsingSquareWiredRingStepIndex_one :
    fkIsingSquareWiredRingStepIndex 1 = 1 := rfl

@[simp] theorem fkIsingSquareWiredRingStepIndex_two :
    fkIsingSquareWiredRingStepIndex 2 = 1 := rfl

@[simp] theorem fkIsingSquareWiredRingStepIndex_three :
    fkIsingSquareWiredRingStepIndex 3 = 1 := rfl

@[simp] theorem fkIsingSquareWiredRingStepIndex_four :
    fkIsingSquareWiredRingStepIndex 4 = 0 := rfl

@[simp] theorem fkIsingSquareWiredRingStepIndex_five :
    fkIsingSquareWiredRingStepIndex 5 = 2 := rfl

@[simp] theorem fkIsingSquareWiredRingStepIndex_six :
    fkIsingSquareWiredRingStepIndex 6 = 2 := rfl

@[simp] theorem fkIsingSquareWiredRingStepIndex_seven :
    fkIsingSquareWiredRingStepIndex 7 = 2 := rfl

end
end StatMech.Universality
