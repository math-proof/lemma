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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part6


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

@[simp] theorem fkIsingSquareWiredPortSlot_direction_turn (i : Fin 8) :
    fkIsingSquareWiredPortSlot
        (fkIsingSquareWiredPortSlotDirection i)
        (fkIsingSquareWiredPortSlotTurn i) = i := by
  fin_cases i <;> rfl

@[simp] theorem fkIsingSquareWiredPortSlotDirection_slot
    (d : FKIsingSquareDirection) (turn : FKIsingSquareCornerTurn) :
    fkIsingSquareWiredPortSlotDirection
        (fkIsingSquareWiredPortSlot d turn) = d := by
  cases d <;> cases turn <;> rfl

@[simp] theorem fkIsingSquareWiredPortSlotTurn_slot
    (d : FKIsingSquareDirection) (turn : FKIsingSquareCornerTurn) :
    fkIsingSquareWiredPortSlotTurn
        (fkIsingSquareWiredPortSlot d turn) = turn := by
  cases d <;> cases turn <;> rfl

@[simp] theorem fkIsingSquareWiredPortOctagonOffset_slot
    (d : FKIsingSquareDirection) (turn : FKIsingSquareCornerTurn) :
    fkIsingSquareWiredPortOctagonOffset
        (fkIsingSquareWiredPortSlot d turn) =
      fkIsingSquareWiredPortOffset d turn := by
  cases d <;> cases turn <;> rfl


theorem fkIsingSquareWiredPortOctagonOffset_succ_unitDiagonal (i : Fin 8) :
    ∃ a : Fin 4,
      fkIsingSquareWiredPortOctagonOffset (i + 1) =
        fkIsingSquareWiredPortOctagonOffset i +
          fkIsingSquareWiredUnitDiagonalStep a := by
  fin_cases i
  · exact ⟨3, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨2, by decide⟩


end
end StatMech.Universality
