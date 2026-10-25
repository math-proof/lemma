/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSpinGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusGraphTransition.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusHomology.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationSpinGauge.Part5
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSpinGauge


namespace StatMech.FrontierA

open StatMech.Onsager


@[simp] theorem triangularTorusXMovement_target
    (L : Nat) (d : triangularTorusDart L) :
    (ons_dirStep L (triangularTorusXMovementDirection d.2) d.1).1 =
      (d.1 - triangularTorusDirectionStep L d.2).1 := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;>
    simp [triangularTorusXMovementDirection,
      triangularTorusDirectionStep, ons_dirStep] <;> ring

@[simp] theorem triangularTorusYMovement_target
    (L : Nat) (d : triangularTorusDart L) :
    (ons_dirStep L (triangularTorusYMovementDirection d.2) d.1).2 =
      (d.1 - triangularTorusDirectionStep L d.2).2 := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;>
    simp [triangularTorusYMovementDirection,
      triangularTorusDirectionStep, ons_dirStep] <;> ring


theorem triangularTorusDirectionPhase_eq_movement_zpow
    (L : Nat) (a b : Fin 2) (d : triangularTorusDart L) :
    triangularTorusDirectionPhase (ons_spinPhase L a)
        (ons_spinPhase L b) d.2 =
      ons_spinPhase L a ^
          (-ons_dirExponentX (triangularTorusXMovementDirection d.2)) *
        ons_spinPhase L b ^
          (-ons_dirExponentY (triangularTorusYMovementDirection d.2)) := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;>
    simp [triangularTorusDirectionPhase,
      triangularTorusXMovementDirection,
      triangularTorusYMovementDirection,
      ons_dirExponentX, ons_dirExponentY] <;> ring


end StatMech.FrontierA
