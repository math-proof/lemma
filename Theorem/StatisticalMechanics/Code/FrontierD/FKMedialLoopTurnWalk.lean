/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurnWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurnWalk
open Equiv


namespace StatMech.FrontierD

open StatMech.Onsager

open FKMedialTurningFiber

variable {T : EvenTorus}

theorem two_mul_turnPow_strandDirection
    (pairing : FKMedialLoopPairing T)
    (d : FKMedialBlackDart T) :
    2 * ons_turnPow (fkMedialStrandDirection pairing d.1)
        (fkMedialStrandDirection pairing
          (fkMedialBlackBoundaryPerm pairing d).1) =
      -(turnSign (pairing d.1.1) (fkMedialVertexParity d.1.1) +
        turnSign (pairing (fkMedialBlackBoundaryPerm pairing d).1.1)
          (fkMedialVertexParity
            (fkMedialBlackBoundaryPerm pairing d).1.1)) := by
  rcases d with ⟨⟨⟨i, j⟩, side⟩, hd⟩
  cases hp : pairing (i, j) <;> cases side
  all_goals simp [fkMedialCheckerColor, fkMedialSideVertical] at hd
  all_goals simp only [fkMedialBlackBoundaryPerm_val, fkMedialLocalMate,
    fkMedialBondMate, hp, fkMedialStrandDirection]
  all_goals generalize hq : pairing _ = q
  all_goals cases q
  all_goals simp_all [ons_turnPow, turnSign]

end StatMech.FrontierD
