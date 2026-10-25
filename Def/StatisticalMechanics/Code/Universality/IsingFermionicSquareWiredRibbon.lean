/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Theorem.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.FKTutte
open Equiv SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredDartSideColor : FKIsingMedialSide → Bool
  | .west | .east => false
  | .south | .north => true

def fkIsingSquareWiredTurnColor : FKIsingSquareCornerTurn → Bool
  | .counterclockwise => false
  | .clockwise => true


def fkIsingSquareWiredCarrierColor (n : Nat) :
    FKIsingSquareWiredCarrier n → Bool
  | .dart d => fkIsingSquareWiredDartSideColor d.2
  | .bond d => !fkIsingSquareWiredTurnColor
      (fkIsingSquareSideCorner d.2).2
  | .source => true
  | .terminal => false

end
end StatMech.Universality
