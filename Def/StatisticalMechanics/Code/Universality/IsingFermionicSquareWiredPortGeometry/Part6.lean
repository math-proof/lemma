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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part5


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

def fkIsingSquareWiredPortOctagonOffset : Fin 8 → Int × Int :=
  ![(1, -2), (2, -1), (1, 0), (0, 1),
    (-1, 2), (-2, 1), (-1, 0), (0, -1)]


def fkIsingSquareWiredPortSlot :
    FKIsingSquareDirection → FKIsingSquareCornerTurn → Fin 8
  | .east, .clockwise => 1
  | .east, .counterclockwise => 2
  | .north, .clockwise => 3
  | .north, .counterclockwise => 4
  | .west, .clockwise => 5
  | .west, .counterclockwise => 6
  | .south, .clockwise => 7
  | .south, .counterclockwise => 0


def fkIsingSquareWiredPortSlotDirection : Fin 8 → FKIsingSquareDirection :=
  ![.south, .east, .east, .north, .north, .west, .west, .south]


def fkIsingSquareWiredPortSlotTurn : Fin 8 → FKIsingSquareCornerTurn :=
  ![.counterclockwise, .clockwise, .counterclockwise, .clockwise,
    .counterclockwise, .clockwise, .counterclockwise, .clockwise]

end
end StatMech.Universality
