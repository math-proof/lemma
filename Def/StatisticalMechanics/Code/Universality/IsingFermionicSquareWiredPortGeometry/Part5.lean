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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

def fkIsingSquareWiredPortOffset :
    FKIsingSquareDirection → FKIsingSquareCornerTurn → Int × Int
  | .east, .counterclockwise => (1, 0)
  | .east, .clockwise => (2, -1)
  | .north, .counterclockwise => (-1, 2)
  | .north, .clockwise => (0, 1)
  | .west, .counterclockwise => (-1, 0)
  | .west, .clockwise => (-2, 1)
  | .south, .counterclockwise => (1, -2)
  | .south, .clockwise => (0, -1)


end
end StatMech.Universality
