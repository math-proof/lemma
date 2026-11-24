module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part4


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
