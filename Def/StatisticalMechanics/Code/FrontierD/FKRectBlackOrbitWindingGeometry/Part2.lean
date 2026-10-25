/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

def fkRectMedialRibbonPortOffset : FKMedialSide → Int × Int
  | .west => (2, 4)
  | .east => (6, 4)
  | .south => (4, 2)
  | .north => (4, 6)

def fkRectMedialOppositeSide : FKMedialSide → FKMedialSide
  | .west => .east
  | .east => .west
  | .south => .north
  | .north => .south


def fkRectMedialRibbonLocalBlock
    (pairing : Bool) (side : FKMedialSide) : List (Fin 4) :=
  match pairing, side with
  | false, .west => [1, 1, 0, 0]
  | false, .north => [2, 2, 3, 3]
  | false, .east => [3, 3, 2, 2]
  | false, .south => [0, 0, 1, 1]
  | true, .west => [3, 3, 0, 0]
  | true, .south => [2, 2, 1, 1]
  | true, .east => [1, 1, 2, 2]
  | true, .north => [0, 0, 3, 3]


def fkRectMedialRibbonBlock
    (pairing : Bool) (side : FKMedialSide) : List (Fin 4) :=
  fkRectMedialRibbonLocalBlock pairing side ++
    List.replicate 4 (fkRectMedialSideDirection
      (fkRectMedialLocalMateSide pairing side))

end
end StatMech.FrontierD
