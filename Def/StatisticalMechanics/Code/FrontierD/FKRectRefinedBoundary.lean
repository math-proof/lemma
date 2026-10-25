/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialBoundaryWalk.Part2


namespace StatMech.FrontierD

noncomputable section

def fkRectRefinedSideOffset : FKMedialSide → Int × Int
  | .west => (-1, -1)
  | .east => (1, 1)
  | .south => (-1, 1)
  | .north => (1, -1)


def fkRectRefinedDartPoint (c : Int × Int) (side : FKMedialSide) :
    Int × Int :=
  (c.1 + (fkRectRefinedSideOffset side).1,
    c.2 + (fkRectRefinedSideOffset side).2)


def fkRectRefinedBondCenter (c : Int × Int) (side : FKMedialSide) :
    Int × Int :=
  (c.1 + 2 * (fkRectRefinedSideOffset side).1,
    c.2 + 2 * (fkRectRefinedSideOffset side).2)


def fkRectMedialLocalMateSide (pairing : Bool) :
    FKMedialSide → FKMedialSide
  | .west => if pairing then .south else .north
  | .east => if pairing then .north else .south
  | .south => if pairing then .west else .east
  | .north => if pairing then .east else .west

end
end StatMech.FrontierD
