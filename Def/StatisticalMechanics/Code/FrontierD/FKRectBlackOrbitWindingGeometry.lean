/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part8


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

def fkRectMedialSideDirection : FKMedialSide → Fin 4
  | .west => 2
  | .east => 0
  | .south => 3
  | .north => 1


def fkRectMedialSidePotential : FKMedialSide → Int × Int
  | .west => (0, 0)
  | .east => (1, 1)
  | .south => (0, 1)
  | .north => (1, 0)


def fkRectBlackBoundaryMedialDirection
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialBlackDart T) : Fin 4 :=
  fkRectMedialSideDirection (fkMedialLocalMate pairing d.1).2


end
end StatMech.FrontierD
