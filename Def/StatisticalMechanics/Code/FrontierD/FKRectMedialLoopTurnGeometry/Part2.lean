/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedEdgeCenterClass
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurnWalk.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnGeometry.Part2


namespace StatMech.FrontierD

noncomputable section

def fkRectRefinedDartResidue (horizontal : Bool)
    (side : FKMedialSide) : ZMod 4 × ZMod 4 :=
  match horizontal, side with
  | true, .west => (1, 3)
  | true, .east => (3, 1)
  | true, .south => (1, 1)
  | true, .north => (3, 3)
  | false, .west => (3, 1)
  | false, .east => (1, 3)
  | false, .south => (3, 3)
  | false, .north => (1, 1)

end
end StatMech.FrontierD
