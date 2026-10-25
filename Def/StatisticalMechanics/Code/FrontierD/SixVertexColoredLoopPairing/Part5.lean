/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part7


namespace StatMech.FrontierD

noncomputable section

def fkMedialLocalSideMate
    (pairing : Bool) (side : FKMedialSide) : FKMedialSide :=
  match pairing, side with
  | false, .west => .north
  | false, .north => .west
  | false, .east => .south
  | false, .south => .east
  | true, .west => .south
  | true, .south => .west
  | true, .east => .north
  | true, .north => .east

end
end StatMech.FrontierD
