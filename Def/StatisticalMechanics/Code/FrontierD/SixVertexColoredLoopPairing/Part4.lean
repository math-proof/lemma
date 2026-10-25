/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part6


namespace StatMech.FrontierD

noncomputable section

def FKColoredLocalPairing.sideColor
    (cfg : FKColoredLocalPairing) (side : FKMedialSide) : Bool :=
  match cfg.pairing, side with
  | false, .west => cfg.west
  | false, .north => cfg.west
  | false, .east => cfg.east
  | false, .south => cfg.east
  | true, .west => cfg.west
  | true, .south => cfg.west
  | true, .east => cfg.east
  | true, .north => cfg.east

end
end StatMech.FrontierD
