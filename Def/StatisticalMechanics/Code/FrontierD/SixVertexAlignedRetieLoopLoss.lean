/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedRetieLoopLoss.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTransitionRetieExact.Part3


namespace StatMech.FrontierD

namespace FourByTwoAlignedRetieLoopLoss

def omega : SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoArrowsOfMasks 0x0f 0x00

def eta : SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoArrowsOfMasks 0x0f 0x33

def lowerPairing : FKMedialLoopPairing sixVertexFourByTwoTorus :=
  fun v => decide (v.2.val = 0)

def upperPairing : FKMedialLoopPairing sixVertexFourByTwoTorus :=
  fun v => decide (2 <= v.1.val) ^^ decide (v.2.val = 1)

def source : Bool -> FKMedialLoopPairing sixVertexFourByTwoTorus
  | false => lowerPairing
  | true => upperPairing

def first : sixVertexFourByTwoTorus.Vertex :=
  sixVertexFourByTwoVertex 0 0

def second : sixVertexFourByTwoTorus.Vertex :=
  sixVertexFourByTwoVertex 1 1

def retie (pairing : FKMedialLoopPairing sixVertexFourByTwoTorus) :
    FKMedialLoopPairing sixVertexFourByTwoTorus :=
  fkMedialTogglePairingAt
    (fkMedialTogglePairingAt pairing first) second

end FourByTwoAlignedRetieLoopLoss
end StatMech.FrontierD
