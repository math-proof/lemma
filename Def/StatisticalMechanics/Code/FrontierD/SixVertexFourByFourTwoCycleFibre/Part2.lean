/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourAuditedSourceFirst :
    SixVertexArrows sixVertexFourByFourTorus :=
  sixVertexFourByFourArrowsOfMasks 0x003c 0x4441

def sixVertexFourByFourAuditedSourceSecond :
    SixVertexArrows sixVertexFourByFourTorus :=
  sixVertexFourByFourArrowsOfMasks 0x0609 0xdd77

def sixVertexFourByFourAuditedTargetFirst :
    SixVertexArrows sixVertexFourByFourTorus :=
  sixVertexFourByFourArrowsOfMasks 0x003c 0x6663

def sixVertexFourByFourAuditedTargetSecond :
    SixVertexArrows sixVertexFourByFourTorus :=
  sixVertexFourByFourArrowsOfMasks 0x0609 0x9933

end
end StatMech.FrontierD
