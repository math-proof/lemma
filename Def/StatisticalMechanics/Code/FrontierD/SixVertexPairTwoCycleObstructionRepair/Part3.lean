/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionMatchingNoGo.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoArrowsOfMasks
    (horizontalMask verticalMask : Nat) :
    SixVertexArrows sixVertexFourByTwoTorus where
  horizontal v := horizontalMask.testBit (v.2.val * 4 + v.1.val)
  vertical v := verticalMask.testBit (v.2.val * 4 + v.1.val)

def sixVertexFourByTwoExceptionalSourceFirst (i : Fin 4) :
    SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoArrowsOfMasks
    (if i.val % 2 = 0 then 0x00 else 0xff) 0x00

def sixVertexFourByTwoExceptionalSourceSecond (i : Fin 4) :
    SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoArrowsOfMasks
    (if i.val < 2 then 0x5a else 0xa5)
    (if i.val < 2 then 0xa5 else 0x5a)

def sixVertexFourByTwoExceptionalTargetFirst (i : Fin 4) :
    SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoArrowsOfMasks
    (if i.val = 0 then 0x1e else if i.val = 1 then 0xd2
      else if i.val = 2 then 0x2d else 0xe1)
    (if i.val = 0 then 0x21 else if i.val = 1 then 0x24
      else if i.val = 2 then 0x42 else 0x12)

def sixVertexFourByTwoExceptionalTargetSecond (i : Fin 4) :
    SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoArrowsOfMasks
    (if i.val = 0 then 0x4b else if i.val = 1 then 0x78
      else if i.val = 2 then 0x87 else 0xb4)
    (if i.val = 0 then 0x84 else if i.val = 1 then 0x81
      else if i.val = 2 then 0x18 else 0x48)

def sixVertexFourByTwoExceptionalCycleSign (i : Fin 4) : Bool :=
  decide (i.val % 2 = 0)

end
end StatMech.FrontierD
