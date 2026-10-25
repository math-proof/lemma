/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part10


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourColumnMask : Fin 4 -> Nat := ![
  0x1111, 0x2222, 0x4444, 0x8888
]

def sixVertexFourByFourToggleVerticalColumn
    (column : Fin 4) (omega : SixVertexArrows sixVertexFourByFourTorus) :
    SixVertexArrows sixVertexFourByFourTorus where
  horizontal := omega.horizontal
  vertical v := if v.1 = column then !omega.vertical v else omega.vertical v

end
end StatMech.FrontierD
