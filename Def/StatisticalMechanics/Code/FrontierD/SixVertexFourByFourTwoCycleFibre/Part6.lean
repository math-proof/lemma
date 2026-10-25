/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part5


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourAuditedParamHorizontalRowsFirst
    (p : SixVertexFourByFourAuditedHorizontalParameters) :
    Fin 4 -> SixVertexRow 4 := ![
  sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask
    (sixVertexFourByFourAllowedHorizontalIndex
      (sixVertexFourByFourAuditedRowZero p.1).1)),
  sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask
    (sixVertexFourByFourAllowedHorizontalIndex
      (sixVertexFourByFourAuditedRowMiddle p.2.1).1)),
  sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask
    (sixVertexFourByFourAllowedHorizontalIndex
      (sixVertexFourByFourAuditedRowMiddle p.2.2.1).1)),
  sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask
    (sixVertexFourByFourAllowedHorizontalIndex
      (sixVertexFourByFourAuditedRowLast p.2.2.2).1))
]

def sixVertexFourByFourAuditedParamHorizontalRowsSecond
    (p : SixVertexFourByFourAuditedHorizontalParameters) :
    Fin 4 -> SixVertexRow 4 := ![
  sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask
    (sixVertexFourByFourAllowedHorizontalIndex
      (sixVertexFourByFourAuditedRowZero p.1).2)),
  sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask
    (sixVertexFourByFourAllowedHorizontalIndex
      (sixVertexFourByFourAuditedRowMiddle p.2.1).2)),
  sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask
    (sixVertexFourByFourAllowedHorizontalIndex
      (sixVertexFourByFourAuditedRowMiddle p.2.2.1).2)),
  sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask
    (sixVertexFourByFourAllowedHorizontalIndex
      (sixVertexFourByFourAuditedRowLast p.2.2.2).2))
]

end
end StatMech.FrontierD
