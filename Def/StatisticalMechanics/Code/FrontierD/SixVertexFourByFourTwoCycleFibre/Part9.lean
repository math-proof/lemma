/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleFibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part8


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourAuditedParamSourceFirst
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam : Fin 4) :
    SixVertexArrows sixVertexFourByFourTorus :=
  { horizontal := fun v =>
      sixVertexFourByFourAuditedParamHorizontalRowsFirst p v.2 v.1
    vertical := fun v =>
      sixVertexFourByFourAuditedParamVerticalRowsFirst p seam v.2 v.1 }

def sixVertexFourByFourAuditedParamSourceSecond
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam : Fin 4) :
    SixVertexArrows sixVertexFourByFourTorus :=
  { horizontal := fun v =>
      sixVertexFourByFourAuditedParamHorizontalRowsSecond p v.2 v.1
    vertical := fun v =>
      sixVertexFourByFourAuditedParamVerticalRowsSecond p seam v.2 v.1 }

end
end StatMech.FrontierD
