/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourParameterCompleteness.Part2


namespace StatMech.FrontierD

def sixVertexFourByFourAuditedParameterSourcePair
    (p : SixVertexFourByFourAuditedHorizontalParameters) :
    SixVertexArrows sixVertexFourByFourTorus ×
      SixVertexArrows sixVertexFourByFourTorus :=
  let seams := sixVertexFourByFourAuditedDecodedSeams p.1
  (sixVertexFourByFourAuditedParamSourceFirst p seams.1,
    sixVertexFourByFourAuditedParamSourceSecond p seams.2)

def SixVertexFourByFourAuditedParameterValid
    (p : SixVertexFourByFourAuditedHorizontalParameters) : Prop :=
  (sixVertexFourByFourAuditedParameterSourcePair p).1.IceRule /\
    (sixVertexFourByFourAuditedParameterSourcePair p).2.IceRule /\
    sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourAuditedParameterSourcePair p).1
          (svFinLast sixVertexFourByFourTorus.height_pos)) = 1 /\
    sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourAuditedParameterSourcePair p).2
          (svFinLast sixVertexFourByFourTorus.height_pos)) = 3

end StatMech.FrontierD
