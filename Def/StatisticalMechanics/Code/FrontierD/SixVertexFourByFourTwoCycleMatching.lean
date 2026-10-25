/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part13


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourAuditedCoordinateTargetPair
    (c : SixVertexFourByFourAuditedCoordinates) :
    SixVertexArrows sixVertexFourByFourTorus ×
      SixVertexArrows sixVertexFourByFourTorus :=
  let p := sixVertexFourByFourAuditedCoordinateParameters c
  let columns := sixVertexFourByFourAuditedRepairColumns
    c.firstSeam c.secondSeam
  (sixVertexFourByFourAuditedParamTargetFirst p c.firstSeam columns.1,
    sixVertexFourByFourAuditedParamTargetSecond p c.secondSeam columns.2)

def SixVertexFourByFourAuditedCoordinateTargetPairValid
    (c : SixVertexFourByFourAuditedCoordinates) : Prop :=
  (sixVertexFourByFourAuditedCoordinateTargetPair c).1.IceRule /\
    (sixVertexFourByFourAuditedCoordinateTargetPair c).2.IceRule /\
    sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourAuditedCoordinateTargetPair c).1
          (svFinLast sixVertexFourByFourTorus.height_pos)) = 2 /\
    sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourAuditedCoordinateTargetPair c).2
          (svFinLast sixVertexFourByFourTorus.height_pos)) = 2

end
end StatMech.FrontierD
