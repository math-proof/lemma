/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourTwoCycleMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleFibre.Part13
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleMatching


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourAuditedCoordinateHorizontalRows
    (c : SixVertexFourByFourAuditedCoordinates) :
    (Fin 4 -> SixVertexRow 4) × (Fin 4 -> SixVertexRow 4) :=
  let p := sixVertexFourByFourAuditedCoordinateParameters c
  (sixVertexFourByFourAuditedParamHorizontalRowsFirst p,
    sixVertexFourByFourAuditedParamHorizontalRowsSecond p)

end
end StatMech.FrontierD
