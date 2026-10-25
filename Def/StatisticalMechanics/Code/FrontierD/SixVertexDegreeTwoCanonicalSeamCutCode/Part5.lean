/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalSeamCutCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalSeamCutCode.Part4


namespace StatMech.FrontierD

noncomputable section

def SixVertexCanonicalSameStrandCutCode.decodeSeamPair
    {T : EvenTorus} (code : SixVertexCanonicalSameStrandCutCode T) :
    SixVertexTorusEdge T × SixVertexTorusEdge T :=
  (sixVertexDecodeVerticalPhysicalEdge
      (code.arcs.first.edge code.arcs.first.firstIndex).physical,
    sixVertexDecodeVerticalPhysicalEdge
      (code.arcs.second.edge code.arcs.second.firstIndex).physical)


end
end StatMech.FrontierD
