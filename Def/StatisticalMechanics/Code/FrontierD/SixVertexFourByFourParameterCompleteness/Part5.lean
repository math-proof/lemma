module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourParameterCompleteness.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

def sixVertexFourByFourAuditedValidParameterSourcePair
    (p : SixVertexFourByFourAuditedValidParameter) :
    SixVertexArrows sixVertexFourByFourTorus ×
      SixVertexArrows sixVertexFourByFourTorus :=
  sixVertexFourByFourAuditedParameterSourcePair p.1

noncomputable def sixVertexFourByFourAuditedValidParameterTargetPair
    (p : SixVertexFourByFourAuditedValidParameter) :
    SixVertexArrows sixVertexFourByFourTorus ×
      SixVertexArrows sixVertexFourByFourTorus :=
  sixVertexFourByFourAuditedCoordinateTargetPair
    (sixVertexFourByFourAuditedValidParameterCoordinate p)

end StatMech.FrontierD
