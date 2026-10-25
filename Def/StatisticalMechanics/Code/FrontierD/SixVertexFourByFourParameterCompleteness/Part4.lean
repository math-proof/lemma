/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourParameterCompleteness.Part4


namespace StatMech.FrontierD

def SixVertexFourByFourAuditedValidParameter :=
  {p : SixVertexFourByFourAuditedHorizontalParameters //
    SixVertexFourByFourAuditedParameterValid p}

noncomputable def sixVertexFourByFourAuditedValidParameterCoordinate
    (p : SixVertexFourByFourAuditedValidParameter) :
    SixVertexFourByFourAuditedCoordinates :=
  Classical.choose
    (sixVertexFourByFourAudited_parameterValid_uniqueCoordinate p.1 p.2).exists

end StatMech.FrontierD
