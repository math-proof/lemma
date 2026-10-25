/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourParameterCompleteness.Part4


namespace StatMech.FrontierD

theorem sixVertexFourByFourAuditedValidParameterCoordinate_spec
    (p : SixVertexFourByFourAuditedValidParameter) :
    sixVertexFourByFourAuditedCoordinateParameters
        (sixVertexFourByFourAuditedValidParameterCoordinate p) = p.1 :=
  Classical.choose_spec
    (sixVertexFourByFourAudited_parameterValid_uniqueCoordinate p.1 p.2).exists

theorem sixVertexFourByFourAuditedValidParameterCoordinate_injective :
    Function.Injective sixVertexFourByFourAuditedValidParameterCoordinate := by
  intro p q hcoordinate
  apply Subtype.ext
  rw [← sixVertexFourByFourAuditedValidParameterCoordinate_spec p,
    ← sixVertexFourByFourAuditedValidParameterCoordinate_spec q,
    hcoordinate]

end StatMech.FrontierD
