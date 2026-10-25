/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourParameterCompleteness.Part3


namespace StatMech.FrontierD

noncomputable def sixVertexFourByFourAuditedValidParameterSet :
    Finset SixVertexFourByFourAuditedHorizontalParameters := by
  classical
  exact Finset.univ.filter SixVertexFourByFourAuditedParameterValid

end StatMech.FrontierD
