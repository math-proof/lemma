/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleMatching.Part3
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton


namespace StatMech.FrontierD

def sixVertexFourByFourAuditedFirstInnerB (seam : Fin 4) (middle : Fin 16) : Bool :=
  decide (middle = sixVertexFourByFourAuditedMiddleB seam ||
    middle = sixVertexFourByFourAuditedMiddleBNext seam)

def sixVertexFourByFourAuditedFirstOuterB (middle : Fin 16) : Bool :=
  decide (middle.val < 4 || 12 <= middle.val)

def sixVertexFourByFourAuditedSecondInnerB (seam : Fin 4) (middle : Fin 16) : Bool :=
  decide (middle = sixVertexFourByFourAuditedMiddleA seam ||
    middle = sixVertexFourByFourAuditedMiddleC seam)

def sixVertexFourByFourAuditedSecondOuterB (middle : Fin 16) : Bool :=
  decide (4 <= middle.val && middle.val < 12)

def sixVertexFourByFourAuditedFirstCrossB
    (seam : Fin 4) (firstMiddle secondMiddle : Fin 16) : Bool :=
  (sixVertexFourByFourAuditedFirstOuterB firstMiddle && sixVertexFourByFourAuditedFirstInnerB seam secondMiddle) ||
    (sixVertexFourByFourAuditedFirstInnerB seam firstMiddle && sixVertexFourByFourAuditedFirstOuterB secondMiddle)

def sixVertexFourByFourAuditedSecondCrossB
    (seam : Fin 4) (firstMiddle secondMiddle : Fin 16) : Bool :=
  (sixVertexFourByFourAuditedSecondInnerB seam firstMiddle && sixVertexFourByFourAuditedSecondOuterB secondMiddle) ||
    (sixVertexFourByFourAuditedSecondOuterB firstMiddle && sixVertexFourByFourAuditedSecondInnerB seam secondMiddle)

end StatMech.FrontierD
