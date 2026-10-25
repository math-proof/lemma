/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleMatching.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton.Part3


namespace StatMech.FrontierD

def sixVertexFourByFourAuditedMiddlePathAllowed
    (firstSeam secondSeam : Fin 4) (firstMiddle secondMiddle : Fin 16) : Prop :=
  (sixVertexFourByFourAuditedFirstTransition (sixVertexFourByFourAuditedOppositeSeam firstSeam) firstMiddle >>= fun s =>
      sixVertexFourByFourAuditedFirstTransition s secondMiddle) = some firstSeam /\
    (sixVertexFourByFourAuditedSecondTransition (sixVertexFourByFourAuditedOppositeSeam secondSeam) firstMiddle >>= fun s =>
      sixVertexFourByFourAuditedSecondTransition s secondMiddle) = some secondSeam

end StatMech.FrontierD
