/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleMatching.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton.Part5


namespace StatMech.FrontierD

theorem sixVertexFourByFourAudited_firstPath_iff_cross
    (seam : Fin 4) (firstMiddle secondMiddle : Fin 16) :
    (sixVertexFourByFourAuditedFirstTransition (sixVertexFourByFourAuditedOppositeSeam seam) firstMiddle >>= fun s =>
        sixVertexFourByFourAuditedFirstTransition s secondMiddle) = some seam <->
      sixVertexFourByFourAuditedFirstCrossB seam firstMiddle secondMiddle = true := by
  fin_cases seam <;> decide +revert

theorem sixVertexFourByFourAudited_secondPath_iff_cross
    (seam : Fin 4) (firstMiddle secondMiddle : Fin 16) :
    (sixVertexFourByFourAuditedSecondTransition (sixVertexFourByFourAuditedOppositeSeam seam) firstMiddle >>= fun s =>
        sixVertexFourByFourAuditedSecondTransition s secondMiddle) = some seam <->
      sixVertexFourByFourAuditedSecondCrossB seam firstMiddle secondMiddle = true := by
  fin_cases seam <;> decide +revert

theorem sixVertexFourByFourAudited_crosses_iff_template
    (firstSeam secondSeam : Fin 4) (firstMiddle secondMiddle : Fin 16) :
    sixVertexFourByFourAuditedFirstCrossB firstSeam firstMiddle secondMiddle = true /\
        sixVertexFourByFourAuditedSecondCrossB secondSeam firstMiddle secondMiddle = true <->
      exists middle : Fin 8,
        (firstMiddle, secondMiddle) =
          sixVertexFourByFourAuditedMiddlePair
            firstSeam secondSeam middle := by
  fin_cases firstSeam <;> fin_cases secondSeam <;> decide +revert

theorem sixVertexFourByFourAudited_middlePathAllowed_iff_template
    (firstSeam secondSeam : Fin 4) (firstMiddle secondMiddle : Fin 16) :
    sixVertexFourByFourAuditedMiddlePathAllowed firstSeam secondSeam firstMiddle secondMiddle <->
      exists middle : Fin 8,
        (firstMiddle, secondMiddle) =
          sixVertexFourByFourAuditedMiddlePair
            firstSeam secondSeam middle := by
  unfold sixVertexFourByFourAuditedMiddlePathAllowed
  rw [sixVertexFourByFourAudited_firstPath_iff_cross, sixVertexFourByFourAudited_secondPath_iff_cross]
  exact sixVertexFourByFourAudited_crosses_iff_template _ _ _ _

end StatMech.FrontierD
