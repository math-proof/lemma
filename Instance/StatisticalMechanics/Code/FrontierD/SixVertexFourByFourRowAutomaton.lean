/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleMatching.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton.Part4


namespace StatMech.FrontierD

instance sixVertexFourByFourAuditedMiddlePathAllowedDecidable firstSeam secondSeam
    firstMiddle secondMiddle :
    Decidable (sixVertexFourByFourAuditedMiddlePathAllowed firstSeam secondSeam
      firstMiddle secondMiddle) := by
  unfold sixVertexFourByFourAuditedMiddlePathAllowed
  infer_instance

end StatMech.FrontierD
