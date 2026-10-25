/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneStateSumBlocks/Block181.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneStateSumBlocks.Block181


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in


theorem directStateBlock181_checked :
    rawMomentDirectBlock 362 2 =
      rawMomentPolyOfCoefficientList generatedDirectCoefficientBlock181 := by
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
