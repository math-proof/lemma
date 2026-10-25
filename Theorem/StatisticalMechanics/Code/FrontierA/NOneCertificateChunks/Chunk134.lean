/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk134.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk134


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts268_checked :
    rawMomentVCounts 268 = generatedVCounts268 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts268_checked :
    rawMomentQCounts 268 = generatedQCounts268 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients268_checked :
    rawMomentStateCoefficientList 268 = generatedStateCoefficients268 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts268_checked, qCounts268_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
