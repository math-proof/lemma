/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk185.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk185


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts370_checked :
    rawMomentVCounts 370 = generatedVCounts370 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts370_checked :
    rawMomentQCounts 370 = generatedQCounts370 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients370_checked :
    rawMomentStateCoefficientList 370 = generatedStateCoefficients370 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts370_checked, qCounts370_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
