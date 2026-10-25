/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk045.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk045


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts90_checked :
    rawMomentVCounts 90 = generatedVCounts90 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts90_checked :
    rawMomentQCounts 90 = generatedQCounts90 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients90_checked :
    rawMomentStateCoefficientList 90 = generatedStateCoefficients90 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts90_checked, qCounts90_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
