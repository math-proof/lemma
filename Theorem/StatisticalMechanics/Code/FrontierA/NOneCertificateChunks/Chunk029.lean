/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk029.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk029


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts58_checked :
    rawMomentVCounts 58 = generatedVCounts58 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts58_checked :
    rawMomentQCounts 58 = generatedQCounts58 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients58_checked :
    rawMomentStateCoefficientList 58 = generatedStateCoefficients58 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts58_checked, qCounts58_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
