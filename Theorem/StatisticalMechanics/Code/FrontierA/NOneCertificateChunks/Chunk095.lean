/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk095.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk095


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts190_checked :
    rawMomentVCounts 190 = generatedVCounts190 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts190_checked :
    rawMomentQCounts 190 = generatedQCounts190 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients190_checked :
    rawMomentStateCoefficientList 190 = generatedStateCoefficients190 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts190_checked, qCounts190_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
