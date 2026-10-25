/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk034.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk034


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts68_checked :
    rawMomentVCounts 68 = generatedVCounts68 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts68_checked :
    rawMomentQCounts 68 = generatedQCounts68 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients68_checked :
    rawMomentStateCoefficientList 68 = generatedStateCoefficients68 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts68_checked, qCounts68_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
