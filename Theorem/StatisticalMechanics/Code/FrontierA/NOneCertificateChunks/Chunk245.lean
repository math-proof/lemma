/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk245.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk245


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts490_checked :
    rawMomentVCounts 490 = generatedVCounts490 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts490_checked :
    rawMomentQCounts 490 = generatedQCounts490 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients490_checked :
    rawMomentStateCoefficientList 490 = generatedStateCoefficients490 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts490_checked, qCounts490_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
