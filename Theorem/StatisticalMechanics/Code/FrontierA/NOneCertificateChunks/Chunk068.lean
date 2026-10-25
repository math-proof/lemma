/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk068.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk068


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts136_checked :
    rawMomentVCounts 136 = generatedVCounts136 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts136_checked :
    rawMomentQCounts 136 = generatedQCounts136 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients136_checked :
    rawMomentStateCoefficientList 136 = generatedStateCoefficients136 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts136_checked, qCounts136_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
