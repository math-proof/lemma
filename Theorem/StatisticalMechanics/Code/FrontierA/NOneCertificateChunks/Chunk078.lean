/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk078.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk078


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts156_checked :
    rawMomentVCounts 156 = generatedVCounts156 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts156_checked :
    rawMomentQCounts 156 = generatedQCounts156 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients156_checked :
    rawMomentStateCoefficientList 156 = generatedStateCoefficients156 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts156_checked, qCounts156_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
