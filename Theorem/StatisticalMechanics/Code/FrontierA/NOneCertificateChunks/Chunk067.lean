/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk067.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk067


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts134_checked :
    rawMomentVCounts 134 = generatedVCounts134 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts134_checked :
    rawMomentQCounts 134 = generatedQCounts134 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients134_checked :
    rawMomentStateCoefficientList 134 = generatedStateCoefficients134 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts134_checked, qCounts134_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
