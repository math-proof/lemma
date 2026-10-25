/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk082.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk082


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts164_checked :
    rawMomentVCounts 164 = generatedVCounts164 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts164_checked :
    rawMomentQCounts 164 = generatedQCounts164 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients164_checked :
    rawMomentStateCoefficientList 164 = generatedStateCoefficients164 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts164_checked, qCounts164_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
