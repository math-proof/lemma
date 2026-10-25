/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk196.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk196


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts392_checked :
    rawMomentVCounts 392 = generatedVCounts392 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts392_checked :
    rawMomentQCounts 392 = generatedQCounts392 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients392_checked :
    rawMomentStateCoefficientList 392 = generatedStateCoefficients392 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts392_checked, qCounts392_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
