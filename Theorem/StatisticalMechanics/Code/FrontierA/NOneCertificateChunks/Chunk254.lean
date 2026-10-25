/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk254.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk254


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts508_checked :
    rawMomentVCounts 508 = generatedVCounts508 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts508_checked :
    rawMomentQCounts 508 = generatedQCounts508 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients508_checked :
    rawMomentStateCoefficientList 508 = generatedStateCoefficients508 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts508_checked, qCounts508_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
