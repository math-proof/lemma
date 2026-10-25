/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk205.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk205


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts410_checked :
    rawMomentVCounts 410 = generatedVCounts410 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts410_checked :
    rawMomentQCounts 410 = generatedQCounts410 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients410_checked :
    rawMomentStateCoefficientList 410 = generatedStateCoefficients410 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts410_checked, qCounts410_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
