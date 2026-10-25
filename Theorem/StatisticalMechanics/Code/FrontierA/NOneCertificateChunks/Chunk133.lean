/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk133.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk133


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts266_checked :
    rawMomentVCounts 266 = generatedVCounts266 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts266_checked :
    rawMomentQCounts 266 = generatedQCounts266 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients266_checked :
    rawMomentStateCoefficientList 266 = generatedStateCoefficients266 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts266_checked, qCounts266_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
