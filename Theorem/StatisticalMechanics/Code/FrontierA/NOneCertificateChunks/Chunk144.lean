/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk144.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk144


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts288_checked :
    rawMomentVCounts 288 = generatedVCounts288 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts288_checked :
    rawMomentQCounts 288 = generatedQCounts288 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients288_checked :
    rawMomentStateCoefficientList 288 = generatedStateCoefficients288 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts288_checked, qCounts288_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
