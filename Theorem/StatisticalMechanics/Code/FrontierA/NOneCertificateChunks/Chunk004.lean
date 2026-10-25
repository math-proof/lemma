/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk004.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk004


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts8_checked :
    rawMomentVCounts 8 = generatedVCounts8 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts8_checked :
    rawMomentQCounts 8 = generatedQCounts8 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients8_checked :
    rawMomentStateCoefficientList 8 = generatedStateCoefficients8 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts8_checked, qCounts8_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
