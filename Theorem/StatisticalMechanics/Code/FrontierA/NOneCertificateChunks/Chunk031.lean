/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk031.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk031


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts62_checked :
    rawMomentVCounts 62 = generatedVCounts62 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts62_checked :
    rawMomentQCounts 62 = generatedQCounts62 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients62_checked :
    rawMomentStateCoefficientList 62 = generatedStateCoefficients62 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts62_checked, qCounts62_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
