/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk016.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk016


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts32_checked :
    rawMomentVCounts 32 = generatedVCounts32 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts32_checked :
    rawMomentQCounts 32 = generatedQCounts32 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients32_checked :
    rawMomentStateCoefficientList 32 = generatedStateCoefficients32 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts32_checked, qCounts32_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
