/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk088.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk088


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts176_checked :
    rawMomentVCounts 176 = generatedVCounts176 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts176_checked :
    rawMomentQCounts 176 = generatedQCounts176 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients176_checked :
    rawMomentStateCoefficientList 176 = generatedStateCoefficients176 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts176_checked, qCounts176_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
