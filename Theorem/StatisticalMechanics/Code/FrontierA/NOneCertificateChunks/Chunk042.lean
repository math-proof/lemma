/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk042.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk042


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts84_checked :
    rawMomentVCounts 84 = generatedVCounts84 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts84_checked :
    rawMomentQCounts 84 = generatedQCounts84 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients84_checked :
    rawMomentStateCoefficientList 84 = generatedStateCoefficients84 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts84_checked, qCounts84_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
