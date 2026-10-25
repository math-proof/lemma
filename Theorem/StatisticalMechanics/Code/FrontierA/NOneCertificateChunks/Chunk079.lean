/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk079.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk079


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts158_checked :
    rawMomentVCounts 158 = generatedVCounts158 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts158_checked :
    rawMomentQCounts 158 = generatedQCounts158 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients158_checked :
    rawMomentStateCoefficientList 158 = generatedStateCoefficients158 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts158_checked, qCounts158_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
