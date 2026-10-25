/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk145.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk145


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts290_checked :
    rawMomentVCounts 290 = generatedVCounts290 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts290_checked :
    rawMomentQCounts 290 = generatedQCounts290 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients290_checked :
    rawMomentStateCoefficientList 290 = generatedStateCoefficients290 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts290_checked, qCounts290_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
