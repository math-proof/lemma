/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk209.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk209


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts418_checked :
    rawMomentVCounts 418 = generatedVCounts418 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts418_checked :
    rawMomentQCounts 418 = generatedQCounts418 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients418_checked :
    rawMomentStateCoefficientList 418 = generatedStateCoefficients418 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts418_checked, qCounts418_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
