/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk191.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk191


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts382_checked :
    rawMomentVCounts 382 = generatedVCounts382 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts382_checked :
    rawMomentQCounts 382 = generatedQCounts382 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients382_checked :
    rawMomentStateCoefficientList 382 = generatedStateCoefficients382 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts382_checked, qCounts382_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
