/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk140.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk140


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts280_checked :
    rawMomentVCounts 280 = generatedVCounts280 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts280_checked :
    rawMomentQCounts 280 = generatedQCounts280 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients280_checked :
    rawMomentStateCoefficientList 280 = generatedStateCoefficients280 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts280_checked, qCounts280_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
