/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk154.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk154


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts308_checked :
    rawMomentVCounts 308 = generatedVCounts308 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts308_checked :
    rawMomentQCounts 308 = generatedQCounts308 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients308_checked :
    rawMomentStateCoefficientList 308 = generatedStateCoefficients308 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts308_checked, qCounts308_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
