/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk060.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk060


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts120_checked :
    rawMomentVCounts 120 = generatedVCounts120 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts120_checked :
    rawMomentQCounts 120 = generatedQCounts120 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients120_checked :
    rawMomentStateCoefficientList 120 = generatedStateCoefficients120 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts120_checked, qCounts120_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
