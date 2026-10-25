/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk253.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk253


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts506_checked :
    rawMomentVCounts 506 = generatedVCounts506 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts506_checked :
    rawMomentQCounts 506 = generatedQCounts506 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients506_checked :
    rawMomentStateCoefficientList 506 = generatedStateCoefficients506 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts506_checked, qCounts506_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
