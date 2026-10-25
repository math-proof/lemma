/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk138.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk138


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts276_checked :
    rawMomentVCounts 276 = generatedVCounts276 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts276_checked :
    rawMomentQCounts 276 = generatedQCounts276 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients276_checked :
    rawMomentStateCoefficientList 276 = generatedStateCoefficients276 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts276_checked, qCounts276_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
