/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk170.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk170


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts340_checked :
    rawMomentVCounts 340 = generatedVCounts340 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts340_checked :
    rawMomentQCounts 340 = generatedQCounts340 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients340_checked :
    rawMomentStateCoefficientList 340 = generatedStateCoefficients340 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts340_checked, qCounts340_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
