/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk007.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk007


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts14_checked :
    rawMomentVCounts 14 = generatedVCounts14 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts14_checked :
    rawMomentQCounts 14 = generatedQCounts14 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients14_checked :
    rawMomentStateCoefficientList 14 = generatedStateCoefficients14 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts14_checked, qCounts14_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
