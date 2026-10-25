/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk090.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk090


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts180_checked :
    rawMomentVCounts 180 = generatedVCounts180 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts180_checked :
    rawMomentQCounts 180 = generatedQCounts180 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients180_checked :
    rawMomentStateCoefficientList 180 = generatedStateCoefficients180 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts180_checked, qCounts180_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
