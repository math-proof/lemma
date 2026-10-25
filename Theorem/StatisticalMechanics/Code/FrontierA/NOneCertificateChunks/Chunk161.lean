/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk161.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk161


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts322_checked :
    rawMomentVCounts 322 = generatedVCounts322 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts322_checked :
    rawMomentQCounts 322 = generatedQCounts322 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients322_checked :
    rawMomentStateCoefficientList 322 = generatedStateCoefficients322 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts322_checked, qCounts322_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
