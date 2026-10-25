/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk035.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk035


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts70_checked :
    rawMomentVCounts 70 = generatedVCounts70 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts70_checked :
    rawMomentQCounts 70 = generatedQCounts70 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients70_checked :
    rawMomentStateCoefficientList 70 = generatedStateCoefficients70 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts70_checked, qCounts70_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
