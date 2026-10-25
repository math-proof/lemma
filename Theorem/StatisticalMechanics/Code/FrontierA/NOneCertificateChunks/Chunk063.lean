/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk063.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk063


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts126_checked :
    rawMomentVCounts 126 = generatedVCounts126 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts126_checked :
    rawMomentQCounts 126 = generatedQCounts126 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients126_checked :
    rawMomentStateCoefficientList 126 = generatedStateCoefficients126 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts126_checked, qCounts126_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
