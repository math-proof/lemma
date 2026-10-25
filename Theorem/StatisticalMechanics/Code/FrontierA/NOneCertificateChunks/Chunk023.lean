/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk023.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk023


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts46_checked :
    rawMomentVCounts 46 = generatedVCounts46 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts46_checked :
    rawMomentQCounts 46 = generatedQCounts46 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients46_checked :
    rawMomentStateCoefficientList 46 = generatedStateCoefficients46 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts46_checked, qCounts46_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
