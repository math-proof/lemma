/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk224.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk224


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts448_checked :
    rawMomentVCounts 448 = generatedVCounts448 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts448_checked :
    rawMomentQCounts 448 = generatedQCounts448 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients448_checked :
    rawMomentStateCoefficientList 448 = generatedStateCoefficients448 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts448_checked, qCounts448_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
