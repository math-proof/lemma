/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk135.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk135


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts270_checked :
    rawMomentVCounts 270 = generatedVCounts270 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts270_checked :
    rawMomentQCounts 270 = generatedQCounts270 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients270_checked :
    rawMomentStateCoefficientList 270 = generatedStateCoefficients270 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts270_checked, qCounts270_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
