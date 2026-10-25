/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk166.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk166


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts332_checked :
    rawMomentVCounts 332 = generatedVCounts332 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts332_checked :
    rawMomentQCounts 332 = generatedQCounts332 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients332_checked :
    rawMomentStateCoefficientList 332 = generatedStateCoefficients332 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts332_checked, qCounts332_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
