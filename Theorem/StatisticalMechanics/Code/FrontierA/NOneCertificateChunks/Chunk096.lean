/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk096.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk096


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts192_checked :
    rawMomentVCounts 192 = generatedVCounts192 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts192_checked :
    rawMomentQCounts 192 = generatedQCounts192 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients192_checked :
    rawMomentStateCoefficientList 192 = generatedStateCoefficients192 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts192_checked, qCounts192_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
