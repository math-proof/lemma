/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk071.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk071


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts142_checked :
    rawMomentVCounts 142 = generatedVCounts142 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts142_checked :
    rawMomentQCounts 142 = generatedQCounts142 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients142_checked :
    rawMomentStateCoefficientList 142 = generatedStateCoefficients142 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts142_checked, qCounts142_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
