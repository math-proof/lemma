/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk241.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk241


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts482_checked :
    rawMomentVCounts 482 = generatedVCounts482 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts482_checked :
    rawMomentQCounts 482 = generatedQCounts482 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients482_checked :
    rawMomentStateCoefficientList 482 = generatedStateCoefficients482 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts482_checked, qCounts482_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
