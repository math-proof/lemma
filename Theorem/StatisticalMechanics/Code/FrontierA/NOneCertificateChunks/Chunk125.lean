/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk125.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk125


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts250_checked :
    rawMomentVCounts 250 = generatedVCounts250 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts250_checked :
    rawMomentQCounts 250 = generatedQCounts250 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients250_checked :
    rawMomentStateCoefficientList 250 = generatedStateCoefficients250 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts250_checked, qCounts250_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
