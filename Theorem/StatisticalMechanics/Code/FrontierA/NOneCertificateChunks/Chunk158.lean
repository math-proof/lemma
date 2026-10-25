/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk158.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk158


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts316_checked :
    rawMomentVCounts 316 = generatedVCounts316 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts316_checked :
    rawMomentQCounts 316 = generatedQCounts316 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients316_checked :
    rawMomentStateCoefficientList 316 = generatedStateCoefficients316 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts316_checked, qCounts316_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
