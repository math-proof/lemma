/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk199.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk199


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts398_checked :
    rawMomentVCounts 398 = generatedVCounts398 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts398_checked :
    rawMomentQCounts 398 = generatedQCounts398 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients398_checked :
    rawMomentStateCoefficientList 398 = generatedStateCoefficients398 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts398_checked, qCounts398_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
