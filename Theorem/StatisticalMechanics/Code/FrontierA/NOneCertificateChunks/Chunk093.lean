/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk093.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk093


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts186_checked :
    rawMomentVCounts 186 = generatedVCounts186 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts186_checked :
    rawMomentQCounts 186 = generatedQCounts186 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients186_checked :
    rawMomentStateCoefficientList 186 = generatedStateCoefficients186 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts186_checked, qCounts186_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
