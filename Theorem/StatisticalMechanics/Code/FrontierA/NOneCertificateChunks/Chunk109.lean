/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk109.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk109


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts218_checked :
    rawMomentVCounts 218 = generatedVCounts218 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts218_checked :
    rawMomentQCounts 218 = generatedQCounts218 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients218_checked :
    rawMomentStateCoefficientList 218 = generatedStateCoefficients218 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts218_checked, qCounts218_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
