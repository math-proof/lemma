/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk211.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk211


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts422_checked :
    rawMomentVCounts 422 = generatedVCounts422 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts422_checked :
    rawMomentQCounts 422 = generatedQCounts422 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients422_checked :
    rawMomentStateCoefficientList 422 = generatedStateCoefficients422 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts422_checked, qCounts422_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
