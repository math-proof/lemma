/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk189.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk189


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts378_checked :
    rawMomentVCounts 378 = generatedVCounts378 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts378_checked :
    rawMomentQCounts 378 = generatedQCounts378 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients378_checked :
    rawMomentStateCoefficientList 378 = generatedStateCoefficients378 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts378_checked, qCounts378_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
