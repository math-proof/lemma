/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk249.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk249


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts498_checked :
    rawMomentVCounts 498 = generatedVCounts498 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts498_checked :
    rawMomentQCounts 498 = generatedQCounts498 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients498_checked :
    rawMomentStateCoefficientList 498 = generatedStateCoefficients498 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts498_checked, qCounts498_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
