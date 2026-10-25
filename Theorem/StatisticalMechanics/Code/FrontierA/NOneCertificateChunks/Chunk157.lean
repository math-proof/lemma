/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk157.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk157


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts314_checked :
    rawMomentVCounts 314 = generatedVCounts314 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts314_checked :
    rawMomentQCounts 314 = generatedQCounts314 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients314_checked :
    rawMomentStateCoefficientList 314 = generatedStateCoefficients314 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts314_checked, qCounts314_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
