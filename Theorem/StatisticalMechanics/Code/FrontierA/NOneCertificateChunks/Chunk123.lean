/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk123.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk123


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts246_checked :
    rawMomentVCounts 246 = generatedVCounts246 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts246_checked :
    rawMomentQCounts 246 = generatedQCounts246 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients246_checked :
    rawMomentStateCoefficientList 246 = generatedStateCoefficients246 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts246_checked, qCounts246_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
