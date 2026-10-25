/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk216.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk216


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts432_checked :
    rawMomentVCounts 432 = generatedVCounts432 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts432_checked :
    rawMomentQCounts 432 = generatedQCounts432 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients432_checked :
    rawMomentStateCoefficientList 432 = generatedStateCoefficients432 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts432_checked, qCounts432_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
