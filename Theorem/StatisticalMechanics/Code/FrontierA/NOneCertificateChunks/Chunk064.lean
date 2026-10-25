/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk064.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk064


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts128_checked :
    rawMomentVCounts 128 = generatedVCounts128 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts128_checked :
    rawMomentQCounts 128 = generatedQCounts128 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients128_checked :
    rawMomentStateCoefficientList 128 = generatedStateCoefficients128 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts128_checked, qCounts128_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
