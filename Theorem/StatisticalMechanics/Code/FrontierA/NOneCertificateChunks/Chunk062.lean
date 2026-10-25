/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk062.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk062


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts124_checked :
    rawMomentVCounts 124 = generatedVCounts124 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts124_checked :
    rawMomentQCounts 124 = generatedQCounts124 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients124_checked :
    rawMomentStateCoefficientList 124 = generatedStateCoefficients124 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts124_checked, qCounts124_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
