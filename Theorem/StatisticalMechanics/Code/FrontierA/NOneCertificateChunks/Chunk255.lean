/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk255.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk255


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts510_checked :
    rawMomentVCounts 510 = generatedVCounts510 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts510_checked :
    rawMomentQCounts 510 = generatedQCounts510 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients510_checked :
    rawMomentStateCoefficientList 510 = generatedStateCoefficients510 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts510_checked, qCounts510_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
