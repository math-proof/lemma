/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk243.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk243


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts486_checked :
    rawMomentVCounts 486 = generatedVCounts486 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts486_checked :
    rawMomentQCounts 486 = generatedQCounts486 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients486_checked :
    rawMomentStateCoefficientList 486 = generatedStateCoefficients486 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts486_checked, qCounts486_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
