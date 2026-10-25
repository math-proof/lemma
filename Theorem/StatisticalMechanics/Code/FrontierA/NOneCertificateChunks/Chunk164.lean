/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk164.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk164


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts328_checked :
    rawMomentVCounts 328 = generatedVCounts328 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts328_checked :
    rawMomentQCounts 328 = generatedQCounts328 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients328_checked :
    rawMomentStateCoefficientList 328 = generatedStateCoefficients328 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts328_checked, qCounts328_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
