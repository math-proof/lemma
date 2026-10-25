/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk174.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk174


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts348_checked :
    rawMomentVCounts 348 = generatedVCounts348 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts348_checked :
    rawMomentQCounts 348 = generatedQCounts348 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients348_checked :
    rawMomentStateCoefficientList 348 = generatedStateCoefficients348 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts348_checked, qCounts348_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
