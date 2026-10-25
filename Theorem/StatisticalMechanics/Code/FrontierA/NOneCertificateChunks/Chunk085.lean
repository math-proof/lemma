/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk085.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk085


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts170_checked :
    rawMomentVCounts 170 = generatedVCounts170 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts170_checked :
    rawMomentQCounts 170 = generatedQCounts170 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients170_checked :
    rawMomentStateCoefficientList 170 = generatedStateCoefficients170 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts170_checked, qCounts170_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
