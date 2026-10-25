/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk070.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk070


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts140_checked :
    rawMomentVCounts 140 = generatedVCounts140 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts140_checked :
    rawMomentQCounts 140 = generatedQCounts140 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients140_checked :
    rawMomentStateCoefficientList 140 = generatedStateCoefficients140 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts140_checked, qCounts140_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
