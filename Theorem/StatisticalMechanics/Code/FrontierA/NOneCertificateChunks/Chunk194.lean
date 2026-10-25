/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk194.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk194


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts388_checked :
    rawMomentVCounts 388 = generatedVCounts388 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts388_checked :
    rawMomentQCounts 388 = generatedQCounts388 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients388_checked :
    rawMomentStateCoefficientList 388 = generatedStateCoefficients388 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts388_checked, qCounts388_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
