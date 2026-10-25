/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk155.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk155


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts310_checked :
    rawMomentVCounts 310 = generatedVCounts310 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts310_checked :
    rawMomentQCounts 310 = generatedQCounts310 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients310_checked :
    rawMomentStateCoefficientList 310 = generatedStateCoefficients310 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts310_checked, qCounts310_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
