/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk000.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk000


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts0_checked :
    rawMomentVCounts 0 = generatedVCounts0 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts0_checked :
    rawMomentQCounts 0 = generatedQCounts0 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients0_checked :
    rawMomentStateCoefficientList 0 = generatedStateCoefficients0 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts0_checked, qCounts0_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
