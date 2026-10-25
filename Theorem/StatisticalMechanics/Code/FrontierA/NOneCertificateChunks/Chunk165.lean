/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk165.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk165


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts330_checked :
    rawMomentVCounts 330 = generatedVCounts330 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts330_checked :
    rawMomentQCounts 330 = generatedQCounts330 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients330_checked :
    rawMomentStateCoefficientList 330 = generatedStateCoefficients330 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts330_checked, qCounts330_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
