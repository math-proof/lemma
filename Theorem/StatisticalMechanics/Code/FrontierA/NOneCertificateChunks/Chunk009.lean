/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk009.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk009


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts18_checked :
    rawMomentVCounts 18 = generatedVCounts18 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts18_checked :
    rawMomentQCounts 18 = generatedQCounts18 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients18_checked :
    rawMomentStateCoefficientList 18 = generatedStateCoefficients18 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts18_checked, qCounts18_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
