/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk221.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk221


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts442_checked :
    rawMomentVCounts 442 = generatedVCounts442 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts442_checked :
    rawMomentQCounts 442 = generatedQCounts442 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients442_checked :
    rawMomentStateCoefficientList 442 = generatedStateCoefficients442 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts442_checked, qCounts442_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
