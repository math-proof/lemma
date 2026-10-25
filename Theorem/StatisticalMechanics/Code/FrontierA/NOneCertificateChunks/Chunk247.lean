/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk247.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk247


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts494_checked :
    rawMomentVCounts 494 = generatedVCounts494 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts494_checked :
    rawMomentQCounts 494 = generatedQCounts494 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients494_checked :
    rawMomentStateCoefficientList 494 = generatedStateCoefficients494 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts494_checked, qCounts494_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
