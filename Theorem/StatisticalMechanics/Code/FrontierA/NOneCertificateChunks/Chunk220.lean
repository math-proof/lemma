/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk220.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk220


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts440_checked :
    rawMomentVCounts 440 = generatedVCounts440 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts440_checked :
    rawMomentQCounts 440 = generatedQCounts440 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients440_checked :
    rawMomentStateCoefficientList 440 = generatedStateCoefficients440 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts440_checked, qCounts440_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
