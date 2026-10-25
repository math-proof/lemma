/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk219.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk219


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts438_checked :
    rawMomentVCounts 438 = generatedVCounts438 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts438_checked :
    rawMomentQCounts 438 = generatedQCounts438 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients438_checked :
    rawMomentStateCoefficientList 438 = generatedStateCoefficients438 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts438_checked, qCounts438_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
