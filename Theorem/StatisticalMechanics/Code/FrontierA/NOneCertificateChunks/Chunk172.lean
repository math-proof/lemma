/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk172.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk172


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts344_checked :
    rawMomentVCounts 344 = generatedVCounts344 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts344_checked :
    rawMomentQCounts 344 = generatedQCounts344 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients344_checked :
    rawMomentStateCoefficientList 344 = generatedStateCoefficients344 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts344_checked, qCounts344_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
