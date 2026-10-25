/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk190.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk190.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts381_checked :
    rawMomentVCounts 381 = generatedVCounts381 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts381_checked :
    rawMomentQCounts 381 = generatedQCounts381 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients381_checked :
    rawMomentStateCoefficientList 381 = generatedStateCoefficients381 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts381_checked, qCounts381_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
