/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk185.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk185.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts371_checked :
    rawMomentVCounts 371 = generatedVCounts371 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts371_checked :
    rawMomentQCounts 371 = generatedQCounts371 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients371_checked :
    rawMomentStateCoefficientList 371 = generatedStateCoefficients371 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts371_checked, qCounts371_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
